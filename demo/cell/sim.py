# One supervised run of the pick-and-place cell in MuJoCo: the plant with its non-idealities, the
# 1 kHz computed-torque controller on the nominal model, and the loop at period h whose every
# decision is the supervisor's answer on its line protocol. The run returns its event log, its
# traces and one record per move with every measured quantity next to the bound it is checked
# against. The time loop is sequential by causality (closed loop with an external supervisor);
# every per-sample quantity is computed afterwards on the whole trace at once.
import shlex
import subprocess
from pathlib import Path

import mujoco
import numpy as np

import arm

repo = Path(__file__).resolve().parents[2]
exe = repo / ".lake/build/bin/cell-supervisor"

nominal = dict(
    omega=80.0, delta=0.05, h=0.1, T=2.0, bound=25, dt=0.00025, ctrl=0.001, limit=150.0,
    coulomb=[0.0] * 3, viscous=[0.0] * 3, armature=[0.0] * 3, counts=0, cutoff=0.0, delay=False,
    payload=0.0, load_radius=0.035, fault=None, tail=1.0,
)


class Exe:
    """The supervisor executable on its line protocol; every line sent and every answer is kept."""

    kind = "exe"

    def __init__(self, cmd=str(exe)):
        self.p = subprocess.Popen(shlex.split(cmd), cwd=repo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
        self.transcript = []

    def send(self, line):
        self.p.stdin.write(line + "\n")
        self.p.stdin.flush()
        ans = self.p.stdout.readline().strip()
        self.transcript.append((line, ans))
        return ans

    def close(self):
        self.p.stdin.close()
        self.p.wait()


def supervisor():
    return Exe()


def fmt(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def parse(ans):
    word, _, rest = ans.partition(" ")
    st = dict(kv.split("=", 1) for kv in rest.split()) if word == "ok" else {}
    return word, st


def build(scene, cfg):
    m = mujoco.MjModel.from_xml_string(arm.mjcf(scene, dt=cfg["dt"], limit=cfg["limit"] or 1e9))
    m.dof_armature[:] = cfg["armature"]
    m.dof_damping[:] = cfg["viscous"]
    m.dof_frictionloss[:] = cfg["coulomb"]
    return m


def run(scene, cfg, plan, sup):
    """Drive one run. `plan` is the list of waypoint names the planner requests, in order."""
    W = arm.waypoints(scene)
    cl = arm.cells(scene)
    m = build(scene, cfg)
    d = mujoco.MjData(m)
    caps = [m.geom("cap1").id, m.geom("cap2").id]
    obs = [o["name"] for o in scene["obstacles"]]
    oid = [m.geom(o).id for o in obs]
    pay = m.body("payload").id
    w, delta, T, h, ctrl = cfg["omega"], cfg["delta"], cfg["T"], cfg["h"], cfg["ctrl"]
    nsub, nper, nT = round(ctrl / cfg["dt"]), round(h / ctrl), round(T / h)
    da, va = delta, 2 * w * delta
    res = 2 * np.pi / cfg["counts"] if cfg["counts"] else 0.0
    alpha = 1 - np.exp(-2 * np.pi * cfg["cutoff"] * ctrl) if cfg["cutoff"] else 1.0

    home = scene["waypoints"][[x["role"] for x in scene["waypoints"]].index("home")]["name"]
    cells_words = " ".join(" ".join(fmt(x) for x in lo + hi) for lo, hi in cl)
    ans = sup.send(f"params {cfg['bound']} {' '.join(fmt(x) for x in W[home]['exact'])} {cells_words}")
    events = [dict(k=0, cmd="params", ans=ans.split()[0])]
    d.qpos[:] = W[home]["rad"]
    mujoco.mj_forward(m, d)

    # moves: (name_from, name_to, a, b, t0, k0); index -1 is the hold at home before the first move
    moves = []
    a = b = W[home]["rad"].copy()
    # the run starts with the rest move home -> home admitted at boundary 0, as in the loop model
    t0, cur, queue, busy, faulted, age = 0.0, home, [home] + list(plan), False, False, 0
    qprev = np.round(d.qpos / res) * res if res else d.qpos.copy()
    vf = np.zeros(3)
    tau_prev = None
    log_t, log_q, log_v, log_a, log_tau, log_mv = [], [], [], [], [], []
    ctl_tau, ctl_mv, dist, end_k, stop_at = [], [], [], None, None
    # at every boundary: k, max |measured - true| of position and velocity, and, while a busy move
    # is due, the arrival test on the measured and on the true sample
    bnd = []
    k_ctrl = 0
    while True:
        t = k_ctrl * ctrl
        q_meas = np.round(d.qpos / res) * res if res else d.qpos.copy()
        if cfg["cutoff"]:
            vf = vf + alpha * ((q_meas - qprev) / ctrl - vf)
        else:
            vf = d.qvel.copy()
        qprev = q_meas
        if k_ctrl % nper == 0:
            k = k_ctrl // nper
            if busy:
                mv = moves[-1]
                arrived = np.all(np.abs(q_meas - mv["b"]) <= da) and np.all(np.abs(vf) <= va)
                arrived_true = np.all(np.abs(d.qpos - mv["b"]) <= da) and np.all(np.abs(d.qvel) <= va)
                due = k - mv["k0"] >= nT
                bnd.append([k, np.abs(q_meas - d.qpos).max(), np.abs(vf - d.qvel).max(), due, arrived, arrived_true])
            else:
                bnd.append([k, np.abs(q_meas - d.qpos).max(), np.abs(vf - d.qvel).max(), False, False, False])
            if busy:
                if k - mv["k0"] >= nT and arrived:
                    word, st = parse(sup.send("finish"))
                    events.append(dict(k=k, cmd="finish", ans=word))
                    mv.update(k_end=k, outcome="finish", t_end=t)
                    cur = mv["to"]
                    if W[cur]["role"] == "pick":
                        m.body_mass[pay] = cfg["payload"]
                        m.body_inertia[pay] = 0.4 * cfg["payload"] * cfg["load_radius"]**2 + 1e-12
                    if W[cur]["role"] == "place":
                        m.body_mass[pay], m.body_inertia[pay] = 1e-9, 1e-12
                elif age == cfg["bound"]:
                    word, st = parse(sup.send("timeout"))
                    events.append(dict(k=k, cmd="timeout", ans=word))
                    mv.update(k_end=k, outcome="timeout", t_end=t)
                    # protective stop: hold the measured configuration
                    a = b = q_meas.copy()
                    t0 = t
                else:
                    word, st = parse(sup.send("tick"))
                    events.append(dict(k=k, cmd="tick", ans=word))
                busy, faulted, age = st["busy"] == "true", st["faulted"] == "true", int(st["age"])
            elif not faulted:
                # idle: forward requests, reject the unlinked ones (a blocked admit leaves the state
                # unchanged), and admit the first linked one; no admission at a boundary that
                # already had its policy action (finish or timeout above)
                while queue:
                    name = queue[0]
                    wd = " ".join(fmt(x) for x in W[name]["exact"])
                    sup.send(f"request {wd}")
                    ans = sup.send(f"admit {wd}")
                    word, st2 = parse(ans)
                    if ans == "blocked not-linked":
                        word, st2 = parse(sup.send(f"reject {wd}"))
                        events.append(dict(k=k, cmd="reject", target=name, ans=word))
                        queue.pop(0)
                        continue
                    events.append(dict(k=k, cmd="admit", target=name, ans=ans if word != "ok" else "ok"))
                    if word == "ok":
                        queue.pop(0)
                        a, b, t0 = W[cur]["rad"].copy(), W[name]["rad"].copy(), t
                        moves.append(dict(frm=cur, to=name, a=a, b=b, t0=t, k0=k, k_end=None, outcome=None))
                        busy, faulted, age = st2["busy"] == "true", st2["faulted"] == "true", int(st2["age"])
                    break
            else:
                # faulted: the protective stop admits nothing; the harness tries once and records the answer
                if queue:
                    name = queue.pop(0)
                    wd = " ".join(fmt(x) for x in W[name]["exact"])
                    sup.send(f"request {wd}")
                    ans = sup.send(f"admit {wd}")
                    events.append(dict(k=k, cmd="admit", target=name, ans=ans))
                    queue = []
            if stop_at is None and not busy and (not queue or faulted):
                stop_at = k + round(cfg["tail"] / h)
            if stop_at is not None and k >= stop_at:
                break
        f = cfg["fault"]
        if f and len(moves) > f["move"] and t >= moves[f["move"]]["t0"] + f["frac"] * T and m.dof_frictionloss[f["joint"]] < f["torque"]:
            m.dof_frictionloss[f["joint"]] = f["torque"]
            events.append(dict(k=k_ctrl / nper, cmd="fault", joint=f["joint"]))
        r, rd, rdd = arm.reference(a, b, t0, T, t)
        tau = arm.computed_torque(w, r, rd, rdd, q_meas, vf)
        ctl_tau.append(tau)
        ctl_mv.append(len(moves) - 1)
        if cfg["delay"]:
            tau, tau_prev = (tau if tau_prev is None else tau_prev), tau
        d.ctrl[:] = tau
        for j in range(nsub):
            log_t.append(t + j * cfg["dt"])
            log_q.append(d.qpos.copy())
            log_v.append(d.qvel.copy())
            mujoco.mj_step(m, d)
            log_a.append(d.qacc.copy())
            log_tau.append(d.actuator_force.copy())
            log_mv.append(len(moves) - 1)
            if j == 0:
                dist.append([mujoco.mj_geomDistance(m, d, c, o, 1.0, None) for c in caps for o in oid])
        k_ctrl += 1
    trace = dict(t=np.array(log_t), q=np.array(log_q), v=np.array(log_v), qacc=np.array(log_a), tau=np.array(log_tau),
                 mv=np.array(log_mv), ctl_tau=np.array(ctl_tau), ctl_mv=np.array(ctl_mv), dist=np.array(dist).reshape(-1, 2, len(oid)))
    trace["bnd"] = np.array(bnd, float)
    return dict(moves=moves, events=events, trace=trace, obstacles=obs)


def analyse(scene, cfg, out):
    """Per-move records, computed on the whole trace at once."""
    tr, moves = out["trace"], out["moves"]
    w, delta, T = cfg["omega"], cfg["delta"], cfg["T"]
    W = arm.waypoints(scene)
    home = W[[x["name"] for x in scene["waypoints"] if x["role"] == "home"][0]]["rad"]
    A = np.array([home] + [mv["a"] for mv in moves])
    B = np.array([home] + [mv["b"] for mv in moves])
    T0 = np.array([0.0] + [mv["t0"] for mv in moves])
    i = tr["mv"] + 1
    t = tr["t"]
    s, sd, sdd = arm.quintic((t - T0[i]) / T)
    # after a timeout the reference is the held configuration; those samples are excluded below
    r = A[i] + s[:, None] * (B[i] - A[i])
    inside = ((t > T0[i]) & (t < T0[i] + T))[:, None]
    rd = inside * sd[:, None] / T * (B[i] - A[i])
    rdd = inside * sdd[:, None] / T**2 * (B[i] - A[i])
    e, ed = tr["q"] - r, tr["v"] - rd
    z = ed + w * e
    M = arm.mass(tr["q"])
    dtot = np.einsum("nij,nj->ni", M, tr["qacc"] - rdd + 2 * w * ed + w**2 * e)
    minvd = np.linalg.solve(M, dtot[..., None])[..., 0]
    dpl = np.einsum("nij,nj->ni", M, tr["qacc"]) + arm.bias(tr["q"], tr["v"]) - tr["tau"]
    lam = np.linalg.eigvalsh(M)[:, 0]
    cl = arm.cells(scene)
    lo = np.radians(np.array([[float(x) for x in c[0]] for c in cl]))
    hi = np.radians(np.array([[float(x) for x in c[1]] for c in cl]))
    infl = scene["cell_inflation_rad"]
    L = scene["tool_lipschitz_L"]
    ctl_i = tr["ctl_mv"] + 1
    nsub = round(cfg["ctrl"] / cfg["dt"])
    qc = tr["q"][::nsub]
    recs = []
    for j, mv in enumerate(moves):
        sel = (i == j + 1) & ((t <= mv["t_end"]) if mv["outcome"] == "timeout" else True)
        cs = ctl_i == j + 1
        # cells containing both ends; the excess of the configuration beyond the best inflated cell
        both = np.all((lo <= mv["a"] + 1e-12) & (mv["a"] <= hi + 1e-12) & (lo <= mv["b"] + 1e-12) & (mv["b"] <= hi + 1e-12), 1)
        q = tr["q"][sel]
        exc = np.maximum(lo[both][:, None] - infl - q, q - hi[both][:, None] - infl).max(2).max(1).min() if both.any() else None
        bd = tr["bnd"]
        kb = (bd[:, 0] >= mv["k0"]) & (bd[:, 0] <= (mv["k_end"] if mv["k_end"] is not None else np.inf))
        dueb = kb & (bd[:, 3] > 0)
        fin = None
        if mv["outcome"] == "finish":
            n_fin = np.searchsorted(t, mv["t_end"])
            qf = tr["q"][n_fin]
            fin = dict(tool_err=float(np.linalg.norm(arm.tool(qf) - arm.tool(mv["b"]))),
                       joint_err=float(np.abs(qf - mv["b"]).max()), speed=float(np.abs(tr["v"][n_fin]).max()))
        recs.append(dict(
            move=j, frm=mv["frm"], to=mv["to"], k0=mv["k0"], k_end=mv["k_end"], outcome=mv["outcome"],
            due=mv["k0"] + round(T / cfg["h"]),
            e_over_delta=float(np.abs(e[sel]).max() / delta), z_over_wdelta=float(np.abs(z[sel]).max() / (w * delta)),
            ed_over_2wdelta=float(np.abs(ed[sel]).max() / (2 * w * delta)),
            e_max=np.abs(e[sel]).max(0).tolist(), z_max=np.abs(z[sel]).max(0).tolist(),
            d_total=float(np.linalg.norm(dtot[sel], axis=1).max()), d_plant=float(np.linalg.norm(dpl[sel], axis=1).max()),
            d_total_rms=float(np.sqrt((np.linalg.norm(dtot[sel], axis=1)**2).mean())),
            minvd_over_w2delta=float(np.abs(minvd[sel]).max() / (w**2 * delta)),
            m0_visited=float(lam[sel].min()),
            cell_excess_rad=None if exc is None else float(exc),
            dist=dict(zip(out["obstacles"], tr["dist"][cs].min(0).min(0).tolist())),
            dist_ref=dict(zip(out["obstacles"], arm.capsule_distance(qc[cs], scene).min(0).min(0).tolist())),
            dist_link=[dict(zip(out["obstacles"], x)) for x in tr["dist"][cs].min(0).tolist()],
            tau_cmd_peak=np.abs(tr["ctl_tau"][cs]).max(0).tolist(), tau_applied_peak=np.abs(tr["tau"][sel]).max(0).tolist(),
            saturated=int((np.abs(tr["ctl_tau"][cs]) >= (cfg["limit"] or np.inf) - 1e-9).any(1).sum()),
            finish=fin, tool_bound=L * delta,
            meas_q_max=float(bd[kb, 1].max()), meas_v_max=float(bd[kb, 2].max()),
            due_boundaries=int(dueb.sum()), arrival_disagree=int((dueb & (bd[:, 4] != bd[:, 5])).sum()),
            arrival_true_at_end=bool(bd[kb, 5][-1]) if kb.any() else None,
        ))
    return recs
