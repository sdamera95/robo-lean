# One supervised run of the pick-and-place cell in MuJoCo: the plant with its non-idealities, the
# 1 kHz computed-torque controller on the nominal model, and the loop at period h whose every
# decision is the cell program's: at each period boundary the harness sends the boundary index, the
# sample and the planner's new requests, and acts on the actions the program answers. The run
# returns its event log, its traces and one record per move with every measured quantity next to
# the bound it is checked against. The time loop is sequential by causality (closed loop with an
# external program); every per-sample quantity is computed afterwards on the whole trace at once.
import math
import os
import shlex
import subprocess
from fractions import Fraction
from pathlib import Path

import mujoco
import numpy as np

import arm

repo = Path(__file__).resolve().parents[2]
# the command that starts the program, run from the repository root
exe = os.environ.get("CELL_SUPERVISOR_CMD", ".lake/build/bin/cell-supervisor")


def tolerances(w, delta):
    """The arrival tolerances the program decides with at gain w and tube radius delta, as exact
    rationals: the position tolerance in degrees, delta plus 1/2000 rad rounded up to a quarter
    degree, and the speed tolerance 2 w delta + 1/5 in rad/s (at (80, 0.03): 7/4 and 5)."""
    w, delta = Fraction(str(w)), Fraction(str(delta))
    return dict(pos_tol_deg=Fraction(math.ceil(4 * math.degrees(float(delta) + 1 / 2000)), 4),
                vel_tol=2 * w * delta + Fraction(1, 5))


nominal = dict(
    omega=80.0, delta=0.05, h=0.1, T=2.0, bound=25, dt=0.00025, ctrl=0.001, limit=150.0,
    coulomb=[0.0] * 3, viscous=[0.0] * 3, armature=[0.0] * 3, counts=0, cutoff=0.0, delay=False,
    payload=0.0, load_radius=0.035, fault=None, tail=1.0, model=None, **tolerances(80.0, 0.05),
)

# the realistic plant of one cycle: friction, rotor inertia, encoders, filter, delay and a payload
realistic = dict(nominal, limit=150.0, coulomb=[2.0, 2.0, 1.0], viscous=[1.0, 1.0, 0.5], armature=[0.05] * 3,
                 counts=2**18, cutoff=100.0, delay=True, payload=1.0)


class Exe:
    """The cell program on its line protocol; every line sent and every answer is kept."""

    kind = "exe"

    def __init__(self, cmd=exe):
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
    # model error of the plant: factors on each link's mass, mass-centre offset and principal
    # inertias (the link lengths and joint axes stay exact; the controller keeps the nominal model)
    if cfg.get("model"):
        ids = [m.body(b).id for b in ("link1", "link2", "link3")]
        m.body_mass[ids] *= cfg["model"]["mass"]
        m.body_ipos[ids] *= np.array(cfg["model"]["offset"])[:, None]
        m.body_inertia[ids] *= np.array(cfg["model"]["inertia"])[:, None]
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
    w, T, h, ctrl = cfg["omega"], cfg["T"], cfg["h"], cfg["ctrl"]
    nsub, nper, nT = round(ctrl / cfg["dt"]), round(h / ctrl), round(T / h)
    res = 2 * np.pi / cfg["counts"] if cfg["counts"] else 0.0
    alpha = 1 - np.exp(-2 * np.pi * cfg["cutoff"] * ctrl) if cfg["cutoff"] else 1.0
    # the sample sent to the program is in encoder counts; on the plant without quantization
    # (counts 0) the controller reads the exact position and only the sample sent to the program is
    # quantized, at 2^40 counts per revolution
    cpr = cfg["counts"] or 2**40
    step = 2 * np.pi / cpr
    # the program's tolerances in radians, for the record of the arrival test only
    pt, vt = np.radians(float(cfg["pos_tol_deg"])), float(cfg["vel_tol"])

    home = scene["waypoints"][[x["role"] for x in scene["waypoints"]].index("home")]["name"]
    name = {W[n]["exact"]: n for n in W}
    words = lambda n: " ".join(fmt(x) for x in W[n]["exact"])
    at = lambda wd: name[tuple(Fraction(x) for x in wd.split(","))]
    cells_words = " ".join(" ".join(fmt(x) for x in lo + hi) for lo, hi in cl)
    events = []
    for line in (f"params {cfg['bound']} {words(home)} {cells_words}",
                 f"policy {fmt(Fraction(str(h)))} {fmt(Fraction(str(T)))} {fmt(cfg['pos_tol_deg'])} {fmt(cfg['vel_tol'])} {cpr}"):
        ans = sup.send(line)
        if not ans.startswith("ok "):
            raise RuntimeError(line + " -> " + ans)
        events.append(dict(k=0, cmd=line.split()[0], ans="ok"))
    d.qpos[:] = W[home]["rad"]
    mujoco.mj_forward(m, d)

    # moves: (name_from, name_to, a, b, t0, k0); index -1 is the hold at home before the first move
    moves = []
    a = b = W[home]["rad"].copy()
    # the planner's requests reach the program at boundary 0: home first, so that the program's first
    # decision is the rest move home -> home admitted at boundary 0, as in the loop model
    t0, reqs, busy = 0.0, [home] + list(plan), False
    qprev = np.round(d.qpos / res) * res if res else d.qpos.copy()
    vf = np.zeros(3)
    tau_prev = None
    log_t, log_q, log_v, log_a, log_tau, log_mv = [], [], [], [], [], []
    ctl_tau, ctl_mv, dist, end_k, stop_at = [], [], [], None, None
    # a record that decides nothing: at every boundary, k, max |sample - true| of position and
    # velocity, and, while a busy move is due, the arrival test with the program's tolerances (in
    # radians) on the sample and on the true state
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
            counts = np.round(d.qpos / step).astype(np.int64)
            qs = counts * step
            due = busy and k - moves[-1]["k0"] >= nT
            arr = busy and bool(np.all(np.abs(qs - moves[-1]["b"]) <= pt) and np.all(np.abs(vf) <= vt))
            arr_true = busy and bool(np.all(np.abs(d.qpos - moves[-1]["b"]) <= pt) and np.all(np.abs(d.qvel) <= vt))
            bnd.append([k, np.abs(qs - d.qpos).max(), np.abs(vf - d.qvel).max(), due, arr, arr_true])

            # the sample: the encoder counts and the exact rational value of each velocity estimate
            sample = [str(c) for c in counts] + [fmt(Fraction(float(x))) for x in vf]
            line = " ".join(["boundary", str(k)] + sample + [words(n) for n in reqs])
            reqs = []
            ans = sup.send(line)
            word, st = parse(ans)
            if word != "ok" or "acts" not in st:
                raise RuntimeError(line + " -> " + ans)
            for act in st["acts"].split(";") if st["acts"] != "-" else []:
                kind, _, wd = act.partition(":")
                if kind == "admit":
                    frm, to, k0 = at(st["src"]), at(st["goal"]), int(st["start"])
                    # the reference starts at the control clock's time of boundary k0
                    a, b, t0 = W[frm]["rad"].copy(), W[to]["rad"].copy(), k0 * nper * ctrl
                    moves.append(dict(frm=frm, to=to, a=a, b=b, t0=t0, k0=k0, k_end=None, outcome=None))
                    events.append(dict(k=k, cmd="admit", target=to, ans="ok"))
                if kind == "reject":
                    events.append(dict(k=k, cmd="reject", target=at(wd), ans="ok"))
                if kind == "tick":
                    events.append(dict(k=k, cmd="tick", ans="ok"))
                if kind == "finish":
                    events.append(dict(k=k, cmd="finish", ans="ok"))
                    moves[-1].update(k_end=k, outcome="finish", t_end=t)
                    role = W[at(st["at"])]["role"]
                    if role == "pick":
                        m.body_mass[pay] = cfg["payload"]
                        m.body_inertia[pay] = 0.4 * cfg["payload"] * cfg["load_radius"]**2 + 1e-12
                    if role == "place":
                        m.body_mass[pay], m.body_inertia[pay] = 1e-9, 1e-12
                if kind == "timeout":
                    events.append(dict(k=k, cmd="timeout", ans="ok"))
                    moves[-1].update(k_end=k, outcome="timeout", t_end=t)
                    # protective stop: hold the measured configuration
                    a = b = q_meas.copy()
                    t0 = t
            busy, faulted, pending = st["busy"] == "true", st["faulted"] == "true", st["pending"] != "-"
            if stop_at is None and not busy and (not pending or faulted):
                stop_at = k + round(cfg["tail"] / h)
            if stop_at is not None and k >= stop_at:
                break
        f = cfg["fault"]
        if f and len(moves) > f["move"] and t >= moves[f["move"]]["t0"] + f["frac"] * T and m.dof_damping[f["joint"]] < f["damping"]:
            # the joint seizes: a brake modelled as a very large viscous damping (implicit integration)
            m.dof_damping[f["joint"]] = f["damping"]
            events.append(dict(k=k_ctrl / nper, cmd="fault", joint=f["joint"], t=t))
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
    out = dict(moves=moves, events=events, trace=trace, obstacles=obs)
    fe = [e for e in events if e["cmd"] == "fault"]
    if fe:
        # how far the seized joint moved between the seizure and the end of the run
        qj = trace["q"][trace["t"] >= fe[0]["t"], fe[0]["joint"]]
        out["fault_motion_deg"] = float(np.degrees(np.abs(qj - qj[0]).max()))
    return out


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
        # (cell_excess_rad <= 0 means inside the inflated cell) and the excursion beyond the
        # uninflated cell (excursion_rad = cell_excess_rad + inflation, allowed up to the inflation)
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
            excursion_rad=None if exc is None else float(exc + infl),
            dist=dict(zip(out["obstacles"], tr["dist"][cs].min(0).min(0).tolist())),
            dist_ref=dict(zip(out["obstacles"], arm.capsule_distance(qc[cs], scene).min(0).min(0).tolist())),
            dist_link=[dict(zip(out["obstacles"], x)) for x in tr["dist"][cs].min(0).tolist()],
            tau_cmd_peak=np.abs(tr["ctl_tau"][cs]).max(0).tolist(), tau_applied_peak=np.abs(tr["tau"][sel]).max(0).tolist(),
            saturated=int((np.abs(tr["ctl_tau"][cs]) >= (cfg["limit"] or np.inf) - 1e-9).any(1).sum()),
            tau_step_max=float(np.abs(np.diff(tr["ctl_tau"][cs], axis=0)).max()) if cs.sum() > 1 else 0.0,
            tau_step_rms=float(np.sqrt((np.diff(tr["ctl_tau"][cs], axis=0)**2).mean())) if cs.sum() > 1 else 0.0,
            finish=fin, tool_bound=L * delta,
            meas_q_max=float(bd[kb, 1].max()), meas_v_max=float(bd[kb, 2].max()),
            due_boundaries=int(dueb.sum()), arrival_disagree=int((dueb & (bd[:, 4] != bd[:, 5])).sum()),
            arrival_true_at_end=bool(bd[kb, 5][-1]) if kb.any() else None,
        ))
    return recs
