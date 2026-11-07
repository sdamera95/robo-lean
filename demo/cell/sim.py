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
import model
import queue_planner
import queue_reference

repo = Path(__file__).resolve().parents[2]
# the command that starts the program, run from the repository root
exe = os.environ.get("CELL_SUPERVISOR_CMD", ".lake/build/bin/cell-supervisor")
# the command that starts the program on the queue supervisor, run from the repository root
exe_queue = os.environ.get("CELL_SUPERVISOR_QUEUE_CMD", ".lake/build/bin/cell-supervisor-queue")


def tolerances(w, delta, eps_q=Fraction(1, 2000), eps_v=Fraction(1, 5)):
    """The arrival tolerances the program decides with at gain w and tube radius delta, as exact
    rationals: the position tolerance in degrees, delta plus the position sample allowance eps_q
    (rad) rounded up to a quarter degree, and the speed tolerance 2 w delta + eps_v in rad/s for
    the speed sample allowance eps_v (at (80, 0.03): 7/4 and 5 with eps_q = 1/2000, 3 and 5 with
    eps_q = 1/50; at (50, 0.03) with eps_q = 1/50 and eps_v = 3/10: 3 and 33/10)."""
    w, delta = Fraction(str(w)), Fraction(str(delta))
    return dict(pos_tol_deg=Fraction(math.ceil(4 * math.degrees(float(delta) + float(eps_q))), 4),
                vel_tol=2 * w * delta + eps_v)


nominal = dict(
    omega=80.0, delta=0.05, h=0.1, T=2.0, bound=25, dt=0.00025, ctrl=0.001, limit=150.0,
    coulomb=[0.0] * 3, viscous=[0.0] * 3, armature=[0.0] * 3, counts=0, cutoff=0.0, delay=False,
    payload=0.0, load_radius=0.035, fault=None, tail=1.0, model=None, **tolerances(80.0, 0.05),
    # elastic joints (None: rigid), the side the encoders read, the actuator's time constant (s),
    # encoder noise (counts), timing jitter (substeps) and the seed of the noise and the jitter
    stiffness=None, joint_damping=None, sense="link", lag=0.0, enc_noise=0, jitter=0, plant_seed=0,
    # the controller's model: the rotor inertia J on every joint (kg m^2) and the part's nominal mass
    # m_hat (kg), on while the plant carries the part (from a pick finish to a place finish)
    model_rotor=0.0, model_payload=0.0,
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


class QueueExe(Exe):
    """The program on the queue supervisor. Every line is also sent to the Python reference of its
    protocol (queue_reference.py), whose answer must be the program's: the reference only labels
    each request's outcome (queued, or refused with the conditions that failed), which the
    program's answer does not carry, and the queue just before an admission; it decides nothing."""

    kind = "exe-queue"

    def __init__(self, cmd=exe_queue):
        super().__init__(cmd)
        self.ref = queue_reference.QueueSupervisor()

    def send(self, line):
        ans = super().send(line)
        ref = self.ref.send(line)
        if ref != ans:
            raise RuntimeError("reference differs: " + line + " -> " + ans + " / " + str(ref))
        return ans


def supervisor(queue=False):
    return QueueExe() if queue else Exe()


def fmt(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def parse(ans):
    word, _, rest = ans.partition(" ")
    st = dict(kv.split("=", 1) for kv in rest.split()) if word == "ok" else {}
    return word, st


def elastic(cfg):
    """The joint stiffness and damping as arrays of three, or None for the rigid plant (stiffness
    None or 0)."""
    K = np.zeros(3) + (cfg.get("stiffness") or 0.0)
    if not K.any():
        return None
    assert (K > 0).all() and np.all(np.zeros(3) + cfg["armature"] > 0), "elastic joints need stiffness and rotor inertia on every joint"
    return K, np.zeros(3) + (cfg.get("joint_damping") or 0.0)


def build(scene, cfg):
    el = elastic(cfg)
    if el is not None:
        # elastic joints: rotor inertia and friction (Coulomb and viscous) sit on the motor side, the
        # links carry none
        m = mujoco.MjModel.from_xml_string(arm.mjcf(scene, dt=cfg["dt"], limit=cfg["limit"] or 1e9, stiffness=el[0], joint_damping=el[1],
                                                    rotor=np.zeros(3) + cfg["armature"]))
        mv = [m.jnt_dofadr[m.joint(f"m{i}").id] for i in range(3)]
        m.dof_damping[mv] = cfg["viscous"]
        m.dof_frictionloss[mv] = cfg["coulomb"]
    else:
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
    """Drive one run. `plan` is the list of waypoint names the planner requests, in order. With
    `cfg["queue"]` (the queue's capacity, the urgent scenario's probabilities or None, the seed of
    its draws) the program is the queue supervisor's, `sup` a `QueueExe`, and the requests are sent
    by `queue_planner.QueuePlanner`; otherwise the whole plan is sent at boundary 0."""
    queue = cfg.get("queue")
    W = arm.waypoints(scene)
    cl = arm.cells(scene)
    m = build(scene, cfg)
    d = mujoco.MjData(m)
    el = elastic(cfg)
    # coordinates of the links (the theorem's state, the one the trace keeps) and of the motors (the
    # links' own on the rigid plant), and the side the encoders read
    lq = np.array([m.jnt_qposadr[m.joint(f"j{i}").id] for i in range(3)])
    lv = np.array([m.jnt_dofadr[m.joint(f"j{i}").id] for i in range(3)])
    rq = np.array([m.jnt_qposadr[m.joint(f"m{i}").id] for i in range(3)]) if el is not None else lq
    rv = np.array([m.jnt_dofadr[m.joint(f"m{i}").id] for i in range(3)]) if el is not None else lv
    motor = cfg.get("sense", "link") == "motor"
    assert cfg.get("sense", "link") in ("link", "motor")
    sq, sv = (rq, rv) if motor else (lq, lv)
    # encoder noise: an integer number of counts per sample, uniform over -n..n, on the counts the
    # controller and the program read; timing jitter: each control step's torque takes effect a
    # uniform random number 0..n of substeps late (never, if that is the whole period), the previous
    # torque held meanwhile; actuator lag: a first-order low-pass on the torque, exact per substep
    nn, nj, lag = cfg.get("enc_noise", 0), cfg.get("jitter", 0), cfg.get("lag", 0.0)
    assert not nn or cfg["counts"], "encoder noise needs encoders (counts)"
    rng = np.random.default_rng(cfg.get("plant_seed", 0))
    decay = np.exp(-cfg["dt"] / lag) if lag else 0.0
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
    bound_words = str(cfg["bound"]) + (" " + str(queue["capacity"]) if queue else "")
    for line in (f"params {bound_words} {words(home)} {cells_words}",
                 f"policy {fmt(Fraction(str(h)))} {fmt(Fraction(str(T)))} {fmt(cfg['pos_tol_deg'])} {fmt(cfg['vel_tol'])} {cpr}"):
        ans = sup.send(line)
        if not ans.startswith("ok "):
            raise RuntimeError(line + " -> " + ans)
        events.append(dict(k=0, cmd=line.split()[0], ans="ok"))
    d.qpos[lq] = W[home]["rad"]
    mujoco.mj_forward(m, d)
    if el is not None:
        # start at rest in static equilibrium: each spring carries its link's gravity torque
        d.qpos[rq] = d.qpos[lq] + d.qfrc_bias[lv] / el[0]
        mujoco.mj_forward(m, d)

    # moves: (name_from, name_to, a, b, t0, k0); index -1 is the hold at home before the first move
    moves = []
    a = b = W[home]["rad"].copy()
    # the planner's requests reach the program at boundary 0: home first, so that the program's first
    # decision is the rest move home -> home admitted at boundary 0, as in the loop model
    t0, reqs, busy = 0.0, [home] + list(plan), False
    if queue:
        # the planner sends the requests; the queue and the fault flag of the program's last answer,
        # the move it admitted at the last boundary, and the priority of each queued waypoint
        pl = queue_planner.QueuePlanner(reqs, W, queue["capacity"], queue["urgent"], queue["seed"])
        qnames, qfaulted, adm, qprio = [], False, None, {}
    qprev = np.round(d.qpos[sq] / res) * res if res else d.qpos[sq].copy()
    vf = np.zeros(3)
    tau_prev = held = ta = unstable = None
    log_t, log_q, log_v, log_a, log_tau, log_mv = [], [], [], [], [], []
    # elastic plant: motor angles, velocities and accelerations and the spring torque on the links;
    # the noise and jitter drawn
    log_qm, log_vm, log_am, log_sp, log_nz, log_jit = [], [], [], [], [], []
    # the controller's model: rotor inertia, the part's nominal mass, and whether the part is held
    # (logged per simulator step)
    J_hat, m_hat, carry = cfg.get("model_rotor", 0.0), cfg.get("model_payload", 0.0), False
    log_carry = []
    ctl_tau, ctl_mv, dist, end_k, stop_at = [], [], [], None, None
    # a record that decides nothing: at every boundary, k, max |sample - true| of position and
    # velocity, and, while a busy move is due, the arrival test with the program's tolerances (in
    # radians) on the sample and on the true state
    bnd = []
    k_ctrl = 0
    while True:
        t = k_ctrl * ctrl
        nz = rng.integers(-nn, nn + 1, 3) if nn else 0
        if nn:
            log_nz.append(nz)
        q_meas = (np.round(d.qpos[sq] / res) + nz) * res if res else d.qpos[sq].copy()
        if cfg["cutoff"]:
            vf = vf + alpha * ((q_meas - qprev) / ctrl - vf)
        else:
            vf = d.qvel[sv].copy()
        qprev = q_meas
        if k_ctrl % nper == 0:
            k = k_ctrl // nper
            counts = np.round(d.qpos[sq] / step).astype(np.int64) + nz
            qs = counts * step
            ql, vl = d.qpos[lq], d.qvel[lv]
            due = busy and k - moves[-1]["k0"] >= nT
            arr = busy and bool(np.all(np.abs(qs - moves[-1]["b"]) <= pt) and np.all(np.abs(vf) <= vt))
            arr_true = busy and bool(np.all(np.abs(ql - moves[-1]["b"]) <= pt) and np.all(np.abs(vl) <= vt))
            bnd.append([k, np.abs(qs - ql).max(), np.abs(vf - vl).max(), due, arr, arr_true])

            # the sample: the encoder counts and the exact rational value of each velocity estimate
            sample = [str(c) for c in counts] + [fmt(Fraction(float(x))) for x in vf]
            if queue:
                reqs = pl.requests(qnames, qfaulted, adm)
                line = " ".join(["boundary", str(k)] + sample + [words(n) + " " + p for n, p in reqs])
            else:
                line = " ".join(["boundary", str(k)] + sample + [words(n) for n in reqs])
            ans = sup.send(line)
            word, st = parse(ans)
            if word != "ok" or "acts" not in st:
                raise RuntimeError(line + " -> " + ans)
            if queue:
                # each request's outcome as the reference labels it (the program's answer has been
                # checked equal to the reference's)
                for (n, p), o in zip(reqs, sup.ref.outcomes):
                    events.append(dict(k=k, cmd="request", target=n, prio=p, outcome=queue_reference.outcome_words(o), ans="ok"))
                    if o["queued"]:
                        qprio[n] = p
                adm = None
            reqs = []
            for act in st["acts"].split(";") if st["acts"] != "-" else []:
                kind, _, wd = act.partition(":")
                if kind == "admit":
                    frm, to, k0 = at(st["src"]), at(st["goal"]), int(st["start"])
                    # the reference starts at the control clock's time of boundary k0
                    a, b, t0 = W[frm]["rad"].copy(), W[to]["rad"].copy(), k0 * nper * ctrl
                    moves.append(dict(frm=frm, to=to, a=a, b=b, t0=t0, k0=k0, k_end=None, outcome=None))
                    ev = dict(k=k, cmd="admit", target=to, ans="ok")
                    if queue:
                        # the admitted waypoint's priority and the queue just before the admission
                        adm = (frm, to, qprio.pop(to))
                        moves[-1]["prio"] = adm[2]
                        ev.update(prio=adm[2], queue=[name[w] for w in sup.ref.admitted["queue"]])
                    events.append(ev)
                if kind == "reject":
                    events.append(dict(k=k, cmd="reject", target=at(wd), ans="ok"))
                if kind == "tick":
                    events.append(dict(k=k, cmd="tick", ans="ok"))
                if kind == "finish":
                    events.append(dict(k=k, cmd="finish", ans="ok"))
                    moves[-1].update(k_end=k, outcome="finish", t_end=t)
                    role = W[at(st["at"])]["role"]
                    # the part attaches to the plant and enters the controller's model together
                    if role == "pick":
                        m.body_mass[pay] = cfg["payload"]
                        m.body_inertia[pay] = 0.4 * cfg["payload"] * cfg["load_radius"]**2 + 1e-12
                        carry = True
                    if role == "place":
                        m.body_mass[pay], m.body_inertia[pay] = 1e-9, 1e-12
                        carry = False
                if kind == "timeout":
                    events.append(dict(k=k, cmd="timeout", ans="ok"))
                    moves[-1].update(k_end=k, outcome="timeout", t_end=t)
                    # protective stop: hold the measured configuration
                    a = b = q_meas.copy()
                    t0 = t
                    if queue:
                        # the timeout rejects the queued requests and empties the queue
                        qprio = {}
            if queue:
                busy, faulted = st["busy"] == "true", st["faulted"] == "true"
                qnames, qfaulted = [at(x) for x in st["requested"].split(";")] if st["requested"] != "-" else [], faulted
                pending = bool(qnames) or pl.left()
            else:
                busy, faulted, pending = st["busy"] == "true", st["faulted"] == "true", st["pending"] != "-"
            if stop_at is None and not busy and (not pending or faulted):
                stop_at = k + round(cfg["tail"] / h)
            if stop_at is not None and k >= stop_at:
                break
        f = cfg["fault"]
        if f and len(moves) > f["move"] and t >= moves[f["move"]]["t0"] + f["frac"] * T and m.dof_damping[lv[f["joint"]]] < f["damping"]:
            # the joint seizes: a brake modelled as a very large viscous damping (implicit integration)
            m.dof_damping[lv[f["joint"]]] = f["damping"]
            events.append(dict(k=k_ctrl / nper, cmd="fault", joint=f["joint"], t=t))
        r, rd, rdd = arm.reference(a, b, t0, T, t)
        tau = model.computed_torque(w, r, rd, rdd, q_meas, vf, J_hat, m_hat if carry else 0.0)
        ctl_tau.append(tau)
        ctl_mv.append(len(moves) - 1)
        if cfg["delay"]:
            tau, tau_prev = (tau if tau_prev is None else tau_prev), tau
        if lag and cfg["limit"]:
            # the lag filters the torque the drive can deliver
            tau = np.clip(tau, -cfg["limit"], cfg["limit"])
        jit = int(rng.integers(0, nj + 1)) if nj else 0
        if nj:
            log_jit.append(jit)
        for j in range(nsub):
            u = tau if j >= jit or held is None else held
            if lag:
                # the filter's output at the end of the substep, the input held over it
                ta = u if ta is None else u + (ta - u) * decay
                d.ctrl[:] = ta
            else:
                d.ctrl[:] = u
            log_t.append(t + j * cfg["dt"])
            log_q.append(d.qpos[lq].copy())
            log_v.append(d.qvel[lv].copy())
            log_carry.append(carry)
            if el is not None:
                log_qm.append(d.qpos[rq].copy())
                log_vm.append(d.qvel[rv].copy())
            mujoco.mj_step(m, d)
            log_a.append(d.qacc[lv].copy())
            log_tau.append(d.actuator_force.copy())
            log_mv.append(len(moves) - 1)
            if el is not None:
                log_am.append(d.qacc[rv].copy())
                log_sp.append(d.qfrc_passive[lv].copy())
            if j == 0:
                dist.append([mujoco.mj_geomDistance(m, d, c, o, 1.0, None) for c in caps for o in oid])
            if d.warning[mujoco.mjtWarning.mjWARN_BADQACC].number:
                # the integration diverged and MuJoCo reset the state: the run ends here
                unstable = t + j * cfg["dt"]
                break
        if unstable is not None:
            break
        if jit < nsub:
            held = tau
        k_ctrl += 1
    trace = dict(t=np.array(log_t), q=np.array(log_q), v=np.array(log_v), qacc=np.array(log_a), tau=np.array(log_tau),
                 mv=np.array(log_mv), ctl_tau=np.array(ctl_tau), ctl_mv=np.array(ctl_mv), dist=np.array(dist).reshape(-1, 2, len(oid)))
    trace["bnd"] = np.array(bnd, float)
    trace["carry"] = np.array(log_carry, bool)
    if el is not None:
        trace.update(qm=np.array(log_qm), vm=np.array(log_vm), qacc_m=np.array(log_am), spring=np.array(log_sp))
    if nn:
        trace["noise"] = np.array(log_nz)
    if nj:
        trace["jitter"] = np.array(log_jit)
    out = dict(moves=moves, events=events, trace=trace, obstacles=obs)
    if unstable is not None:
        out["unstable_t"] = unstable
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
    # the controller's model at each sample, with its payload on where the part was held: d_total is
    # the disturbance relative to that model, M_hat (e'' + 2 w e' + w^2 e), and minvd is
    # M_hat^-1 d_total, the acceleration-level residual e'' + 2 w e' + w^2 e of the error equation on
    # the link-side trace (equal to it up to round-off whatever M_hat is); d_plant is
    # M_hat theta'' + C_hat theta' + N_hat minus the applied torque
    J_hat, m_hat = cfg.get("model_rotor", 0.0), cfg.get("model_payload", 0.0)
    if np.any(J_hat) or np.any(m_hat):
        mp = m_hat * tr["carry"]
        M, bias = model.mass(tr["q"], J_hat, mp), model.bias(tr["q"], tr["v"], mp)
    else:
        M, bias = arm.mass(tr["q"]), arm.bias(tr["q"], tr["v"])
    dtot = np.einsum("nij,nj->ni", M, tr["qacc"] - rdd + 2 * w * ed + w**2 * e)
    minvd = np.linalg.solve(M, dtot[..., None])[..., 0]
    dpl = np.einsum("nij,nj->ni", M, tr["qacc"]) + bias - tr["tau"]
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
        if "qm" in tr:
            # elastic joints: the drive's largest deflection max |theta_m - theta| over the move (rad)
            recs[-1]["deflection_max"] = float(np.abs(tr["qm"][sel] - q).max())
        if "prio" in mv:
            # queue supervisor: the priority of the request the move was admitted from
            recs[-1]["prio"] = mv["prio"]
    return recs
