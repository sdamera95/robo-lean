# The runs of the evaluation: the randomized campaign, the gain variants, the stress sweeps, the
# ablation of the disturbance and the fault run, each with a fixed seed, and the worker that runs
# one of them and returns its per-move records.
import json
from fractions import Fraction

import numpy as np

import arm
import sim

scene = arm.load_scene()
names = {}
for n, w in arm.waypoints(scene).items():
    names.setdefault(w["role"], []).append(n)

# the plant's non-idealities that every realistic run has (fixed), and the ranges of the drawn ones:
# payload, joint friction and rotor inertia, and the plant's model error (factors on each link's
# mass, mass-centre offset and principal inertias; the controller keeps the nominal model)
fixed = dict(limit=150.0, counts=2**18, cutoff=100.0, delay=True)
ranges = dict(payload=(0.0, 5.0), coulomb=(0.0, 10.0), viscous=(0.0, 10.0), armature=(0.0, 0.1),
              mass=(0.9, 1.1), offset=(0.9, 1.1), inertia=(0.8, 1.2))


def plan(rng, cycles, inject=0.25, low=0.5):
    """home -> lift_pick, then `cycles` pick-place cycles over random slots; with probability
    `inject` per cycle the planner also asks for an unlinked move (straight to the place slot), and
    each crossing (both directions) goes through cross_low with probability `low`."""
    p = ["lift_pick"]
    for _ in range(cycles):
        i, j = rng.choice(names["pick"]), rng.choice(names["place"])
        p += [i, "lift_pick"]
        if rng.random() < inject:
            p.append(j)
        p += (["cross_low"] if rng.random() < low else []) + ["lift_place", j, "lift_place"]
        p += (["cross_low"] if rng.random() < low else []) + ["lift_pick"]
    return p


def draw(rng):
    return dict(payload=float(rng.uniform(*ranges["payload"])),
                coulomb=rng.uniform(*ranges["coulomb"], 3).tolist(),
                viscous=rng.uniform(*ranges["viscous"], 3).tolist(),
                armature=rng.uniform(*ranges["armature"], 3).tolist(),
                model=dict(mass=rng.uniform(*ranges["mass"], 3).tolist(), offset=rng.uniform(*ranges["offset"], 3).tolist(),
                           inertia=rng.uniform(*ranges["inertia"], 3).tolist()))


# the nominal plant's settings for the stress, ablation and fault runs (the middle of the ranges,
# no model error)
middle = dict(payload=2.5, coulomb=[5.0] * 3, viscous=[5.0] * 3, armature=[0.05] * 3)

# the ablation's plan (one cycle) and its plant at the top of every range
ablation_plan = ["lift_pick", "pick_2", "lift_pick", "lift_place", "place_2", "lift_place", "lift_pick"]
top = dict(payload=ranges["payload"][1], coulomb=[ranges["coulomb"][1]] * 3, viscous=[ranges["viscous"][1]] * 3,
           armature=[ranges["armature"][1]] * 3, limit=150.0, counts=2**18, cutoff=100.0, delay=True,
           model=dict(mass=[ranges["mass"][1]] * 3, offset=[ranges["offset"][1]] * 3, inertia=[ranges["inertia"][1]] * 3))


def elastic(K, zeta=0.05, rotor=ranges["armature"][1], sense="link"):
    """Elastic joints of stiffness K (N m/rad, every joint) with the damping D = 2 zeta sqrt(K J) of
    damping ratio zeta for the rotor of inertia J against the link held still."""
    return dict(stiffness=[float(K)] * 3, joint_damping=[2 * zeta * float(np.sqrt(K * rotor))] * 3, sense=sense)


# the plant's further non-idealities at their middle values: elastic joints, actuator lag (s), encoder
# noise (counts) and timing jitter (substeps)
mid = dict(elastic=elastic(1e4), lag=dict(lag=0.002), noise=dict(enc_noise=2), jitter=dict(jitter=2))
# the same at the worst values of the sweep's grid
worst = dict(elastic=elastic(3e3), lag=dict(lag=0.005), noise=dict(enc_noise=4), jitter=dict(jitter=4))

# values for a joint of this size from published sources: a size-25 harmonic drive at ratio 100 has a
# catalogue stiffness of 2.7e4 to 5.7e4 N m/rad (whole joints softer, lightweight arms 1e4 to 2e4); the
# identified motor and reducer inertia of the three large joints of an arm of this class, reflected
# through the ratio 100, is 1.5 to 1.9 kg m^2; no damping figure was found, so the damping ratio is
# swept from 0.02 to 0.2; drive lag 0.5 to 2 ms; a 19-bit link encoder; loop jitter within 0.25 ms
rotor = 1.7
cited = dict(elastic=elastic(3e4, rotor=rotor), lag=dict(lag=0.001), noise=dict(enc_noise=1), jitter=dict(jitter=1))
cited_worst = dict(elastic=elastic(1e4, zeta=0.02, rotor=rotor), lag=dict(lag=0.002), noise=dict(enc_noise=2), jitter=dict(jitter=1))

# ------------------------------------------------------------------
# the runs on the nominal model: the controller knows the rotor inertia J = 1.7 kg m^2 on every joint
# and the part's nominal mass m_hat; the plant has the rotor inertia J' = J + e (the same on every
# joint), the part's actual mass m = m_hat + dm, and joint friction within Coulomb level f_c and
# viscous coefficient f_v. The proved condition at each design point (gain, tube radius) is
#   |dm| + rotor |J' - J| + friction (f_c + speed f_v) <= budget
# (kg, kg m^2, N m, N m s, with J' >= 3/2) with the constants below, the friction speed being the
# joint speed bound at that gain (rad/s); f_c and f_v are the largest Coulomb level and viscous
# coefficient over the joints. A design point with no entry is an error.
envelopes = {(80, 0.03): dict(rotor=15 / 4, friction=1 / 150, speed=29 / 5, budget=8 / 5),
             (50, 0.03): dict(rotor=7 / 2, friction=1 / 60, speed=4, budget=3 / 2)}


def envelope_at(w, delta):
    """The constants of the proved condition at gain w and tube radius delta."""
    assert (w, delta) in envelopes, f"no proved envelope at gain {w} and tube radius {delta}"
    return envelopes[(w, delta)]


# the position sample allowance of the measured-sample theorem (rad): the drive's deflection read
# by motor-side encoders; the arrival tolerances become 3 degrees and 5 rad/s at (80, 0.03), 3
# degrees and 16/5 rad/s at (50, 0.03)
eps_q = Fraction(1, 50)
# the speed sample allowance of the nominal-model design (rad/s): the velocity estimate on an
# elastic drive differs from the link speed by the drive's oscillation, up to about 0.22 rad/s at
# gain 50 in the campaign; the arrival tolerances become 33/10 rad/s at (50, 0.03), 51/10 at (80, 0.03)
eps_v = Fraction(3, 10)
# the drawn ranges: rotor inertia error e (kg m^2), Coulomb level (N m) and viscous coefficient
# (N m s) per joint, the part's nominal mass (kg), the joint stiffness (N m/rad, log-uniform, every
# joint the same), the damping ratio of the rotor against the held link (at least 0.05: at 0.02
# the heaviest part at the longest lag exceeds the speed sample allowance at gain 50), and the
# drive lag (s, at most 1 ms: with the one-period torque delay the loop at gain 50 limit-cycles
# for lags above about 1.2 ms, see the lag stress sweep); the encoders read the motor side with
# one count of noise and one substep of jitter
nominal_ranges = dict(e=(-0.05, 0.05), coulomb=(0.0, 5.0), viscous=(0.0, 2.0), part=(0.0, 5.0),
                      stiffness=(1e4, 6e4), zeta=(0.05, 0.2), lag=(0.0005, 0.001))
# the middle of those ranges for the stress runs (the stiffness at the cited nominal 3e4, near the
# log-middle 2.4e4 of the range), no mass error
nominal_middle = dict(e=0.0, coulomb=2.5, viscous=1.0, part=2.5, dm=0.0, stiffness=3e4, zeta=0.125, lag=0.00075)


def envelope_lhs(env, dm, e, coulomb, viscous):
    """The left side of the proved condition with the constants `env` for a mass error dm, a rotor
    inertia error e and the joints' Coulomb levels and viscous coefficients."""
    return abs(dm) + env["rotor"] * abs(e) + env["friction"] * (max(coulomb) + env["speed"] * max(viscous))


def nominal_run(base, e, part, dm, coulomb, viscous, K, zeta, lag, **drawn):
    """The configuration of one run on the nominal model: the model's rotor inertia `rotor` and
    nominal part mass `part`; the plant's rotor inertia rotor + e on every joint, the part's actual
    mass max(part + dm, 0), the friction per joint, elastic joints of stiffness K and damping ratio
    zeta read on the motor side, the drive lag, one count of encoder noise and one substep of
    jitter. The drawn values and the left side of the condition (with the mass error as applied)
    are kept under `envelope`, with the constants of the condition at the run's gain and tube."""
    env = envelope_at(base["omega"], base["delta"])
    Jp = rotor + e
    m = max(part + dm, 0.0)
    lhs = envelope_lhs(env, m - part, e, coulomb, viscous)
    return dict(base, **fixed, model_rotor=rotor, model_payload=part, armature=[Jp] * 3, payload=m,
                coulomb=list(coulomb), viscous=list(viscous), **elastic(K, zeta=zeta, rotor=Jp, sense="motor"),
                lag=lag, enc_noise=1, jitter=1,
                envelope=dict(drawn, e=e, part=part, dm=dm, dm_applied=m - part, lhs=lhs, constants=env, budget=env["budget"]))


def nominal_campaign(nruns, w, delta, keep=3):
    """The randomized campaign on the nominal model; run s draws from the seed [20261107, 94, s], the
    mass error uniform in [-b, b] with b the budget left by the drawn rotor error and friction, so
    that every run is inside the proved envelope."""
    out, tag = [], f"n{w}-{delta}-"
    base = dict(sim.nominal, omega=w, delta=delta, **sim.tolerances(w, delta, eps_q, eps_v))
    R = nominal_ranges
    env = envelope_at(w, delta)
    for s in range(nruns):
        rng = np.random.default_rng([20261107, 94, s])
        e = float(rng.uniform(*R["e"]))
        c, v = rng.uniform(*R["coulomb"], 3).tolist(), rng.uniform(*R["viscous"], 3).tolist()
        part = float(rng.uniform(*R["part"]))
        b = env["budget"] - envelope_lhs(env, 0.0, e, c, v)
        dm = float(rng.uniform(-b, b))
        K = float(np.exp(rng.uniform(*np.log(R["stiffness"]))))
        zeta, lag = float(rng.uniform(*R["zeta"])), float(rng.uniform(*R["lag"]))
        cfg = dict(nominal_run(base, e, part, dm, c, v, K, zeta, lag, b=b), plant_seed=s)
        out.append((tag + str(s).zfill(4), s, cfg, plan(rng, 4), s < keep))
    return out


def nominal_stress(mode, nruns, w, delta):
    """The stress runs on the nominal model: one quantity beyond the envelope, the rest at the
    middle of the campaign's ranges; one pick-place cycle per run from the seed [20261107, 94, 1, s]."""
    base = dict(sim.nominal, omega=w, delta=delta, **sim.tolerances(w, delta, eps_q, eps_v))
    jobs = []

    def add(tag, **kw):
        p = dict(nominal_middle, **kw)
        for s in range(nruns):
            rng = np.random.default_rng([20261107, 94, 1, s])
            cfg = nominal_run(base, p["e"], p["part"], p["dm"], [p["coulomb"]] * 3, [p["viscous"]] * 3, p["stiffness"], p["zeta"], p["lag"])
            jobs.append((f"{tag}-{s}", s, dict(cfg, plant_seed=s), plan(rng, 1, inject=0), False))

    if mode == "nominal-stress-mass":
        # the mass error, both signs while the actual mass stays nonnegative
        for dm in (0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0):
            add(f"dm{dm}", dm=dm)
            if 0 < dm <= nominal_middle["part"]:
                add(f"dm-{dm}", dm=-dm)
    if mode == "nominal-stress-friction":
        for c in (0, 10, 30, 60, 100, 150, 250):
            add(f"coulomb{c}", coulomb=float(c), viscous=1.0)
    if mode == "nominal-stress-rotor":
        for e in (0.0, 0.1, 0.2, 0.4, 0.8):
            add(f"rotor{e}", e=e)
    if mode == "nominal-stress-stiffness":
        for K in (1e3, 2e3, 3e3, 5e3, 1e4, 3e4, 6e4):
            add(f"K{int(K)}", stiffness=K)
    if mode == "nominal-stress-lag":
        # the drive lag beyond the stated 1 ms, at the middle part and at the heaviest
        for ms in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0):
            add(f"lag{ms}", lag=ms * 1e-3)
            add(f"lag{ms}-heavy", lag=ms * 1e-3, part=5.0)
    return jobs


def campaign(nruns, w, delta, keep=3):
    """The randomized campaign at gain w and tube radius delta; run s draws from the seed
    [20261105, s] whatever w and delta are."""
    out, tag = [], f"c{w:g}-{delta:g}-"
    for s in range(nruns):
        rng = np.random.default_rng([20261105, s])
        cfg = dict(sim.nominal, **fixed, **draw(rng), omega=w, delta=delta, **sim.tolerances(w, delta))
        out.append((f"{tag}{s:04d}", s, cfg, plan(rng, 4), s < keep))
    return out


def make(mode, nruns, w, delta):
    """The runs of one mode at gain w and tube radius delta."""
    if mode == "campaign":
        return campaign(nruns, w, delta)
    if mode == "nominal-campaign":
        return nominal_campaign(nruns, w, delta)
    if mode.startswith("nominal-stress-"):
        return nominal_stress(mode, nruns, w, delta)
    nominal = dict(sim.nominal, omega=w, delta=delta, **sim.tolerances(w, delta))
    jobs = []
    if mode == "stress-payload":
        for mp in (0, 2, 4, 6, 8, 10, 12, 15, 20, 25, 30, 40, 50, 60):
            for s in range(nruns):
                rng = np.random.default_rng([20261106, s])
                cfg = dict(nominal, **fixed, **dict(middle, payload=float(mp)))
                jobs.append((f"p{mp:02d}-{s}", s, cfg, plan(rng, 1, inject=0), False))
    if mode == "stress-friction":
        for c in (0, 3, 6, 10, 15, 20, 30, 40, 60, 80, 100, 150):
            for s in range(nruns):
                rng = np.random.default_rng([20261107, s])
                cfg = dict(nominal, **fixed, **dict(middle, coulomb=[float(c)] * 3))
                jobs.append((f"f{c:03d}-{s}", s, cfg, plan(rng, 1, inject=0), False))
    if mode == "ablation":
        p = ablation_plan
        jobs.append(("ideal", 0, dict(nominal), p, False))
        for k in ("payload", "coulomb", "viscous", "armature", "delay"):
            jobs.append((f"only-{k}", 0, dict(nominal, **{k: top[k]}), p, False))
        jobs.append(("only-model-error", 0, dict(nominal, model=top["model"]), p, False))
        jobs.append(("only-encoder", 0, dict(nominal, counts=2**18, cutoff=100.0), p, False))
        jobs.append(("all", 0, dict(nominal, **top), p, True))
    if mode == "fault":
        p = ["lift_pick", "pick_1", "lift_pick", "lift_place", "place_1", "lift_place", "lift_pick"]
        base = dict(nominal, **fixed, **middle)
        # the base yaw joint seizes 30% into the crossing move (move 4; move 0 is the rest move): a
        # brake modelled as a very large viscous damping on that joint, integrated implicitly
        jobs.append(("fault-yaw", 0, dict(base, fault=dict(joint=0, move=4, frac=0.3, damping=1e7)), p, True))
        jobs.append(("fault-free", 0, base, p, True))
    if mode == "plant":
        # the ablation's plant at the top of every range (the reference), each further non-ideality
        # over its grid alone (elastic joints read on either side, damping ratio 0.05), the four
        # together at their middle values
        ref = dict(nominal, **top)
        jobs.append(("ref", 0, ref, ablation_plan, True))
        for K in (3e3, 1e4, 3e4, 1e5):
            for sense in ("link", "motor"):
                jobs.append((f"elastic-{int(K)}-{sense}", 0, dict(ref, **elastic(K, sense=sense)), ablation_plan, False))
        for lag in (0.001, 0.002, 0.005):
            jobs.append((f"lag-{lag}", 0, dict(ref, lag=lag), ablation_plan, False))
        for n in (1, 2, 4):
            jobs.append((f"noise-{n}", 0, dict(ref, enc_noise=n), ablation_plan, False))
        for n in (1, 2, 4):
            jobs.append((f"jitter-{n}", 0, dict(ref, jitter=n), ablation_plan, False))
        jobs.append(("all-mid", 0, dict(ref, **mid["elastic"], **mid["lag"], **mid["noise"], **mid["jitter"]), ablation_plan, True))
    if mode == "plant-worst":
        # the four together at the grid's worst values, the encoders on either side, next to the
        # reference plant at the same gain
        ref = dict(nominal, **top)
        jobs.append(("ref", 0, ref, ablation_plan, False))
        for sense in ("link", "motor"):
            cfg = dict(ref, **worst["elastic"], **worst["lag"], **worst["noise"], **worst["jitter"])
            jobs.append((f"all-worst-{sense}-w{int(w)}", 0, dict(cfg, sense=sense), ablation_plan, sense == "link"))
    if mode in ("plant-cited", "plant-cited-worst"):
        # the reference plant with the cited rotor inertia, rigid and elastic
        ref = dict(nominal, **top)
        heavy = dict(ref, armature=[rotor] * 3)
        jobs.append(("ref", 0, ref, ablation_plan, False))
        jobs.append(("ref-rotor", 0, heavy, ablation_plan, False))
    if mode == "plant-cited":
        # stiffness over the cited range, the damping ratio over 0.02 to 0.2, either side sensed; the
        # four together at the cited middle values and at the cited worst values
        for K in (1e4, 3e4, 6e4):
            for z in (0.02, 0.05, 0.2):
                for sense in ("link", "motor"):
                    jobs.append((f"elastic-{int(K)}-z{z}-{sense}", 0, dict(heavy, **elastic(K, zeta=z, rotor=rotor, sense=sense)), ablation_plan, False))
        for name, v in (("cited-mid", cited), ("cited-worst", cited_worst)):
            for sense in ("link", "motor"):
                cfg = dict(heavy, **v["elastic"], **v["lag"], **v["noise"], **v["jitter"])
                jobs.append((f"{name}-{sense}", 0, dict(cfg, sense=sense), ablation_plan, sense == "link"))
    if mode == "plant-cited-worst":
        # the four together at the cited worst values at this gain
        for sense in ("link", "motor"):
            cfg = dict(heavy, **cited_worst["elastic"], **cited_worst["lag"], **cited_worst["noise"], **cited_worst["jitter"])
            jobs.append((f"cited-worst-{sense}-w{int(w)}", 0, dict(cfg, sense=sense), ablation_plan, sense == "link"))
    return jobs


def one(job, outdir=None, sup=None):
    """Run one job with the supervisor `sup` (the executable when None); return the per-move
    records, the event log and the supervisor transcript."""
    tag, seed, cfg, p, keep = job
    sup = sup or sim.supervisor()
    o = sim.run(scene, cfg, p, sup)
    sup.close()
    recs = sim.analyse(scene, cfg, o)
    if keep and outdir is not None:
        tr = o["trace"]
        np.savez_compressed(outdir / "traces" / f"{tag}.npz", **{k: v for k, v in tr.items()},
                            moves=json.dumps([{k: (v.tolist() if isinstance(v, np.ndarray) else v) for k, v in mv.items()} for mv in o["moves"]]),
                            events=json.dumps(o["events"]), cfg=json.dumps(cfg, default=str))
    c = {k: cfg[k] for k in ("omega", "delta", "payload", "coulomb", "viscous", "armature", "model", "counts", "cutoff", "delay", "limit", "fault")}
    c.update({k: cfg.get(k) for k in ("stiffness", "joint_damping", "sense", "lag", "enc_noise", "jitter")})
    c.update({k: cfg.get(k) for k in ("model_rotor", "model_payload", "envelope")})
    c.update(pos_tol_deg=str(cfg["pos_tol_deg"]), vel_tol=str(cfg["vel_tol"]))
    lines = [dict(r, run=tag, seed=seed, supervisor=sup.kind, cfg=c) for r in recs]
    ev = dict(run=tag, seed=seed, supervisor=sup.kind, events=o["events"], fault_motion_deg=o.get("fault_motion_deg"))
    if "unstable_t" in o:
        ev["unstable_t"] = o["unstable_t"]
    return lines, ev, sup.transcript
