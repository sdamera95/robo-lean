# The runs of the evaluation: the randomized campaign, the gain variants, the stress sweeps, the
# ablation of the disturbance and the fault run, each with a fixed seed, and the worker that runs
# one of them and returns its per-move records.
import json

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


def campaign(nruns, w, delta, keep=3):
    """The randomized campaign at gain w and tube radius delta; run s draws from the seed
    [20261105, s] whatever w and delta are."""
    out, tag = [], f"c{w:g}-{delta:g}-"
    for s in range(nruns):
        rng = np.random.default_rng([20261105, s])
        cfg = dict(sim.nominal, **fixed, **draw(rng), omega=w, delta=delta)
        out.append((f"{tag}{s:04d}", s, cfg, plan(rng, 4), s < keep))
    return out


def make(mode, nruns, w, delta):
    """The runs of one mode at gain w and tube radius delta."""
    if mode == "campaign":
        return campaign(nruns, w, delta)
    nominal = dict(sim.nominal, omega=w, delta=delta)
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
        p = ["lift_pick", "pick_2", "lift_pick", "lift_place", "place_2", "lift_place", "lift_pick"]
        top = dict(payload=ranges["payload"][1], coulomb=[ranges["coulomb"][1]] * 3, viscous=[ranges["viscous"][1]] * 3,
                   armature=[ranges["armature"][1]] * 3, limit=150.0, counts=2**18, cutoff=100.0, delay=True,
                   model=dict(mass=[ranges["mass"][1]] * 3, offset=[ranges["offset"][1]] * 3, inertia=[ranges["inertia"][1]] * 3))
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
                            events=json.dumps(o["events"]), cfg=json.dumps(cfg))
    c = {k: cfg[k] for k in ("omega", "delta", "payload", "coulomb", "viscous", "armature", "model", "counts", "cutoff", "delay", "limit", "fault")}
    lines = [dict(r, run=tag, seed=seed, supervisor=sup.kind, cfg=c) for r in recs]
    ev = dict(run=tag, seed=seed, supervisor=sup.kind, events=o["events"], fault_motion_deg=o.get("fault_motion_deg"))
    return lines, ev, sup.transcript
