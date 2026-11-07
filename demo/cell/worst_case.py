# The worst case over the plant class of the nominal-model campaign at the design point
# (w, delta) = (50, 3/100) of the two quantities the theorem's hypotheses bound: the acceleration
# quantity max_i |(M^-1 d)_i| / (w^2 delta) (against 1) and the speed sample error max |v_s - v|
# (against 3/10 rad/s); the position sample error (against 1/50 rad) is recorded, not searched.
# The class: the rotor inertia error, the Coulomb level and the viscous coefficient in the
# campaign's ranges, the mass error inside the proved condition
#   |dm| + 7/2 |e| + (f_c + 4 f_v) / 60 <= 3/2,
# the part's nominal mass in [0, 5] kg, the stiffness in [1e4, 6e4] N m/rad, the damping ratio in
# [0.05, 0.2] and the drive lag in [0.5, 1] ms. Three searches:
#   corners: every combination of the extremes of the ranges, the mass error at the edge of the
#     budget left by the other errors with either sign, on the middle plan (one cycle, the stress
#     runs' plan) and on the plans of campaign runs 404 and 179 (largest acceleration quantity) and
#     290 (largest speed sample error), each with its run's plant seed;
#   vertices: the vertices of the proved condition itself (one error at the whole budget, the
#     rotor error down to J' = 3/2), outside the campaign's ranges, at the middle of the other
#     ranges with the part at 5/2 and 5 kg, on the middle plan and on run 404's plan;
#   search: Nelder-Mead from the five campaign runs with the largest acceleration quantity and the
#     five with the largest speed sample error, over the continuous variables in the unit box of
#     their ranges (the per-joint friction keeps the starting run's proportions and scales with its
#     largest joint), the mass error projected onto the budget's edge when the condition binds,
#     the plan and the plant seed of the starting run fixed; at most 60 runs per start, and a stop
#     once the initial simplex is done and the best value has improved by less than 1 percent over
#     the last ten runs.
# Writes one JSON line per run to <outdir>/corners.jsonl, vertices.jsonl and search.jsonl, the
# tables and the searches' traces to <outdir>/summary.json, and prints the corner table, the
# vertices and the best value per start.
# Usage: uv run python worst_case.py <outdir> <workers>
import itertools
import json
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

import jobs
import sim

outdir, workers = Path(sys.argv[1]), int(sys.argv[2])
w, delta = 50.0, 0.03
env = jobs.envelope_at(w, delta)
R = jobs.nominal_ranges
eps_q, eps_v = float(jobs.eps_q), float(jobs.eps_v)
base = dict(sim.nominal, omega=w, delta=delta, **sim.tolerances(w, delta, jobs.eps_q, jobs.eps_v))
camp = jobs.nominal_campaign(500, w, delta)
plans = {"middle": (jobs.plan(np.random.default_rng([20261107, 94, 1, 0]), 1, inject=0), 0)}
for s in (404, 179, 290):
    plans[f"run{s}"] = (camp[s][3], s)


def left(x, dm=0.0):
    """The left side of the proved condition for the configuration x with the mass error dm."""
    return jobs.envelope_lhs(env, dm, x["e"], x["coulomb"], x["viscous"])


def edge(x, sign):
    """x with the mass error at the edge of the budget left by its other errors."""
    return dict(x, dm=sign * (env["budget"] - left(x)))


def evaluate(job):
    """One run of the configuration x on the named plan; its two quantities, the position sample
    error, the moves where the quantities peak and the run's outcomes."""
    group, tag, x, pname = job
    p, seed = plans[pname]
    cfg = dict(jobs.nominal_run(base, x["e"], x["part"], x["dm"], x["coulomb"], x["viscous"], x["K"], x["zeta"], x["lag"]), plant_seed=seed)
    t = time.time()
    lines, ev, _ = jobs.one((tag, seed, cfg, p, False))
    a = np.array([r["minvd_over_w2delta"] for r in lines])
    v = np.array([r["meas_v_max"] for r in lines])
    q = np.array([r["meas_q_max"] for r in lines])
    legs = [r["frm"] + "->" + r["to"] for r in lines]
    ok = np.array([r["outcome"] == "finish" and r["k_end"] == r["due"] for r in lines])
    return dict(group=group, tag=tag, plan=pname, seed=seed, x=x, dm_applied=cfg["envelope"]["dm_applied"], lhs=cfg["envelope"]["lhs"],
                accel=float(a.max()), accel_move=legs[int(a.argmax())], speed=float(v.max()), speed_move=legs[int(v.argmax())],
                pos=float(q.max()), moves=len(lines), finish_at_due=int(ok.sum()), other=[r["outcome"] for r in lines if r["outcome"] != "finish"],
                saturated=int(sum(r["saturated"] for r in lines)), unstable_t=ev.get("unstable_t"), wall_s=time.time() - t)


def show(r):
    x = r["x"]
    print(r["tag"], r["plan"], "dm", round(r["dm_applied"], 3), "e", round(x["e"], 3), "fc", round(max(x["coulomb"]), 2), "fv", round(max(x["viscous"]), 2),
          "part", round(x["part"], 2), "K", round(x["K"]), "zeta", round(x["zeta"], 3), "lag ms", round(1e3 * x["lag"], 3), "lhs", round(r["lhs"], 3),
          "accel", round(r["accel"], 4), r["accel_move"], "speed", round(r["speed"], 4), r["speed_move"], "pos", round(r["pos"], 5),
          "due", r["finish_at_due"], "of", r["moves"], "sat", r["saturated"], "unstable", r["unstable_t"])


def run_all(group, todo):
    out = []
    with Pool(workers) as pool, open(outdir / f"{group}.jsonl", "w") as f:
        for r in pool.imap(evaluate, todo, chunksize=1):
            f.write(json.dumps(r) + "\n")
            f.flush()
            out.append(r)
    return out


# ------------------------------------------------------------------
# corners and vertices
outdir.mkdir(parents=True, exist_ok=True)
t0 = time.time()
corners = []
for pname in plans:
    for e, fc, fv, part, K, zeta, lag, sign in itertools.product(R["e"], R["coulomb"], R["viscous"], R["part"], R["stiffness"], R["zeta"], R["lag"], (1, -1)):
        x = edge(dict(e=e, coulomb=[fc] * 3, viscous=[fv] * 3, part=part, K=K, zeta=zeta, lag=lag), sign)
        corners.append(("corner", f"corner-{pname}-{len(corners):04d}", x, pname))
corner_runs = run_all("corners", corners)

b = env["budget"]
mid = dict(e=0.0, coulomb=[0.0] * 3, viscous=[0.0] * 3, K=3e4, zeta=0.125, lag=0.00075, dm=0.0)
J_low = 1.5 - jobs.rotor
vertices = [dict(mid, dm=b), dict(mid, dm=-b), dict(mid, e=b / env["rotor"]),
            edge(dict(mid, e=J_low), 1), edge(dict(mid, e=J_low), -1),
            dict(mid, coulomb=[b / env["friction"]] * 3), dict(mid, viscous=[b / (env["friction"] * env["speed"])] * 3)]
todo = [("vertex", f"vertex-{pname}-{i}-part{part}", dict(x, part=part), pname)
        for pname in ("middle", "run404") for part in (2.5, 5.0) for i, x in enumerate(vertices)]
vertex_runs = run_all("vertices", todo)
t1 = time.time()

for r in corner_runs:
    show(r)
for pname in plans:
    rs = [r for r in corner_runs if r["plan"] == pname]
    ia, iv = np.argmax([r["accel"] for r in rs]), np.argmax([r["speed"] for r in rs])
    print("corners", pname, "max accel", round(rs[ia]["accel"], 4), rs[ia]["tag"], "max speed", round(rs[iv]["speed"], 4), rs[iv]["tag"],
          "max pos", round(max(r["pos"] for r in rs), 5), "all at due", all(r["finish_at_due"] == r["moves"] for r in rs))
for r in vertex_runs:
    show(r)

# ------------------------------------------------------------------
# local search
lo =np.array([-b, R["e"][0], 0.0, 0.0, R["part"][0], np.log(R["stiffness"][0]), R["zeta"][0], R["lag"][0]])
hi = np.array([b, R["e"][1], R["coulomb"][1], R["viscous"][1], R["part"][1], np.log(R["stiffness"][1]), R["zeta"][1], R["lag"][1]])


def point(u, cs, vs):
    """The configuration at u in the unit box, the friction with the per-joint proportions cs and
    vs, the mass error projected onto the budget's edge."""
    y = lo + u * (hi - lo)
    x = dict(e=y[1], coulomb=(y[2] * cs).tolist(), viscous=(y[3] * vs).tolist(), part=y[4], K=float(np.exp(y[5])), zeta=y[6], lag=y[7])
    m = env["budget"] - left(x)
    return {k: float(v) if np.isscalar(v) else v for k, v in dict(x, dm=np.clip(y[0], -m, m)).items()}


def nelder_mead(u, step=0.15):
    """Nelder-Mead in the unit box, maximizing: yields the points to run and receives their values."""
    d = len(u)
    X = [u] + [np.clip(u + np.where(np.arange(d) == i, step if u[i] + step <= 1 else -step, 0.0), 0, 1) for i in range(d)]
    F = []
    for x in X:
        F.append((yield x))
    X, F = np.array(X), np.array(F)
    while True:
        o = np.argsort(-F)
        X, F = X[o], F[o]
        c = X[:-1].mean(0)
        xr = np.clip(2 * c - X[-1], 0, 1)
        fr = yield xr
        if fr > F[0]:
            xe = np.clip(3 * c - 2 * X[-1], 0, 1)
            fe = yield xe
            X[-1], F[-1] = (xe, fe) if fe > fr else (xr, fr)
        elif fr > F[-2]:
            X[-1], F[-1] = xr, fr
        else:
            xc = (c + X[-1]) / 2
            fc = yield xc
            if fc > F[-1]:
                X[-1], F[-1] = xc, fc
            else:
                for i in range(1, d + 1):
                    X[i] = (X[0] + X[i]) / 2
                    F[i] = yield X[i]


def search(start):
    """The search from one campaign run for one quantity; the trace of every run it made."""
    s, kind = start
    cfg = camp[s][2]
    ev = cfg["envelope"]
    c, v = np.array(cfg["coulomb"]), np.array(cfg["viscous"])
    zeta = cfg["joint_damping"][0] / (2 * np.sqrt(cfg["stiffness"][0] * cfg["armature"][0]))
    y = np.array([ev["dm"], ev["e"], c.max(), v.max(), ev["part"], np.log(cfg["stiffness"][0]), zeta, cfg["lag"]])
    gen = nelder_mead((y - lo) / (hi - lo))
    u, trace, seen, vals = next(gen), [], {}, []
    while True:
        key = tuple(np.round(u, 12))
        if key not in seen:
            r = evaluate(("search", f"search-{kind}-run{s}-{len(trace):02d}", point(u, c / c.max(), v / v.max()), f"run{s}"))
            seen[key] = r["accel"] if kind == "accel" else r["speed"]
            trace.append(dict(r, start=s, kind=kind, u=u.tolist()))
            vals.append(seen[key])
            best = np.maximum.accumulate(vals)
            if len(vals) >= 60 or (len(vals) >= len(u) + 11 and best[-1] < 1.01 * best[-11]):
                return trace
        u = gen.send(seen[key])


# the campaign runs at (50, 3/100) with the five largest acceleration quantities (0.638, 0.620,
# 0.565, 0.559, 0.530) and the five largest speed sample errors (0.220, 0.155, 0.149, 0.147, 0.143);
# each search's first run is its campaign run again
starts = [(404, "accel"), (179, "accel"), (185, "accel"), (8, "accel"), (279, "accel"),
          (290, "speed"), (396, "speed"), (338, "speed"), (324, "speed"), (110, "speed")]
for s, _ in starts:
    plans[f"run{s}"] = (camp[s][3], s)
traces = []
with Pool(workers) as pool, open(outdir / "search.jsonl", "w") as f:
    for tr in pool.imap(search, starts, chunksize=1):
        for r in tr:
            f.write(json.dumps(r) + "\n")
        f.flush()
        traces.append(tr)
t2 = time.time()

best = []
for (s, kind), tr in zip(starts, traces):
    vals = np.array([r[kind] for r in tr])
    i = int(vals.argmax())
    best.append(dict(start=s, kind=kind, first=float(vals[0]), best=float(vals[i]), runs=len(tr), at=tr[i]))
    print("start run", s, kind, "first run", round(vals[0], 4), "best", round(vals[i], 4), "after", len(tr), "runs")
    show(tr[i])

table = [dict(tag=r["tag"], plan=r["plan"], x=r["x"], dm_applied=r["dm_applied"], lhs=r["lhs"], accel=r["accel"], speed=r["speed"], pos=r["pos"],
              finish_at_due=r["finish_at_due"], moves=r["moves"]) for r in corner_runs]
summary = dict(omega=w, delta=delta, constants=env, eps_q=eps_q, eps_v=eps_v, ranges=R, plans={k: dict(plan=p, seed=s) for k, (p, s) in plans.items()},
               corners=table, vertices=vertex_runs, starts=best,
               traces=[dict(start=s, kind=kind, values=[r[kind] for r in tr], best=np.maximum.accumulate([r[kind] for r in tr]).tolist())
                       for (s, kind), tr in zip(starts, traces)],
               wall_s=dict(corners_and_vertices=t1 - t0, search=t2 - t1))
with open(outdir / "summary.json", "w") as f:
    json.dump(summary, f, indent=1)
print("wall s corners and vertices", round(t1 - t0), "search", round(t2 - t1))
