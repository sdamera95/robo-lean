# One run per setting of the plant's further non-idealities (modes plant and plant-worst of jobs.py) in
# parallel, every decision by the cell program. Writes one JSON line per move to
# <outdir>/<mode>-<omega>-<delta>.jsonl, one line per run with its summary and wall time to
# <outdir>/<mode>-<omega>-<delta>-runs.jsonl, and prints one line per run: the largest
# max_i |(M^-1 d)_i| / (w^2 delta), the largest sample errors at the boundaries against 1/2000 rad and
# 1/5 rad/s, the largest |e_i| / delta, the moves' outcomes with k_end - k0, the smallest capsule
# distance, the peak commanded and applied torques and the wall time.
# Usage: uv run python plant_sweep.py <mode> <outdir> <workers> <omega> <delta>
import json
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import jobs


def timed(job):
    t = time.time()
    lines, ev, _ = jobs.one(job, outdir=outdir)
    return lines, ev, time.time() - t


mode, outdir, workers = sys.argv[1], Path(sys.argv[2]), int(sys.argv[3])
w, delta = float(sys.argv[4]), float(sys.argv[5])
(outdir / "traces").mkdir(parents=True, exist_ok=True)
todo = jobs.make(mode, 1, w, delta)
name = f"{mode}-{sys.argv[4]}-{sys.argv[5]}"
with Pool(workers) as pool:
    res = pool.map(timed, todo, chunksize=1)
runs = []
for (tag, _, cfg, _, _), (lines, ev, wall) in zip(todo, res):
    runs.append(dict(
        run=tag, omega=w, delta=delta, cfg=lines[0]["cfg"], wall_s=wall, sim_s=ev["events"][-1]["k"] * cfg["h"],
        unstable_t=ev.get("unstable_t"),
        minvd_over_w2delta=max(r["minvd_over_w2delta"] for r in lines),
        meas_q_max=max(r["meas_q_max"] for r in lines), meas_v_max=max(r["meas_v_max"] for r in lines),
        e_over_delta=max(r["e_over_delta"] for r in lines), z_over_wdelta=max(r["z_over_wdelta"] for r in lines),
        outcomes=[[r["outcome"], None if r["k_end"] is None else r["k_end"] - r["k0"]] for r in lines],
        dist_min=min(min(r["dist"].values()) for r in lines),
        tau_cmd_peak=max(max(r["tau_cmd_peak"]) for r in lines), tau_applied_peak=max(max(r["tau_applied_peak"]) for r in lines),
        saturated=sum(r["saturated"] for r in lines),
    ))
with open(outdir / f"{name}.jsonl", "w") as f:
    for lines, _, _ in res:
        for r in lines:
            f.write(json.dumps(r) + "\n")
with open(outdir / f"{name}-runs.jsonl", "w") as f:
    for r in runs:
        f.write(json.dumps(r) + "\n")
for r in runs:
    fin = [k for o, k in r["outcomes"] if o == "finish"]
    print(r["run"], "w", w, "d", delta, "minvd/w2d", round(r["minvd_over_w2delta"], 3),
          "q_s-q", round(r["meas_q_max"], 6), "v_f-v", round(r["meas_v_max"], 4), "e/d", round(r["e_over_delta"], 3),
          "finish", len(fin), "of", len(r["outcomes"]), "k_end-k0", sorted(set(fin)),
          "other", [o for o, _ in r["outcomes"] if o != "finish"], "dist", round(r["dist_min"], 4),
          "tau cmd", round(r["tau_cmd_peak"], 1), "applied", round(r["tau_applied_peak"], 1), "sat", r["saturated"],
          "unstable", r["unstable_t"], "wall s", round(r["wall_s"], 1))
