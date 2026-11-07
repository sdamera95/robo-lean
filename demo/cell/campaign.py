# Run one mode of the evaluation with the cell program taking every decision. One JSON
# line per move goes to <outdir>/<mode>.jsonl, the event logs to <outdir>/<mode>-events.jsonl and
# the traces of selected runs to <outdir>/traces/. Usage:
#   uv run python campaign.py <mode> <outdir> <runs> <workers> <omega> <delta> [queue [urgent]]
# with mode one of: campaign, stress-payload, stress-friction, ablation, fault and the nominal-model
# modes of jobs.py; the files are named <mode>-<omega>-<delta>. With `queue` the program is the queue
# supervisor's (cell-supervisor-queue) at the capacity of jobs.py, and the files are named
# <mode>-<omega>-<delta>-queue; with `queue urgent` the planner also sends the urgent scenario's
# requests, and the files are named <mode>-<omega>-<delta>-queue-urgent.
import json
import sys
import time
from functools import partial
from multiprocessing import Pool
from pathlib import Path

import jobs

mode, outdir = sys.argv[1], Path(sys.argv[2])
nruns, workers = int(sys.argv[3]), int(sys.argv[4])
w, delta = float(sys.argv[5]), float(sys.argv[6])
extra = sys.argv[7:]
assert extra in ([], ["queue"], ["queue", "urgent"]), "the options are queue or queue urgent"
queue = dict(capacity=jobs.capacity, urgent=jobs.urgent if "urgent" in extra else None) if extra else None
todo = jobs.make(mode, nruns, w, delta, queue)
name = "-".join([mode, sys.argv[5], sys.argv[6]] + extra)
(outdir / "traces").mkdir(parents=True, exist_ok=True)
t = time.time()
with Pool(workers) as pool:
    res = pool.map(partial(jobs.one, outdir=outdir), todo, chunksize=1)
with open(outdir / f"{name}.jsonl", "w") as f:
    for lines, _, _ in res:
        for r in lines:
            f.write(json.dumps(r) + "\n")
with open(outdir / f"{name}-events.jsonl", "w") as f:
    for _, ev, _ in res:
        f.write(json.dumps(ev) + "\n")
print(name, "runs", len(todo), "moves", sum(len(l) for l, _, _ in res), "wall s", round(time.time() - t, 1),
      "supervisor", sorted({r[1]["supervisor"] for r in res}))
