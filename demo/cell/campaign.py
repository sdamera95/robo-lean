# Run one mode of the evaluation with the supervisor executable driving every decision. One JSON
# line per move goes to <outdir>/<mode>.jsonl, the event logs to <outdir>/<mode>-events.jsonl and
# the traces of selected runs to <outdir>/traces/. Usage:
#   uv run python campaign.py <mode> <outdir> [runs] [workers]
# with mode one of: campaign, omega, stress-payload, stress-friction, ablation, fault.
import json
import sys
import time
from functools import partial
from multiprocessing import Pool
from pathlib import Path

import jobs

mode, outdir = sys.argv[1], Path(sys.argv[2])
nruns = int(sys.argv[3]) if len(sys.argv) > 3 else 500
workers = int(sys.argv[4]) if len(sys.argv) > 4 else 16
todo = jobs.make(mode, nruns)
(outdir / "traces").mkdir(parents=True, exist_ok=True)
t = time.time()
with Pool(workers) as pool:
    res = pool.map(partial(jobs.one, outdir=outdir), todo, chunksize=1)
with open(outdir / f"{mode}.jsonl", "w") as f:
    for lines, _, _ in res:
        for r in lines:
            f.write(json.dumps(r) + "\n")
with open(outdir / f"{mode}-events.jsonl", "w") as f:
    for _, ev, _ in res:
        f.write(json.dumps(ev) + "\n")
print(mode, "runs", len(todo), "moves", sum(len(l) for l, _, _ in res), "wall s", round(time.time() - t, 1),
      "supervisor", sorted({r[1]["supervisor"] for r in res}))
