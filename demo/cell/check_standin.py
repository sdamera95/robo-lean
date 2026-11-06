# Differential check of the Python stand-in (the reference kept only for this check) against the
# cell program on the boundary protocol: the campaign runs at omega = 80, delta = 0.05 are driven by
# the stand-in, and every line sent to it is replayed through a fresh instance of the program, answer
# by answer. The program is started by the command in CELL_SUPERVISOR_CMD (default
# .lake/build/bin/cell-supervisor, run from the repository root). Prints the agreement or the first
# difference. Usage:
#   uv run python check_standin.py [runs] [workers] [earlier campaign jsonl to compare records with]
import json
import sys
from multiprocessing import Pool

import jobs
import sim
from standin_supervisor import Supervisor

nruns = int(sys.argv[1]) if len(sys.argv) > 1 else 500
workers = int(sys.argv[2]) if len(sys.argv) > 2 else 16


class StandIn(Supervisor):
    kind = "standin"

    def __init__(self):
        super().__init__()
        self.transcript = []

    def send(self, line):
        ans = super().send(line)
        self.transcript.append((line, ans))
        return ans

    def close(self):
        pass


def check(job):
    lines, _, tr = jobs.one(job, sup=StandIn())
    exe = sim.Exe()
    first = None
    for i, (cmd, ans) in enumerate(tr):
        got = exe.send(cmd)
        if got != ans and first is None:
            first = dict(run=job[0], line=i, cmd=cmd, standin=ans, exe=got)
    exe.close()
    return job[0], len(tr), first, [(r["k_end"], r["e_over_delta"]) for r in lines]


with Pool(workers) as pool:
    res = pool.map(check, jobs.campaign(nruns, 80.0, 0.05), chunksize=1)
diffs = [r[2] for r in res if r[2]]
print("runs", len(res), "answer lines compared", sum(r[1] for r in res), "runs with a difference", len(diffs))
print("first difference", diffs[0] if diffs else None)
if len(sys.argv) > 3:
    old = {}
    for l in open(sys.argv[3]):
        r = json.loads(l)
        old.setdefault(r["run"], []).append((r["k_end"], r["e_over_delta"]))
    same = sum(old.get(tag) == recs for tag, _, _, recs in res)
    print("runs whose finish boundaries and tube use equal the earlier stand-in campaign", same, "of", len(res))
