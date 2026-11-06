# A short run through the boundary protocol: one or two pick-place cycles on the realistic plant at
# (omega, delta) = (80, 0.03), every decision the program's. Prints one line per move and writes the
# moves and the transcript (each line sent, then the answer) to <outdir>.
# Usage: uv run python smoke.py <outdir> [cycles]
import json
import sys
import time
from pathlib import Path

import arm
import sim

out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
cycles = int(sys.argv[2]) if len(sys.argv) > 2 else 1
scene = arm.load_scene()
# the first cycle asks once for the unlinked move lift_pick -> place_2, which the program rejects;
# the second crosses through cross_low
plan = ["lift_pick", "pick_2", "lift_pick", "place_2", "lift_place", "place_2", "lift_place", "lift_pick"]
if cycles > 1:
    plan += ["pick_1", "lift_pick", "cross_low", "lift_place", "place_1", "lift_place", "lift_pick"]
cfg = dict(sim.realistic, omega=80.0, delta=0.03, **sim.tolerances(80.0, 0.03))

sup = sim.supervisor()
t = time.time()
o = sim.run(scene, cfg, plan, sup)
sup.close()
recs = sim.analyse(scene, cfg, o)
print("command", sim.exe)
print("policy", sup.transcript[1][0])
print("boundaries", len(sup.transcript) - 2, "wall s", round(time.time() - t, 1), "sim s", round(o["trace"]["t"][-1], 1))
for r in recs:
    print(r["frm"], "->", r["to"], r["outcome"], "k0", r["k0"], "end", r["k_end"], "due", r["due"],
          "e/d", round(r["e_over_delta"], 4), "tool err", None if r["finish"] is None else round(r["finish"]["tool_err"], 5))
print("rejected", [e["target"] for e in o["events"] if e["cmd"] == "reject"])
with open(out / "smoke-moves.jsonl", "w") as f:
    for r in recs:
        f.write(json.dumps(r) + "\n")
with open(out / "smoke-transcript.txt", "w") as f:
    for line, ans in sup.transcript:
        f.write("> " + line + "\n< " + ans + "\n")
