# One pick-place cycle, on the ideal plant and on the realistic plant, with the per-move numbers.
# Usage: uv run python cycle.py [outdir]
import json
import sys
import time
from pathlib import Path

import numpy as np

import arm
import sim

out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("out")
out.mkdir(parents=True, exist_ok=True)
scene = arm.load_scene()
plan = ["lift_pick", "pick_2", "lift_pick", "place_2", "lift_place", "place_2", "lift_place", "lift_pick"]

realistic = dict(sim.nominal, limit=150.0, coulomb=[2.0, 2.0, 1.0], viscous=[1.0, 1.0, 0.5], armature=[0.05] * 3,
                 counts=2**18, cutoff=100.0, delay=True, payload=1.0)


def go(name, cfg):
    sup = sim.supervisor()
    t = time.time()
    o = sim.run(scene, cfg, plan, sup)
    sup.close()
    recs = sim.analyse(scene, cfg, o)
    print(name, "supervisor", sup.kind, "wall s", round(time.time() - t, 1), "sim s", round(o["trace"]["t"][-1], 1))
    for r in recs:
        print(" ", r["frm"], "->", r["to"], r["outcome"], "k0", r["k0"], "end", r["k_end"], "due", r["due"],
              "e/d", round(r["e_over_delta"], 4), "z/wd", round(r["z_over_wdelta"], 4),
              "|d|", round(r["d_total"], 2), "m0", round(r["m0_visited"], 3),
              "min dist", round(min(r["dist"].values()), 3), "tau", round(max(r["tau_cmd_peak"]), 1),
              "tool err", None if r["finish"] is None else round(r["finish"]["tool_err"], 5))
    rej = [e for e in o["events"] if e["cmd"] == "reject"]
    print("  rejected", [e["target"] for e in rej])
    with open(out / f"cycle-{name}.jsonl", "w") as f:
        for r in recs:
            f.write(json.dumps(dict(r, run=name, cfg={k: v for k, v in cfg.items()})) + "\n")
    return o, recs


go("ideal", sim.nominal)
go("realistic", realistic)
