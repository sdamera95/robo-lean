# Summary of an evaluation directory: the randomized campaign at every candidate (gain, tube radius)
# pair, the design point the selection rule picks, and the stress sweeps, ablation and fault run at
# that point, every measured quantity against its bound. Usage:
#   uv run python summarize.py <outdir> [<omega> <delta>]   (writes <outdir>/summary.json)
# A design point given on the command line overrides the rule's (both are recorded); the standstill
# torque dither from dither.py is included when <outdir>/dither.json exists.
import json
import sys
from pathlib import Path

from bounds import bounds, candidates, choose, clean, col, fails, load

out = Path(sys.argv[1])
S = {"campaign": {}}
for w, d in candidates:
    R = load(out, f"campaign-{w}-{d}")
    if R:
        b = bounds(R)
        S["campaign"][f"{w}-{d}"] = dict(clean(b), runs=len({r["run"] for r in R}), supervisor=sorted({r["supervisor"] for r in R}), fails=fails(b))
rule = choose(S["campaign"])
design = tuple(sys.argv[2:4]) if len(sys.argv) > 3 else rule
S["design_point_by_rule"] = dict(omega=rule[0], delta=rule[1]) if rule else None
S["design_point"] = dict(omega=design[0], delta=design[1]) if design else None
if (out / "dither.json").exists():
    S["standstill_dither"] = json.load(open(out / "dither.json"))
if design:
    w, d = design
    R = load(out, f"campaign-{w}-{d}")
    pay = col(R, lambda r: r["cfg"]["payload"])
    S["campaign_by_payload"] = {f"{lo}-{lo + 1}": clean({k: v for k, v in bounds([r for r, p in zip(R, pay) if lo <= p < lo + 1]).items()
                                                        if k in ("moves", "hyp_sharp", "hyp", "hyp_fraction_ok", "tube_e", "d_max", "acc_max")})
                                for lo in (0, 1, 2, 3, 4) if any(lo <= p < lo + 1 for p in pay)}
    for mode, key, unit in (("stress-payload", "payload", "kg"), ("stress-friction", "coulomb", "N m")):
        R = load(out, f"{mode}-{w}-{d}")
        if not R:
            continue
        level = (lambda r: r["cfg"]["payload"]) if key == "payload" else (lambda r: r["cfg"]["coulomb"][0])
        rows, first = [], {}
        for v in sorted({level(r) for r in R}):
            b = bounds([r for r in R if level(r) == v])
            f = fails(b)
            for x in f:
                first.setdefault(x, v)
            rows.append(dict(clean({k: b[k] for k in ("moves", "hyp_sharp", "acc_max", "hyp", "tube_e", "tube_z", "e_max", "timeouts", "late",
                                                     "dist_min", "torque_peak", "saturated_steps", "tool_ratio", "excursion_max")}), level=v, fails=f))
        S[mode] = dict(unit=unit, levels=rows, first_failure=first)
    R = load(out, f"ablation-{w}-{d}")
    if R:
        S["ablation"] = {run: clean({k: v for k, v in bounds([r for r in R if r["run"] == run]).items() if k in ("d_max", "acc_max", "hyp_sharp", "tube_e")})
                         for run in dict.fromkeys(r["run"] for r in R)}
    R = load(out, f"fault-{w}-{d}")
    if R:
        ev = [json.loads(l) for l in open(out / f"fault-{w}-{d}-events.jsonl")]
        S["fault"] = {e["run"]: dict(outcomes=[(r["to"], r["outcome"], r["k0"], r["k_end"]) for r in R if r["run"] == e["run"]],
                                     events=[x for x in e["events"] if x["cmd"] != "tick"][-4:],
                                     seized_joint_motion_deg=e.get("fault_motion_deg")) for e in ev}
json.dump(S, open(out / "summary.json", "w"), indent=1, default=float)
print(json.dumps(S, indent=1, default=float))
