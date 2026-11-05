# Summary of a campaign directory: every measured quantity against the bound it is checked against,
# for the randomized campaign, the gain variants, the stress sweeps, the ablation and the fault run.
# Usage: uv run python summarize.py <outdir>   (writes <outdir>/summary.json)
import json
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np

import arm

out = Path(sys.argv[1])
scene = arm.load_scene()
m0 = float(F(9, 100))  # the inertia bound of the arm on the scene's envelope, as stated for the proof
clear = scene["clearance"]


def load(name):
    p = out / f"{name}.jsonl"
    return [json.loads(l) for l in open(p)] if p.exists() else []


def col(R, f):
    return np.array([f(r) for r in R], float)


def bounds(R):
    """Worst value of every checked quantity over the moves R, each as a ratio to its bound (a
    ratio above 1 is a violation), plus the raw extremes."""
    w = col(R, lambda r: r["cfg"]["omega"])
    dl = col(R, lambda r: r["cfg"]["delta"])
    fin = [r for r in R if r["outcome"] == "finish"]
    return dict(
        moves=len(R), finished=len(fin), timeouts=sum(r["outcome"] == "timeout" for r in R),
        late=sum(r["outcome"] == "finish" and r["k_end"] != r["due"] for r in R),
        tube_e=col(R, lambda r: r["e_over_delta"]).max(), tube_z=col(R, lambda r: r["z_over_wdelta"]).max(),
        speed=col(R, lambda r: r["ed_over_2wdelta"]).max(),
        hyp=(col(R, lambda r: r["d_total"]) / (m0 * w**2 * dl)).max(),
        hyp_fraction_ok=float((col(R, lambda r: r["d_total"]) <= m0 * w**2 * dl).mean()),
        hyp_sharp=col(R, lambda r: r["minvd_over_w2delta"]).max(),
        d_max=col(R, lambda r: r["d_total"]).max(), d_p99=float(np.percentile(col(R, lambda r: r["d_total"]), 99)),
        d_plant_max=col(R, lambda r: r["d_plant"]).max(),
        budget=float((m0 * w**2 * dl).max()),
        dist_min=col(R, lambda r: min(r["dist"].values())).min(),
        dist_ref_min=col(R, lambda r: min(r["dist_ref"].values())).min(),
        clearance_ratio=clear / min(col(R, lambda r: min(r["dist"].values())).min(), col(R, lambda r: min(r["dist_ref"].values())).min()),
        cell_excess_max=col(R, lambda r: r["cell_excess_rad"]).max(),
        torque_peak=col(R, lambda r: max(r["tau_cmd_peak"])).max(), saturated_steps=int(col(R, lambda r: r["saturated"]).sum()),
        tool_err_max=col(fin, lambda r: r["finish"]["tool_err"]).max() if fin else None,
        tool_ratio=(col(fin, lambda r: r["finish"]["tool_err"]).max() / fin[0]["tool_bound"]) if fin else None,
        min_m0_visited=col(R, lambda r: r["m0_visited"]).min(),
        hyp_sharp_fraction_ok=float((col(R, lambda r: r["minvd_over_w2delta"]) <= 1).mean()),
        meas_q_max=col(R, lambda r: r.get("meas_q_max", float("nan"))).max(),
        meas_v_max=col(R, lambda r: r.get("meas_v_max", float("nan"))).max(),
        due_boundaries=int(col(R, lambda r: r.get("due_boundaries", 0)).sum()),
        arrival_disagree=int(col(R, lambda r: r.get("arrival_disagree", 0)).sum()),
        finish_true_arrived=int(sum(bool(r.get("arrival_true_at_end")) for r in fin)),
    )


def fails(b):
    """The checked bounds that this group of moves violates."""
    f = []
    if b["hyp"] > 1: f.append("disturbance hypothesis")
    if b["hyp_sharp"] > 1: f.append("acceleration hypothesis")
    if b["tube_e"] > 1 or b["tube_z"] > 1: f.append("tube")
    if b["timeouts"] or b["late"]: f.append("finish time")
    if b["clearance_ratio"] > 1: f.append("clearance")
    if b["tool_ratio"] is not None and b["tool_ratio"] > 1: f.append("tool error")
    if b["torque_peak"] >= 150 - 1e-9: f.append("torque limit")
    if b["cell_excess_max"] > 0: f.append("inflated cell")
    return f


def clean(x):
    return {k: (round(float(v), 6) if isinstance(v, (float, np.floating)) else v) for k, v in x.items()}


S = {}
R = load("campaign")
if R:
    S["campaign"] = clean(bounds(R))
    S["campaign"]["runs"] = len({r["run"] for r in R})
    S["campaign"]["supervisor"] = sorted({r["supervisor"] for r in R})
    S["campaign"]["fails"] = fails(bounds(R))
    S["campaign"]["by_payload_bin"] = {}
    pay = col(R, lambda r: r["cfg"]["payload"])
    for lo in (0.0, 0.5, 1.0, 1.5):
        sel = [r for r, p in zip(R, pay) if lo <= p < lo + 0.5]
        if sel:
            b = bounds(sel)
            S["campaign"]["by_payload_bin"][f"{lo}-{lo + 0.5}"] = clean(dict(moves=b["moves"], hyp=b["hyp"], hyp_fraction_ok=b["hyp_fraction_ok"], tube_e=b["tube_e"], d_max=b["d_max"]))
R = load("omega")
for w in (40.0, 60.0):
    sel = [r for r in R if r["cfg"]["omega"] == w]
    if sel:
        b = bounds(sel)
        S[f"omega{int(w)}"] = dict(clean(b), fails=fails(b))
for mode, key, lab in (("stress-payload", "payload", "kg"), ("stress-friction", "coulomb", "N m")):
    R = load(mode)
    if not R:
        continue
    levels = sorted({r["cfg"][key] if key == "payload" else r["cfg"][key][0] for r in R})
    rows, first = [], {}
    for v in levels:
        sel = [r for r in R if (r["cfg"][key] if key == "payload" else r["cfg"][key][0]) == v]
        b = bounds(sel)
        f = fails(b)
        for x in f:
            first.setdefault(x, v)
        rows.append(dict(clean(dict(level=v, moves=b["moves"], hyp=b["hyp"], hyp_sharp=b["hyp_sharp"], tube_e=b["tube_e"], tube_z=b["tube_z"],
                                    timeouts=b["timeouts"], late=b["late"], dist_min=min(b["dist_min"], b["dist_ref_min"]),
                                    torque_peak=b["torque_peak"], tool_ratio=b["tool_ratio"] or -1, cell_excess_max=b["cell_excess_max"])), fails=f))
    S[mode] = dict(unit=lab, levels=rows, first_failure=first)
R = load("ablation")
if R:
    S["ablation"] = {run: clean(dict(d_max=bounds([r for r in R if r["run"] == run])["d_max"],
                                     tube_e=bounds([r for r in R if r["run"] == run])["tube_e"],
                                     hyp_sharp=bounds([r for r in R if r["run"] == run])["hyp_sharp"]))
                     for run in dict.fromkeys(r["run"] for r in R)}
R = load("fault")
if R:
    ev = {json.loads(l)["run"]: json.loads(l)["events"] for l in open(out / "fault-events.jsonl")}
    S["fault"] = {run: dict(outcomes=[(r["to"], r["outcome"], r["k0"], r["k_end"]) for r in R if r["run"] == run],
                            events=[e for e in ev[run] if e["cmd"] not in ("tick",)][-4:]) for run in ev}

json.dump(S, open(out / "summary.json", "w"), indent=1, default=float)
print(json.dumps(S, indent=1, default=float))
