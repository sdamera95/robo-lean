# Every measured quantity of a group of moves against the bound it is checked against, the bounds a
# group violates, and the rule that picks the design point among the candidate (gain, tube radius)
# pairs from the campaign records.
import json
from fractions import Fraction as F

import numpy as np

import arm

scene = arm.load_scene()
m0 = float(F(9, 100))  # the inertia bound of the arm on the scene's envelope, as stated for the proof
clear = scene["clearance"]
infl = scene["cell_inflation_rad"]
L = scene["tool_lipschitz_L"]
limit = 150.0
# candidate (gain, tube radius) pairs as written in the file names, in the order of preference of the
# selection rule; the last is a comparison only
candidates = [("120", "0.02"), ("80", "0.03"), ("80", "0.05"), ("60", "0.05")]


def load(out, name):
    p = out / f"{name}.jsonl"
    return [json.loads(l) for l in open(p)] if p.exists() else []


def col(R, f):
    return np.array([f(r) for r in R], float)


def bounds(R):
    """Worst value of every checked quantity over the moves R, in absolute units and as a ratio to
    its bound (a ratio above 1 is a violation)."""
    w = col(R, lambda r: r["cfg"]["omega"])
    dl = col(R, lambda r: r["cfg"]["delta"])
    fin = [r for r in R if r["outcome"] == "finish"]
    acc = col(R, lambda r: r["minvd_over_w2delta"]) * w**2 * dl
    dn = col(R, lambda r: r["d_total"])
    dist = np.minimum(col(R, lambda r: min(r["dist"].values())), col(R, lambda r: min(r["dist_ref"].values())))
    exc = col(R, lambda r: r["cell_excess_rad"]) + infl
    tool = col(fin, lambda r: r["finish"]["tool_err"]) if fin else np.array([np.nan])
    return dict(
        moves=len(R), finished=len(fin), timeouts=sum(r["outcome"] == "timeout" for r in R),
        late=sum(r["outcome"] == "finish" and r["k_end"] != r["due"] for r in R),
        acc_max=acc.max(), acc_budget=float((w**2 * dl).max()), hyp_sharp=col(R, lambda r: r["minvd_over_w2delta"]).max(),
        hyp_sharp_fraction_ok=float((col(R, lambda r: r["minvd_over_w2delta"]) <= 1).mean()),
        e_max=(col(R, lambda r: r["e_over_delta"]) * dl).max(), delta=float(dl.max()),
        tube_e=col(R, lambda r: r["e_over_delta"]).max(), tube_z=col(R, lambda r: r["z_over_wdelta"]).max(),
        d_max=dn.max(), budget=float((m0 * w**2 * dl).max()), hyp=(dn / (m0 * w**2 * dl)).max(),
        hyp_fraction_ok=float((dn <= m0 * w**2 * dl).mean()),
        d_plant_max=col(R, lambda r: r["d_plant"]).max(),
        dist_min=dist.min(), clearance=clear, clearance_ratio=clear / dist.min(),
        excursion_max=exc.max(), inflation=infl, excursion_fraction=float((exc > 0).mean()),
        tool_err_max=float(np.nanmax(tool)), tool_bound=float(L * dl.max()), tool_ratio=float(np.nanmax(tool) / (L * dl.max())),
        torque_peak=col(R, lambda r: max(r["tau_cmd_peak"])).max(), saturated_steps=int(col(R, lambda r: r["saturated"]).sum()),
        tau_step_max=col(R, lambda r: r.get("tau_step_max", np.nan)).max(),
        tau_step_rms=col(R, lambda r: r.get("tau_step_rms", np.nan)).max(),
        meas_q_max=col(R, lambda r: r["meas_q_max"]).max(), meas_v_max=col(R, lambda r: r["meas_v_max"]).max(),
        due_boundaries=int(col(R, lambda r: r["due_boundaries"]).sum()),
        arrival_disagree=int(col(R, lambda r: r["arrival_disagree"]).sum()),
        min_m0_visited=col(R, lambda r: r["m0_visited"]).min(),
    )


def fails(b):
    """The checked bounds that this group of moves violates."""
    f = []
    if b["hyp_sharp"] > 1: f.append("acceleration hypothesis")
    if b["hyp"] > 1: f.append("torque-norm hypothesis")
    if b["tube_e"] > 1 or b["tube_z"] > 1: f.append("tube")
    if b["timeouts"] or b["late"]: f.append("finish time")
    if b["clearance_ratio"] > 1: f.append("clearance")
    if b["tool_ratio"] > 1: f.append("tool error")
    if b["saturated_steps"] or b["torque_peak"] >= limit - 1e-9: f.append("torque limit")
    if b["excursion_max"] > infl: f.append("inflated cell")
    return f


def choose(table):
    """The first candidate (in the order of `candidates`, comparison excluded) on which every move
    finishes at k0 + ceil(T/h), nothing saturates and the acceleration ratio is at most 0.8."""
    for w, d in candidates[:3]:
        b = table.get(f"{w}-{d}")
        if b and not b["timeouts"] and not b["late"] and not b["saturated_steps"] and b["hyp_sharp"] <= 0.8:
            return w, d
    return None


def clean(x):
    return {k: (round(float(v), 6) if isinstance(v, (float, np.floating)) else v) for k, v in x.items()}
