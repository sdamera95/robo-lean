# Figures of the MuJoCo evaluation of the cell, from a campaign directory, in SVG and PDF.
# Usage: uv run python figures.py <outdir> [figdir]
import json
import logging
import sys
from fractions import Fraction as F
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

import arm

out = Path(sys.argv[1])
figdir = Path(sys.argv[2]) if len(sys.argv) > 2 else out / "figures"
figdir.mkdir(parents=True, exist_ok=True)
logging.getLogger("fontTools").setLevel(logging.ERROR)
plt.rcParams.update({
    "font.family": "serif", "font.serif": ["cmr10"], "mathtext.fontset": "cm",
    "axes.formatter.use_mathtext": True, "axes.unicode_minus": True,
    "font.size": 7.5, "axes.labelsize": 7.5, "xtick.labelsize": 7, "ytick.labelsize": 7, "legend.fontsize": 7,
    "axes.linewidth": 0.5, "xtick.major.width": 0.5, "ytick.major.width": 0.5, "xtick.major.size": 2.5,
    "ytick.major.size": 2.5, "xtick.major.pad": 2, "ytick.major.pad": 2, "axes.labelpad": 2,
    "lines.linewidth": 0.9, "axes.spines.top": False, "axes.spines.right": False,
    "pdf.fonttype": 42, "svg.fonttype": "path",
})
BLUE, GREEN, ORANGE, VERM, DARK, GREY = "#0072B2", "#009E73", "#E69F00", "#D55E00", "0.2", "0.55"
scene = arm.load_scene()
m0 = float(F(9, 100))


def save(fig, name):
    fig.savefig(figdir / f"cell-{name}.pdf")
    fig.savefig(figdir / f"cell-{name}.svg")
    plt.close(fig)


S = json.load(open(out / "summary.json"))
dw, dd = S["design_point"]["omega"], S["design_point"]["delta"]
design = rf"$\omega={dw}$ rad/s, $\delta={dd}$ rad"


def load(name):
    return [json.loads(l) for l in open(out / f"{name}.jsonl")]


def trace(tag):
    z = np.load(out / "traces" / f"{tag}.npz")
    return {k: z[k] for k in z.files}, json.loads(str(z["moves"])), json.loads(str(z["events"])), json.loads(str(z["cfg"]))


def box_faces(lo, hi):
    x = np.array([[lo[0], lo[1], lo[2]], [hi[0], lo[1], lo[2]], [hi[0], hi[1], lo[2]], [lo[0], hi[1], lo[2]],
                  [lo[0], lo[1], hi[2]], [hi[0], lo[1], hi[2]], [hi[0], hi[1], hi[2]], [lo[0], hi[1], hi[2]]])
    f = [[0, 1, 2, 3], [4, 5, 6, 7], [0, 1, 5, 4], [2, 3, 7, 6], [1, 2, 6, 5], [0, 3, 7, 4]]
    return [x[i] for i in f]


# ------------------------------------------------------------------
# the scene with the arm and one cycle's swept links

tr, moves, events, cfg = trace(f"c{dw}-{dd}-0000")
# the first pick-place cycle: from leaving home up to the return to lift_pick after the place slot
placed = next(i for i, mv in enumerate(moves) if arm.waypoints(scene)[mv["to"]]["role"] == "place")
cyc = moves[1:next(i for i in range(placed, len(moves)) if moves[i]["to"] == "lift_pick") + 1]
t_end = cyc[-1]["t_end"]
q = tr["q"][(tr["t"] <= t_end)][::400]
P = arm.points(q)
cellcol = {"pick": ORANGE, "cross": BLUE, "place": GREEN}
fig = plt.figure(figsize=(6.9, 2.9))
fig.subplots_adjust(left=0.0, right=0.98, wspace=0.25)
ax = fig.add_subplot(1, 2, 1, projection="3d", computed_zorder=False)
for o in scene["obstacles"]:
    if o["kind"] == "box":
        ax.add_collection3d(Poly3DCollection(box_faces(o["lo"], o["hi"]), facecolor="0.75", edgecolor="0.45", linewidth=0.3, alpha=0.45))
xx, yy = np.meshgrid([-1.0, 1.0], [-0.25, 1.0])
ax.plot_surface(xx, yy, 0 * xx, color="0.9", alpha=0.35, linewidth=0)
xx, zz = np.meshgrid([-1.0, 1.0], [0, 1.0])
ax.plot_surface(xx, 0 * xx - 0.25, zz, color="0.85", alpha=0.25, linewidth=0)
for p in P:
    ax.plot(p[:, 0], p[:, 1], p[:, 2], color=BLUE, alpha=0.25, linewidth=0.6)
ax.plot(P[:, 2, 0], P[:, 2, 1], P[:, 2, 2], color=VERM, linewidth=1.0, label="tool path")
home = arm.points(arm.waypoints(scene)["home"]["rad"])
ax.plot(home[:, 0], home[:, 1], home[:, 2], color=DARK, linewidth=2.2, solid_capstyle="round", label="arm at home")
ax.plot([0, 0], [0, 0], [0, arm.l0], color=DARK, linewidth=3)
for name, w in arm.waypoints(scene).items():
    p = arm.tool(w["rad"])
    ax.scatter(*p, s=6, color={"pick": ORANGE, "place": GREEN}.get(w["role"], DARK), depthshade=False, zorder=5)
ax.set_xlim(-0.9, 0.9), ax.set_ylim(-0.3, 1.0), ax.set_zlim(0, 0.9)
ax.set_box_aspect((1.8, 1.3, 0.9))
ax.view_init(elev=24, azim=-62)
ax.set_xlabel("$x$ (m)", labelpad=-6), ax.set_ylabel("$y$ (m)", labelpad=-6)
ax.text2D(1.09, 0.58, "$z$ (m)", transform=ax.transAxes, fontsize=7.5)
ax.tick_params(pad=-2, labelsize=6)
ax.legend(loc="upper left", frameon=False, fontsize=6.5)
ax.set_title("(a) scene, one cycle's swept links (" + design + ")", fontsize=7.5, pad=0)
ax2 = fig.add_subplot(1, 2, 2)
for o in scene["obstacles"]:
    if o["kind"] == "box":
        ax2.add_patch(plt.Rectangle(o["lo"][:2], o["hi"][0] - o["lo"][0], o["hi"][1] - o["lo"][1], color="0.75", zorder=1))
        ax2.text((o["lo"][0] + o["hi"][0]) / 2, o["hi"][1] + 0.02, o["name"], ha="center", fontsize=6.5, color=DARK)
ax2.axhspan(-0.4, -0.25, color="0.85", zorder=0)
ax2.text(0, -0.33, "rear wall", ha="center", fontsize=6.5, color=DARK)
for mv in cyc:
    sel = (tr["t"] >= mv["t0"]) & (tr["t"] <= mv["t_end"])
    pt = arm.tool(tr["q"][sel][::50])
    b = np.array(mv["b"]); a = np.array(mv["a"])
    ax2.plot(pt[:, 0], pt[:, 1], color=VERM, linewidth=0.9)
el = P[:, 1]
ax2.plot(el[:, 0], el[:, 1], ".", color=BLUE, markersize=1.2, label="elbow")
ax2.plot(P[:, 2, 0], P[:, 2, 1], ".", color=VERM, markersize=1.2, label="tool")
for name, w in arm.waypoints(scene).items():
    p = arm.tool(w["rad"])
    ax2.plot(p[0], p[1], "o", markersize=2.5, color={"pick": ORANGE, "place": GREEN}.get(w["role"], DARK))
ax2.plot(0, 0, "s", color=DARK, markersize=3)
ax2.set_aspect("equal")
ax2.set_xlim(-1.0, 1.0), ax2.set_ylim(-0.4, 1.0)
ax2.set_xlabel("$x$ (m)"), ax2.set_ylabel("$y$ (m)")
ax2.text(-0.75, 0.9, "pick side", fontsize=6.5, color=ORANGE), ax2.text(0.45, 0.9, "place side", fontsize=6.5, color=GREEN)
ax2.set_title("(b) top view: tool and elbow over the cycle", fontsize=7.5)
save(fig, "scene")

# ------------------------------------------------------------------
# measured against certified over the campaign

R = load(f"campaign-{dw}-{dd}")
w, dl = R[0]["cfg"]["omega"], R[0]["cfg"]["delta"]
e = np.array([r["e_over_delta"] for r in R])
z = np.array([r["z_over_wdelta"] for r in R])
dist = np.array([min(min(r["dist"].values()), min(r["dist_ref"].values())) for r in R])
dist_o = {o: np.array([min(r["dist"][o], r["dist_ref"][o]) for r in R]) for o in R[0]["dist"]}
lag = np.array([r["k_end"] - r["k0"] for r in R if r["outcome"] == "finish"])
dn = np.array([r["d_total"] for r in R])
pay = np.array([r["cfg"]["payload"] for r in R])
tool = np.array([r["finish"]["tool_err"] for r in R if r["finish"]])
fig, axs = plt.subplots(1, 4, figsize=(6.9, 1.85))
ax = axs[0]
bins = np.linspace(0, 1.05, 43)
ax.hist(e, bins=bins, color=BLUE, alpha=0.8, label=r"$\max|e_i|/\delta$")
ax.hist(z, bins=bins, histtype="step", color=VERM, label=r"$\max|z_i|/(\omega\delta)$")
ax.axvline(1, color=DARK, linestyle="--", linewidth=0.7)
ax.text(0.97, ax.get_ylim()[1] * 0.5, "certified", rotation=90, ha="right", va="center", fontsize=6.5, color=DARK)
ax.set_xlabel("tube use per move"), ax.set_ylabel("moves")
ax.legend(frameon=False, loc="upper center", fontsize=6.2)
ax.set_title(rf"(a) tube, $\delta={dd}$ rad", fontsize=7.5)
ax = axs[1]
cols = {"table": GREY, "divider": VERM, "shelf": GREEN, "rear_wall": BLUE}
for o, v in dist_o.items():
    ax.step(np.sort(v), np.arange(1, len(v) + 1) / len(v), where="post", color=cols.get(o, DARK), label=o.replace("_", " "))
ax.axvline(scene["clearance"], color=DARK, linestyle="--", linewidth=0.7)
ax.text(scene["clearance"] + 0.01, 0.55, "certified $c$", fontsize=6.5, color=DARK, rotation=90, va="center")
ax.set_xlim(0, max(0.7, dist.max() + 0.05))
ax.set_xlabel("min distance per move (m)"), ax.set_ylabel("fraction of moves")
ax.legend(frameon=False, fontsize=6, loc="lower right")
ax.set_title("(b) clearance", fontsize=7.5)
ax = axs[2]
ks, cnt = np.unique(lag, return_counts=True)
ax.bar(ks, cnt, width=0.8, color=BLUE)
due = round(R[0]["due"] - R[0]["k0"])
bound = 25
ax.axvline(due, color=DARK, linestyle="--", linewidth=0.7)
ax.axvline(bound + 1, color=VERM, linestyle=":", linewidth=0.9)
ax.text(due - 0.7, cnt.max() * 0.5, r"due: $k_0+\lceil T/h\rceil$", rotation=90, ha="right", va="center", fontsize=6.5)
ax.text(bound + 0.7, cnt.max() * 0.5, "timeout", rotation=90, ha="right", va="center", fontsize=6.5, color=VERM)
ax.set_xlim(17, 28)
ax.set_xlabel("finish boundary $-\\,k_0$"), ax.set_ylabel("moves")
ax.set_title("(c) finish time", fontsize=7.5)
ax = axs[3]
sharp = np.array([r["minvd_over_w2delta"] for r in R])
ax.scatter(pay, sharp, s=2.5, color=BLUE, alpha=0.6, linewidths=0, zorder=3, label=r"$\max_i|(\hat M^{-1}d)_i|/(\omega^2\delta)$ (assumed)")
ax.scatter(pay, dn / (m0 * w**2 * dl), s=1.5, color=VERM, alpha=0.25, linewidths=0, label=r"$\|d\|_2/(m_0\omega^2\delta)$ (secondary)")
ax.axhline(1, color=DARK, linestyle="--", linewidth=0.7)
ax.set_ylim(0, max(1.5, (dn / (m0 * w**2 * dl)).max() * 1.45))
ax.set_xlabel("payload (kg)"), ax.set_ylabel("measured / allowed")
ax.legend(frameon=False, fontsize=6, loc="upper left", markerscale=4, borderaxespad=0.1)
ax.set_title(rf"(d) disturbance, $\omega^2\delta={round(w**2 * dl)}$ rad/s$^2$", fontsize=7.5)
fig.suptitle(f"randomized campaign, {len({r['run'] for r in R})} runs, {len(R)} moves, design point " + design, fontsize=7.5, y=0.985)
fig.tight_layout(w_pad=0.6, rect=(0, 0, 1, 0.97))
save(fig, "campaign")

# ------------------------------------------------------------------
# the fault run: a seized base joint, the timeout and the faulted supervisor

tr, moves, events, cfg = trace("fault-yaw")
t = tr["t"]
fig, axs = plt.subplots(2, 1, figsize=(3.4, 2.6), sharex=True, gridspec_kw=dict(height_ratios=[1.4, 1]))
ax = axs[0]
A = np.array([[0, 0, 0]] + [mv["a"] for mv in moves]); B = np.array([[0, 0, 0]] + [mv["b"] for mv in moves])
T0 = np.array([0.0] + [mv["t0"] for mv in moves])
home = arm.waypoints(scene)["home"]["rad"]
A[0] = B[0] = home
i = tr["mv"] + 1
s = arm.quintic((t - T0[i]) / cfg["T"])[0]
r = A[i] + s[:, None] * (B[i] - A[i])
tto = [mv for mv in moves if mv["outcome"] == "timeout"][0]["t_end"]
keep = t <= tto
ax.plot(t[keep], np.degrees(r[keep, 0]), color=GREY, linestyle="--", label=r"reference $r_0$")
ax.plot(t, np.degrees(tr["q"][:, 0]), color=BLUE, label=r"base yaw $\theta_0$")
fe = [e for e in events if e["cmd"] == "fault"][0]
tf = fe["t"]
ax.axvline(tf, color=VERM, linewidth=0.7)
held = np.degrees(np.abs(tr["q"][t >= tf, 0] - tr["q"][t >= tf, 0][0]).max())
ax.text(tf + 0.1, 40, "joint seizes", color=VERM, fontsize=6.5)
ax.text(tf - 0.15, 18, f"held: moves {round(held, 4)} deg\nafter the seizure", color=DARK, fontsize=6.2, ha="right")
ax.set_title("fault run, " + design, fontsize=7.5)
ax.axvline(tto, color=DARK, linewidth=0.7, linestyle=":")
ax.set_ylabel("angle (deg)")
ax.legend(frameon=False, fontsize=6.2, loc="lower left")
ax = axs[1]
k, age, ages = 0, 0, []
for e in events:
    if e["cmd"] == "admit" and e["ans"] == "ok":
        age = 0
    if e["cmd"] == "tick":
        age += 1
    if e["cmd"] in ("finish", "timeout"):
        age = 0
    ages.append((e["k"] * cfg["h"], age))
ages = np.array(ages)
ax.step(ages[:, 0], ages[:, 1], where="post", color=BLUE)
ax.axhline(cfg["bound"], color=VERM, linestyle="--", linewidth=0.7)
ax.text(0.1, cfg["bound"] + 1, "bound", color=VERM, fontsize=6.5)
for e in events:
    if e["cmd"] == "timeout":
        ax.annotate("timeout: faulted;\nnext admit blocked", (e["k"] * cfg["h"], 25), (e["k"] * cfg["h"] + 0.15, 9), fontsize=6.5,
                    arrowprops=dict(arrowstyle="-", linewidth=0.5))
ax.set_ylim(0, 30)
ax.set_xlabel("time (s)"), ax.set_ylabel("supervisor age")
fig.tight_layout(h_pad=0.4)
save(fig, "fault")

# ------------------------------------------------------------------
# stress: the bounds against payload and friction

fig, axs = plt.subplots(1, 2, figsize=(6.9, 2.1), sharey=True)
for ax, key, lab, ttl in ((axs[0], "stress-payload", "payload (kg)", "(a) payload sweep"), (axs[1], "stress-friction", "Coulomb friction per joint (N m)", "(b) friction sweep")):
    L = S[key]["levels"]
    ax.set_title(ttl + ", " + design, fontsize=7.5)
    v = np.array([x["level"] for x in L])
    ax.plot(v, [x["hyp_sharp"] for x in L], "v-", color=VERM, markersize=2.5, label=r"$\max|(\hat M^{-1}d)_i|/(\omega^2\delta)$")
    ax.plot(v, [x["hyp"] for x in L], "o--", color=VERM, markersize=2.5, alpha=0.6, label=r"$\max\|d\|_2/(m_0\omega^2\delta)$")
    ax.plot(v, [x["tube_e"] for x in L], "s-", color=BLUE, markersize=2.5, label=r"$\max|e_i|/\delta$")
    ax.plot(v, [scene["clearance"] / max(x["dist_min"], 1e-3) for x in L], "^-", color=GREEN, markersize=2.5, label=r"$c\,/\,$min distance")
    ax.plot(v, [x["torque_peak"] / 150 for x in L], "d-", color=ORANGE, markersize=2.5, label="peak commanded torque / 150 N m")
    ax.axhline(1, color=DARK, linestyle="--", linewidth=0.7)
    late = [x["level"] for x in L if x["timeouts"] or x["late"]]
    if late:
        ax.axvspan(min(late), v.max(), color="0.9", zorder=0)
        ax.text(min(late), 0.1, " late finishes\n and timeouts", fontsize=6.5, color=DARK, transform=ax.get_xaxis_transform())
    ax.set_yscale("log")
    ax.set_xlabel(lab)
axs[0].set_ylabel("measured / certified")
h, l = axs[0].get_legend_handles_labels()
fig.legend(h, l, frameon=False, fontsize=6.5, loc="upper center", ncol=5)
fig.tight_layout(w_pad=0.6, rect=(0, 0, 1, 0.86))
save(fig, "stress")
print("figures in", figdir)
