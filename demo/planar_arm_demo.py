# Planar two-link arm under PD control, with every request, admission, rejection, tick,
# finish and timeout decided by the Lean executable supervisor (RoboLean/Demo/Main.lean)
# running as a subprocess: by default the native executable that `lake build` compiles
# (`lake exe planar-arm-supervisor`), or the command in ROBO_LEAN_SUPERVISOR, for example the
# interpreter `lake env lean --run RoboLean/Demo/Main.lean`. The simulation is floating point
# and unverified; it illustrates the loop, it is not evidence for any theorem.

import json
import os
import shlex
import subprocess
from fractions import Fraction as F
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import solve_ivp

repo = Path(__file__).resolve().parent.parent
out = Path(__file__).resolve().parent / "out"
out.mkdir(exist_ok=True)

# ------------------------------------------------------------------
# arm parameters (the demo's choice; MLS prints none)
# homogeneous bars: centre of mass at mid-link, I_zi = m_i l_i^2 / 12

l1, l2 = F(1), F(1, 2)
m1, m2 = 1.0, 1.0
r1, r2 = float(l1) / 2, float(l2) / 2
Iz1, Iz2 = m1 * float(l1) ** 2 / 12, m2 * float(l2) ** 2 / 12

# MLS (4.10), printed p. 165, as in RoboLean.Examples.PlanarTwoLinkDynamics,
# planarTwoLinkArm_massMatrix and planarTwoLinkArm_coriolisMatrix
al = Iz1 + Iz2 + m1 * r1 ** 2 + m2 * (float(l1) ** 2 + r2 ** 2)
be = m2 * float(l1) * r2
de = Iz2 + m2 * r2 ** 2

# PD with compensation of N (N = 0 in the horizontal plane), K_p = K_v = I, the gains of
# RoboLean.Examples.PlanarTwoLinkControl,
# planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque'
Kp = np.eye(2)
Kv = np.eye(2)

# supervisor loop settings (the demo's choice, tuned by experiment)
period = 0.5
bound = 18
tol = 0.02
hold_after = 8

# scenario: (arrival period, x, y), exact rationals in the frame of planarArmXY
scenario = [
    (0, F(1), F(1, 2)),
    (3, F(3, 2), F(1)),
    (5, F(0), F(1)),
    (8, F(1, 4), F(1, 8)),
    (10, F(-1), F(1, 2)),
    (12, F(1, 2), F(-1)),
    (14, F(-2), F(1)),
    (60, F(6, 5), F(-1, 2)),
    (62, F(3, 5), F(1, 5)),
    (64, F(9, 10), F(6, 5)),
    (66, F(0), F(-1, 5)),
]
q0 = np.zeros(2)

# ------------------------------------------------------------------
# dynamics, kinematics and inverse kinematics


def field(t, z, qd):
    q, v = z[:2], z[2:]
    c, s = np.cos(q[1]), np.sin(q[1])
    M = np.array([[al + 2 * be * c, de + be * c], [de + be * c, de]])
    C = np.array([[-be * s * v[1], -be * s * (v[0] + v[1])], [be * s * v[0], 0.0]])
    tau = -Kv @ v - Kp @ (q - qd)
    return np.concatenate([v, np.linalg.solve(M, tau - C @ v)])


def xy(q):
    # planarArmXY in RoboLean.Examples.WorkspaceControl; q has shape (2, ...)
    a, b = float(l1), float(l2)
    return np.array([a * np.cos(q[0]) + b * np.cos(q[0] + q[1]), a * np.sin(q[0]) + b * np.sin(q[0] + q[1])])


def ik(x, y):
    # MLS (3.16), printed p. 98, the minus branch theta1 = atan2(y, x) - beta, theta2 = pi - alpha
    # (RoboLean.Examples.PlanarTwoLinkInverseKinematics, planarTwoLink_inverseKinematics_minus);
    # the arccos arguments are clipped to [-1, 1] in floating point, which is unverified
    a, b = float(l1), float(l2)
    r = np.hypot(x, y)
    alpha = np.arccos(np.clip((a * a + b * b - r * r) / (2 * a * b), -1, 1))
    beta = np.arccos(np.clip((r * r + a * a - b * b) / (2 * a * r), -1, 1))
    return np.array([np.arctan2(y, x) - beta, np.pi - alpha])


def annulus(t):
    # the guard in exact rational arithmetic, computed independently of the executable
    s = t[0] * t[0] + t[1] * t[1]
    return (l1 - l2) ** 2 <= s <= (l1 + l2) ** 2


# ------------------------------------------------------------------
# supervisor subprocess and protocol

cmd = os.environ.get("ROBO_LEAN_SUPERVISOR", "lake exe planar-arm-supervisor")
proc = subprocess.Popen(shlex.split(cmd), cwd=repo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
lines = []
now = 0.0


def fmt(q):
    return str(q.numerator) if q.denominator == 1 else str(q.numerator) + "/" + str(q.denominator)


def targets(w):
    if w == "-":
        return []
    return [tuple(F(c) for c in p.split(",")) for p in w.split(";")]


def parse(ans):
    kv = dict(w.split("=") for w in ans[3:].split())
    return {"busy": kv["busy"] == "true", "age": int(kv["age"]), "requested": targets(kv["requested"]),
            "commanded": targets(kv["commanded"]), "rejected": targets(kv["rejected"]),
            "timedOut": targets(kv["timedOut"])}


def send(line):
    # every ok answer carries the executable's state, which the loop takes as the truth
    global s
    proc.stdin.write(line + "\n")
    proc.stdin.flush()
    ans = proc.stdout.readline().strip()
    lines.append({"t": now, "sent": line, "answer": ans})
    assert ans.startswith("ok ") or ans.startswith("blocked "), (line, ans)
    if ans.startswith("ok "):
        s = parse(ans)
    return ans


def act(word, t=None):
    return send(word if t is None else word + " " + fmt(t[0]) + " " + fmt(t[1]))


# ------------------------------------------------------------------
# admission policy

events = []
checks = []
residuals = []
pending = []


def event(kind, t, ans):
    events.append({"t": now, "kind": kind, "target": [fmt(t[0]), fmt(t[1])], "answer": ans})


def decide(t, verdict, word, ans):
    # verdict is the guard value the executable's answer implies: Action.blocker checks
    # not-requested, then not-reachable, then not-idle, so admit ok and blocked not-idle
    # mean reachable, blocked not-reachable and reject ok mean not reachable
    g = annulus(t)
    checks.append({"t": now, "target": [fmt(t[0]), fmt(t[1])], "action": word, "answer": ans,
                   "executable_reachable": verdict, "python_reachable": g, "agree": verdict == g})
    assert verdict == g, (t, ans)


def try_admit(t):
    # admit a requested target; reject it if unreachable, keep it pending if the arm is busy
    global qd
    ans = act("admit", t)
    if ans.startswith("ok"):
        decide(t, True, "admit", ans)
        assert s["busy"] and s["commanded"] == [t] and t not in s["requested"], ans
        qd = ik(float(t[0]), float(t[1]))
        res = float(np.hypot(*(xy(qd) - np.array([float(t[0]), float(t[1])]))))
        residuals.append({"target": [fmt(t[0]), fmt(t[1])], "theta_d": qd.tolist(), "residual": res})
        pending.remove(t)
        event("admit", t, ans)
        return True
    if ans == "blocked not-idle":
        decide(t, True, "admit", ans)
        event("blocked", t, ans)
        return False
    assert ans == "blocked not-reachable", ans
    decide(t, False, "admit", ans)
    event("blocked", t, ans)
    ans = act("reject", t)
    assert ans.startswith("ok"), ans
    decide(t, False, "reject", ans)
    assert t in s["rejected"] and t not in s["requested"], ans
    pending.remove(t)
    event("reject", t, ans)
    return False


def admit_next():
    for t in list(pending):
        if try_admit(t):
            return


# ------------------------------------------------------------------
# event loop over supervisor periods

s = None
ans = send("params " + fmt(l1) + " " + fmt(l2) + " " + str(bound))
assert ans.startswith("ok") and not s["busy"] and s["age"] == 0 and s["requested"] == [], ans

z = np.concatenate([q0, np.zeros(2)])
qd = q0.copy()
dense_t, dense_z, dense_qd = [], [], []
samples = []
k = 0
hold = 0
while hold <= hold_after:
    for t in [(x, y) for j, x, y in scenario if j == k]:
        ans = act("request", t)
        assert ans.startswith("ok") and t in s["requested"], ans
        pending.append(t)
        event("request", t, ans)
        try_admit(t)

    assert sorted(pending) == sorted(s["requested"]), s
    samples.append({"t": now, "theta": z[:2].tolist(), "theta_dot": z[2:].tolist(), "theta_d": qd.tolist(),
                    "end_effector": xy(z[:2]).tolist(), "age": s["age"], "busy": s["busy"]})

    sol = solve_ivp(field, (now, now + period), z, args=(qd,), t_eval=np.linspace(now, now + period, 11), rtol=1e-9, atol=1e-11)
    assert sol.success, sol.message
    dense_t.append(sol.t[:-1])
    dense_z.append(sol.y[:, :-1])
    dense_qd.append(np.repeat(qd[:, None], 10, axis=1))
    z = sol.y[:, -1]
    now += period
    k += 1

    p = xy(z[:2])
    if s["busy"]:
        t = s["commanded"][0]
        if np.hypot(p[0] - float(t[0]), p[1] - float(t[1])) <= tol:
            ans = act("finish")
            assert ans.startswith("ok") and not s["busy"] and s["commanded"] == [], ans
            event("finish", t, ans)
            qd = z[:2].copy()
            admit_next()
        elif s["age"] == bound:
            ans = act("timeout")
            assert ans.startswith("ok") and not s["busy"] and t in s["timedOut"], ans
            event("timeout", t, ans)
            qd = z[:2].copy()
            admit_next()
        else:
            age = s["age"]
            ans = act("tick")
            assert ans.startswith("ok") and s["busy"] and s["age"] == age + 1, ans

    done = k > max(j for j, x, y in scenario) and not pending and not s["busy"]
    hold = hold + 1 if done else 0
    assert k < 2000, "scenario did not finish"

send("quit")
final = s
proc.stdin.close()
assert proc.wait() == 0

# ------------------------------------------------------------------
# outcomes per target

outcome = {}
for e in events:
    if e["kind"] in ("admit", "finish", "timeout", "reject"):
        outcome[tuple(e["target"])] = e["kind"]
table = [{"target": [fmt(x), fmt(y)], "r": float(np.hypot(float(x), float(y))), "inside": annulus((x, y)),
          "outcome": outcome[(fmt(x), fmt(y))]} for j, x, y in scenario]
for row in table:
    print(row["target"], round(row["r"], 3), row["inside"], row["outcome"])
print("max IK residual", max(r["residual"] for r in residuals))
print("guard checks", len(checks), "all agree", all(c["agree"] for c in checks))

# ------------------------------------------------------------------
# run log

log = {
    "parameters": {"note": "the demo's choice; MLS prints no numeric parameters",
                   "l1": fmt(l1), "l2": fmt(l2), "m1": m1, "m2": m2, "r1": r1, "r2": r2, "Iz1": Iz1, "Iz2": Iz2,
                   "alpha": al, "beta": be, "delta": de, "Kp": Kp.tolist(), "Kv": Kv.tolist(), "q0": q0.tolist()},
    "supervisor": {"bound": bound, "period": period, "tolerance": tol, "command": cmd, "cwd": str(repo)},
    "policy": "finish when the end effector is within the tolerance of the commanded target, else timeout at "
              "age = bound, else tick; on finish or timeout the set point becomes the current configuration "
              "until the next admission",
    "scenario": [{"period": j, "target": [fmt(x), fmt(y)]} for j, x, y in scenario],
    "outcomes": table,
    "protocol": lines,
    "events": events,
    "ik_residuals": residuals,
    "guard_checks": checks,
    "samples": samples,
    "final_state": {key: (v if not isinstance(v, list) else [[fmt(a), fmt(b)] for a, b in v]) for key, v in final.items()},
}
(out / "run-log.json").write_text(json.dumps(log, indent=1))

# ------------------------------------------------------------------
# plots

T = np.concatenate(dense_t)
Z = np.concatenate(dense_z, axis=1)
QD = np.concatenate(dense_qd, axis=1)
P = xy(Z[:2])
ink, muted = "#0b0b0b", "#898781"
blue, orange, aqua, yellow, red = "#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e34948"
plt.rcParams.update({"font.size": 9, "axes.spines.top": False, "axes.spines.right": False,
                     "axes.edgecolor": muted, "axes.labelcolor": ink, "xtick.color": muted, "ytick.color": muted})


def save(fig, name):
    fig.savefig(out / (name + ".svg"), bbox_inches="tight")
    fig.savefig(out / (name + ".pdf"), bbox_inches="tight")
    plt.close(fig)


fig, ax = plt.subplots(figsize=(6, 6))
c = np.linspace(0, 2 * np.pi, 400)
for rad in (float(l1 - l2), float(l1 + l2)):
    ax.plot(rad * np.cos(c), rad * np.sin(c), color=muted, lw=1, ls="--")
ax.plot(P[0], P[1], color=blue, lw=1.5, label="end-effector path")
style = {"finish": (aqua, "o", "finished"), "timeout": (yellow, "s", "timed out"), "reject": (red, "X", "rejected")}
for kind, (col, mk, lab) in style.items():
    pts = np.array([[float(x), float(y)] for j, x, y in scenario if outcome[(fmt(x), fmt(y))] == kind])
    if len(pts):
        ax.scatter(pts[:, 0], pts[:, 1], color=col, marker=mk, s=60, edgecolor="white", lw=1, zorder=3, label=lab)
for i, (j, x, y) in enumerate(scenario):
    ax.annotate(str(i + 1), (float(x), float(y)), xytext=(5, 5), textcoords="offset points", color=ink)
ax.set_aspect("equal")
ax.set_xlabel("x")
ax.set_ylabel("y")
ax.set_title("End-effector path, annulus 1/2 <= r <= 3/2, targets by outcome", color=ink)
ax.legend(frameon=False, loc="lower left", fontsize=8)
save(fig, "path")

fig, axs = plt.subplots(2, 1, figsize=(8, 5), sharex=True)
for i, ax in enumerate(axs):
    ax.plot(T, Z[i], color=blue, lw=1.5, label="theta" + str(i + 1))
    ax.plot(T, QD[i], color=orange, lw=1.5, ls="--", label="set point")
    ax.set_ylabel("theta" + str(i + 1) + " (rad)")
    ax.legend(frameon=False, fontsize=8, loc="upper right")
axs[1].set_xlabel("time (s)")
axs[0].set_title("Joint angles and set points", color=ink)
save(fig, "joints")

st = np.array([d["t"] for d in samples])
age = np.array([d["age"] for d in samples])
busy = np.array([d["busy"] for d in samples])
fig, axs = plt.subplots(2, 1, figsize=(11, 5.5), sharex=True, gridspec_kw={"height_ratios": [1, 1.3]})
ax = axs[0]
d = np.diff(np.concatenate([[0], busy.astype(int), [0]]))
for i, (a, b) in enumerate(zip(np.flatnonzero(d == 1), np.flatnonzero(d == -1))):
    ax.axvspan(st[a], st[b], color=blue, alpha=0.12, lw=0, label="busy" if i == 0 else None)
ax.step(st, age, where="post", color=blue, lw=1.5, label="age")
ax.axhline(bound, color=muted, lw=1, ls="--")
ax.text(st[0], bound + 0.4, "bound = " + str(bound), color=muted, fontsize=8)
ax.set_ylabel("age (ticks)")
ax.set_ylim(0, bound + 5)
ax.legend(frameon=False, fontsize=8, loc="upper right", ncol=2)
ax.set_title("Supervisor timeline", color=ink)
ax = axs[1]
kinds = ["request", "admit", "blocked not-idle", "blocked not-reachable", "reject", "finish", "timeout"]
cols = {"request": muted, "admit": blue, "blocked": orange, "reject": red, "finish": aqua, "timeout": yellow}
index = {(fmt(x), fmt(y)): i + 1 for i, (j, x, y) in enumerate(scenario)}
for e in events:
    yk = kinds.index(e["answer"] if e["kind"] == "blocked" else e["kind"])
    ax.scatter([e["t"]], [yk], color=cols[e["kind"]], s=40, zorder=3)
    lab = str(index[tuple(e["target"])])
    ax.annotate(lab, (e["t"], yk), xytext=(3, 4), textcoords="offset points", fontsize=7, color=ink)
ax.set_yticks(range(len(kinds)))
ax.set_yticklabels(kinds)
ax.set_ylim(-0.6, len(kinds) - 0.4)
ax.set_xlabel("time (s)")
save(fig, "timeline")
