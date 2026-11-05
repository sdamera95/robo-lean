# Differential test of two independent executable semantics of the planar arm's timeout
# supervisor: the Lean executable RoboLean.Demo.Main (as interpreted by `lake env lean --run`
# and as the native `lake exe planar-arm-supervisor`) and Veil's executable transition system
# of the same supervisor (Examples/RoboLean/PlanarArmTimeoutSupervisorReplay.lean in the
# sibling Veil project). Both replay the same action traces; the script compares the state after
# every action. A disagreement is reported and makes the script exit with status 1.
#
# Run: cd demo && uv run python veil_differential_test.py
# Environment: ROBO_LEAN_VEIL, the Veil project directory (default ../../robo-lean-veil from this
# file, the sibling of the repository).
#
# Traces: random traces drawn with numpy from a fixed seed over the demo's eleven targets
# (l1 = 1, l2 = 1/2, bound = 45, shorter than the demo loop's 232 so that commands time out within
# a trace), plus the protocol transcript supervisor-transcript.txt read with the executable's
# grammar.
#
# Action file out/veil-trace-actions.jsonl, JSON lines:
#   header {"trace": i, "targets": k, "reachable": [bools], "bound": n, "a": "1", "b": "1/2",
#     "points": [["x", "y"], ...]} (a, b and points are read only on the Lean side);
#   action {"trace": i, "step": j, "action": "request|admit|reject|finish|tick|timeout",
#     "target": t} (target index only for request, admit, reject).
# State files out/veil-trace-states.jsonl and out/lean-<interpreter|native>-states.jsonl,
# one line per action-file line:
#   {"trace": i, "step": j, "accepted": bool, "requested": [...], "commanded": [...],
#     "rejected": [...], "timedOut": [...], "busy": bool, "age": n} with sorted target indices,
#   step -1 for the initial state; Veil adds "successors" and "failures", Lean adds "blocked"
#   (the guard) for a refused action, whose state is read back with the protocol command `state`.
# Other outputs: out/veil-replay.log (Veil's output, exit code, wall time) and
# out/veil-differential-report.json (counts, first disagreements, accepted actions by kind).
#
# Limits: this is a finite test of agreement on the traces it runs, not a proof; the Lean
# compiler and interpreter, Veil's code extraction and the pipes between the processes are
# trusted.

import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

here = Path(__file__).resolve().parent
repo = here.parent
out = here / "out"
out.mkdir(exist_ok=True)
veil = Path(os.environ.get("ROBO_LEAN_VEIL", repo.parent / "robo-lean-veil")).resolve()
replay = "Examples/RoboLean/PlanarArmTimeoutSupervisorReplay.lean"
commands = {"interpreter": "lake env lean --run RoboLean/Demo/Main.lean",
            "native": "lake exe planar-arm-supervisor"}
fields = ["requested", "commanded", "rejected", "timedOut", "busy", "age"]
kinds = ["request", "admit", "reject", "finish", "tick", "timeout"]

# ------------------------------------------------------------------
# demo instance, exact guard and protocol helpers (as in planar_arm_demo.py)

l1, l2, bound = F(1), F(1, 2), 45
points = [(F(1), F(1, 2)), (F(3, 2), F(1)), (F(0), F(1)), (F(1, 4), F(1, 8)), (F(-1), F(1, 2)),
          (F(1, 2), F(-1)), (F(-2), F(1)), (F(6, 5), F(-1, 2)), (F(3, 5), F(1, 5)),
          (F(9, 10), F(6, 5)), (F(0), F(-1, 5))]


def annulus(a, b, t):
    # the guard in exact rational arithmetic, computed independently of either executable
    s = t[0] * t[0] + t[1] * t[1]
    return (a - b) ** 2 <= s <= (a + b) ** 2


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


def trace(a, b, n, pts, steps):
    return {"a": a, "b": b, "bound": n, "points": pts, "index": {p: i for i, p in enumerate(pts)},
            "reachable": [annulus(a, b, p) for p in pts], "steps": steps}


# ------------------------------------------------------------------
# random traces

seed = 20261027
ntraces, length = 200, 200
probs = [0.12, 0.12, 0.06, 0.02, 0.60, 0.08]
follow_p = 0.7

rng = np.random.default_rng(seed)
kind = rng.choice(len(kinds), size=(ntraces, length), p=probs)
tgt = rng.integers(0, len(points), size=(ntraces, length))
# admit and reject take the target of the most recent request with probability follow_p
pos = np.where(kind == 0, np.arange(length), -1)
last = np.maximum.accumulate(pos, axis=1)
recent = np.take_along_axis(tgt, np.maximum(last, 0), axis=1)
follow = ((kind == 1) | (kind == 2)) & (last >= 0) & (rng.random((ntraces, length)) < follow_p)
tgt = np.where(follow, recent, tgt)

traces = []
for i in range(ntraces):
    steps = [(kinds[k], int(t) if k < 3 else None) for k, t in zip(kind[i], tgt[i])]
    traces.append(trace(l1, l2, bound, points, steps))

# ------------------------------------------------------------------
# the protocol transcript as further traces, read with the executable's grammar

ratw = re.compile(r"-?[0-9]+(/[0-9]+|\.[0-9]+)?")
natw = re.compile(r"[0-9]+")


def rat(w):
    if not ratw.fullmatch(w) or ("/" in w and int(w.split("/")[1]) == 0):
        return None
    return F(w)


ntranscript = 0
cur = None
for line in (here / "supervisor-transcript.txt").read_text().splitlines():
    w = [x for x in line.strip().split(" ") if x]
    if w == ["quit"]:
        break
    if len(w) == 4 and w[0] == "params":
        a, b = rat(w[1]), rat(w[2])
        if a is not None and b is not None and a > 0 and b > 0 and natw.fullmatch(w[3]):
            cur = {"a": a, "b": b, "bound": int(w[3]), "steps": []}
            traces.append(cur)
            ntranscript += 1
        continue
    if cur is None:
        continue
    if len(w) == 3 and w[0] in kinds[:3] and rat(w[1]) is not None and rat(w[2]) is not None:
        cur["steps"].append((w[0], (rat(w[1]), rat(w[2]))))
    elif len(w) == 1 and w[0] in kinds[3:]:
        cur["steps"].append((w[0], None))

for i in range(ntraces, len(traces)):
    t = traces[i]
    pts = list(dict.fromkeys(p for _, p in t["steps"] if p is not None))
    assert pts, "a transcript trace has no target"
    traces[i] = trace(t["a"], t["b"], t["bound"], pts,
                      [(k, None if p is None else pts.index(p)) for k, p in t["steps"]])

# ------------------------------------------------------------------
# action file

actions_path = out / "veil-trace-actions.jsonl"
action_of = {}
with open(actions_path, "w") as f:
    for i, t in enumerate(traces):
        f.write(json.dumps({"trace": i, "targets": len(t["points"]), "reachable": t["reachable"],
                            "bound": t["bound"], "a": fmt(t["a"]), "b": fmt(t["b"]),
                            "points": [[fmt(x), fmt(y)] for x, y in t["points"]]}) + "\n")
        action_of[(i, -1)] = "params"
        for j, (k, p) in enumerate(t["steps"]):
            line = {"trace": i, "step": j, "action": k}
            if p is not None:
                line["target"] = p
            f.write(json.dumps(line) + "\n")
            action_of[(i, j)] = k if p is None else k + " " + str(p)

nactions = sum(len(t["steps"]) for t in traces)

# ------------------------------------------------------------------
# Veil side

veil_states = out / "veil-trace-states.jsonl"
env = dict(os.environ, ROBO_LEAN_TRACE_IN=str(actions_path), ROBO_LEAN_TRACE_OUT=str(veil_states))
start = time.time()
res = subprocess.run(["lake", "lean", replay], cwd=veil, env=env, capture_output=True, text=True)
veil_time = round(time.time() - start, 1)
(out / "veil-replay.log").write_text(
    "command: lake lean " + replay + "\ncwd: " + str(veil) + "\nexit code: " + str(res.returncode) +
    "\nwall time (s): " + str(veil_time) + "\nstdout:\n" + res.stdout + "stderr:\n" + res.stderr)
assert res.returncode == 0, res.stdout + res.stderr
veil_rows = [json.loads(l) for l in veil_states.read_text().splitlines() if l]
veil_rev = subprocess.run(["git", "-C", str(veil), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
replay_sha = hashlib.sha256((veil / replay).read_bytes()).hexdigest()

# ------------------------------------------------------------------
# Lean side


def indices(t, s):
    return {**{k: sorted(t["index"][p] for p in s[k]) for k in fields[:4]}, "busy": s["busy"], "age": s["age"]}


def lean_run(cmd):
    proc = subprocess.Popen(shlex.split(cmd), cwd=repo, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            text=True, bufsize=1)

    def send(line):
        proc.stdin.write(line + "\n")
        proc.stdin.flush()
        return proc.stdout.readline().strip()

    rows, answers = [], []
    for i, t in enumerate(traces):
        ans = send("params " + fmt(t["a"]) + " " + fmt(t["b"]) + " " + str(t["bound"]))
        answers.append(ans)
        assert ans.startswith("ok "), (i, ans)
        s = indices(t, parse(ans))
        rows.append({"trace": i, "step": -1, "accepted": True, **s})
        for j, (k, p) in enumerate(t["steps"]):
            line = k if p is None else k + " " + fmt(t["points"][p][0]) + " " + fmt(t["points"][p][1])
            ans = send(line)
            answers.append(ans)
            if ans.startswith("ok "):
                s = indices(t, parse(ans))
                rows.append({"trace": i, "step": j, "accepted": True, **s})
            else:
                assert ans.startswith("blocked "), (i, j, line, ans)
                # a refusal reports no state: ask for it, so that "unchanged" is observed
                st = send("state")
                answers.append(st)
                assert st.startswith("ok "), (i, j, st)
                s = indices(t, parse(st))
                rows.append({"trace": i, "step": j, "accepted": False, **s, "blocked": ans[8:]})
    answers.append(send("quit"))
    proc.stdin.close()
    assert proc.wait() == 0, cmd
    return rows, answers


lean = {}
for name, cmd in commands.items():
    start = time.time()
    rows, answers = lean_run(cmd)
    lean[name] = {"rows": rows, "answers": answers, "time": round(time.time() - start, 1)}
    with open(out / ("lean-" + name + "-states.jsonl"), "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

# ------------------------------------------------------------------
# comparison


def compare(rows, ref):
    assert len(rows) == len(ref), (len(rows), len(ref))
    agree = {k: 0 for k in ["accepted"] + fields}
    disagree = {k: 0 for k in agree}
    full, first = 0, []
    for r, v in zip(rows, ref):
        assert (r["trace"], r["step"]) == (v["trace"], v["step"]), (r, v)
        bad = [k for k in agree if r[k] != v[k]]
        for k in agree:
            if k in bad:
                disagree[k] += 1
            else:
                agree[k] += 1
        full += not bad
        if bad and len(first) < 20:
            first.append({"trace": r["trace"], "step": r["step"], "action": action_of[(r["trace"], r["step"])],
                          "fields": {k: {"lean": r[k], "veil": v[k]} for k in bad}})
    return {"lines": len(rows), "agree": agree, "disagree": disagree, "agree_all": full,
            "disagree_any": len(rows) - full, "first_disagreements": first}


results = {name: compare(lean[name]["rows"], veil_rows) for name in commands}

ai, an = lean["interpreter"]["answers"], lean["native"]["answers"]
assert len(ai) == len(an)
lean_mismatch = [{"line": n, "interpreter": x, "native": y} for n, (x, y) in enumerate(zip(ai, an)) if x != y]

succ = [v["successors"] for v in veil_rows if v["step"] >= 0]
successors = {"0": succ.count(0), "1": succ.count(1), "more": sum(m > 1 for m in succ)}
failures = sum(v.get("failures", 0) for v in veil_rows)

accepted = {k: 0 for k in kinds}
traces_with = {k: set() for k in kinds}
for r in lean["interpreter"]["rows"]:
    if r["step"] >= 0 and r["accepted"]:
        k = traces[r["trace"]]["steps"][r["step"]][0]
        accepted[k] += 1
        traces_with[k].add(r["trace"])
traces_with = {k: len(v) for k, v in traces_with.items()}

found = sum(r["disagree_any"] for r in results.values()) + len(lean_mismatch)

report = {
    "seed": seed,
    "random_traces": ntraces,
    "random_trace_length": length,
    "kind_probabilities": dict(zip(kinds, probs)),
    "follow_request_probability": follow_p,
    "transcript_traces": ntranscript,
    "traces": len(traces),
    "actions": nactions,
    "demo_instance": {"a": fmt(l1), "b": fmt(l2), "bound": bound, "points": [[fmt(x), fmt(y)] for x, y in points]},
    "lean_commands": {name: {"command": cmd, "cwd": str(repo), "wall_time_s": lean[name]["time"]}
                      for name, cmd in commands.items()},
    "veil": {"path": str(veil), "git_head": veil_rev, "replay_file": replay, "replay_sha256": replay_sha,
             "command": "lake lean " + replay, "exit_code": res.returncode, "wall_time_s": veil_time,
             "stdout": res.stdout.strip()},
    "lean_vs_veil": results,
    "interpreter_vs_native": {"lines": len(ai), "mismatches": len(lean_mismatch), "first": lean_mismatch[:20]},
    "veil_successors": successors,
    "veil_failures": failures,
    "accepted_by_kind": accepted,
    "traces_with_accepted_kind": traces_with,
    "disagreements": found,
}
(out / "veil-differential-report.json").write_text(json.dumps(report, indent=1))

print("seed", seed, "traces", len(traces), "(" + str(ntraces), "random,", ntranscript, "transcript)", "actions", nactions)
print("veil:", res.stdout.strip(), "in", veil_time, "s")
for name in commands:
    r = results[name]
    print(name, "vs veil:", r["lines"], "lines,", r["agree_all"], "agree on everything,",
          r["disagree_any"], "disagree;", "disagreements by field", r["disagree"], "in", lean[name]["time"], "s")
print("interpreter vs native:", len(ai), "answers,", len(lean_mismatch), "mismatches")
print("veil successors", successors, "failures", failures)
print("accepted by kind", accepted)
print("traces with an accepted action of each kind", traces_with)
print("disagreements", found)
sys.exit(1 if found else 0)
