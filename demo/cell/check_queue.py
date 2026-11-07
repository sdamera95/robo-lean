# Differential check of the Python reference of the queue supervisor's line protocol
# (queue_reference.py, written from the Lean definitions) against the compiled program: randomized
# sequences of per-action commands and of the boundary protocol are driven through the reference,
# and every line is replayed through a fresh instance of the program, answer by answer. The program
# is started by the command in CELL_SUPERVISOR_QUEUE_CMD (default
# .lake/build/bin/cell-supervisor-queue, run from the repository root). Fixed seeds. Prints the
# agreement or the first difference, and how often each refusal reason, each blocker and each
# answer occurred. `replay(transcript)` replays a list of (line, answer) pairs, for example the
# transcript of a simulated run. Usage:
#   uv run python check_queue.py [action sequences] [boundary sequences] [workers]
import os
import random
import shlex
import subprocess
import sys
from collections import Counter
from fractions import Fraction as F
from multiprocessing import Pool
from pathlib import Path

import arm
from queue_reference import QueueSupervisor, blocker_names, reason_names

repo = Path(arm.__file__).resolve().parents[2]
exe = os.environ.get("CELL_SUPERVISOR_QUEUE_CMD", ".lake/build/bin/cell-supervisor-queue")

scene = arm.load_scene()
cells = arm.cells(scene)
pool = [w["exact"] for w in arm.waypoints(scene).values()]
home = (F(0), F(-40), F(30))
# off the scene's table: two points inside the cross cell with fractional angles, two outside every cell
offscene = [(F(-7, 3), F(-40), F(30)), (F(1, 3), F(-61, 2), F(45)), (F(200), F(-1, 7), F(5)), (F(0), F(0), F(0))]
policy_line = "policy 1/10 2 3 33/10 262144"
cpr = 262144


def replay(transcript, cmd=exe):
    """Send every line of the transcript to a fresh program and compare its answers; a line whose
    recorded answer is None (a blank line) expects none. The first difference, or None."""
    p = subprocess.Popen(shlex.split(cmd), cwd=repo, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    first = None
    for i, (line, ans) in enumerate(transcript):
        p.stdin.write(line + "\n")
        p.stdin.flush()
        got = None if ans is None else p.stdout.readline().rstrip("\n")
        if got != ans and first is None:
            first = dict(line=i, cmd=line, reference=ans, exe=got)
    p.stdin.close()
    rest = p.stdout.read()
    p.wait()
    if rest and first is None:
        first = dict(line=len(transcript), cmd=None, reference=None, exe=rest)
    return first


# ------------------------------------------------------------------
# writing numbers and lines

def txt(rng, x):
    """A rational in one of the forms the program parses: n, n/d (not necessarily reduced) or n.f."""
    sign = "-" if x < 0 or (x == 0 and rng.random() < 0.1) else ""
    a = abs(x)
    forms = [str(a.numerator * 3) + "/" + str(a.denominator * 3), str(a.numerator) + "/" + str(a.denominator)]
    if a.denominator == 1:
        forms += [str(a.numerator)] * 3 + [str(a.numerator) + ".0"]
    if 10**6 % a.denominator == 0:
        d = a.numerator * 10**6 // a.denominator
        forms.append(str(d // 10**6) + "." + str(d % 10**6).zfill(6))
    return sign + rng.choice(forms)


def wtxt(rng, w):
    return " ".join(txt(rng, x) for x in w)


bad_numbers = ["4x", "1/0", "--3", "1.2.3", "1/2/3", "+3", "1e3", ".5", "5.", "-", "1/-2", "0x10"]


def cells_txt(rng, cl):
    return " ".join(wtxt(rng, lo) + " " + wtxt(rng, hi) for lo, hi in cl)


def params_line(rng, bound, cap, h, cl):
    return "params " + str(bound) + " " + str(cap) + " " + wtxt(rng, h) + (" " + cells_txt(rng, cl) if cl else "")


def bad_params(rng):
    good = "2 3 0 -40 30 " + cells_txt(rng, cells)
    return rng.choice([
        "params", "params 2 3 0 -40", "params x 3 0 -40 30", "params 2 3/1 0 -40 30", "params 2.0 3 0 -40 30",
        "params -1 3 0 -40 30", "params 2 3 0 -40 30 1 2 3", "params 2 3 0 -40 30 10 0 0 0 0 0",
        "params 2 3 0 -40 30 0 0 0 1 1 " + rng.choice(bad_numbers), "params " + good + " 1 2",
        "params " + good + " 5 5 5 4 6 6", "params 2 3 0 " + rng.choice(bad_numbers) + " 30",
    ])


def junk(rng):
    w = wtxt(rng, rng.choice(pool))
    return rng.choice([
        "request " + w, "request " + w + " high", "request 1 " + rng.choice(bad_numbers) + " 2 normal",
        "request " + rng.choice(bad_numbers) + " 0 0 bogus", "admit 1 2 3", "reject " + w, "finish now", "tick tock",
        "frobnicate", "state now", "quit please", "boundary", "boundary 0 0 0 0 0 0", "boundary 0 0 0 0 0 0 0",
        "request\t" + w + " normal", "state\x0b", "\ttick", "tick\r", "  state  ", "", "   ", "\t",
        "REQUEST " + w + " normal", "request " + w + " Normal", "policy 1/10 2 3 33/10", "policy 0 2 3 33/10 262144",
        "policy 1/10 2 -3 33/10 262144", "policy 1/10 2 3 33/10 0", "policy 1/10 x 3 33/10 262144",
    ])


# ------------------------------------------------------------------
# command sequences

class Sequence:
    """The reference with the transcript of every line and answer, and the counts of what happened."""

    def __init__(self):
        self.sup = QueueSupervisor()
        self.transcript = []
        self.count = Counter()

    def send(self, line):
        s = self.sup.s
        ans = self.sup.send(line)
        self.transcript.append((line, ans))
        c = self.count
        if ans is None:
            c["blank"] += 1
        elif ans.startswith("blocked "):
            c[ans] += 1
        elif ans.startswith("error expected boundary"):
            c["error expected boundary n"] += 1
        elif ans.startswith("error "):
            c[ans] += 1
        elif ans.startswith("ok acts="):
            for a in ans.split(" ")[1][5:].split(";"):
                c["act " + a.split(":")[0]] += 1
        for o in self.sup.outcomes:
            for r in o["reasons"]:
                c[r] += 1
            c["queued" if o["queued"] else "refused"] += 1
        if ans and ans.startswith("ok") and self.sup.p:
            cap = self.sup.p["capacity"]
            if cap and len(self.sup.s["requested"]) == cap and len(s["requested"]) < cap:
                c["full queue reached"] += 1
            if self.sup.s["faulted"] and not s["faulted"]:
                c["timeout"] += 1
                if s["requested"]:
                    c["timeout with a nonempty queue"] += 1
        if self.sup.admitted:
            c["admission recorded"] += 1
        return ans


def pick_request(rng, sup):
    """A request: mostly one linked to its predecessor, sometimes any waypoint, now and then off
    the scene's table."""
    prio = "urgent" if rng.random() < 0.3 else "normal"
    allw = pool + offscene
    if rng.random() < 0.1:
        return rng.choice(offscene), prio
    if sup.p is None or rng.random() < 0.3:
        return rng.choice(allw), prio
    base = sup.front(sup.s) if prio == "urgent" else sup.pred(sup.s)
    near = [w for w in allw if sup.linked(base, w)]
    return rng.choice(near or allw), prio


def action_sequence(seed):
    rng = random.Random(seed)
    se = Sequence()
    for _ in range(rng.randint(0, 2)):
        se.send(rng.choice(["state", "tick", "admit", "request 0 -40 30 normal", policy_line, "boundary 0 0 0 0 0 0 0", junk(rng)]))

    def new_params():
        if rng.random() < 0.1:
            se.send(bad_params(rng))
        cl = cells if rng.random() < 0.85 else [] if rng.random() < 0.5 else cells + [((F(-1, 2), F(-50), F(0)), (F(80), F(-35), F(40)))]
        h = home if rng.random() < 0.7 else rng.choice(pool + offscene)
        se.send(params_line(rng, rng.randint(0, 4), rng.randint(0, 8), h, cl))

    new_params()
    for _ in range(rng.randint(10, 60)):
        sup, r = se.sup, rng.random()
        if sup.s["busy"] and r < 0.35:
            se.send(rng.choice(["tick", "tick", "tick", "timeout", "finish"]))
        elif r < 0.45:
            w, prio = pick_request(rng, sup)
            se.send("request " + wtxt(rng, w) + " " + prio)
        elif r < 0.57:
            se.send("admit")
        elif r < 0.64:
            se.send("finish")
        elif r < 0.76:
            se.send("tick")
        elif r < 0.82:
            se.send("timeout")
        elif r < 0.85:
            se.send("state")
        elif r < 0.95:
            se.send(junk(rng))
        elif r < 0.98:
            new_params()
        elif r < 0.99:
            se.send(policy_line)
        else:
            se.send(bad_params(rng))
    if rng.random() < 0.5:
        se.send("quit")
    return se


def sample(rng, sup, near):
    """A boundary's sample: encoder counts near the goal of the active move (within about 3.2
    degrees) or anywhere within 90 degrees, and joint speeds in rad/s, sometimes at the tolerance."""
    g = sup.goal
    if near:
        counts = [round(x * cpr / 360) + rng.randint(-2330, 2330) for x in g]
    else:
        counts = [rng.randint(-65536, 65536) for _ in range(3)]
    vel = [rng.choice([F(33, 10), F(-33, 10)]) if rng.random() < 0.05 else F(rng.randint(-400, 400), 100) for _ in range(3)]
    if not near and rng.random() < 0.5:
        vel = [F(rng.randint(-2000, 2000), 100) for _ in range(3)]
    return counts, vel


def ctxt(rng, n):
    return rng.choice([str(n), str(n), str(n), str(n) + ".0", str(2 * n) + "/2"])


def boundary_sequence(seed):
    rng = random.Random(10**6 + seed)
    se = Sequence()
    bound = 25 if rng.random() < 0.7 else rng.randint(0, 6)
    cap = 8 if rng.random() < 0.7 else rng.randint(0, 7)
    p_near = rng.uniform(0.3, 1.0)

    def start():
        se.send(params_line(rng, bound, cap, home, cells))
        se.send(policy_line)

    if rng.random() < 0.2:
        se.send("boundary 0 0 0 0 0 0 0")
    start()
    for _ in range(rng.randint(200, 400)):
        sup, r = se.sup, rng.random()
        reqs = []
        if rng.random() < 0.15:
            for _ in range(rng.randint(1, 4)):
                reqs.append(pick_request(rng, sup))
        counts, vel = sample(rng, sup, rng.random() < p_near)
        k = sup.next
        tail = " ".join(ctxt(rng, n) for n in counts) + " " + " ".join(txt(rng, v) for v in vel)
        rtxt = "".join(" " + wtxt(rng, w) + " " + prio for w, prio in reqs)
        if r < 0.02:
            se.send("boundary " + str(k + rng.choice([1, 2, -1, 5])) + " " + tail + rtxt)
        elif r < 0.035:
            se.send(rng.choice([
                "boundary " + rng.choice(["x", "1.0", "-1", "1/1"]) + " " + tail + rtxt,
                "boundary " + str(k) + " 1/2 0 0 0 0 0" + rtxt,
                "boundary " + str(k) + " " + tail + rtxt + " 1 2 3",
                "boundary " + str(k) + " " + tail + " 0 -40 30 high",
                "boundary " + str(k) + " " + tail + " 0 " + rng.choice(bad_numbers) + " 30 normal",
            ]))
        elif r < 0.06:
            se.send(rng.choice(["state", "tick", "admit", "request 0 -40 30 normal", junk(rng)]))
        elif r < 0.063:
            se.send(policy_line)
        elif r < 0.065 or (sup.s["faulted"] and r < 0.1):
            start()
        else:
            se.send("boundary " + str(k) + " " + tail + rtxt)
    if rng.random() < 0.5:
        se.send("quit")
    return se


def check(job):
    kind, seed = job
    se = action_sequence(seed) if kind == "action" else boundary_sequence(seed)
    return len(se.transcript), replay(se.transcript), se.count


def report(name, res, keys):
    diffs = [r[1] for r in res if r[1]]
    total = sum((r[2] for r in res), Counter())
    print(name, "sequences", len(res), "lines compared", sum(r[0] for r in res), "sequences with a difference", len(diffs))
    print(name, "first difference", diffs[0] if diffs else None)
    print(name, "refusal reasons", [(k, total[k]) for k in reason_names])
    print(name, "blockers", [(k, total["blocked " + k]) for k in blocker_names])
    print(name, "events", [(k, total[k]) for k in keys])
    print(name, "error answers", sorted((k, v) for k, v in total.items() if k.startswith("error")))


if __name__ == "__main__":
    nact = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    nbnd = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 16
    with Pool(workers) as p:
        ra = p.map(check, [("action", i) for i in range(nact)], chunksize=8)
        rb = p.map(check, [("boundary", i) for i in range(nbnd)], chunksize=1)
    report("per-action", ra, ["queued", "refused", "full queue reached", "timeout", "timeout with a nonempty queue", "blank"])
    report("boundary", rb, ["queued", "refused", "act request", "act admit", "act finish", "act tick", "act timeout", "act -",
                            "admission recorded", "full queue reached", "timeout", "timeout with a nonempty queue", "blank"])
