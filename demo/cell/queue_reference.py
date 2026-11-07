# REFERENCE ONLY: a Python model of the line protocol of the queue supervisor and its policy
# (RoboLean/Cell/MainQueue.lean, on SupervisorQueue.lean and PolicyQueue.lean), written from the
# Lean definitions and kept as the reference of the differential check against the compiled program
# (check_queue.py). Beside each answer it records, for every request a command processed, whether
# it was queued and which conditions of `queueable` failed, and the queue just before an admission.
# A line after `quit` is out of its scope (the program has stopped).
from fractions import Fraction as F

from standin_supervisor import init, insert, integer, nat, rat, render, waypoints, wp, wps

reason_names = ["unlinked-pred", "unlinked-front", "unlinked-head", "duplicate", "full"]
blocker_names = ["no-command", "empty", "not-idle", "faulted", "not-busy", "age-at-bound", "age-not-at-bound"]


def words(line):
    """The words of a line as the program splits it: ASCII space, tab, CR and LF trimmed at both
    ends, then split on single spaces with the empty words dropped."""
    return [x for x in line.strip(" \t\r\n").split(" ") if x]


def act(a):
    return "request:" + wp(a[1]) + ":" + a[2] if a[0] == "request" else a[0]


def outcome_words(o):
    if o["queued"]:
        return "queued-tail" if o["prio"] == "normal" else "queued-head"
    return "refused:" + "+".join(o["reasons"])


class QueueSupervisor:
    kind = "queue-reference"

    def __init__(self):
        self.p = None
        self.cfg = None
        self.s = init((F(0), F(0), F(0)))
        self.src, self.goal, self.start, self.next = self.s["at"], self.s["at"], 0, 0
        self.outcomes = []
        self.admitted = None

    def close(self):
        pass

    # ------------------------------------------------------------------
    # the queue supervisor

    def linked(self, a, b):
        return any(all(lo[k] <= a[k] <= hi[k] and lo[k] <= b[k] <= hi[k] for k in range(3)) for lo, hi in self.p["cells"])

    def front(self, s):
        return (s["commanded"][0] if s["commanded"] else s["at"]) if s["busy"] else s["at"]

    def pred(self, s):
        return s["requested"][-1] if s["requested"] else self.front(s)

    def reasons(self, s, w, prio):
        """The conditions of `queueable` that fail for the request; empty when it is queued."""
        q = s["requested"]
        r = []
        if prio == "normal" and not self.linked(self.pred(s), w):
            r.append("unlinked-pred")
        if prio == "urgent" and not self.linked(self.front(s), w):
            r.append("unlinked-front")
        if prio == "urgent" and q and not self.linked(w, q[0]):
            r.append("unlinked-head")
        if w in q:
            r.append("duplicate")
        if len(q) >= self.p["capacity"]:
            r.append("full")
        return r

    def blocker(self, s, a):
        if a[0] == "request":
            return "no-command" if s["busy"] and not s["commanded"] else None
        if a[0] == "admit":
            return ("empty" if not s["requested"] else "not-idle" if s["busy"] else
                    "faulted" if s["faulted"] else None)
        if a[0] == "finish":
            return "not-busy" if not s["busy"] else "no-command" if not s["commanded"] else None
        if a[0] == "tick":
            return "not-busy" if not s["busy"] else None if s["age"] < self.p["bound"] else "age-at-bound"
        if a[0] == "timeout":
            return "not-busy" if not s["busy"] else None if s["age"] == self.p["bound"] else "age-not-at-bound"

    def step(self, s, a):
        """The state after the action, or None when a guard fails; `s` is left unchanged."""
        if self.blocker(s, a):
            return None
        s = dict(s)
        if a[0] == "request":
            w, prio = a[1], a[2]
            if not self.reasons(s, w, prio):
                s["requested"] = s["requested"] + [w] if prio == "normal" else [w] + s["requested"]
            else:
                s["rejected"] = insert(w, s["rejected"])
        if a[0] == "admit":
            s.update(requested=s["requested"][1:], commanded=[s["requested"][0]], busy=True, age=0)
        if a[0] == "finish":
            s.update(at=s["commanded"][0] if s["commanded"] else s["at"], commanded=[], busy=False, age=0)
        if a[0] == "tick":
            s["age"] += 1
        if a[0] == "timeout":
            to, rej = s["timedOut"], s["rejected"]
            for y in reversed(s["commanded"]):
                to = insert(y, to)
            for y in reversed(s["requested"]):
                rej = insert(y, rej)
            s.update(timedOut=to, commanded=[], rejected=rej, requested=[], busy=False, faulted=True, age=0)
        return s

    def request(self, s, w, prio):
        """The state after `request w prio` and its outcome, or None when blocked."""
        r = self.reasons(s, w, prio)
        s1 = self.step(s, ("request", w, prio))
        return None if s1 is None else (s1, dict(w=w, prio=prio, queued=not r, reasons=r))

    # ------------------------------------------------------------------
    # the policy at a period boundary

    def render_policy(self):
        return render(self.s) + " src=" + wp(self.src) + " goal=" + wp(self.goal) + " start=" + str(self.start)

    def arrived(self, g, counts, vel):
        c = self.cfg
        return all(abs(F(n) * 360 / c["cpr"] - g[i]) <= c["posTol"] and abs(vel[i]) <= c["velTol"] for i, n in enumerate(counts))

    def boundary(self, k, reqs, counts, vel):
        """The actions, the new (supervisor state, src, goal, start), the outcomes and the
        admission, or None when the supervisor blocks an action."""
        c, s, outs = self.cfg, self.s, []
        for w, prio in reqs:
            r = self.request(s, w, prio)
            if r is None:
                return None
            s, o = r
            outs.append(o)
        acts = [("request", w, prio) for w, prio in reqs]
        if s["busy"]:
            due = self.start * c["h"] + c["T"] <= k * c["h"]
            a = (("finish",) if due and self.arrived(self.goal, counts, vel) else
                 ("timeout",) if s["age"] == self.p["bound"] else ("tick",))
            s1 = self.step(s, a)
            return None if s1 is None else (acts + [a], (s1, self.src, self.goal, self.start), outs, None)
        if s["faulted"] or not s["requested"]:
            return acts, (s, self.src, self.goal, self.start), outs, None
        s1 = self.step(s, ("admit",))
        h = s["requested"][0]
        return None if s1 is None else (acts + [("admit",)], (s1, s["at"], h, k), outs, dict(w=h, queue=list(s["requested"])))

    # ------------------------------------------------------------------
    # the line protocol

    def params(self, a):
        if len(a) < 5:
            return "error usage: params bound capacity h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]..."
        bound, cap, home = nat(a[0]), nat(a[1]), waypoints(a[2:5])
        if bound is None or cap is None or home is None:
            return "error bad params"
        cl = []
        for i in range(5, len(a), 6):
            lo, hi = waypoints(a[i:i + 3]), waypoints(a[i + 3:i + 6])
            if len(a) - i < 6 or lo is None or hi is None:
                return "error bad params"
            if any(lo[0][j] > hi[0][j] for j in range(3)):
                return "error empty cell"
            cl.append((lo[0], hi[0]))
        home = home[0]
        self.p, self.cfg = dict(bound=bound, capacity=cap, home=home, cells=cl), None
        self.s, self.src, self.goal, self.start, self.next = init(home), home, home, 0, 0
        return "ok " + render(self.s)

    def policy(self, a):
        if self.p is None:
            return "error no params"
        if len(a) != 5:
            return "error usage: policy h T posTol velTol cpr"
        h, T, pt, vt, cpr = rat(a[0]), rat(a[1]), rat(a[2]), rat(a[3]), nat(a[4])
        if None in (h, T, pt, vt, cpr) or not (h > 0 and T > 0 and pt >= 0 and vt >= 0 and cpr > 0):
            return "error bad policy"
        home = self.p["home"]
        self.cfg = dict(h=h, T=T, posTol=pt, velTol=vt, cpr=cpr)
        self.s, self.src, self.goal, self.start, self.next = init(home), home, home, 0, 0
        return "ok " + self.render_policy()

    def boundary_line(self, w):
        if self.cfg is None:
            return "error no policy"
        k, counts, vel = nat(w[1]), [integer(x) for x in w[2:5]], [rat(x) for x in w[5:8]]
        rs = w[8:]
        groups = [rs[i:i + 4] for i in range(0, len(rs), 4)]
        reqs = [(waypoints(g[:3]), g[3]) for g in groups] if len(rs) % 4 == 0 else None
        if reqs is not None and any(x is None or p not in ("normal", "urgent") for x, p in reqs):
            reqs = None
        if k is None or None in counts or None in vel or reqs is None:
            return "error bad boundary"
        if k != self.next:
            return "error expected boundary " + str(self.next)
        r = self.boundary(k, [(x[0], p) for x, p in reqs], counts, vel)
        if r is None:
            return "error blocked"
        acts, (self.s, self.src, self.goal, self.start), self.outcomes, self.admitted = r
        self.next += 1
        return "ok acts=" + (";".join(act(a) for a in acts) if acts else "-") + " " + self.render_policy()

    def send(self, line):
        """The program's answer to one line, or None for a blank line (the program answers
        nothing)."""
        self.outcomes, self.admitted = [], None
        w = words(line)
        if not w:
            return None
        if w in (["state"], ["quit"]):
            return "ok " + render(self.s)
        if w[0] == "params":
            return self.params(w[1:])
        if w[0] == "policy":
            return self.policy(w[1:])
        if w[0] == "boundary" and len(w) >= 8:
            return self.boundary_line(w)
        if self.p is None:
            return "error no params"
        if self.cfg is not None:
            return "error policy mode"
        if w[0] == "request" and len(w) == 5:
            x = waypoints(w[1:4])
            if x is None:
                return "error bad waypoint"
            if w[4] not in ("normal", "urgent"):
                return "error bad priority"
            r = self.request(self.s, x[0], w[4])
            if r is None:
                return "blocked " + self.blocker(self.s, ("request", x[0], w[4]))
            self.s, o = r
            self.outcomes = [o]
            return "ok " + render(self.s)
        if w not in (["admit"], ["finish"], ["tick"], ["timeout"]):
            return "error unknown command"
        a = (w[0],)
        s1 = self.step(self.s, a)
        if s1 is None:
            return "blocked " + self.blocker(self.s, a)
        self.s = s1
        return "ok " + render(self.s)
