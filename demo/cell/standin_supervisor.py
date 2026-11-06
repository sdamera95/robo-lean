# REFERENCE ONLY: a Python model of the cell program's line protocol (the supervisor's per-action
# commands, and the policy's boundary protocol), kept as the reference of the differential check
# against the compiled program (check_standin.py). It is not on the run path: every run of the
# evaluation is driven by the program.
from fractions import Fraction as F


def nat(w):
    return int(w) if w and all(c in "0123456789" for c in w) else None


def rat(w):
    """`n`, `n/d` (d > 0) or `n.f`, with an optional leading `-`, as the program parses them."""
    neg = w.startswith("-")
    body = w[1:] if neg else w
    parts, dots = body.split("/"), body.split(".")
    if len(parts) == 2:
        n, d = nat(parts[0]), nat(parts[1])
        q = F(n, d) if n is not None and d else None
    elif len(parts) > 2:
        q = None
    elif len(dots) == 1:
        q = None if nat(body) is None else F(nat(body))
    elif len(dots) == 2:
        i, f = nat(dots[0]), nat(dots[1])
        q = F(i) + F(f, 10 ** len(dots[1])) if i is not None and f is not None else None
    else:
        q = None
    return -q if neg and q is not None else q


def integer(w):
    q = rat(w)
    return q.numerator if q is not None and q.denominator == 1 else None


def waypoints(ws):
    if len(ws) % 3:
        return None
    l = [tuple(rat(x) for x in ws[i:i + 3]) for i in range(0, len(ws), 3)]
    return None if any(None in w for w in l) else l


def num(x):
    return str(x.numerator) if x.denominator == 1 else str(x.numerator) + "/" + str(x.denominator)


def wp(w):
    return ",".join(num(x) for x in w)


def wps(l):
    return ";".join(wp(w) for w in l) if l else "-"


def act(a):
    return a[0] + ":" + wp(a[1]) if a[0] in ("request", "admit", "reject") else a[0]


def render(s):
    b = lambda x: "true" if x else "false"
    return ("busy=" + b(s["busy"]) + " faulted=" + b(s["faulted"]) + " age=" + str(s["age"]) + " at=" + wp(s["at"]) +
            " requested=" + wps(s["requested"]) + " commanded=" + wps(s["commanded"]) +
            " rejected=" + wps(s["rejected"]) + " timedOut=" + wps(s["timedOut"]))


def init(home):
    return dict(requested=[], commanded=[], rejected=[], timedOut=[], busy=False, faulted=False, age=0, at=home)


def insert(x, l):
    return l if x in l else [x] + l


class Supervisor:
    def __init__(self):
        self.p = None
        self.cfg = None
        self.s = init((F(0), F(0), F(0)))

    def linked(self, a, b):
        return any(all(lo[k] <= a[k] <= hi[k] and lo[k] <= b[k] <= hi[k] for k in range(3)) for lo, hi in self.p["cells"])

    def blocker(self, s, a):
        x = a[1] if len(a) > 1 else None
        if a[0] == "admit":
            return ("not-requested" if x not in s["requested"] else "not-idle" if s["busy"] else
                    "faulted" if s["faulted"] else "not-linked" if not self.linked(s["at"], x) else None)
        if a[0] == "reject":
            return "not-requested" if x not in s["requested"] else "linked" if self.linked(s["at"], x) else None
        if a[0] == "finish":
            return "not-busy" if not s["busy"] else "no-command" if not s["commanded"] else None
        if a[0] == "tick":
            return "not-busy" if not s["busy"] else None if s["age"] < self.p["bound"] else "age-at-bound"
        if a[0] == "timeout":
            return "not-busy" if not s["busy"] else None if s["age"] == self.p["bound"] else "age-not-at-bound"
        return None

    def step(self, s, a):
        """The state after the action, or None when a guard fails; `s` is left unchanged."""
        if self.blocker(s, a):
            return None
        s, x = dict(s), a[1] if len(a) > 1 else None
        if a[0] == "request":
            s["requested"] = insert(x, s["requested"])
        if a[0] == "admit":
            s.update(requested=[y for y in s["requested"] if y != x], commanded=[x], busy=True, age=0)
        if a[0] == "reject":
            s.update(requested=[y for y in s["requested"] if y != x], rejected=insert(x, s["rejected"]))
        if a[0] == "finish":
            s.update(at=s["commanded"][0], commanded=[], busy=False, age=0)
        if a[0] == "tick":
            s["age"] += 1
        if a[0] == "timeout":
            to = s["timedOut"]
            for y in reversed(s["commanded"]):
                to = insert(y, to)
            s.update(timedOut=to, commanded=[], busy=False, faulted=True, age=0)
        return s

    # ------------------------------------------------------------------
    # the policy at a period boundary

    def render_policy(self):
        return (render(self.s) + " src=" + wp(self.src) + " goal=" + wp(self.goal) + " start=" + str(self.start) +
                " pending=" + wps(self.pending))

    def arrived(self, g, counts, vel):
        c = self.cfg
        return all(abs(F(n) * 360 / c["cpr"] - g[i]) <= c["posTol"] and abs(vel[i]) <= c["velTol"] for i, n in enumerate(counts))

    def boundary(self, k, reqs, counts, vel):
        """The actions and the new (supervisor state, src, goal, start, pending), or None when
        the supervisor blocks an action."""
        c, s = self.cfg, self.s
        if s["busy"]:
            due = self.start * c["h"] + c["T"] <= k * c["h"]
            a = (("finish",) if due and self.arrived(self.goal, counts, vel) else
                 ("timeout",) if s["age"] == self.p["bound"] else ("tick",))
            s1 = self.step(s, a)
            return None if s1 is None else ([a], (s1, self.src, self.goal, self.start, self.pending + reqs))
        if s["faulted"]:
            return [], (s, self.src, self.goal, self.start, self.pending + reqs)
        acts, q = [], self.pending + reqs
        while q:
            w = q.pop(0)
            s1 = self.step(s, ("request", w))
            if s1 is None:
                return None
            acts.append(("request", w))
            if self.linked(s["at"], w):
                s2 = self.step(s1, ("admit", w))
                return None if s2 is None else (acts + [("admit", w)], (s2, s1["at"], w, k, q))
            s = self.step(s1, ("reject", w))
            if s is None:
                return None
            acts.append(("reject", w))
        return acts, (s, self.src, self.goal, self.start, [])

    # ------------------------------------------------------------------
    # the line protocol

    def send(self, line):
        w = line.split()
        if w in (["state"], ["quit"]):
            return "ok " + render(self.s)
        if w[0] == "params":
            if len(w) < 5:
                return "error usage: params bound h0 h1 h2 [lo0 lo1 lo2 hi0 hi1 hi2]..."
            bound, home = nat(w[1]), waypoints(w[2:5])
            if bound is None or home is None:
                return "error bad params"
            cl = []
            for i in range(5, len(w), 6):
                lo, hi = waypoints(w[i:i + 3]), waypoints(w[i + 3:i + 6])
                if len(w) - i < 6 or lo is None or hi is None:
                    return "error bad params"
                if any(lo[0][j] > hi[0][j] for j in range(3)):
                    return "error empty cell"
                cl.append((lo[0], hi[0]))
            self.p, self.cfg, self.s = dict(bound=bound, home=home[0], cells=cl), None, init(home[0])
            return "ok " + render(self.s)
        if w[0] == "policy":
            if self.p is None:
                return "error no params"
            if len(w) != 6:
                return "error usage: policy h T posTol velTol cpr"
            h, T, pt, vt, cpr = rat(w[1]), rat(w[2]), rat(w[3]), rat(w[4]), nat(w[5])
            if None in (h, T, pt, vt, cpr) or not (h > 0 and T > 0 and pt >= 0 and vt >= 0 and cpr > 0):
                return "error bad policy"
            home = self.p["home"]
            self.cfg = dict(h=h, T=T, posTol=pt, velTol=vt, cpr=cpr)
            self.s, self.src, self.goal, self.start, self.pending, self.next = init(home), home, home, 0, [], 0
            return "ok " + self.render_policy()
        if w[0] == "boundary" and len(w) >= 8:
            if self.cfg is None:
                return "error no policy"
            k, counts, vel, reqs = nat(w[1]), [integer(x) for x in w[2:5]], [rat(x) for x in w[5:8]], waypoints(w[8:])
            if k is None or None in counts or None in vel or reqs is None:
                return "error bad boundary"
            if k != self.next:
                return "error expected boundary " + str(self.next)
            r = self.boundary(k, reqs, counts, vel)
            if r is None:
                return "error blocked"
            acts, (self.s, self.src, self.goal, self.start, self.pending) = r
            self.next += 1
            return "ok acts=" + (";".join(act(a) for a in acts) if acts else "-") + " " + self.render_policy()
        if self.p is None:
            return "error no params"
        if self.cfg is not None:
            return "error policy mode"
        if w[0] in ("request", "admit", "reject") and len(w) == 4:
            x = waypoints(w[1:4])
            if x is None:
                return "error bad waypoint"
            a = (w[0], x[0])
        elif w in (["finish"], ["tick"], ["timeout"]):
            a = (w[0],)
        else:
            return "error unknown command"
        s1 = self.step(self.s, a)
        if s1 is None:
            return "blocked " + self.blocker(self.s, a)
        self.s = s1
        return "ok " + render(self.s)
