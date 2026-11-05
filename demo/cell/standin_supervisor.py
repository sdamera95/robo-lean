# REFERENCE ONLY: a Python model of the cell supervisor's line protocol, kept as the reference of
# the differential check against the supervisor executable (check_standin.py). It is not on the
# run path: every run of the evaluation is driven by the executable.
from fractions import Fraction as F


def rat(x):
    return F(x)


def wp(w):
    return ",".join(str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}" for x in w)


def wps(l):
    return ";".join(wp(w) for w in l) if l else "-"


class Supervisor:
    def __init__(self):
        self.p = None

    def render(self):
        s = self.s
        b = lambda x: "true" if x else "false"
        return (f"busy={b(s['busy'])} faulted={b(s['faulted'])} age={s['age']} at={wp(s['at'])} "
                f"requested={wps(s['requested'])} commanded={wps(s['commanded'])} "
                f"rejected={wps(s['rejected'])} timedOut={wps(s['timedOut'])}")

    def linked(self, a, b):
        return any(all(lo[k] <= a[k] <= hi[k] and lo[k] <= b[k] <= hi[k] for k in range(3)) for lo, hi in self.p["cells"])

    def send(self, line):
        w = line.split()
        if w in (["state"], ["quit"]):
            return "ok " + self.render() if self.p else "error no params"
        if w[0] == "params":
            bound, home, rest = int(w[1]), tuple(rat(x) for x in w[2:5]), [rat(x) for x in w[5:]]
            cl = [(tuple(rest[i:i + 3]), tuple(rest[i + 3:i + 6])) for i in range(0, len(rest), 6)]
            if any(lo[k] > hi[k] for lo, hi in cl for k in range(3)):
                return "error empty cell"
            self.p = dict(bound=bound, home=home, cells=cl)
            self.s = dict(requested=[], commanded=[], rejected=[], timedOut=[], busy=False, faulted=False, age=0, at=home)
            return "ok " + self.render()
        if self.p is None:
            return "error no params"
        s, bound = self.s, self.p["bound"]
        x = tuple(rat(v) for v in w[1:4]) if len(w) == 4 else None
        if w[0] == "request":
            if x not in s["requested"]:
                s["requested"].insert(0, x)
        elif w[0] == "admit":
            g = ("not-requested" if x not in s["requested"] else "not-idle" if s["busy"] else
                 "faulted" if s["faulted"] else "not-linked" if not self.linked(s["at"], x) else None)
            if g:
                return "blocked " + g
            s["requested"].remove(x)
            s.update(commanded=[x], busy=True, age=0)
        elif w[0] == "reject":
            g = "not-requested" if x not in s["requested"] else "linked" if self.linked(s["at"], x) else None
            if g:
                return "blocked " + g
            s["requested"].remove(x)
            if x not in s["rejected"]:
                s["rejected"].insert(0, x)
        elif w[0] == "finish":
            if not s["busy"]:
                return "blocked not-busy"
            s.update(at=s["commanded"][0], commanded=[], busy=False, age=0)
        elif w[0] == "tick":
            g = "not-busy" if not s["busy"] else "age-at-bound" if s["age"] >= bound else None
            if g:
                return "blocked " + g
            s["age"] += 1
        elif w[0] == "timeout":
            g = "not-busy" if not s["busy"] else "age-not-at-bound" if s["age"] != bound else None
            if g:
                return "blocked " + g
            s.update(timedOut=s["commanded"] + s["timedOut"], commanded=[], busy=False, age=0, faulted=True)
        else:
            return "error unknown command"
        return "ok " + self.render()
