# The planner of a run with the queue supervisor (cell-supervisor-queue). It decides only which
# requests to send and when; every decision of the loop (queue, refuse, admit, tick, finish, time
# out) is the program's.
#
# Normal requests: the plan (home first) in order, at every boundary as many next waypoints as keep
# the queue the program last reported at most `capacity` long, never a waypoint already queued (the
# queue holds no duplicates, so the planner waits until that waypoint has been admitted), and
# nothing once the supervisor has faulted. Without urgent requests the moves are those of the
# request-set program on the same plan: the plan's unlinked request is refused when it is sent,
# where the request-set program rejects it when it reaches the head of its own queue.
#
# Urgent requests (the urgent scenario), drawn from the run's own generator at the boundary after
# the admission of a move of the plan (a normal request), once per cycle each:
#   repick, probability 1/2: after the admission of the cycle's pick slot, an urgent request for
#     another pick slot, drawn uniformly; it is linked to the commanded pick slot and to the queue's
#     head (lift_pick), so it is inserted at the head, unless the queue is full, and served first;
#   home_place, probability 1/4: after the admission of the cycle's place slot, an urgent request
#     for home, which is not linked to the place slot: refused;
#   home_cross, probability 1/4: after the admission of lift_place on the way to the place side, an
#     urgent request for home, linked to lift_place, while the queue's head (the cycle's place slot)
#     is not linked to home: refused;
#   flood, probability 1/4: at the same boundary, after `home_cross`, urgent requests for every
#     other place slot in random order, each linked to lift_place and to the head before it:
#     inserted while the queue holds fewer than `capacity` waypoints, refused once it is full.
import numpy as np


class QueuePlanner:
    def __init__(self, items, W, capacity, urgent, seed):
        self.items, self.i, self.cap, self.urgent = list(items), 0, capacity, urgent
        self.rng = np.random.default_rng(seed)
        self.role = {n: W[n]["role"] for n in W}
        self.picks = sorted(n for n in W if W[n]["role"] == "pick")
        self.places = sorted(n for n in W if W[n]["role"] == "place")
        self.home = [n for n in W if W[n]["role"] == "home"][0]

    def left(self):
        return self.i < len(self.items)

    def requests(self, queue, faulted, admitted):
        """The requests (name, priority) to send at this boundary, given the queue (names, head
        first) and the fault flag of the program's last answer, and the move (from, to, priority)
        it admitted at the last boundary, if any."""
        if faulted:
            return []
        out = []
        while self.left() and len(queue) + len(out) < self.cap and self.items[self.i] not in queue + [n for n, _ in out]:
            out.append((self.items[self.i], "normal"))
            self.i += 1
        if self.urgent and admitted is not None and admitted[2] == "normal":
            out += self.urgent_requests(admitted[0], admitted[1], queue)
        return out

    def urgent_requests(self, frm, to, queue):
        u, out = self.urgent, []
        if self.role[to] == "pick" and self.rng.random() < u["repick"]:
            out.append((str(self.rng.choice([n for n in self.picks if n != to])), "urgent"))
        if self.role[to] == "place" and self.rng.random() < u["home_place"]:
            out.append((self.home, "urgent"))
        if to == "lift_place" and self.role[frm] != "place":
            if self.rng.random() < u["home_cross"]:
                out.append((self.home, "urgent"))
            if self.rng.random() < u["flood"]:
                others = [n for n in self.places if not queue or n != queue[0]]
                out += [(str(n), "urgent") for n in self.rng.permutation(others)]
        return out
