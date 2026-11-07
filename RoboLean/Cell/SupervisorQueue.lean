import RoboLean.Cell.Supervisor

/-!
# An executable cell supervisor with a priority request queue

This module is the cell supervisor of `RoboLean.Cell.Supervisor` with the planner's requests held
in a bounded queue with two priorities, and the link test moved from admission to enqueueing. It
reuses the state `RoboLean.Cell.Supervisor.State`, reading its list `requested` as the queue in
the order of service (head first), and its link test `RoboLean.Cell.Supervisor.linked`. It
imports only the core-only module `RoboLean.Cell.Supervisor`, so it compiles and runs without
Mathlib.

* A normal request `w` joins the tail of the queue. It is tested against its predecessor: the last
  queued waypoint when the queue is not empty, otherwise the commanded waypoint when a move is
  active, otherwise the waypoint the arm is at (`pred`). An urgent request is inserted at the head,
  so that among urgent requests the latest is served first; it is tested against the commanded
  waypoint when a move is active, otherwise the waypoint the arm is at (`front`), and, when the
  queue is not empty, the old head must be linked to it. A request is queued when it passes its
  link tests, is not already queued and the queue holds fewer than `capacity` waypoints;
  otherwise it is recorded as rejected. `step` accepts a request in every state except a busy
  one with no commanded waypoint, which the contract's first clause excludes.
* `admit` takes the head of the queue while the supervisor is idle and not faulted, with no link
  test of its own.
* `finish` and `tick` are as before; a timeout also rejects every queued request and empties the
  queue.

The contract `Contract` states the six clauses of `RoboLean.Cell.Supervisor.Contract` for the runs
of this supervisor; its proof needs an invariant over the queue (every queued waypoint linked to
its predecessor, the head linked to the waypoint the arm is at while idle and to the commanded
waypoint while busy), since `admit` no longer tests the link.

Units and frame as in `RoboLean.Cell.Supervisor`: waypoints are joint angles of the three-link arm
of MLS Example 4.3 (printed p. 172) in rational degrees. The supervisor is a design model, not
taken from MLS.
-/

namespace RoboLean.Cell.SupervisorQueue

open RoboLean.Cell.Supervisor (Waypoint State linked)

/-- The parameters of the queue supervisor: those of `RoboLean.Cell.Supervisor.Params` (the cells
that define `linked`, the home waypoint, the age bound) and the number of requests the queue can
hold. A design model, not from MLS. -/
structure Params extends RoboLean.Cell.Supervisor.Params where
  /-- The number of requests the queue can hold. -/
  capacity : Nat
  deriving Repr

/-- The priority of a request: a normal request joins the tail of the queue, an urgent one is
inserted at the head. A design model, not from MLS. -/
inductive Priority where
  /-- Joins the tail of the queue. -/
  | normal
  /-- Is inserted at the head of the queue. -/
  | urgent
  deriving Repr, DecidableEq

/-- The actions of the queue supervisor: a request with its priority, the admission of the head
of the queue, the end of the active move, one clock tick and the timeout of the active move. A
design model, not from MLS. -/
inductive Action where
  /-- The planner requests a waypoint with a priority; it is queued or rejected. -/
  | request (w : Waypoint) (prio : Priority)
  /-- The head of the queue is commanded while the supervisor is idle and not faulted. -/
  | admit
  /-- The controller finishes the move to the commanded waypoint. -/
  | finish
  /-- One clock tick while a move is active and below the age bound. -/
  | tick
  /-- The active move has reached the age bound: it times out, the queue is rejected and the
  supervisor faults. -/
  | timeout
  deriving Repr

/-- The waypoint ahead of the queue: the commanded waypoint (the head of the list) when a move is
active, otherwise the waypoint the arm is at. An urgent request is tested against it. A design
model, not from MLS. -/
def front (s : State) : Waypoint :=
  if s.busy then s.commanded.headD s.current else s.current

/-- The predecessor of a normal request: the last queued waypoint when the queue is not empty,
otherwise `front`. A design model, not from MLS. -/
def pred (s : State) : Waypoint :=
  s.requested.getLast?.getD (front s)

/-- Whether a request `w` with the priority `prio` is queued: it is linked to its predecessor
(`pred` for a normal request; for an urgent one `front`, and the old head of a nonempty queue is
linked to it), it is not already queued, and the queue holds fewer than `capacity` waypoints. A
design model, not from MLS. -/
def queueable (p : Params) (s : State) (w : Waypoint) : Priority → Bool
  | .normal =>
    linked p.cells (pred s) w && decide (w ∉ s.requested) &&
      decide (s.requested.length < p.capacity)
  | .urgent =>
    linked p.cells (front s) w && s.requested.head?.all (linked p.cells w ·) &&
      decide (w ∉ s.requested) && decide (s.requested.length < p.capacity)

/-- The first guard of an action that fails in a state, as a short name, or `none` when every
guard holds: a request needs a commanded waypoint when a move is active (a state no run reaches
fails it); `admit` needs a nonempty queue and an idle supervisor that is not faulted; `finish`,
`tick` and `timeout` as in `RoboLean.Cell.Supervisor.Action.blocker`. A design model, not from
MLS. -/
def Action.blocker (p : Params) (s : State) : Action → Option String
  | .request _ _ => if s.busy && s.commanded.isEmpty then some "no-command" else none
  | .admit =>
    if s.requested.isEmpty then some "empty"
    else if s.busy = true then some "not-idle"
    else if s.faulted = true then some "faulted"
    else none
  | .finish =>
    if s.busy = false then some "not-busy"
    else if s.commanded.isEmpty then some "no-command"
    else none
  | .tick =>
    if s.busy = false then some "not-busy"
    else if s.age < p.bound then none
    else some "age-at-bound"
  | .timeout =>
    if s.busy = false then some "not-busy"
    else if s.age = p.bound then none
    else some "age-not-at-bound"

/-- The effect of an action on a state, without its guard: a request that is `queueable` joins
the tail (normal) or the head (urgent) of the queue, otherwise it is added to the rejected
waypoints; `admit` makes the head of the queue the only commanded waypoint, removes it from the
queue, makes the supervisor busy and resets the age; `finish` puts the arm at the commanded
waypoint, clears the command, makes the supervisor idle and resets the age; `tick` adds one to the
age; `timeout` moves the commanded waypoint to the timed-out waypoints and the queued ones to the
rejected waypoints, empties the queue, makes the supervisor idle, resets the age and sets the fault
flag. A design model, not from MLS. -/
def effect (p : Params) (s : State) : Action → State
  | .request w prio =>
    if queueable p s w prio then
      match prio with
      | .normal => { s with requested := s.requested ++ [w] }
      | .urgent => { s with requested := w :: s.requested }
    else { s with rejected := s.rejected.insert w }
  | .admit =>
    match s.requested with
    | [] => s
    | h :: rest => { s with requested := rest, commanded := [h], busy := true, age := 0 }
  | .finish =>
    { s with current := s.commanded.headD s.current, commanded := [], busy := false, age := 0 }
  | .tick => { s with age := s.age + 1 }
  | .timeout =>
    { s with timedOut := s.commanded.foldr List.insert s.timedOut, commanded := [],
             rejected := s.requested.foldr List.insert s.rejected, requested := [],
             busy := false, faulted := true, age := 0 }

/-- One step of the queue supervisor: `none` when a guard of the action fails (`Action.blocker`
names it), otherwise the state after the action. A design model, not from MLS. -/
def step (p : Params) (s : State) (act : Action) : Option State :=
  match act.blocker p s with
  | some _ => none
  | none => some (effect p s act)

/-- Run a list of actions from a state: `none` as soon as one action is blocked, otherwise the
final state. A design model, not from MLS. -/
def run (p : Params) : State → List Action → Option State
  | s, [] => some s
  | s, act :: acts =>
    match step p s act with
    | none => none
    | some s' => run p s' acts

/-- **The queue supervisor's contract.** For the parameters `p`, every state `s` that the queue
supervisor reaches from its initial state at `p.home` by a list of actions, each accepted,
satisfies the six clauses of `RoboLean.Cell.Supervisor.Contract`: a busy supervisor has exactly
one commanded waypoint, linked by the link test to the waypoint the arm is at; an idle supervisor
has no commanded waypoint; the age is at most the bound; an idle supervisor has age zero; a
faulted supervisor is idle; every commanded waypoint is linked to the waypoint the arm is at. A
design statement, not from MLS; waypoints are rational degrees and the age counts ticks. -/
def Contract (p : Params) : Prop :=
  ∀ (acts : List Action) (s : State),
    run p (RoboLean.Cell.Supervisor.State.init p.home) acts = some s →
    (s.busy = true → ∃ w, linked p.cells s.current w = true ∧ ∀ u, u ∈ s.commanded ↔ u = w) ∧
      (s.busy = false → ∀ u, u ∉ s.commanded) ∧
      s.age ≤ p.bound ∧
      (s.busy = false → s.age = 0) ∧
      (s.faulted = true → s.busy = false) ∧
      (∀ u, u ∈ s.commanded → linked p.cells s.current u = true)

/-! ### Text encoding for the line protocol -/

/-- Parse a priority: `normal` or `urgent`. Not from MLS. -/
def parsePriority? : String → Option Priority
  | "normal" => some .normal
  | "urgent" => some .urgent
  | _ => none

/-- Parse an action from the words of one protocol line: `request a b c normal`,
`request a b c urgent`, `admit`, `finish`, `tick` or `timeout`, with the joint angles in degrees
as accepted by `RoboLean.Cell.Supervisor.parseWaypoint?`. Not from MLS. -/
def Action.parse : List String → Except String Action
  | ["request", a, b, c, prio] =>
    match RoboLean.Cell.Supervisor.parseWaypoint? a b c, parsePriority? prio with
    | some w, some pr => .ok (.request w pr)
    | none, _ => .error "bad waypoint"
    | _, none => .error "bad priority"
  | ["admit"] => .ok .admit
  | ["finish"] => .ok .finish
  | ["tick"] => .ok .tick
  | ["timeout"] => .ok .timeout
  | _ => .error "unknown command"

end RoboLean.Cell.SupervisorQueue
