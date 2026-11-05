import RoboLean.Demo.Supervisor

/-!
# An executable cell supervisor over rational degree waypoints

This module is a computable mirror of the cell supervisor `RoboLean.Design.CellSupervisor`: the
same six actions with the same guards and effects, over waypoints of three rational joint angles
in degrees, with lists in place of sets, `Bool` flags and a natural-number age. Two waypoints are
linked when some cell of a given list of rational boxes contains both, decided by searching the
list. It imports only the core-only module `RoboLean.Demo.Supervisor`, for its number parsers, so
that it compiles and runs without Mathlib. The module `RoboLean.Cell.SupervisorRefines` proves
that the list search decides "some cell of the list contains both", that every transition of
`step` is a step of the design relation on the abstracted state, that `step` blocks an action
exactly when a design guard fails, and that every state reached by `run` from `State.init` is a
reachable state of the design supervisor.

Units and frame. A waypoint `(θ₀, θ₁, θ₂)` lists the joint angles of the three-link elbow arm of
MLS Example 4.3 (printed p. 172) in the library's convention: base yaw, shoulder, elbow, all in
degrees, the arm along `+y` at the zero configuration and a negative shoulder angle raising the
arm. A cell is a closed box of such joint vectors, given by its lower and upper corners.

The supervisor is a design model, not taken from MLS. Lists are compared only through
membership: the abstraction to the design model reads a list `l` as the set `{w | w ∈ l}`.
-/

namespace RoboLean.Cell.Supervisor

/-- A waypoint of the cell: the joint angles `(θ₀, θ₁, θ₂)` (base yaw, shoulder, elbow) of the
three-link arm of MLS Example 4.3, printed p. 172, in rational degrees, with the library's
convention (arm along `+y` at zero, negative shoulder angle raising the arm). A design convention
of the executable, not from MLS. -/
abbrev Waypoint := Rat × Rat × Rat

/-- A cell: the closed box of waypoints between the lower corner `lo` and the upper corner `hi`,
coordinate by coordinate, in degrees. A design model, not from MLS. -/
structure Box where
  /-- The lower corner. -/
  lo : Waypoint
  /-- The upper corner. -/
  hi : Waypoint
  deriving Repr, DecidableEq

/-- The cell contains the waypoint: `lo.k ≤ w.k ≤ hi.k` for each of the three joint angles,
decided over `ℚ`. A design model, not from MLS. -/
def Box.contains (c : Box) (w : Waypoint) : Bool :=
  decide (c.lo.1 ≤ w.1) && decide (w.1 ≤ c.hi.1) &&
    decide (c.lo.2.1 ≤ w.2.1) && decide (w.2.1 ≤ c.hi.2.1) &&
    decide (c.lo.2.2 ≤ w.2.2) && decide (w.2.2 ≤ c.hi.2.2)

/-- Two waypoints are linked when some cell of the list contains both, decided by searching the
list; `RoboLean.Cell.Supervisor.linked_eq_true_iff` states the equivalence. A design model, not
from MLS. -/
def linked (cells : List Box) (a b : Waypoint) : Bool :=
  cells.any fun c => c.contains a && c.contains b

/-- The parameters of the executable supervisor: the cells that define `linked`, the home
waypoint the arm starts at, and the age bound, a number of `tick` actions. A design model, not
from MLS. -/
structure Params where
  /-- The cells; two waypoints are linked when one cell contains both. -/
  cells : List Box
  /-- The waypoint the arm is at initially. -/
  home : Waypoint
  /-- The age bound: a move times out after this many ticks. -/
  bound : Nat
  deriving Repr

/-- The state of the executable supervisor: the pending requests, the commanded waypoint, the
rejected and the timed-out waypoints as lists (read as the sets of their members), whether a move
is active, whether the supervisor has faulted, the number of ticks since the active move was
admitted, and the waypoint the arm is at. The concrete counterpart of
`RoboLean.Design.CellSupervisor.State`. A design model, not from MLS. -/
structure State where
  /-- Pending requests from the planner. -/
  requested : List Waypoint
  /-- The waypoint of the active move. -/
  commanded : List Waypoint
  /-- Waypoints the supervisor has rejected. -/
  rejected : List Waypoint
  /-- Waypoints whose move timed out. -/
  timedOut : List Waypoint
  /-- A move is active. -/
  busy : Bool
  /-- The supervisor has timed out a move; it admits nothing from then on. -/
  faulted : Bool
  /-- The number of ticks since the active move was admitted. -/
  age : Nat
  /-- The waypoint the arm is at. -/
  current : Waypoint
  deriving Repr, DecidableEq

/-- The initial state at the home waypoint: no request, no command, no rejection, no timeout,
idle, not faulted, age zero, the arm at `home`. The concrete counterpart of
`RoboLean.Design.CellSupervisor.init`. A design model, not from MLS. -/
def State.init (home : Waypoint) : State where
  requested := []
  commanded := []
  rejected := []
  timedOut := []
  busy := false
  faulted := false
  age := 0
  current := home

/-- The actions of the supervisor, one for each constructor of
`RoboLean.Design.CellSupervisor.Step`: a request from the planner, the admission or rejection of
a requested waypoint, the end of the active move, one clock tick, and the timeout of the active
move. `finish` takes no argument: it finishes the move to the commanded waypoint. A design model,
not from MLS. -/
inductive Action where
  /-- The planner requests a waypoint. Not from MLS. -/
  | request (w : Waypoint)
  /-- A requested waypoint linked to the current one is commanded while the supervisor is idle
  and not faulted. Not from MLS. -/
  | admit (w : Waypoint)
  /-- A requested waypoint not linked to the current one is rejected. Not from MLS. -/
  | reject (w : Waypoint)
  /-- The controller finishes the move to the commanded waypoint. Not from MLS. -/
  | finish
  /-- One clock tick while a move is active and below the age bound. Not from MLS. -/
  | tick
  /-- The active move has reached the age bound: it times out and the supervisor faults.
  Not from MLS. -/
  | timeout
  deriving Repr

/-- The first guard of an action that fails in a state, as a short name, or `none` when every
guard holds. The guards are those of `RoboLean.Design.CellSupervisor.Step`, in its order:
`admit w` needs `w` requested, an idle and not faulted supervisor and `linked current w`;
`reject w` needs `w` requested and `linked current w = false`; `finish` needs a busy supervisor
and a commanded waypoint; `tick` needs a busy supervisor and `age < bound`; `timeout` needs a busy
supervisor and `age = bound`; `request` has no guard. A design model, not from MLS. -/
def Action.blocker (p : Params) (s : State) : Action → Option String
  | .request _ => none
  | .admit w =>
    if w ∉ s.requested then some "not-requested"
    else if s.busy = true then some "not-idle"
    else if s.faulted = true then some "faulted"
    else if linked p.cells s.current w = false then some "not-linked"
    else none
  | .reject w =>
    if w ∉ s.requested then some "not-requested"
    else if linked p.cells s.current w = true then some "linked"
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

/-- The effect of an action on a state, without its guard, as in the constructors of
`RoboLean.Design.CellSupervisor.Step`: `request w` adds `w` to the requests; `admit w` removes
`w` from the requests, makes it the only commanded waypoint, makes the supervisor busy and resets
the age; `reject w` moves `w` from the requests to the rejected waypoints; `finish` puts the arm
at the commanded waypoint (the head of the list), clears the command, makes the supervisor idle
and resets the age; `tick` adds one to the age; `timeout` moves the commanded waypoint to the
timed-out waypoints, makes the supervisor idle, resets the age and sets the fault flag. A design
model, not from MLS. -/
def State.apply (s : State) : Action → State
  | .request w => { s with requested := s.requested.insert w }
  | .admit w =>
    { s with requested := s.requested.filter (· != w), commanded := [w], busy := true, age := 0 }
  | .reject w =>
    { s with requested := s.requested.filter (· != w), rejected := s.rejected.insert w }
  | .finish =>
    { s with current := s.commanded.headD s.current, commanded := [], busy := false, age := 0 }
  | .tick => { s with age := s.age + 1 }
  | .timeout =>
    { s with timedOut := s.commanded.foldr List.insert s.timedOut, commanded := [],
             busy := false, faulted := true, age := 0 }

/-- One step of the executable supervisor: `none` when a guard of the action fails
(`Action.blocker` names it), otherwise the state after the action. Every `some` result is a step
of `RoboLean.Design.CellSupervisor.Step` on the abstracted state
(`RoboLean.Cell.Supervisor.step_sound`). A design model, not from MLS. -/
def step (p : Params) (s : State) (act : Action) : Option State :=
  match act.blocker p s with
  | some _ => none
  | none => some (s.apply act)

/-- Run a list of actions from a state: `none` as soon as one action is blocked, otherwise the
final state. Every state reached from `State.init p.home` is a reachable state of the design
supervisor (`RoboLean.Cell.Supervisor.reachableState_of_run`). A design model, not from MLS. -/
def run (p : Params) : State → List Action → Option State
  | s, [] => some s
  | s, act :: acts =>
    match step p s act with
    | none => none
    | some s' => run p s' acts

/-! ### Text encoding for the line protocol -/

/-- Parse the three joint angles of a waypoint, in degrees, each a rational as accepted by
`RoboLean.Demo.parseRat?` (`n`, `n/d` or `n.f`, with an optional leading `-`). Not from MLS. -/
def parseWaypoint? (a b c : String) : Option Waypoint := do
  let a ← RoboLean.Demo.parseRat? a
  let b ← RoboLean.Demo.parseRat? b
  let c ← RoboLean.Demo.parseRat? c
  some (a, b, c)

/-- Parse an action from the words of one protocol line: `request a b c`, `admit a b c`,
`reject a b c`, `finish`, `tick` or `timeout`, with the joint angles in degrees as accepted by
`parseWaypoint?`. Not from MLS. -/
def Action.parse : List String → Except String Action
  | ["request", a, b, c] =>
    match parseWaypoint? a b c with
    | some w => .ok (.request w)
    | none => .error "bad waypoint"
  | ["admit", a, b, c] =>
    match parseWaypoint? a b c with
    | some w => .ok (.admit w)
    | none => .error "bad waypoint"
  | ["reject", a, b, c] =>
    match parseWaypoint? a b c with
    | some w => .ok (.reject w)
    | none => .error "bad waypoint"
  | ["finish"] => .ok .finish
  | ["tick"] => .ok .tick
  | ["timeout"] => .ok .timeout
  | _ => .error "unknown command"

/-- A waypoint as `a,b,c`, each angle in degrees as an integer `n` or a reduced fraction
`n/d`. Not from MLS. -/
def renderWaypoint (w : Waypoint) : String :=
  toString w.1 ++ "," ++ toString w.2.1 ++ "," ++ toString w.2.2

/-- A list of waypoints separated by `;`, or `-` when empty. Not from MLS. -/
def renderWaypoints (l : List Waypoint) : String :=
  if l.isEmpty then "-" else ";".intercalate (l.map renderWaypoint)

/-- A state on one line: `busy=<bool> faulted=<bool> age=<n> at=<waypoint>
requested=<waypoints> commanded=<waypoints> rejected=<waypoints> timedOut=<waypoints>`.
Not from MLS. -/
def State.render (s : State) : String :=
  "busy=" ++ toString s.busy ++ " faulted=" ++ toString s.faulted ++
    " age=" ++ toString s.age ++ " at=" ++ renderWaypoint s.current ++
    " requested=" ++ renderWaypoints s.requested ++
    " commanded=" ++ renderWaypoints s.commanded ++
    " rejected=" ++ renderWaypoints s.rejected ++
    " timedOut=" ++ renderWaypoints s.timedOut

end RoboLean.Cell.Supervisor
