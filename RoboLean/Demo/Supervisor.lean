/-!
# An executable timeout supervisor for the planar two-link arm

This module is a computable mirror of the timeout supervisor
`RoboLean.Design.PlanarArmTimeoutSupervisor`: the same six actions with the same guards and
effects, over rational targets, with lists in place of sets, a `Bool` flag and a natural-number
age. It imports nothing beyond the Lean core, so that it compiles and runs without Mathlib. The
module `RoboLean.Demo.SupervisorRefines` proves that the guard `reachable` decides the annulus
condition `planarGuard` on the cast target, that every transition of `step` is a step of the
design relation on the abstracted state, and that every state reached by `run` from `State.init`
is a reachable state of the design supervisor.

Frame and units. A target `(x, y) : ℚ × ℚ` is a point of the arm's plane in the frame of the
book's planar two-link arm (MLS Figure 3.7a, printed p. 97, and Figure 4.4, p. 164): the base
joint at the origin, `x` along the arm at the zero configuration. The library's kinematic arm
`Examples.planarTwoLink` points along `+y` at the zero configuration, and the book's point
`(x, y)` is its point `vec (-y) x 0`. Link lengths are `a = l₁` and `b = l₂`, in any unit shared
with the targets.

Guard. For positive link lengths, the reachable workspace of MLS eq. (3.12), printed p. 95, of
the planar two-link arm with unrestricted joints is the annulus `|a - b| ≤ ‖p‖ ≤ a + b`. The
executable guard decides it in squared form over `ℚ`, together with `0 ≤ a + b`, which makes the
squared form equivalent to the norm form for every `a`, `b`.

The supervisor is a design model, not taken from MLS. Lists may be compared only through
membership: the abstraction to the design model reads a list `l` as the set `{t | t ∈ l}`.
-/

namespace RoboLean.Demo

/-- A target `(x, y)` of the arm's plane with rational coordinates, in the frame of the book's
planar two-link arm (MLS Figure 3.7a, p. 97; Figure 4.4, p. 164): `x` along the arm at the zero
configuration. A design convention of the executable, not from MLS. -/
abbrev Target := Rat × Rat

/-- The parameters of the executable supervisor: the link lengths `a = l₁`, `b = l₂` of the
planar two-link arm (MLS Figure 3.7a, p. 97) and the age bound of the timeout supervisor, a
number of `tick` actions. A design model, not from MLS. -/
structure Params where
  /-- The first link length `l₁`. -/
  a : Rat
  /-- The second link length `l₂`. -/
  b : Rat
  /-- The age bound: a command times out after this many ticks. -/
  bound : Nat
  deriving Repr

/-- The state of the executable supervisor: the pending requests, the active command, the
rejected and the timed-out targets as lists (read as the sets of their members), whether a
command is active, and the number of ticks since the active command was admitted. The concrete
counterpart of `RoboLean.Design.PlanarArmTimeoutSupervisor.State`. A design model, not from
MLS. -/
structure State where
  /-- Pending requests from the planner. -/
  requested : List Target
  /-- The active command sent to the arm controller. -/
  commanded : List Target
  /-- Targets the supervisor has rejected. -/
  rejected : List Target
  /-- Targets whose command timed out. -/
  timedOut : List Target
  /-- A command is active. -/
  busy : Bool
  /-- The number of ticks since the active command was admitted. -/
  age : Nat
  deriving Repr

/-- The initial state: no request, no command, no rejection, no timeout, idle, age zero. The
concrete counterpart of `RoboLean.Design.PlanarArmTimeoutSupervisor.init`. -/
def State.init : State where
  requested := []
  commanded := []
  rejected := []
  timedOut := []
  busy := false
  age := 0

/-- The executable workspace guard: the target `(x, y)` satisfies `0 ≤ a + b` and
`(a - b)² ≤ x² + y² ≤ (a + b)²`, decided over `ℚ`. For positive link lengths this is the
annulus `|l₁ - l₂| ≤ r ≤ l₁ + l₂`, `r = √(x² + y²)`, that bounds the reachable workspace of
MLS eq. (3.12), printed p. 95, and in which MLS p. 98, eq. (3.16), has a solution; the
equivalence with `RoboLean.Design.planarGuard` on the cast target is
`RoboLean.Demo.reachable_eq_true_iff`. The conjunct `0 ≤ a + b` makes the squared form exact
for all rational `a`, `b`. -/
def reachable (p : Params) (t : Target) : Bool :=
  let r := t.1 * t.1 + t.2 * t.2
  decide (0 ≤ p.a + p.b) && decide ((p.a - p.b) * (p.a - p.b) ≤ r) &&
    decide (r ≤ (p.a + p.b) * (p.a + p.b))

/-- The actions of the supervisor, one for each constructor of
`RoboLean.Design.PlanarArmTimeoutSupervisor.Step`: a request from the planner, the admission or
rejection of a requested target, the end of the active command, one clock tick, and the timeout
of the active command. A design model, not from MLS. -/
inductive Action where
  /-- The planner requests a target. -/
  | request (t : Target)
  /-- A requested reachable target is commanded while the supervisor is idle. -/
  | admit (t : Target)
  /-- A requested unreachable target is rejected. -/
  | reject (t : Target)
  /-- The arm controller finishes the active command. -/
  | finish
  /-- One clock tick while a command is active and below the age bound. -/
  | tick
  /-- The active command has reached the age bound and times out. -/
  | timeout
  deriving Repr

/-- The first guard of an action that fails in a state, as a short name, or `none` when every
guard holds. The guards are those of `RoboLean.Design.PlanarArmTimeoutSupervisor.Step`:
`admit t` needs `t` requested, `reachable t` and an idle supervisor; `reject t` needs `t`
requested and `reachable t = false`; `finish` needs a busy supervisor; `tick` needs a busy
supervisor and `age < bound`; `timeout` needs a busy supervisor and `age = bound`; `request`
has no guard. -/
def Action.blocker (p : Params) (s : State) : Action → Option String
  | .request _ => none
  | .admit t =>
    if t ∉ s.requested then some "not-requested"
    else if reachable p t = false then some "not-reachable"
    else if s.busy = true then some "not-idle"
    else none
  | .reject t =>
    if t ∉ s.requested then some "not-requested"
    else if reachable p t = true then some "reachable"
    else none
  | .finish => if s.busy = true then none else some "not-busy"
  | .tick =>
    if s.busy = false then some "not-busy"
    else if s.age < p.bound then none
    else some "age-at-bound"
  | .timeout =>
    if s.busy = false then some "not-busy"
    else if s.age = p.bound then none
    else some "age-not-at-bound"

/-- The effect of an action on a state, without its guard, as in the constructors of
`RoboLean.Design.PlanarArmTimeoutSupervisor.Step`: `request t` adds `t` to the requests;
`admit t` removes `t` from the requests, commands it, makes the supervisor busy and resets the
age; `reject t` moves `t` from the requests to the rejected targets; `finish` clears the command,
makes the supervisor idle and resets the age; `tick` adds one to the age; `timeout` moves the
active command to the timed-out targets, makes the supervisor idle and resets the age. -/
def State.apply (s : State) : Action → State
  | .request t => { s with requested := s.requested.insert t }
  | .admit t =>
    { s with requested := s.requested.filter (· != t), commanded := s.commanded.insert t,
             busy := true, age := 0 }
  | .reject t =>
    { s with requested := s.requested.filter (· != t), rejected := s.rejected.insert t }
  | .finish => { s with commanded := [], busy := false, age := 0 }
  | .tick => { s with age := s.age + 1 }
  | .timeout =>
    { s with timedOut := s.commanded.foldr List.insert s.timedOut, commanded := [],
             busy := false, age := 0 }

/-- One step of the executable supervisor: `none` when a guard of the action fails
(`Action.blocker` names it), otherwise the state after the action. Every `some` result is a step
of `RoboLean.Design.PlanarArmTimeoutSupervisor.Step` on the abstracted state
(`RoboLean.Demo.step_sound`). -/
def step (p : Params) (s : State) (act : Action) : Option State :=
  match act.blocker p s with
  | some _ => none
  | none => some (s.apply act)

/-- Run a list of actions from a state: `none` as soon as one action is blocked, otherwise the
final state. Every state reached from `State.init` is a reachable state of the design supervisor
(`RoboLean.Demo.reachableState_of_run`). -/
def run (p : Params) : State → List Action → Option State
  | s, [] => some s
  | s, act :: acts =>
    match step p s act with
    | none => none
    | some s' => run p s' acts

/-! ### Text encoding for the line protocol -/

/-- Parse a natural number written in decimal digits only. -/
def parseNat? (w : String) : Option Nat :=
  if !w.isEmpty && w.all Char.isDigit then w.toNat? else none

/-- Parse a rational number written as an integer `n`, a fraction `n/d` with `d ≠ 0`, or a
decimal `n.f`, each with an optional leading `-`. -/
def parseRat? (w : String) : Option Rat :=
  let neg := w.startsWith "-"
  let body := if neg then (w.drop 1).toString else w
  let mag : Option Rat :=
    match body.splitOn "/" with
    | [n, d] => do
      let n ← parseNat? n
      let d ← parseNat? d
      if d = 0 then none else some ((n : Rat) / (d : Rat))
    | [w'] =>
      match w'.splitOn "." with
      | [i] => (parseNat? i).map fun n => (n : Rat)
      | [i, f] => do
        let i ← parseNat? i
        let f' ← parseNat? f
        some ((i : Rat) + (f' : Rat) / ((10 ^ f.length : Nat) : Rat))
      | _ => none
    | _ => none
  mag.map fun q => if neg then -q else q

/-- Parse the two coordinates of a target. -/
def parseTarget? (x y : String) : Option Target := do
  let x ← parseRat? x
  let y ← parseRat? y
  some (x, y)

/-- Parse an action from the words of one protocol line: `request x y`, `admit x y`,
`reject x y`, `finish`, `tick` or `timeout`, with rational coordinates as accepted by
`parseRat?`. -/
def Action.parse : List String → Except String Action
  | ["request", x, y] =>
    match parseTarget? x y with
    | some t => .ok (.request t)
    | none => .error "bad target"
  | ["admit", x, y] =>
    match parseTarget? x y with
    | some t => .ok (.admit t)
    | none => .error "bad target"
  | ["reject", x, y] =>
    match parseTarget? x y with
    | some t => .ok (.reject t)
    | none => .error "bad target"
  | ["finish"] => .ok .finish
  | ["tick"] => .ok .tick
  | ["timeout"] => .ok .timeout
  | _ => .error "unknown command"

/-- A target as `x,y`, each coordinate an integer `n` or a reduced fraction `n/d`. -/
def renderTarget (t : Target) : String :=
  toString t.1 ++ "," ++ toString t.2

/-- A list of targets separated by `;`, or `-` when empty. -/
def renderTargets (l : List Target) : String :=
  if l.isEmpty then "-" else ";".intercalate (l.map renderTarget)

/-- A state on one line:
`busy=<bool> age=<n> requested=<targets> commanded=<targets> rejected=<targets>
timedOut=<targets>`. -/
def State.render (s : State) : String :=
  "busy=" ++ toString s.busy ++ " age=" ++ toString s.age ++
    " requested=" ++ renderTargets s.requested ++
    " commanded=" ++ renderTargets s.commanded ++
    " rejected=" ++ renderTargets s.rejected ++
    " timedOut=" ++ renderTargets s.timedOut

end RoboLean.Demo
