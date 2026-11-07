import RoboLean.Cell.SupervisorQueue
import RoboLean.Cell.Policy

/-!
# The supervisory policy of the cell as a program, on the queue supervisor

This module is the decision procedure of the sampled loop at a period boundary of
`RoboLean.Cell.Policy`, written for the queue supervisor of `RoboLean.Cell.SupervisorQueue`: the
planner's requests are held in the supervisor's bounded priority queue, not in the policy's state.
Given the boundary index, the requests that arrived since the last boundary (each a waypoint with a
priority), the measured sample and the policy's state, `boundary` returns the actions it sends to
the queue supervisor and the new state, and applies the supervisor's own `step` to every action. It
imports only the core-only modules `RoboLean.Cell.SupervisorQueue` and `RoboLean.Cell.Policy`, so
the executable built from it runs without Mathlib.

The decisions at boundary `k`:

* the requests are forwarded in their order of arrival (`request w prio`), busy or idle; the queue
  supervisor queues each or records it as rejected;
* then, while the supervisor is busy, the policy sends one action: `finish` when the move is due
  (`start · h + T ≤ k · h`) and the sample has arrived at the goal, otherwise `timeout` when the age
  equals the supervisor's bound, otherwise `tick` (the tests of `RoboLean.Cell.Policy`);
* while idle and faulted, or idle with an empty queue, the policy sends nothing;
* while idle, not faulted, with the queue's head `h`, the policy sends `admit`, and the controller's
  record becomes the move from the arm's waypoint to `h`, admitted at this boundary.

The sample, its units and the arrival tolerances are those of `RoboLean.Cell.Policy`: encoder counts
read as degrees, joint speeds in rad/s, waypoints and the position tolerance in degrees, the period
and the duration in seconds. `IsProgramRun` says that a sequence of states and actions is the
program's own output on a stream of requests and samples. Waypoints are joint angles of the
three-link arm of MLS Example 4.3 (printed p. 172) in rational degrees. A design model, not from
MLS.
-/

namespace RoboLean.Cell.PolicyQueue

open RoboLean.Cell.Supervisor (Waypoint renderWaypoint parseWaypoint?)
open RoboLean.Cell.SupervisorQueue (Priority)

/-- The configuration of the policy on the queue supervisor: the configuration of
`RoboLean.Cell.Policy.Config` (the supervisor's cells, home waypoint and age bound, the period and
the move duration in seconds, the arrival tolerances in degrees and rad/s, the encoder resolution)
and the number of requests the supervisor's queue can hold. A design model, not from MLS. -/
structure Config extends Policy.Config where
  /-- The number of requests the queue supervisor can hold. -/
  capacity : Nat
  deriving Repr

/-- The queue supervisor's parameters of a configuration: the supervisor's parameters `cfg.sup` and
the queue's capacity. A design model, not from MLS. -/
def Config.qsup (cfg : Config) : SupervisorQueue.Params where
  toParams := cfg.sup
  capacity := cfg.capacity

/-- The state of the policy on the queue supervisor: the supervisor's state (whose list `requested`
is the queue, head first) and the controller's record of the last admitted move (from `src` to
`goal`, admitted at boundary `start`; waypoints in degrees). The policy keeps no request list of its
own. A design model, not from MLS. -/
structure State where
  /-- The queue supervisor's state. -/
  sup : Supervisor.State
  /-- The start waypoint of the last admitted move. -/
  src : Waypoint
  /-- The goal waypoint of the last admitted move. -/
  goal : Waypoint
  /-- The boundary index at which the last move was admitted. -/
  start : Nat
  deriving Repr, DecidableEq

/-- The initial state: the supervisor's initial state at the home waypoint (empty queue) and the
rest move from home to home admitted at boundary `0`. A design model, not from MLS. -/
def State.init (cfg : Config) : State where
  sup := Supervisor.State.init cfg.sup.home
  src := cfg.sup.home
  goal := cfg.sup.home
  start := 0

/-- The state of `RoboLean.Cell.Policy` with the same supervisor state and record and no pending
request; used to reuse that module's time test `Policy.due`, which reads only the admission
boundary. A design model, not from MLS. -/
def State.toPolicy (st : State) : Policy.State where
  sup := st.sup
  src := st.src
  goal := st.goal
  start := st.start
  pending := []

/-- The action of a busy policy at boundary `k`: `finish` when the move is due
(`RoboLean.Cell.Policy.due`) and the sample has arrived at the goal
(`RoboLean.Cell.Policy.arrived`), otherwise `timeout` when the age equals the bound, otherwise
`tick`; the decisions of `RoboLean.Cell.Policy.busyAction`, as actions of the queue supervisor. A
design model, not from MLS. -/
def busyAction (cfg : Config) (k : Nat) (st : State) (s : Policy.Sample) : SupervisorQueue.Action :=
  if Policy.due cfg.toConfig st.toPolicy k && Policy.arrived cfg.toConfig st.goal s then .finish
  else if st.sup.age = cfg.sup.bound then .timeout
  else .tick

/-- The requests forwarded at a boundary, in their order of arrival: `request w prio` for each
request `(w, prio)`. A design model, not from MLS. -/
def requestActions (reqs : List (Waypoint × Priority)) : List SupervisorQueue.Action :=
  reqs.map fun r => .request r.1 r.2

/-- **The policy at a period boundary, on the queue supervisor.** At boundary `k`, with the
requests `reqs` that arrived since the last boundary and the sample `smp`, from the state `st`: the
requests are forwarded in their order of arrival and run by the queue supervisor to a state `s₁`;
then a busy supervisor is sent `busyAction`; an idle and faulted one, or an idle one with an empty
queue, is sent nothing; an idle one that is not faulted, with the queue's head `h`, is sent `admit`,
and the controller's record becomes the move from the arm's waypoint to `h` admitted at `k`. Every
action is applied with the queue supervisor's `step`; the result is the actions sent (the requests,
then the policy's action) and the new state, or `none` if the supervisor blocks an action. A design
model, not from MLS. -/
def boundary (cfg : Config) (k : Nat) (reqs : List (Waypoint × Priority)) (smp : Policy.Sample)
    (st : State) : Option (List SupervisorQueue.Action × State) :=
  match SupervisorQueue.run cfg.qsup st.sup (requestActions reqs) with
  | none => none
  | some s₁ =>
    if s₁.busy then
      match SupervisorQueue.step cfg.qsup s₁ (busyAction cfg k { st with sup := s₁ } smp) with
      | none => none
      | some s' =>
        some (requestActions reqs ++ [busyAction cfg k { st with sup := s₁ } smp],
          { st with sup := s' })
    else if s₁.faulted then
      some (requestActions reqs, { st with sup := s₁ })
    else
      match s₁.requested with
      | [] => some (requestActions reqs, { st with sup := s₁ })
      | h :: _ =>
        match SupervisorQueue.step cfg.qsup s₁ .admit with
        | none => none
        | some s₂ =>
          some (requestActions reqs ++ [.admit],
            { sup := s₂, src := s₁.current, goal := h, start := k })

/-- **A run of the program on the queue supervisor.** The states `st k` before boundary `k` and the
actions `acts k` sent at boundary `k` are the program's own output on the stream of requests
`reqs k` and samples `smp k`: `st 0` is the initial state and `boundary` at every boundary `k`
returns `acts k` and `st (k + 1)`. A design model, not from MLS. -/
def IsProgramRun (cfg : Config) (reqs : Nat → List (Waypoint × Priority))
    (smp : Nat → Policy.Sample) (st : Nat → State) (acts : Nat → List SupervisorQueue.Action) :
    Prop :=
  st 0 = State.init cfg ∧
    ∀ k : Nat, boundary cfg k (reqs k) (smp k) (st k) = some (acts k, st (k + 1))

/-! ### Text encoding for the boundary protocol -/

/-- Parse a list of requests, four words each: the three joint angles in degrees, as accepted by
`RoboLean.Cell.Supervisor.parseWaypoint?`, and the priority `normal` or `urgent`. A design
convention, not from MLS. -/
def parseRequests : List String → Option (List (Waypoint × Priority))
  | [] => some []
  | a :: b :: c :: prio :: rest => do
    let w ← parseWaypoint? a b c
    let pr ← SupervisorQueue.parsePriority? prio
    let ws ← parseRequests rest
    some ((w, pr) :: ws)
  | _ => none

/-- A priority as one word: `normal` or `urgent`. A design convention, not from MLS. -/
def renderPriority : Priority → String
  | .normal => "normal"
  | .urgent => "urgent"

/-- An action of the queue supervisor as one word: `request:a,b,c:normal`, `request:a,b,c:urgent`,
`admit`, `finish`, `tick` or `timeout`, angles in degrees as `renderWaypoint` writes them. A design
convention, not from MLS. -/
def renderAction : SupervisorQueue.Action → String
  | .request w prio => "request:" ++ renderWaypoint w ++ ":" ++ renderPriority prio
  | .admit => "admit"
  | .finish => "finish"
  | .tick => "tick"
  | .timeout => "timeout"

/-- A list of actions separated by `;`, or `-` when empty. A design convention, not from MLS. -/
def renderActions (l : List SupervisorQueue.Action) : String :=
  if l.isEmpty then "-" else ";".intercalate (l.map renderAction)

/-- A policy state on one line: the supervisor's state as `Supervisor.State.render` writes it (its
`requested` field is the queue, head first), then `src=<waypoint> goal=<waypoint> start=<n>`. A
design convention, not from MLS. -/
def State.render (st : State) : String :=
  st.sup.render ++ " src=" ++ renderWaypoint st.src ++ " goal=" ++ renderWaypoint st.goal ++
    " start=" ++ toString st.start

end RoboLean.Cell.PolicyQueue
