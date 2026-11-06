import RoboLean.Cell.Supervisor

/-!
# The supervisory policy of the cell as a program

This module is the decision procedure of the sampled loop at a period boundary, written as an
executable function over exact rationals: given the boundary index, the requests that arrived
since the last boundary, the measured sample and the policy's state, `boundary` returns the
actions it sends to the cell supervisor and the new state, and applies the supervisor's own `step`
to every action. It imports only the core-only module `RoboLean.Cell.Supervisor`, so the
executable built from it runs without Mathlib.

The decisions are those of the loop model (`RoboLean.Cell.Loop.PolicyStep` and `Boundary`):

* while the supervisor is busy, the requests are queued and the policy sends one action: `finish`
  when the move is due (`start · h + T ≤ k · h`) and the sample has arrived at the goal (every
  joint within `posTol` degrees of the goal and every joint speed at most `velTol` rad/s),
  otherwise `timeout` when the age equals the supervisor's bound, otherwise `tick`;
* while idle and faulted, the policy sends nothing (a faulted supervisor admits nothing);
* while idle and not faulted, the policy takes the queued requests in their order of arrival: each
  request not linked to the waypoint the arm is at is forwarded (`request`) and rejected
  (`reject`); the first linked one is forwarded and admitted (`admit`), and the controller's
  record becomes the move from the arm's waypoint to it, admitted at this boundary.

The sample is the one the controller reads: three encoder counts, at `countsPerRev` counts per
revolution, giving the joint angles `n · 360 / countsPerRev` in degrees, and three joint speeds in
rad/s, each the exact rational value of a floating-point estimate. Waypoints and the position
tolerance are in degrees, the period and the duration in seconds. `IsProgramRun` says that a
sequence of states and actions is the program's own output on a stream of requests and samples.

The module `RoboLean.Cell.PolicyRun` proves that every output of `boundary` is a boundary step of
the loop model on the sample read in radians, so that the program's runs are timed runs of the
cell loop by construction. A design model, not from MLS.
-/

namespace RoboLean.Cell.Policy

open RoboLean.Cell.Supervisor

/-- The configuration of the policy: the supervisor's parameters (cells, home waypoint, age
bound), the period `h` and the move duration `T` in seconds, the arrival tolerances `posTol` in
degrees and `velTol` in radians per second, and the encoder resolution in counts per revolution.
A design model, not from MLS. -/
structure Config where
  /-- The supervisor's parameters. -/
  sup : Params
  /-- The period `h` of the loop, in seconds. -/
  period : Rat
  /-- The duration `T` of a move, in seconds. -/
  duration : Rat
  /-- The joint position tolerance of the arrival test, in degrees. -/
  posTol : Rat
  /-- The joint speed tolerance of the arrival test, in radians per second. -/
  velTol : Rat
  /-- The encoder resolution, in counts per revolution. -/
  countsPerRev : Nat
  deriving Repr

/-- A sample at a period boundary: the encoder counts of the three joints (base yaw, shoulder,
elbow) and the three joint speed estimates in radians per second, each an exact rational. A
design model, not from MLS. -/
structure Sample where
  /-- The encoder counts of the three joints. -/
  counts : Int × Int × Int
  /-- The joint speed estimates, in radians per second. -/
  vel : Rat × Rat × Rat
  deriving Repr, DecidableEq

/-- An encoder count as an angle in degrees: `n · 360 / cpr` for `cpr` counts per revolution. A
design convention, not from MLS. -/
def countsToDeg (cpr : Nat) (n : Int) : Rat :=
  (n : Rat) * 360 / (cpr : Rat)

/-- The joint angles of a sample, in degrees, at the configuration's encoder resolution. A design
convention, not from MLS. -/
def Sample.angle (cfg : Config) (s : Sample) : Waypoint :=
  (countsToDeg cfg.countsPerRev s.counts.1, countsToDeg cfg.countsPerRev s.counts.2.1,
    countsToDeg cfg.countsPerRev s.counts.2.2)

/-- The state of the policy: the supervisor's state, the controller's record of the last
admitted move (from `src` to `goal`, admitted at boundary `start`; waypoints in degrees) and the
queue of requests not yet taken, in their order of arrival. A design model, not from MLS. -/
structure State where
  /-- The supervisor's state. -/
  sup : Supervisor.State
  /-- The start waypoint of the last admitted move. -/
  src : Waypoint
  /-- The goal waypoint of the last admitted move. -/
  goal : Waypoint
  /-- The boundary index at which the last move was admitted. -/
  start : Nat
  /-- The requests not yet taken, oldest first. -/
  pending : List Waypoint
  deriving Repr, DecidableEq

/-- The initial state: the supervisor's initial state at the home waypoint, the rest move from
home to home admitted at boundary `0`, and no queued request. A design model, not from MLS. -/
def State.init (cfg : Config) : State where
  sup := Supervisor.State.init cfg.sup.home
  src := cfg.sup.home
  goal := cfg.sup.home
  start := 0
  pending := []

/-- The time test at boundary `k`: the last admitted move has had its full duration,
`start · h + T ≤ k · h`, decided over `ℚ` (seconds). A design model, not from MLS. -/
def due (cfg : Config) (st : State) (k : Nat) : Bool :=
  decide ((st.start : Rat) * cfg.period + cfg.duration ≤ (k : Rat) * cfg.period)

/-- `|a| ≤ tol`, decided over `ℚ` as `a ≤ tol` and `-a ≤ tol`. A design convention, not from
MLS. -/
def absLe (a tol : Rat) : Bool :=
  decide (a ≤ tol) && decide (-a ≤ tol)

/-- The arrival test for the goal `g` on a sample: for each joint in turn, the angle is within
`posTol` degrees of the goal's and the speed is at most `velTol` rad/s in absolute value. A design
model, not from MLS. -/
def arrived (cfg : Config) (g : Waypoint) (s : Sample) : Bool :=
  absLe ((s.angle cfg).1 - g.1) cfg.posTol && absLe s.vel.1 cfg.velTol &&
    absLe ((s.angle cfg).2.1 - g.2.1) cfg.posTol && absLe s.vel.2.1 cfg.velTol &&
    absLe ((s.angle cfg).2.2 - g.2.2) cfg.posTol && absLe s.vel.2.2 cfg.velTol

/-- The action of a busy policy at boundary `k`: `finish` when the move is due and the sample has
arrived at the goal, otherwise `timeout` when the age equals the bound, otherwise `tick`. A design
model, not from MLS. -/
def busyAction (cfg : Config) (k : Nat) (st : State) (s : Sample) : Action :=
  if due cfg st k && arrived cfg st.goal s then .finish
  else if st.sup.age = cfg.sup.bound then .timeout
  else .tick

/-- The idle policy on a queue of requests: each request not linked to the waypoint the arm is at
is forwarded and rejected, and the first linked one is forwarded. The result is the forwarding
and rejecting actions, the supervisor's state after them, the waypoint to admit (if any) and the
rest of the queue; `none` if the supervisor blocks one of the actions. A design model, not from
MLS. -/
def admitNext (p : Params) : Supervisor.State → List Waypoint →
    Option (List Action × Supervisor.State × Option Waypoint × List Waypoint)
  | s, [] => some ([], s, none, [])
  | s, w :: rest =>
    if linked p.cells s.current w then
      match step p s (.request w) with
      | none => none
      | some s₁ => some ([.request w], s₁, some w, rest)
    else
      match step p s (.request w) with
      | none => none
      | some s₁ =>
        match step p s₁ (.reject w) with
        | none => none
        | some s₂ =>
          match admitNext p s₂ rest with
          | none => none
          | some (pre, s₃, adm, rest') => some (.request w :: .reject w :: pre, s₃, adm, rest')

/-- **The policy at a period boundary.** At boundary `k`, with the requests `reqs` that arrived
since the last boundary and the sample `smp`, from the state `st`: the requests are appended to the
queue; a busy policy sends `busyAction`; an idle and faulted policy sends nothing; an idle policy
that is not faulted forwards and rejects the unlinked requests at the head of the queue and admits
the first linked one, recording the move from the arm's waypoint to it admitted at `k`. Every
action is applied with the supervisor's `step`; the result is the actions sent and the new state,
or `none` if the supervisor blocks an action. A design model, not from MLS. -/
def boundary (cfg : Config) (k : Nat) (reqs : List Waypoint) (smp : Sample) (st : State) :
    Option (List Action × State) :=
  if st.sup.busy then
    match step cfg.sup st.sup (busyAction cfg k st smp) with
    | none => none
    | some s' =>
      some ([busyAction cfg k st smp], { st with sup := s', pending := st.pending ++ reqs })
  else if st.sup.faulted then
    some ([], { st with pending := st.pending ++ reqs })
  else
    match admitNext cfg.sup st.sup (st.pending ++ reqs) with
    | none => none
    | some (pre, s₁, none, rest) => some (pre, { st with sup := s₁, pending := rest })
    | some (pre, s₁, some w, rest) =>
      match step cfg.sup s₁ (.admit w) with
      | none => none
      | some s₂ =>
        some (pre ++ [.admit w],
          { sup := s₂, src := s₁.current, goal := w, start := k, pending := rest })

/-- **A run of the program.** The states `st k` before boundary `k` and the actions `acts k` sent
at boundary `k` are the program's own output on the stream of requests `reqs k` and samples
`smp k`: `st 0` is the initial state and `boundary` at every boundary `k` returns `acts k` and
`st (k + 1)`. A design model, not from MLS. -/
def IsProgramRun (cfg : Config) (reqs : Nat → List Waypoint) (smp : Nat → Sample)
    (st : Nat → State) (acts : Nat → List Action) : Prop :=
  st 0 = State.init cfg ∧
    ∀ k : Nat, boundary cfg k (reqs k) (smp k) (st k) = some (acts k, st (k + 1))

/-! ### Text encoding for the boundary protocol -/

/-- Parse an integer: a rational as accepted by `RoboLean.Demo.parseRat?` whose denominator is
`1`. A design convention, not from MLS. -/
def parseInt? (w : String) : Option Int :=
  (RoboLean.Demo.parseRat? w).bind fun q => if q.den = 1 then some q.num else none

/-- Parse a sample from six words: three encoder counts (integers) and three joint speeds
(rationals, rad/s). A design convention, not from MLS. -/
def parseSample? (c₀ c₁ c₂ v₀ v₁ v₂ : String) : Option Sample := do
  let c₀ ← parseInt? c₀
  let c₁ ← parseInt? c₁
  let c₂ ← parseInt? c₂
  let v₀ ← RoboLean.Demo.parseRat? v₀
  let v₁ ← RoboLean.Demo.parseRat? v₁
  let v₂ ← RoboLean.Demo.parseRat? v₂
  some { counts := (c₀, c₁, c₂), vel := (v₀, v₁, v₂) }

/-- Parse a list of waypoints, three angles in degrees each. A design convention, not from
MLS. -/
def parseWaypoints : List String → Option (List Waypoint)
  | [] => some []
  | a :: b :: c :: rest => do
    let w ← parseWaypoint? a b c
    let ws ← parseWaypoints rest
    some (w :: ws)
  | _ => none

/-- Parse the arguments of `policy h T posTol velTol cpr` for the supervisor's parameters `p`:
the period and the duration in seconds (positive rationals), the arrival tolerances in degrees
and in radians per second (nonnegative rationals) and the encoder resolution in counts per
revolution (a positive natural number). A design convention, not from MLS. -/
def parseConfig (p : Params) : List String → Except String Config
  | [h, T, pt, vt, cpr] =>
    match RoboLean.Demo.parseRat? h, RoboLean.Demo.parseRat? T, RoboLean.Demo.parseRat? pt,
        RoboLean.Demo.parseRat? vt, RoboLean.Demo.parseNat? cpr with
    | some h, some T, some pt, some vt, some cpr =>
      if 0 < h ∧ 0 < T ∧ 0 ≤ pt ∧ 0 ≤ vt ∧ 0 < cpr then
        .ok { sup := p, period := h, duration := T, posTol := pt, velTol := vt,
              countsPerRev := cpr }
      else .error "bad policy"
    | _, _, _, _, _ => .error "bad policy"
  | _ => .error "usage: policy h T posTol velTol cpr"

/-- An action as one word: `request:a,b,c`, `admit:a,b,c`, `reject:a,b,c`, `finish`, `tick` or
`timeout`, angles in degrees as `renderWaypoint` writes them. A design convention, not from
MLS. -/
def renderAction : Action → String
  | .request w => "request:" ++ renderWaypoint w
  | .admit w => "admit:" ++ renderWaypoint w
  | .reject w => "reject:" ++ renderWaypoint w
  | .finish => "finish"
  | .tick => "tick"
  | .timeout => "timeout"

/-- A list of actions separated by `;`, or `-` when empty. A design convention, not from
MLS. -/
def renderActions (l : List Action) : String :=
  if l.isEmpty then "-" else ";".intercalate (l.map renderAction)

/-- A policy state on one line: the supervisor's state as `Supervisor.State.render` writes it,
then `src=<waypoint> goal=<waypoint> start=<n> pending=<waypoints>`. A design convention,
not from MLS. -/
def State.render (st : State) : String :=
  st.sup.render ++ " src=" ++ renderWaypoint st.src ++ " goal=" ++ renderWaypoint st.goal ++
    " start=" ++ toString st.start ++ " pending=" ++ renderWaypoints st.pending

end RoboLean.Cell.Policy
