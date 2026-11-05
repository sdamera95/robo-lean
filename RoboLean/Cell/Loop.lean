import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The sampled supervisory loop of a pick-and-place cell

This file defines the sampled loop that joins a waypoint supervisor, a tracking controller and a
plant, over abstract interfaces. A design model, not from MLS.

Time is continuous; the supervisor decides at the boundaries `k h` (`k : ℕ`, period `h > 0`).
The loop state `State W` holds the supervisor's components that the policy reads (the waypoint the
arm is at, `current`; `busy`; `faulted`; the command age `age`) and the controller's record of the
last admitted move (its start `src`, its goal `goal` and the boundary `start` at which it was
admitted). Initially the arm is at a home waypoint, idle, and the last move is the rest move from
home to home admitted at boundary `0`.

The policy at boundary `k`, with the sample `(θ, θ') = (x (k h), v (k h))` of the joint positions
and velocities (`Step`):

* busy with goal `b` admitted at boundary `k₀`: if `k₀ h + T ≤ k h` and
  `∀ i, |θᵢ − bᵢ| ≤ δ_a ∧ |θ'ᵢ| ≤ v_a` (`Due`, `Arrived`) then `finish` (the arm is at `b`, idle,
  age `0`); otherwise, if the age equals the bound, `timeout` (idle, age `0`, faulted); otherwise
  `tick` (the age grows by one);
* idle: either `wait` (nothing changes; this covers an empty request queue, a rejected request and
  a faulted supervisor) or, when not faulted, `admit w` for a waypoint `w` linked to the current
  one: the supervisor becomes busy with age `0`, and the controller's last move becomes the move
  from the current waypoint to `w` admitted at boundary `k`.

So the busy branch is deterministic and the idle branch is any choice the supervisor's guards
allow; at most one action happens at a boundary. A timed run (`IsRun`) starts in `init home` and
takes one step at every boundary from the exact sample at that boundary. Between boundaries the
controller tracks the reference of the last admitted move (`Tracks`, stated through an abstract
predicate `follows a b t₀ t`: at time `t` the motion obeys the closed loop that tracks the
reference of the move from `a` to `b` admitted at time `t₀`).

The other interfaces are abstract as well: the joint vector `pos w` of each waypoint (radians),
the relation `linked`, the move reference `MoveRef` (a curve in the segment between the two joint
vectors that rests at the goal from `t₀ + T` on and has zero velocity for a rest move), the
tracking tube `InTube` (`|eᵢ| ≤ δ` and `|ėᵢ + ω eᵢ| ≤ ω δ` with `e = θ − r`), the move corollary
`MoveCorollary` (the tube around the reference on a finite horizon from the tube around the start
at the admission), the inflated cell `inflate` and the certified cells `CellsCertify`.

These statements concern the ideal sampled loop: exact samples at exact boundaries, no delay, a
motion given together with the run. They say nothing about the existence of a closed-loop
solution, numerics, sensing or a physical arm.
-/

namespace RoboLean.Cell.Loop

open Set

variable {n : ℕ} {W : Type*}

/-- The state of the sampled loop over a waypoint type `W`: the supervisor's components read by
the policy (`current`, the waypoint the arm is at, the specification's `at`; `busy`; `faulted`;
`age`, the number of ticks of the active command) and the controller's record of the last admitted
move (`src` to `goal`, admitted at boundary `start`). A design model, not from MLS. -/
structure State (W : Type*) where
  /-- The waypoint the arm is at (the start of the active move while busy). -/
  current : W
  /-- Whether a move is active. -/
  busy : Bool
  /-- Whether the supervisor has timed out (a protective stop). -/
  faulted : Bool
  /-- The number of ticks since the active move was admitted. -/
  age : ℕ
  /-- The start waypoint of the last admitted move. -/
  src : W
  /-- The goal waypoint of the last admitted move. -/
  goal : W
  /-- The boundary index at which the last admitted move was admitted. -/
  start : ℕ

/-- The initial loop state: at `home`, idle, not faulted, age `0`, and the last move the rest
move from `home` to `home` admitted at boundary `0`. A design model, not from MLS. -/
def init (home : W) : State W :=
  ⟨home, false, false, 0, home, home, 0⟩

/-- The static data of the loop: the joint vector `pos w : Fin n → ℝ` of each waypoint (radians),
the relation `linked` of the supervisor's admission guard, the period `h` (s), the move duration
`T` (s), the arrival tolerances `δ_a` (rad) and `v_a` (rad/s) and the age bound. A design model,
not from MLS. -/
structure Params (n : ℕ) (W : Type*) where
  /-- The joint vector of a waypoint, in radians. -/
  pos : W → Fin n → ℝ
  /-- The admission guard: the move from the first waypoint to the second is allowed. -/
  linked : W → W → Prop
  /-- The sampling period `h`, in seconds. -/
  period : ℝ
  /-- The move duration `T`, in seconds. -/
  duration : ℝ
  /-- The joint position tolerance `δ_a` of the arrival test, in radians. -/
  posTol : ℝ
  /-- The joint speed tolerance `v_a` of the arrival test, in radians per second. -/
  velTol : ℝ
  /-- The age bound of the supervisor, in periods. -/
  bound : ℕ

/-- The time test of the policy at boundary `k`: the active move, admitted at boundary
`s.start`, has had its full duration, `s.start · h + T ≤ k · h`. A design model, not from MLS. -/
def Due (P : Params n W) (s : State W) (k : ℕ) : Prop :=
  (s.start : ℝ) * P.period + P.duration ≤ k * P.period

/-- The arrival test of the policy for the goal `g` and the sampled joint positions `θ` and
velocities `θ'`: `|θᵢ − gᵢ| ≤ δ_a` and `|θ'ᵢ| ≤ v_a` for every joint `i` (radians, radians per
second). A design model, not from MLS. -/
def Arrived (P : Params n W) (g : W) (θ θ' : Fin n → ℝ) : Prop :=
  ∀ i, |θ i - P.pos g i| ≤ P.posTol ∧ |θ' i| ≤ P.velTol

/-- One decision of the policy at boundary `k` from the sample `(θ, θ')`: the busy branch finishes
when the move is due and arrived, times out when not and the age is at the bound, and ticks
otherwise; the idle branch waits, or admits a waypoint linked to the current one when not faulted.
A design model, not from MLS. -/
inductive Step (P : Params n W) (k : ℕ) (θ θ' : Fin n → ℝ) : State W → State W → Prop
  /-- The active move is due and arrived: the arm is at its goal and the loop becomes idle. -/
  | finish (s : State W) (hbusy : s.busy = true) (hdue : Due P s k)
      (harr : Arrived P s.goal θ θ') :
      Step P k θ θ' s { s with current := s.goal, busy := false, age := 0 }
  /-- The active move is not finished and its age is at the bound: the supervisor stops. -/
  | timeout (s : State W) (hbusy : s.busy = true) (hnot : ¬ (Due P s k ∧ Arrived P s.goal θ θ'))
      (hage : s.age = P.bound) :
      Step P k θ θ' s { s with busy := false, faulted := true, age := 0 }
  /-- The active move is not finished and its age is below the bound: one tick. -/
  | tick (s : State W) (hbusy : s.busy = true) (hnot : ¬ (Due P s k ∧ Arrived P s.goal θ θ'))
      (hage : s.age ≠ P.bound) :
      Step P k θ θ' s { s with age := s.age + 1 }
  /-- Idle, nothing is admitted at this boundary. -/
  | wait (s : State W) (hidle : s.busy = false) : Step P k θ θ' s s
  /-- Idle and not faulted, a waypoint linked to the current one is admitted. -/
  | admit (s : State W) (w : W) (hidle : s.busy = false) (hok : s.faulted = false)
      (hlinked : P.linked s.current w) :
      Step P k θ θ' s { s with busy := true, age := 0, src := s.current, goal := w, start := k }

/-- A timed run of the loop for the motion with joint positions `x t` and velocities `v t`: the
sequence `s k` of loop states before the decision at boundary `k` starts at `init home`, and the
state after the decision at boundary `k`, `s (k + 1)`, is a `Step` from `s k` with the exact
sample `(x (k h), v (k h))`. The state `s (k + 1)` is in force on the period from `k h` to
`(k + 1) h`. A design model, not from MLS. -/
def IsRun (P : Params n W) (home : W) (x v : ℝ → Fin n → ℝ) (s : ℕ → State W) : Prop :=
  s 0 = init home ∧ ∀ k : ℕ, Step P k (x (k * P.period)) (v (k * P.period)) (s k) (s (k + 1))

/-- The controller tracks the reference of the last admitted move: on every period
`(k h, (k + 1) h]` the motion obeys `follows a b t₀`, where `a`, `b` and `t₀ = start · h` are the
last admitted move of the state `s (k + 1)` in force on that period. The predicate `follows` is
abstract (for an arm: the disturbed closed-loop equation with the computed torque tracking the
move reference). A design model, not from MLS. -/
def Tracks (P : Params n W) (follows : W → W → ℝ → ℝ → Prop) (s : ℕ → State W) : Prop :=
  ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * P.period) ((k + 1) * P.period),
    follows (s (k + 1)).src (s (k + 1)).goal ((s (k + 1)).start * P.period) t

/-- The tracking tube of radius `δ` (rad) and rate `ω` (1/s) around the reference position `r`
and velocity `r'`, at joint positions `θ` and velocities `θ'`: with `e = θ − r`,
`|eᵢ| ≤ δ` and `|θ'ᵢ − r'ᵢ + ω eᵢ| ≤ ω δ` for every joint (the componentwise tube of the
computed-torque error `z = ė + ω e`). The tube around a waypoint at rest is `InTube δ ω p 0`. A
design statement, not from MLS. -/
def InTube (δ ω : ℝ) (r r' θ θ' : Fin n → ℝ) : Prop :=
  ∀ i, |θ i - r i| ≤ δ ∧ |θ' i - r' i + ω * (θ i - r i)| ≤ ω * δ

/-- The interface of a move reference of duration `T`: positions `pos a b t₀ t` and velocities
`vel a b t₀ t` of the move from the joint vector `a` to `b` started at time `t₀`, such that the
position always lies on the segment from `a` to `b`, the reference rests at `b` from `t₀ + T` on,
and the rest move from `a` to `a` has zero velocity. A design statement, not from MLS. -/
structure MoveRef (n : ℕ) (T : ℝ) where
  /-- The reference position at time `t` of the move from `a` to `b` started at `t₀`. -/
  pos : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ → Fin n → ℝ
  /-- The reference velocity at time `t` of the move from `a` to `b` started at `t₀`. -/
  vel : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ → Fin n → ℝ
  /-- The reference position lies on the segment from `a` to `b`. -/
  pos_mem_segment : ∀ a b t₀ t, pos a b t₀ t ∈ segment ℝ a b
  /-- The reference position is `b` from `t₀ + T` on. -/
  pos_of_le : ∀ a b t₀ t, t₀ + T ≤ t → pos a b t₀ t = b
  /-- The reference velocity is zero from `t₀ + T` on. -/
  vel_of_le : ∀ a b t₀ t, t₀ + T ≤ t → vel a b t₀ t = 0
  /-- The rest move from `a` to `a` has zero velocity. -/
  vel_self : ∀ a t₀ t, vel a a t₀ t = 0

/-- The move corollary, on a finite horizon, as a hypothesis on the motion `(x, v)`: for every
linked move from `a` to `b`, all `0 ≤ t₀ ≤ t₁`, if the motion obeys `follows a b t₀` at every
`t ∈ (t₀, t₁]` and is in the tube around `pos a` at rest at `t₀`, then it is in the tube around
the move reference `R` at every `t ∈ [t₀, t₁]`. A design statement, not from MLS; for an arm under
computed torque with a bounded disturbance it is a theorem about the tracking error. -/
def MoveCorollary (P : Params n W) (R : MoveRef n P.duration) (δ ω : ℝ)
    (follows : W → W → ℝ → ℝ → Prop) (x v : ℝ → Fin n → ℝ) : Prop :=
  ∀ a b : W, P.linked a b → ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ →
    (∀ t ∈ Ioc t₀ t₁, follows a b t₀ t) → InTube δ ω (P.pos a) 0 (x t₀) (v t₀) →
    ∀ t ∈ Icc t₀ t₁,
      InTube δ ω (R.pos (P.pos a) (P.pos b) t₀ t) (R.vel (P.pos a) (P.pos b) t₀ t) (x t) (v t)

/-- The set `C` of joint vectors inflated by `r` in each joint: the joint vectors within `r` of
some point of `C` in every joint (radians). A design statement, not from MLS. -/
def inflate (r : ℝ) (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {θ | ∃ c ∈ C, ∀ i, |θ i - c i| ≤ r}

/-- The certified cells: the joint vectors of every linked pair of waypoints lie in a common
convex cell `C` whose inflation by `δ_c` is clear (`clear θ` for every `θ` in it). For an arm,
`clear θ` says that every point of the links at the joint vector `θ` keeps a clearance from every
obstacle. A design statement, not from MLS. -/
def CellsCertify (P : Params n W) (δc : ℝ) (clear : (Fin n → ℝ) → Prop) : Prop :=
  ∀ a b : W, P.linked a b → ∃ C : Set (Fin n → ℝ),
    Convex ℝ C ∧ P.pos a ∈ C ∧ P.pos b ∈ C ∧ ∀ θ ∈ inflate δc C, clear θ

/-- The standing hypotheses of the assured loop theorem, for the data `P`, the move reference `R`,
the tube radius `δ` and rate `ω`, the home waypoint, the tracking predicate `follows`, the motion
`(x, v)` and the run `s`. The facts about the harness are `run` (the decisions at the boundaries
follow the policy from exact samples), `tracks` (between boundaries the controller tracks the
reference of the last admitted move) and `init_tube` (the arm starts in the tube around home); the
fact about the plant is `move` (the move corollary); the rest are numeric conditions on the
parameters. A design statement, not from MLS. -/
structure Hyps (P : Params n W) (R : MoveRef n P.duration) (δ ω : ℝ) (home : W)
    (follows : W → W → ℝ → ℝ → Prop) (x v : ℝ → Fin n → ℝ) (s : ℕ → State W) : Prop where
  /-- The period is positive. -/
  period_pos : 0 < P.period
  /-- The move duration is positive. -/
  duration_pos : 0 < P.duration
  /-- The age bound is at least the number of periods of a move, `⌈T / h⌉`. -/
  ceil_le_bound : ⌈P.duration / P.period⌉₊ ≤ P.bound
  /-- The tube rate is nonnegative. -/
  rate_nonneg : 0 ≤ ω
  /-- The arrival position tolerance is at least the tube radius. -/
  radius_le_posTol : δ ≤ P.posTol
  /-- The arrival speed tolerance is at least `2 ω δ`. -/
  speed_le_velTol : 2 * ω * δ ≤ P.velTol
  /-- The home waypoint is linked to itself (it lies in a cell). -/
  home_linked : P.linked home home
  /-- The supervisor's decisions follow the policy. -/
  run : IsRun P home x v s
  /-- The controller tracks the reference of the last admitted move. -/
  tracks : Tracks P follows s
  /-- The move corollary holds for the motion. -/
  move : MoveCorollary P R δ ω follows x v
  /-- The arm starts in the tube around home at rest. -/
  init_tube : InTube δ ω (P.pos home) 0 (x 0) (v 0)

/-- The policy is total: at every boundary and from every state some decision is possible, so a
timed run exists for every motion. A design statement, not from MLS. -/
theorem exists_step (P : Params n W) (k : ℕ) (θ θ' : Fin n → ℝ) (s : State W) :
    ∃ s', Step P k θ θ' s s' := by
  cases hb : s.busy
  · exact ⟨s, .wait s hb⟩
  · by_cases hfin : Due P s k ∧ Arrived P s.goal θ θ'
    · exact ⟨_, .finish s hb hfin.1 hfin.2⟩
    · by_cases hage : s.age = P.bound
      · exact ⟨_, .timeout s hb hfin hage⟩
      · exact ⟨_, .tick s hb hfin hage⟩

/-- For every motion `(x, v)` and home waypoint there is a timed run of the loop, built by choosing
a decision at each boundary (`exists_step`). A design statement, not from MLS. -/
theorem exists_isRun (P : Params n W) (home : W) (x v : ℝ → Fin n → ℝ) :
    ∃ s : ℕ → State W, IsRun P home x v s := by
  choose f hf using fun (k : ℕ) (s : State W) =>
    exists_step P k (x (k * P.period)) (v (k * P.period)) s
  let s : ℕ → State W := fun k => Nat.rec (init home) (fun j sj => f j sj) k
  exact ⟨s, rfl, fun k => hf k (s k)⟩

end RoboLean.Cell.Loop
