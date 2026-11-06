import RoboLean.Cell.Assured

/-!
# The sampled loop with the supervisor as a black box

The loop model of `RoboLean.Cell.Loop` builds the supervisor's admission guard into its step
relation: `Step.admit` requires the admitted waypoint to be linked to the current one and the
supervisor not to be faulted. This file removes both conditions. In `OpenStep` an idle loop may
admit any waypoint; whether the admitted move is linked, and whether a faulted supervisor stays
idle, is left to the supervisor, and enters only as a property of the states of a run,
`LoopContract`: at every boundary a busy loop's move from the waypoint the arm is at to the goal
is linked, and a faulted supervisor is idle.

* `OpenStep`, `IsOpenRun`: the policy and the timed runs without the admission guard.
* `LoopContract`: the loop-level form of the supervisor's contract along a run.
* `OpenStep.step`, `IsOpenRun.isRun`: a run of the open loop whose states meet the contract is a
  run of the guarded loop; `Step.openStep`, `IsRun.isOpenRun`, `Hyps.loopContract`: conversely,
  every run of the guarded loop is an open run whose states meet the contract.
* `OpenHyps`: the standing hypotheses of `Hyps` with the open run in place of the guarded one.
* `OpenHyps.assured`: the conclusions of `Hyps.assured` (clearance, no fault, finish on time, tool
  accuracy and the tube at each finish) for every open run whose states meet `LoopContract`.

A design statement, not from MLS; it concerns the ideal sampled loop with exact samples and says
nothing about a physical arm. Units as in `RoboLean.Cell.Loop`: seconds, radians, radians per
second.
-/

namespace RoboLean.Cell.Loop

open Set

variable {n : ℕ} {W : Type*}

/-- One decision of the policy at boundary `k` from the sample `(θ, θ')`, with the supervisor
treated as a black box: as `Step`, except that an idle loop may admit any waypoint `w`, with no
condition on the link from the current waypoint to `w` and none on the fault flag (those are the
supervisor's decisions, not the loop's). A design model, not from MLS. -/
inductive OpenStep (P : Params n W) (k : ℕ) (θ θ' : Fin n → ℝ) : State W → State W → Prop
  /-- The active move is due and arrived: the arm is at its goal and the loop becomes idle. A
  design model, not from MLS. -/
  | finish (s : State W) (hbusy : s.busy = true) (hdue : Due P s k)
      (harr : Arrived P s.goal θ θ') :
      OpenStep P k θ θ' s { s with current := s.goal, busy := false, age := 0 }
  /-- The active move is not finished and its age is at the bound: the supervisor stops. A design
  model, not from MLS. -/
  | timeout (s : State W) (hbusy : s.busy = true) (hnot : ¬ (Due P s k ∧ Arrived P s.goal θ θ'))
      (hage : s.age = P.bound) :
      OpenStep P k θ θ' s { s with busy := false, faulted := true, age := 0 }
  /-- The active move is not finished and its age is below the bound: one tick. A design model,
  not from MLS. -/
  | tick (s : State W) (hbusy : s.busy = true) (hnot : ¬ (Due P s k ∧ Arrived P s.goal θ θ'))
      (hage : s.age ≠ P.bound) :
      OpenStep P k θ θ' s { s with age := s.age + 1 }
  /-- Idle, nothing is admitted at this boundary. A design model, not from MLS. -/
  | wait (s : State W) (hidle : s.busy = false) : OpenStep P k θ θ' s s
  /-- Idle, the supervisor admits the waypoint `w`; the loop does not check the admission. A
  design model, not from MLS. -/
  | admit (s : State W) (w : W) (hidle : s.busy = false) :
      OpenStep P k θ θ' s { s with busy := true, age := 0, src := s.current, goal := w, start := k }

/-- A timed run of the open loop for the motion with joint positions `x t` and velocities `v t`:
`s 0 = init home`, and `s (k + 1)` is an `OpenStep` from `s k` with the exact sample
`(x (k h), v (k h))`. A design model, not from MLS. -/
def IsOpenRun (P : Params n W) (home : W) (x v : ℝ → Fin n → ℝ) (s : ℕ → State W) : Prop :=
  s 0 = init home ∧
    ∀ k : ℕ, OpenStep P k (x (k * P.period)) (v (k * P.period)) (s k) (s (k + 1))

/-- The loop-level form of the supervisor's contract along the states `s`: at every boundary `k`,
if the loop is busy then the move from the waypoint the arm is at to the goal is linked
(`P.linked`), and if the supervisor is faulted then it is idle. A design statement, not from
MLS. -/
def LoopContract (P : Params n W) (s : ℕ → State W) : Prop :=
  ∀ k : ℕ, ((s k).busy = true → P.linked (s k).current (s k).goal) ∧
    ((s k).faulted = true → (s k).busy = false)

/-- An open step into a state that meets the contract is a step of the guarded loop: after an
admission the state is busy, so the contract makes the admitted move linked and, since an
admission keeps the fault flag, the supervisor was not faulted. A design statement, not from
MLS. -/
theorem OpenStep.step {P : Params n W} {k : ℕ} {θ θ' : Fin n → ℝ} {st st' : State W}
    (h : OpenStep P k θ θ' st st')
    (hlinked : st'.busy = true → P.linked st'.current st'.goal)
    (hfault : st'.faulted = true → st'.busy = false) :
    Step P k θ θ' st st' := by
  cases h with
  | finish hbusy hdue harr => exact .finish _ hbusy hdue harr
  | timeout hbusy hnot hage => exact .timeout _ hbusy hnot hage
  | tick hbusy hnot hage => exact .tick _ hbusy hnot hage
  | wait hidle => exact .wait _ hidle
  | admit w hidle =>
    have hok : st.faulted = false := by
      cases hf : st.faulted
      · rfl
      · have := hfault hf
        simp at this
    exact .admit _ w hidle hok (hlinked rfl)

/-- **An open run that meets the contract is a run of the guarded loop.** A design statement, not
from MLS. -/
theorem IsOpenRun.isRun {P : Params n W} {home : W} {x v : ℝ → Fin n → ℝ} {s : ℕ → State W}
    (h : IsOpenRun P home x v s) (hc : LoopContract P s) : IsRun P home x v s :=
  ⟨h.1, fun k => (h.2 k).step (hc (k + 1)).1 (hc (k + 1)).2⟩

/-- Every step of the guarded loop is an open step. A design statement, not from MLS. -/
theorem Step.openStep {P : Params n W} {k : ℕ} {θ θ' : Fin n → ℝ} {st st' : State W}
    (h : Step P k θ θ' st st') : OpenStep P k θ θ' st st' := by
  cases h with
  | finish hbusy hdue harr => exact .finish _ hbusy hdue harr
  | timeout hbusy hnot hage => exact .timeout _ hbusy hnot hage
  | tick hbusy hnot hage => exact .tick _ hbusy hnot hage
  | wait hidle => exact .wait _ hidle
  | admit w hidle _ _ => exact .admit _ w hidle

/-- Every run of the guarded loop is a run of the open loop. A design statement, not from MLS. -/
theorem IsRun.isOpenRun {P : Params n W} {home : W} {x v : ℝ → Fin n → ℝ} {s : ℕ → State W}
    (h : IsRun P home x v s) : IsOpenRun P home x v s :=
  ⟨h.1, fun k => (h.2 k).openStep⟩

/-- The standing hypotheses of the assured loop theorem with the supervisor as a black box: the
fields of `Hyps`, with the timed run of the open loop (`IsOpenRun`) in place of the run of the
guarded loop. Nothing here constrains which waypoints the supervisor admits; that enters through
`LoopContract`. A design statement, not from MLS. -/
structure OpenHyps (P : Params n W) (R : MoveRef n P.duration) (δ ω : ℝ) (home : W)
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
  /-- The decisions at the boundaries follow the open policy. -/
  run : IsOpenRun P home x v s
  /-- The controller tracks the reference of the last admitted move. -/
  tracks : Tracks P follows s
  /-- The move corollary holds for the motion. -/
  move : MoveCorollary P R δ ω follows x v
  /-- The arm starts in the tube around home at rest. -/
  init_tube : InTube δ ω (P.pos home) 0 (x 0) (v 0)

variable {P : Params n W} {R : MoveRef n P.duration} {δ ω : ℝ} {home : W}
  {follows : W → W → ℝ → ℝ → Prop} {x v : ℝ → Fin n → ℝ} {s : ℕ → State W}

/-- The open hypotheses and the contract give the standing hypotheses of the guarded loop. A
design statement, not from MLS. -/
theorem OpenHyps.hyps (H : OpenHyps P R δ ω home follows x v s) (hc : LoopContract P s) :
    Hyps P R δ ω home follows x v s where
  period_pos := H.period_pos
  duration_pos := H.duration_pos
  ceil_le_bound := H.ceil_le_bound
  rate_nonneg := H.rate_nonneg
  radius_le_posTol := H.radius_le_posTol
  speed_le_velTol := H.speed_le_velTol
  home_linked := H.home_linked
  run := H.run.isRun hc
  tracks := H.tracks
  move := H.move
  init_tube := H.init_tube

/-- Along every run of the guarded loop under the standing hypotheses, the states meet the
contract: while busy the arm's waypoint is the start of a linked move, and the supervisor is
never faulted. A design statement, not from MLS. -/
theorem Hyps.loopContract (H : Hyps P R δ ω home follows x v s) : LoopContract P s := fun k => by
  have hI := H.inv k
  refine ⟨fun hb => ?_, fun hf => ?_⟩
  · rw [(hI.busy_spec hb).1]
    exact hI.linked_move
  · rw [hI.faulted_eq] at hf
    exact absurd hf (by simp)

/-- **The assured loop with the supervisor as a black box.** Along every timed run of the open
loop under `OpenHyps` whose states meet the loop-level contract `LoopContract` (busy implies the
move from the arm's waypoint to the goal is linked; faulted implies idle), with cells certified at
an inflation `δ_c ≥ δ` and a tool map with the Lipschitz-type bound `L`:
(a) the configuration is clear at every instant `t ≥ 0`;
(b) the supervisor is never faulted, the age stays below the bound, and a move admitted at
boundary `k₀` is finished at boundary `k₀ + ⌈T/h⌉` with the arm at its goal;
(c) at each finish the tool is within `L δ` of the goal's tool position;
(d) at each finish the motion is in the tube around the goal at rest.
The conclusions are those of `Hyps.assured`. A design statement, not from MLS. -/
theorem OpenHyps.assured {E : Type*} [PseudoMetricSpace E]
    (H : OpenHyps P R δ ω home follows x v s) (hc : LoopContract P s)
    {δc : ℝ} {clear : (Fin n → ℝ) → Prop} (hcert : CellsCertify P δc clear) (hδ : δ ≤ δc)
    {tool : (Fin n → ℝ) → E} {L : ℝ}
    (htool : ∀ θ θ' : Fin n → ℝ, ∀ r : ℝ, (∀ i, |θ i - θ' i| ≤ r) →
      dist (tool θ) (tool θ') ≤ L * r) :
    (∀ t, 0 ≤ t → clear (x t)) ∧
    (∀ k, (s k).faulted = false ∧ (s k).age < P.bound) ∧
    (∀ k₀, (s k₀).busy = false → (s (k₀ + 1)).busy = true →
      (∀ j, j < P.steps → (s (k₀ + 1 + j)).busy = true) ∧
      (s (k₀ + P.steps + 1)).busy = false ∧
      (s (k₀ + P.steps + 1)).current = (s (k₀ + 1)).goal) ∧
    (∀ k, (s k).busy = true → (s (k + 1)).busy = false →
      dist (tool (x (k * P.period))) (tool (P.pos (s k).goal)) ≤ L * δ) ∧
    (∀ k, (s k).busy = true → (s (k + 1)).busy = false →
      (s (k + 1)).current = (s k).goal ∧
      InTube δ ω (P.pos (s k).goal) 0 (x (k * P.period)) (v (k * P.period))) :=
  (H.hyps hc).assured hcert hδ htool

end RoboLean.Cell.Loop
