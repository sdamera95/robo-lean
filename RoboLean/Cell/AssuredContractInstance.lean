import RoboLean.Cell.AssuredContract
import RoboLean.Cell.SupervisorContractHand

/-!
# The earlier assured cell theorems from the contract form

The assured cell theorems of `RoboLean.Cell.AssuredInstanceRight` follow from those of
`RoboLean.Cell.AssuredContract`, which take the supervisor's contract `Supervisor.Contract` as a
premise, with the premise discharged by the hand-written proof `Supervisor.contract_of_design`
(through the design relation `RoboLean.Design.CellSupervisor`). The loop data `cellParams` and
`openCellParams` differ only in the link relation, which a timed run of the cell loop does not
read, so a run for the one is a run for the other.

* `IsCellRun.openCellParams_of_cellParams`: the transfer of a timed run.
* `cell_assured_accel_right_of_contract`, `cell_assured_accel_design_tight_right_of_contract`: the
  statements of `cell_assured_accel_right` and `cell_assured_accel_design_tight_right`, each in one
  term from the contract form.
* `demo_assured_contract_tight_right`: the demonstration run carried through
  `cell_assured_contract_design_tight_right`, so that a concrete motion meets its hypotheses.

The arm is `cellArm` (MLS Example 4.3, printed p. 172, with the cell's parameters) under computed
torque (MLS eq. (4.49), p. 191), with the position and the velocity required to have right
derivatives only. These are design statements, not from MLS. They concern the ideal rigid-body
model with a bounded disturbance and the ideal sampled loop; they do not assert that a closed-loop
solution exists, and say nothing about sensing, delay, actuator limits or a physical arm.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- A timed run of the cell loop for the loop data `cellParams` is one for `openCellParams` with
the same period `h` (s), move duration `T` (s) and arrival tolerances `δ_a` (rad), `v_a` (rad/s):
the two differ only in the link relation, which the policy's decisions do not read. A design
statement, not from MLS. -/
theorem IsCellRun.openCellParams_of_cellParams {h T δa va : ℝ} {x v : ℝ → Fin 3 → ℝ}
    {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams h T δa va) Instances.params x v c acts) :
    IsCellRun (openCellParams h T δa va) Instances.params x v c acts := by
  refine ⟨hrun.1, fun k => ?_⟩
  obtain ⟨pre, pol, s₁, h1, h2, h3, hpol⟩ := hrun.2 k
  refine ⟨pre, pol, s₁, h1, h2, h3, ?_⟩
  generalize c (k + 1) = c' at hpol ⊢
  cases hpol with
  | finish s' hbusy hdue harr hstep => exact .finish _ s' hbusy hdue harr hstep
  | timeout s' hbusy hnot hage hstep => exact .timeout _ s' hbusy hnot hage hstep
  | tick s' hbusy hnot hage hstep => exact .tick _ s' hbusy hnot hage hstep
  | wait hidle => exact .wait _ hidle
  | admit w s' hidle hstep => exact .admit _ w s' hidle hstep

/-- **The assured cell, acceleration from the right, from the contract form.** The statement of
`cell_assured_accel_right`, hypotheses and conclusions unchanged (seconds, radians, radians per
second; the position and the velocity with right derivatives only; the disturbance bounded by
`ω² δ` per joint at the acceleration level), obtained from `cell_assured_contract_right` with the
supervisor's contract given by the hand-written proof `Supervisor.contract_of_design`. A design
statement, not from MLS; the arm is MLS Example 4.3 (printed p. 172) under computed torque (MLS
eq. (4.49), p. 191). -/
theorem cell_assured_accel_right_of_contract {h T δa va ω δ : ℝ} (hh : 0 < h) (hT : 0 < T)
    (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 < ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va) (hδ : δ ≤ 1 / 20)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      CellArmFollowsAccelRightAt ω T δ x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * h) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ k, run Instances.params (State.init Instances.params.home) (actsUpTo acts k) =
      some (c k).sup) ∧
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 1)).sup.commanded = [(c (k₀ + 1)).goal] ∧
      (∀ j, j < ⌈T / h⌉₊ → (c (k₀ + 1 + j)).sup.busy = true) ∧
      (c (k₀ + ⌈T / h⌉₊ + 1)).sup.busy = false ∧
      (c (k₀ + ⌈T / h⌉₊ + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      (c k).sup.commanded = [(c k).goal] ∧ (c (k + 1)).sup.current = (c k).goal ∧
      InTube δ ω (DegPoint.toRad (c k).goal) 0 (x (k * h)) (v (k * h)) ∧
      dist (sceneTool (x (k * h))) (sceneTool (DegPoint.toRad (c k).goal)) ≤ 73 / 50 * δ) :=
  cell_assured_contract_right hh hT hN hω hδa hva hδ
    (Supervisor.contract_of_design Instances.params) hrun.openCellParams_of_cellParams htrack
    hcont h0

/-- **The assured cell at the tube radius `3/100` rad, from the contract form.** The statement of
`cell_assured_accel_design_tight_right`, hypotheses and conclusions unchanged (`h = 1/10` s,
`T = 2` s, `ω = 80` rad/s, `δ = δ_a = 3/100` rad, `v_a = 24/5` rad/s; the position and the velocity
with right derivatives only), obtained from `cell_assured_contract_design_tight_right` with the
supervisor's contract given by the hand-written proof `Supervisor.contract_of_design`. A design
statement, not from MLS. -/
theorem cell_assured_accel_design_tight_right_of_contract {x v acc d : ℝ → Fin 3 → ℝ}
    {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        219 / 5000) :=
  cell_assured_contract_design_tight_right (Supervisor.contract_of_design Instances.params)
    hrun.openCellParams_of_cellParams htrack hcont h0

/-- **A moving arm through the contract form.** The demonstration run (the move from home to the
waypoint above the pick slot, tracked exactly with zero disturbance) meets every hypothesis of
`cell_assured_contract_design_tight_right`, with the supervisor's contract given by the
hand-written proof `Supervisor.contract_of_design` and the one-sided tracking predicate from the
two-sided one through `CellArmFollowsAccelAt.right`. So the links keep `9/100` m from every
obstacle at every `t ≥ 0` (s), the supervisor never faults, and at the finish the tool is within
`219/5000` m of the goal's tool position. The statement of `demo_assured_tight_right`. A design
statement, not from MLS. -/
theorem demo_assured_contract_tight_right :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 (3 / 100) demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using (demoMotion_follows_of (by norm_num) t).right
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_contract_design_tight_right
    (Supervisor.contract_of_design Instances.params)
    (demo_isCellRun_of (by norm_num) (by norm_num)).openCellParams_of_cellParams htrack
    demo_continuousOn (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

end RoboLean.Cell.Loop
