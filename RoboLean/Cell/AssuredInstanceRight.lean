import RoboLean.Cell.AssuredInstanceTight
import RoboLean.Cell.TrackingLoopRight

/-!
# The assured cell with the acceleration required only from the right

The assured cell theorem of `RoboLean.Cell.AssuredInstance` in the acceleration-level form, with
the per-period tracking hypothesis `CellArmFollowsAccelRightAt`: the position and the velocity
of the arm need right derivatives only, so a disturbance that jumps (and with it the
acceleration) is allowed, and `(x, v)` stays continuous on `[0, ∞)` by hypothesis. The
conclusions are those of `cell_assured_accel`. The arm is `cellArm` (MLS Example 4.3, printed
p. 172, with the cell's parameters) under computed torque (MLS eq. (4.49), p. 191).

* `cell_assured_accel_right`: the statement of `cell_assured_accel` with the one-sided predicate.
* `cell_assured_accel_gain80_right`: at `h = 1/10` s, `T = 2` s, `ω = 80` rad/s for every tube
  radius `δ ≤ 1/20` rad.
* `cell_assured_accel_design_tight_right`: at the tube radius `δ = δ_a = 3/100` rad with
  `v_a = 24/5` rad/s, a disturbance of at most `192` rad/s² per joint, a finish `20` boundaries
  after admission and the tool within `219/5000` m of the goal's tool position.
* `demo_assured_tight_right`: the demonstration run meets every hypothesis of
  `cell_assured_accel_design_tight_right`, through `CellArmFollowsAccelAt.right`.

These are design statements, not from MLS. They concern the ideal rigid-body model with a bounded
disturbance and the ideal sampled loop; they do not assert that a closed-loop solution exists, and
say nothing about sensing, delay, actuator limits or a physical arm.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- **The assured cell, disturbance bounded at the acceleration level, acceleration from the
right.** The statement of `cell_assured_accel` with the per-period tracking hypothesis
`CellArmFollowsAccelRightAt`: for the cell's arm `cellArm` under computed torque with the gains
`ω² I`, `2ω I` (MLS eq. (4.49), p. 191, along a motion as on p. 301), the scene's three cells and
obstacles, and the executable cell supervisor with its instance cells and age bound 25: let
`0 < h`, `0 < T`, `⌈T/h⌉ ≤ 25`, `0 < ω`, `δ ≤ min δ_a (1/20)`, `2 ω δ ≤ v_a` (seconds, radians,
radians per second). Then for every timed run `c` of the cell loop with the actions `acts` sent to
the supervisor and every motion `(x, v, acc)` with disturbance torque `d`, under the hypotheses
* (harness, `hrun`) at each boundary `k h` the actions sent are queue actions followed by the
  policy's action on the exact sample `(x (k h), v (k h))`, each accepted by the supervisor;
* (harness and plant, `htrack`) at every instant `t` of each period `(k h, (k + 1) h]` the arm
  obeys its equations of motion `M ẍ + C ẋ + N = F + d` with the computed torque `F` tracking the
  quintic reference of the last admitted move, `x` and `v` have the right derivatives `v t` and
  `acc t` (within `[t, ∞)`, so the acceleration may jump), and `|(M(x)⁻¹ d)ᵢ| ≤ ω² δ` for every
  joint;
* (plant, `hcont`) `(x, v)` is continuous on `[0, ∞)`;
* (harness, `h0`) the arm starts in the tube around home at rest,
the conclusions are: the supervisor's state before boundary `k` is `Supervisor.run` of the actions
sent so far; every point of both links keeps a Euclidean distance of at least `9/100` m from
every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays below 25; a move
admitted at boundary `k₀` (commanded waypoint `goal`) is busy until and finished at boundary
`k₀ + ⌈T/h⌉`, with the arm at `goal`; at each finish the arm is in the tube around the goal at
rest and the tool is within `(73/50) δ` m of the goal's tool position. A design statement, not
from MLS. -/
theorem cell_assured_accel_right {h T δa va ω δ : ℝ} (hh : 0 < h) (hT : 0 < T)
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
  cell_conclusions hrun (cell_hyps hh hT hN hω.le hδa hva hrun htrack
    (cellArm_moveCorollary_accel_right (cellParams h T δa va) hT hω hcont) h0) hδ

/-- **The assured cell at the gain 80, for every tube radius, acceleration from the right.** With
`h = 1/10` s, `T = 2` s, `ω = 80` rad/s, a tube radius `δ ≤ 1/20` rad and arrival tolerances
`δ_a ≥ δ` rad and `v_a ≥ 160 δ` rad/s, and `|(M(x)⁻¹ d)ᵢ| ≤ 6400 δ` rad/s² for every joint (the
predicate `CellArmFollowsAccelRightAt 80 2 δ`, with right derivatives): the links keep `9/100` m
from every obstacle at every `t ≥ 0`, the supervisor never faults and its age stays below 25, a
move admitted at boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish the tool is
within `(73/50) δ` m of the goal's tool position. The hypotheses that remain are those of
`cell_assured_accel_right`: about the harness, that at each boundary the actions sent are queue
actions followed by the policy's action on the exact sample, each accepted by the supervisor
(`hrun`), and that the arm starts in the tube around home at rest (`h0`); about the harness and
the plant, that on each period the arm obeys its equations of motion with the computed torque
tracking the quintic reference of the last admitted move, with the acceleration from the right,
and the disturbance bound above (`htrack`); about the plant, that `(x, v)` is continuous on
`[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_accel_gain80_right {δ δa va : ℝ} (hδ : δ ≤ 1 / 20) (hδa : δ ≤ δa)
    (hva : 160 * δ ≤ va) {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 80 2 δ x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube δ 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        73 / 50 * δ) := by
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_accel_right (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) hδa (by linarith) hδ hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_,
    fun k hbusy hidle => (htool k hbusy hidle).2.2.2⟩
  obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
  rw [design_steps] at h2 h3
  exact ⟨h2, h3⟩

/-- **The assured cell at the tube radius `3/100` rad, acceleration from the right.** With
`h = 1/10` s, `T = 2` s, `ω = 80` rad/s, `δ = δ_a = 3/100` rad and `v_a = 24/5` rad/s, and
`|(M(x)⁻¹ d)ᵢ| ≤ 192` rad/s² for every joint, with the position and the velocity required to
have right derivatives only (`CellArmFollowsAccelRightAt`): the links keep `9/100` m from every
obstacle at every `t ≥ 0`, the supervisor never faults and its age stays below 25, a move
admitted at boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish the tool is
within `219/5000` m of the goal's tool position. The hypotheses that remain are those of
`cell_assured_accel_right`: about the harness, that at each boundary the actions sent are queue
actions followed by the policy's action on the exact sample, each accepted by the supervisor
(`hrun`), and that the arm starts in the tube around home at rest (`h0`); about the harness and
the plant, that on each period the arm obeys its equations of motion with the computed torque
tracking the quintic reference of the last admitted move, with the acceleration from the right,
and the disturbance bound above (`htrack`); about the plant, that `(x, v)` is continuous on
`[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_accel_design_tight_right {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
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
        219 / 5000) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    cell_assured_accel_gain80_right (by norm_num) le_rfl (by norm_num) hrun htrack hcont h0
  exact ⟨h1, h2, h3, fun k hbusy hidle => (h4 k hbusy hidle).trans_eq (by norm_num)⟩

/-- **A moving arm at the tube radius `3/100` rad, acceleration from the right.** The
demonstration run (the move from home to the waypoint above the pick slot, tracked exactly with
zero disturbance) meets every hypothesis of `cell_assured_accel_design_tight_right`: its
two-sided tracking predicate gives the one-sided one through `CellArmFollowsAccelAt.right`. So
the links keep `9/100` m from every obstacle at every `t ≥ 0`, the supervisor never faults, and at
the finish the tool is within `219/5000` m of the goal's tool position. A design statement, not
from MLS. -/
theorem demo_assured_tight_right :
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
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_accel_design_tight_right
    (demo_isCellRun_of (by norm_num) (by norm_num)) htrack demo_continuousOn
    (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

end RoboLean.Cell.Loop
