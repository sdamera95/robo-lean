import RoboLean.Cell.Assured
import RoboLean.Cell.LoopSupervisor
import RoboLean.Cell.CellsSupervisor
import RoboLean.Cell.TrackingLoop

/-!
# The assured pick-and-place cell

The assured loop theorem `Loop.Hyps.assured` instantiated for the cell: the three-link elbow arm
`cellArm` (MLS Example 4.3, printed p. 172, with the cell's lengths, masses and inertias) under
computed torque (MLS eq. (4.49), p. 191) with the gains `ω² I` and `2ω I`, tracking the clamped
quintic move reference, with a disturbance torque `d`; the scene's obstacles and its three cells,
certified at the inflation `1/20` rad; and the executable cell supervisor
`RoboLean.Cell.Supervisor` with the instance cells and the age bound 25, driven by the sampled
policy (`Loop.IsCellRun`).

* `cell_assured_accel`: with the disturbance bounded at the acceleration level,
  `|(M(θ)⁻¹ d)ᵢ| ≤ ω² δ` for every joint, along every timed run and every motion of the arm: the
  supervisor's state at each boundary is `Supervisor.run` of the actions sent so far; the links keep
  a Euclidean distance of at least `9/100` m from every obstacle at every instant `t ≥ 0` (a
  clearance of `3/100` m for the capsules of radius `3/50` m); the supervisor never faults and its
  age stays below 25; a move admitted at boundary `k₀` is finished at boundary `k₀ + ⌈T/h⌉`; at
  each finish the arm is in the tube around the goal and the tool is within `(73/50) δ` m of the
  goal's tool position.
* `cell_assured_torque`: the same with the disturbance bounded in Euclidean norm,
  `‖d‖₂ ≤ (9/100) ω² δ`, the inertia bound coming from the joint envelope that contains every cell
  inflated by `1/10` rad.
* `cell_assured_accel_design`, `cell_assured_torque_design`: the design values `h = 1/10` s,
  `T = 2` s, `ω = 80` rad/s, `δ = δ_a = 1/20` rad, `v_a = 8` rad/s, so that a move finishes at
  boundary `k₀ + 20` and the tool is within `73/1000` m of the goal's tool position.

These are design statements, not from MLS. They concern the ideal rigid-body model with a bounded
disturbance and the ideal sampled loop; they do not assert that a closed-loop solution exists, and
say nothing about sensing, delay, actuator limits or a physical arm.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The loop data of the cell for the period `h` (s), the move duration `T` (s) and the arrival
tolerances `δ_a` (rad), `v_a` (rad/s): waypoints in rational degrees mapped to radians by
`DegPoint.toRad`, the supervisor's link relation on its instance cells as the guard, and the
supervisor's age bound 25. A design definition, not from MLS. -/
def cellParams (h T δa va : ℝ) : Params 3 Waypoint where
  pos := DegPoint.toRad
  linked := CellLinked Instances.params.cells
  period := h
  duration := T
  posTol := δa
  velTol := va
  bound := Instances.params.bound

/-- The supervisor's age bound on its instance data is 25. A design statement, not from MLS. -/
theorem cellParams_bound (h T δa va : ℝ) : (cellParams h T δa va).bound = 25 := rfl

/-- The home waypoint `(0, -40, 30)` degrees is linked to itself: the crossing cell contains it.
A design statement, not from MLS. -/
theorem home_cellLinked : CellLinked Instances.params.cells Instances.params.home
    Instances.params.home :=
  (linked_eq_true_iff _ _ _).mp (by decide +kernel)

/-- The standing hypotheses of the loop theorem for the cell, from a timed run of the executable
supervisor, tracking of the last admitted move and the tube at home at time 0, for any tracking
predicate `follows` for which the move corollary holds. A design statement, not from MLS. -/
theorem cell_hyps {h T δa va ω δ : ℝ} (hh : 0 < h) (hT : 0 < T) (hN : ⌈T / h⌉₊ ≤ 25)
    (hω : 0 ≤ ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va)
    {follows : Waypoint → Waypoint → ℝ → ℝ → Prop}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      follows (c (k + 1)).src (c (k + 1)).goal ((c (k + 1)).start * h) t)
    (hmove : MoveCorollary (cellParams h T δa va) (quinticMoveRef (n := 3) hT) δ ω follows x v)
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    Hyps (cellParams h T δa va) (quinticMoveRef hT) δ ω Instances.params.home follows x v
      (fun k => (c k).toLoop) where
  period_pos := hh
  duration_pos := hT
  ceil_le_bound := hN
  rate_nonneg := hω
  radius_le_posTol := hδa
  speed_le_velTol := hva
  home_linked := home_cellLinked
  run := hrun.isRun (fun _ _ hab => hab) rfl
  tracks := htrack
  move := hmove
  init_tube := h0

/-- The loop's conclusions for the cell, from the standing hypotheses, stated on the executable
supervisor's states. A design statement, not from MLS. -/
theorem cell_conclusions {h T δa va ω δ : ℝ} {hT : 0 < T} {follows : Waypoint → Waypoint → ℝ → ℝ → Prop}
    {x v : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams h T δa va) Instances.params x v c acts)
    (H : Hyps (cellParams h T δa va) (quinticMoveRef hT) δ ω Instances.params.home follows x v
      (fun k => (c k).toLoop)) (hδ : δ ≤ 1 / 20) :
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
      dist (sceneTool (x (k * h))) (sceneTool (DegPoint.toRad (c k).goal)) ≤ 73 / 50 * δ) := by
  have hcert := sceneCells_certify_of_cellLinked (cellParams h T δa va) (fun _ => rfl)
    (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, htube⟩ :=
    H.assured hcert hδ sceneTool_lipschitz
  refine ⟨hrun.run_eq, hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfin k₀ hidle hbusy
    exact ⟨hrun.commanded_eq _ hbusy, h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := htube k hbusy hidle
    exact ⟨hrun.commanded_eq _ hbusy, h1, h2, htool k hbusy hidle⟩

/-- **The assured cell, disturbance bounded at the acceleration level.** For the cell's arm
`cellArm` under computed torque with the gains `ω² I`, `2ω I` (MLS eq. (4.49), p. 191, along a
motion as on p. 301), the scene's three cells and obstacles, and the executable cell supervisor
with its instance cells and age bound 25: let `0 < h`, `0 < T`, `⌈T/h⌉ ≤ 25`, `0 < ω`,
`δ ≤ min δ_a (1/20)`, `2 ω δ ≤ v_a` (seconds, radians, radians per second). Then for every timed
run `c` of the cell loop with the actions `acts` sent to the supervisor and every motion
`(x, v, acc)` with disturbance torque `d`, under the hypotheses
* (harness, `hrun`) at each boundary `k h` the actions sent are queue actions followed by the
  policy's action on the exact sample `(x (k h), v (k h))`, each accepted by the supervisor;
* (harness and plant, `htrack`) on each period `(k h, (k + 1) h]` the arm obeys its equations of
  motion `M ẍ + C ẋ + N = F + d` with the computed torque `F` tracking the quintic reference of
  the last admitted move, `x` and `v` have the derivatives `v` and `acc`, and
  `|(M(x)⁻¹ d)ᵢ| ≤ ω² δ` for every joint;
* (plant, `hcont`) `(x, v)` is continuous on `[0, ∞)`;
* (harness, `h0`) the arm starts in the tube around home at rest,
the conclusions are: the supervisor's state before boundary `k` is `Supervisor.run` of the actions
sent so far; every point of both links keeps a Euclidean distance of at least `9/100` m from
every obstacle at every `t ≥ 0`; the supervisor never faults and its age stays below 25; a move
admitted at boundary `k₀` (commanded waypoint `goal`) is busy until and finished at boundary
`k₀ + ⌈T/h⌉`, with the arm at `goal`; at each finish the arm is in the tube around the goal at
rest and the tool is within `(73/50) δ` m of the goal's tool position. A design statement, not
from MLS. -/
theorem cell_assured_accel {h T δa va ω δ : ℝ} (hh : 0 < h) (hT : 0 < T) (hN : ⌈T / h⌉₊ ≤ 25)
    (hω : 0 < ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va) (hδ : δ ≤ 1 / 20)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      CellArmFollowsAccelAt ω T δ x v acc d (DegPoint.toRad (c (k + 1)).src)
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
    (cellArm_moveCorollary_accel (cellParams h T δa va) hT hω hcont) h0) hδ

/-- Every configuration within `1/10` rad (each joint) of a point of the segment between two
linked waypoints keeps the forearm's mass centre at horizontal distance at least `1/8` m from the
base axis: such a configuration lies in the cell inflated by `1/10`, hence in the joint envelope
(shoulder at most `51°` in magnitude, shoulder plus elbow at most `57°` in magnitude). A design
statement, not from MLS. -/
theorem cell_reach (h T δa va : ℝ) :
    ∀ a b, (cellParams h T δa va).linked a b →
      ∀ p ∈ segment ℝ ((cellParams h T δa va).pos a) ((cellParams h T δa va).pos b),
      ∀ θ : Fin 3 → ℝ, (∀ i, |θ i - p i| ≤ 1 / 10) →
        1 / 8 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  intro a b hab p hp θ hθ
  obtain ⟨B, hB, ha, hb⟩ := (sceneLinked_iff_cellLinked a b).2 hab
  have hpB : p ∈ B.radSet 0 :=
    (B.convex_radSet 0).segment_subset (DegBox.toRad_mem_radSet ha) (DegBox.toRad_mem_radSet hb) hp
  have hθE := radSet_subset_jointEnvelope B hB (DegBox.mem_radSet_of_abs_sub_le hpB hθ)
  have hπ := Real.pi_pos
  obtain ⟨h11, h12⟩ := hθE 1
  obtain ⟨h21, h22⟩ := hθE 2
  simp [DegPoint.toRad, degToRad, jointEnvelope] at h11 h12 h21 h22
  apply cellArm_reach_of_abs_le
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- **The assured cell, disturbance bounded in Euclidean norm.** As `cell_assured_accel`, with the
per-period hypothesis on the disturbance replaced by `‖d(t)‖₂ ≤ d̄` and `0 ≤ d̄ ≤ (9/100) ω² δ`
(N·m, through `CellArmFollowsAt`): the inertia bound `(9/100) ‖w‖₂² ≤ wᵀ M(θ) w` holds on every
configuration within `1/10` rad of the reference, which stays in a cell (`cell_reach`), so no
range hypothesis on the motion remains. A design statement, not from MLS. -/
theorem cell_assured_torque {h T δa va ω δ dbar : ℝ} (hh : 0 < h) (hT : 0 < T)
    (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 < ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va) (hδ : δ ≤ 1 / 20)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 9 / 100 * ω ^ 2 * δ)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      CellArmFollowsAt ω T dbar x v acc d (DegPoint.toRad (c (k + 1)).src)
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
    (cellArm_moveCorollary (cellParams h T δa va) hT hω (by linarith) hdbar₀ hdbar
      (cell_reach h T δa va) hcont) h0) hδ

/-- `⌈T/h⌉ = 20` for `T = 2` s and `h = 1/10` s. A design statement, not from MLS. -/
theorem design_steps : ⌈(2 : ℝ) / (1 / 10)⌉₊ = 20 := by norm_num

/-- **The assured cell at the design values, acceleration-level disturbance bound.** With
`h = 1/10` s, `T = 2` s, `ω = 80` rad/s, `δ = δ_a = 1/20` rad and `v_a = 8` rad/s, and
`|(M(x)⁻¹ d)ᵢ| ≤ 320` rad/s² for every joint: the links keep `9/100` m from every obstacle at
every `t ≥ 0`, the supervisor never faults and its age stays below 25, a move admitted at
boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish the tool is within
`73/1000` m of the goal's tool position. The hypotheses that remain are those of
`cell_assured_accel`: about the harness, that at each boundary the actions sent are queue actions
followed by the policy's action on the exact sample, each accepted by the supervisor (`hrun`), and
that the arm starts in the tube around home at rest (`h0`); about the harness and the plant, that
on each period the arm obeys its equations of motion with the computed torque tracking the quintic
reference of the last admitted move and the disturbance bound above (`htrack`); about the plant,
that `(x, v)` is continuous on `[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_accel_design {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 (1 / 20) 8) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 (1 / 20) x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (1 / 20) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        73 / 1000) := by
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_accel (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) le_rfl (by norm_num) le_rfl hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h2 h3
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    linarith

/-- **The assured cell at the design values, torque-norm disturbance bound.** As
`cell_assured_accel_design` with `‖d(t)‖₂ ≤ d̄` and `0 ≤ d̄ ≤ 144/5` N·m (`(9/100) ω² δ` at
`ω = 80`, `δ = 1/20`). A design statement, not from MLS. -/
theorem cell_assured_torque_design {dbar : ℝ} (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 144 / 5)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 (1 / 20) 8) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAt 80 2 dbar x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (1 / 20) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        73 / 1000) := by
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_torque (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) le_rfl (by norm_num) le_rfl hdbar₀ (by linarith) hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h2 h3
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    linarith

end RoboLean.Cell.Loop
