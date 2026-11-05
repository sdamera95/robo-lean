import RoboLean.Cell.AssuredInstanceMotion

/-!
# The assured cell at the gain 80 for every tube radius

Corollaries of `cell_assured_accel` and `cell_assured_torque` at the period `h = 1/10` s, the move
duration `T = 2` s and the gain `ω = 80` rad/s, for every tube radius `δ ≤ 1/20` rad with arrival
tolerances `δ_a ≥ δ` and `v_a ≥ 160 δ` (`cell_assured_accel_gain80`, `cell_assured_torque_gain80`),
and their instances at the tube radius `δ = 3/100` rad (`cell_assured_accel_design_tight`,
`cell_assured_torque_design_tight`): a disturbance budget of `192` rad/s² per joint at the
acceleration level, or `432/25` N·m in Euclidean norm, a finish at boundary `k₀ + 20` and the tool
within `219/5000` m of the goal's tool position at each finish. The demonstration run of
`RoboLean.Cell.AssuredInstanceMotion` meets every hypothesis at every `0 ≤ δ ≤ 1/20`
(`demo_assured_gain80`, `demo_assured_torque_gain80`) and in particular at `δ = 3/100`
(`demo_assured_tight`, `demo_assured_torque_tight`).

A design statement, not from MLS. The statements concern the ideal rigid-body model with a bounded
disturbance and the ideal sampled loop; they do not assert that a closed-loop solution exists, and
say nothing about sensing, delay, actuator limits or a physical arm.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- **The assured cell at the gain 80, for every tube radius, acceleration-level disturbance
bound.** With `h = 1/10` s, `T = 2` s, `ω = 80` rad/s, a tube radius `δ ≤ 1/20` rad and arrival
tolerances `δ_a ≥ δ` rad and `v_a ≥ 160 δ` rad/s, and `|(M(x)⁻¹ d)ᵢ| ≤ 6400 δ` rad/s² for every
joint (the predicate `CellArmFollowsAccelAt 80 2 δ`): the links keep `9/100` m from every obstacle
at every `t ≥ 0`, the supervisor never faults and its age stays below 25, a move admitted at
boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish the tool is within `(73/50) δ` m
of the goal's tool position. The hypotheses that remain are those of `cell_assured_accel`: about the
harness, that at each boundary the actions sent are queue actions followed by the policy's action
on the exact sample, each accepted by the supervisor (`hrun`), and that the arm starts in the tube
around home at rest (`h0`); about the harness and the plant, that on each period the arm obeys its
equations of motion with the computed torque tracking the quintic reference of the last admitted
move and the disturbance bound above (`htrack`); about the plant, that `(x, v)` is continuous on
`[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_accel_gain80 {δ δa va : ℝ} (hδ : δ ≤ 1 / 20) (hδa : δ ≤ δa)
    (hva : 160 * δ ≤ va) {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 δ x v acc d (DegPoint.toRad (c (k + 1)).src)
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
    cell_assured_accel (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) hδa (by linarith) hδ hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => (htool k hbusy hidle).2.2.2⟩
  obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
  rw [design_steps] at h2 h3
  exact ⟨h2, h3⟩

/-- **The assured cell at the gain 80, for every tube radius, torque-norm disturbance bound.** As
`cell_assured_accel_gain80`, with the per-period disturbance hypothesis `‖d(t)‖₂ ≤ d̄`,
`0 ≤ d̄ ≤ 576 δ` N·m (`(9/100) · 80² · δ`, through `CellArmFollowsAt 80 2 d̄`) and `δ ≤ 1/20` rad,
the inertia bound coming from the joint envelope (`cell_reach`). A design statement, not from
MLS. -/
theorem cell_assured_torque_gain80 {δ δa va dbar : ℝ} (hδ : δ ≤ 1 / 20) (hδa : δ ≤ δa)
    (hva : 160 * δ ≤ va) (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 576 * δ)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAt 80 2 dbar x v acc d (DegPoint.toRad (c (k + 1)).src)
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
    cell_assured_torque (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) hδa (by linarith) hδ hdbar₀ (by linarith) hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => (htool k hbusy hidle).2.2.2⟩
  obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
  rw [design_steps] at h2 h3
  exact ⟨h2, h3⟩

/-- **The assured cell at the tube radius `3/100` rad, acceleration-level disturbance bound.** With
`h = 1/10` s, `T = 2` s, `ω = 80` rad/s, `δ = δ_a = 3/100` rad and `v_a = 24/5` rad/s, and
`|(M(x)⁻¹ d)ᵢ| ≤ 192` rad/s² for every joint: the links keep `9/100` m from every obstacle at every
`t ≥ 0`, the supervisor never faults and its age stays below 25, a move admitted at boundary `k₀`
is finished at boundary `k₀ + 20`, and at each finish the tool is within `219/5000` m of the goal's
tool position. The hypotheses that remain are those of `cell_assured_accel`: about the harness,
that at each boundary the actions sent are queue actions followed by the policy's action on the
exact sample, each accepted by the supervisor (`hrun`), and that the arm starts in the tube around
home at rest (`h0`); about the harness and the plant, that on each period the arm obeys its
equations of motion with the computed torque tracking the quintic reference of the last admitted
move and the disturbance bound above (`htrack`); about the plant, that `(x, v)` is continuous on
`[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_accel_design_tight {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 (3 / 100) x v acc d (DegPoint.toRad (c (k + 1)).src)
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
    cell_assured_accel_gain80 (by norm_num) le_rfl (by norm_num) hrun htrack hcont h0
  exact ⟨h1, h2, h3, fun k hbusy hidle => (h4 k hbusy hidle).trans_eq (by norm_num)⟩

/-- **The assured cell at the tube radius `3/100` rad, torque-norm disturbance bound.** As
`cell_assured_accel_design_tight` with `‖d(t)‖₂ ≤ d̄` and `0 ≤ d̄ ≤ 432/25` N·m
(`(9/100) · 80² · 3/100`). A design statement, not from MLS. -/
theorem cell_assured_torque_design_tight {dbar : ℝ} (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 432 / 25)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (cellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAt 80 2 dbar x v acc d (DegPoint.toRad (c (k + 1)).src)
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
  obtain ⟨h1, h2, h3, h4⟩ := cell_assured_torque_gain80 (by norm_num) le_rfl (by norm_num)
    hdbar₀ (by linarith) hrun htrack hcont h0
  exact ⟨h1, h2, h3, fun k hbusy hidle => (h4 k hbusy hidle).trans_eq (by norm_num)⟩

/-- The demonstration run is a timed run of the cell loop for every nonnegative pair of arrival
tolerances (rad, rad/s): the arm is exactly at the goal at rest when the move is due. A design
statement, not from MLS. -/
theorem demo_isCellRun_of {δa va : ℝ} (hδa : 0 ≤ δa) (hva : 0 ≤ va) :
    IsCellRun (cellParams (1 / 10) 2 δa va) Instances.params demoMotion demoVel demoState
      demoActs := by
  refine ⟨rfl, fun k => ?_⟩
  rcases Nat.lt_or_ge k 21 with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine ⟨[.request Instances.liftPick], [.admit Instances.liftPick],
        { Supervisor.State.init Instances.params.home with requested := [Instances.liftPick] },
        rfl, by simp [IsQueueAction], by decide +kernel, ?_⟩
      have : demoState (0 + 1) = ⟨demoBusy 0,
          ({ CellState.init Instances.params.home with
            sup := { Supervisor.State.init Instances.params.home with
              requested := [Instances.liftPick] } } : CellState).sup.current,
          Instances.liftPick, 0⟩ := rfl
      rw [this]
      exact PolicyStep.admit _ _ _ rfl (by decide +kernel)
    · rcases Nat.lt_or_ge k 20 with hk20 | hk20
      · have hc : demoState k =
            ⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ := by
          simp [demoState, hpos.ne', show k ≤ 20 by omega]
        have hc' : demoState (k + 1) =
            ⟨demoBusy k, Instances.params.home, Instances.liftPick, 0⟩ := by
          simp [demoState, show k + 1 ≤ 20 by omega]
        have ha : demoActs k = [.tick] := by simp [demoActs, hpos.ne', hk20]
        rw [hc, hc', ha]
        refine ⟨[], [.tick], demoBusy (k - 1), rfl, by simp, rfl, ?_⟩
        have e : (⟨demoBusy k, Instances.params.home, Instances.liftPick, 0⟩ : CellState) =
            { (⟨demoBusy (k - 1), Instances.params.home, Instances.liftPick, 0⟩ : CellState) with
              sup := { demoBusy (k - 1) with age := k - 1 + 1 } } := by
          simp [demoBusy, show k - 1 + 1 = k by omega]
        simp only at e ⊢
        rw [e]
        refine PolicyStep.tick _ _ rfl ?_ ?_ ?_
        · rintro ⟨hdue, -⟩
          simp only [Due, CellState.toLoop, cellParams] at hdue
          have : (k : ℝ) ≤ 19 := by exact_mod_cast (show k ≤ 19 by omega)
          push_cast at hdue
          linarith
        · simp [demoBusy, Instances.params]; omega
        · have hlt : k - 1 < 25 := by omega
          simp only [step, Action.blocker, demoBusy, Instances.params, Bool.true_eq_false,
            ↓reduceIte, hlt]
          rfl
      · have hk' : k = 20 := by omega
        subst hk'
        have hc : demoState 20 = ⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ := rfl
        rw [hc]
        refine ⟨[], [.finish], demoBusy 19, rfl, by simp, rfl, ?_⟩
        have e : demoState (20 + 1) =
            { (⟨demoBusy 19, Instances.params.home, Instances.liftPick, 0⟩ : CellState) with
              sup := demoDone } := rfl
        rw [e]
        refine PolicyStep.finish _ _ rfl ?_ ?_ (by decide +kernel)
        · simp only [Due, CellState.toLoop, cellParams]; norm_num
        · intro i
          have h2 : (0 : ℝ) + 2 ≤ ((20 : ℕ) : ℝ) * (1 / 10) := by norm_num
          simp only [cellParams, demoMotion, demoVel, moveRef_of_ge (by norm_num : (0 : ℝ) < 2) h2,
            moveRefDeriv_of_ge (by norm_num : (0 : ℝ) < 2) h2]
          simp [hδa, hva]
  · have hc : demoState k = ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩ := by
      simp [demoState, show k ≠ 0 by omega, show ¬ k ≤ 20 by omega]
    have hc' : demoState (k + 1) = ⟨demoDone, Instances.params.home, Instances.liftPick, 0⟩ := by
      simp [demoState, show ¬ k + 1 ≤ 20 by omega]
    have ha : demoActs k = [] := by
      simp [demoActs, show k ≠ 0 by omega, show ¬ k < 20 by omega, show k ≠ 20 by omega]
    rw [hc, hc', ha]
    exact ⟨[], [], demoDone, rfl, by simp, rfl, PolicyStep.wait _ rfl⟩

/-- The demonstration motion obeys the arm's equations of motion under computed torque tracking
its own reference with zero disturbance, at every time, within the acceleration-level budget
`80² δ` for every `δ ≥ 0`. A design statement, not from MLS. -/
theorem demoMotion_follows_of {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    CellArmFollowsAccelAt 80 2 δ demoMotion demoVel demoAcc 0
      (DegPoint.toRad Instances.params.home) (DegPoint.toRad Instances.liftPick) 0 t := by
  refine ⟨hasDerivAt_moveRef _ _ _ _ t, hasDerivAt_moveRefDeriv _ _ _ _ t, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec_zero, Pi.zero_apply, abs_zero]
    positivity
  · simp [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, demoMotion, demoVel,
      demoAcc]

/-- The demonstration motion starts in the tube of every radius `δ ≥ 0` around home at rest. A
design statement, not from MLS. -/
theorem demo_inTube_zero {δ : ℝ} (hδ : 0 ≤ δ) :
    InTube δ 80 (DegPoint.toRad Instances.params.home) 0 (demoMotion 0) (demoVel 0) := by
  intro i
  simp only [demoMotion, demoVel, moveRef_of_le (by norm_num : (0 : ℝ) < 2) le_rfl,
    moveRefDeriv_of_le (by norm_num : (0 : ℝ) < 2) le_rfl]
  simp only [sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
  exact ⟨hδ, by positivity⟩

/-- The demonstration motion is continuous with its velocity. A design statement, not from MLS. -/
theorem demo_continuousOn : ContinuousOn (fun s => (demoMotion s, demoVel s)) (Ici 0) :=
  (continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_moveRef _ _ _ _ t).continuousAt.prodMk
      (hasDerivAt_moveRefDeriv _ _ _ _ t).continuousAt).continuousOn

/-- **A moving arm at the gain 80, for every tube radius, acceleration-level form.** For every
`0 ≤ δ ≤ 1/20` rad and tolerances `δ_a ≥ δ`, `v_a ≥ 160 δ`, the demonstration run meets every
hypothesis of `cell_assured_accel_gain80`, so its conclusions hold for it. A design statement, not
from MLS. -/
theorem demo_assured_gain80 {δ δa va : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 20) (hδa : δ ≤ δa)
    (hva : 160 * δ ≤ va) :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 73 / 50 * δ) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 δ demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using demoMotion_follows_of hδ0 t
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_accel_gain80 hδ hδa hva
    (demo_isCellRun_of (hδ0.trans hδa) (by linarith)) htrack demo_continuousOn
    (demo_inTube_zero hδ0)
  exact ⟨hclear, hfault, htool⟩

/-- **A moving arm at the gain 80, for every tube radius, torque-norm form.** For every
`0 ≤ δ ≤ 1/20` rad and tolerances `δ_a ≥ δ`, `v_a ≥ 160 δ`, the demonstration run meets every
hypothesis of `cell_assured_torque_gain80` with `d̄ = 0`, so its conclusions hold for it. A design
statement, not from MLS. -/
theorem demo_assured_torque_gain80 {δ δa va : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 20)
    (hδa : δ ≤ δa) (hva : 160 * δ ≤ va) :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 73 / 50 * δ) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAt 80 2 0 demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using demoMotion_follows_torque t
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_torque_gain80 hδ hδa hva le_rfl
    (by linarith) (demo_isCellRun_of (hδ0.trans hδa) (by linarith)) htrack demo_continuousOn
    (demo_inTube_zero hδ0)
  exact ⟨hclear, hfault, htool⟩

/-- **A moving arm at the tube radius `3/100` rad, acceleration-level form.** The demonstration
run meets every hypothesis of `cell_assured_accel_design_tight` (with `δ = δ_a = 3/100` rad,
`v_a = 24/5` rad/s), so the links keep `9/100` m from every obstacle at every `t ≥ 0`, the
supervisor never faults, and at the finish the tool is within `219/5000` m of the goal's tool
position. A design statement, not from MLS. -/
theorem demo_assured_tight :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelAt 80 2 (3 / 100) demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using demoMotion_follows_of (by norm_num) t
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_accel_design_tight
    (demo_isCellRun_of (by norm_num) (by norm_num)) htrack demo_continuousOn
    (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

/-- **A moving arm at the tube radius `3/100` rad, torque-norm form.** The demonstration run meets
every hypothesis of `cell_assured_torque_design_tight` with `d̄ = 0`, so its conclusions hold for
it. A design statement, not from MLS. -/
theorem demo_assured_torque_tight :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAt 80 2 0 demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    simpa using demoMotion_follows_torque t
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_torque_design_tight le_rfl (by norm_num)
    (demo_isCellRun_of (by norm_num) (by norm_num)) htrack demo_continuousOn
    (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

end RoboLean.Cell.Loop
