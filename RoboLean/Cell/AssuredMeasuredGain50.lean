import RoboLean.Cell.AssuredNominalGain50

/-!
# The assured cell at the gain 50 with the program's run and a bounded disturbance

The measured-sample theorem `cell_assured_measured_right` at the gain-50 design point, with the
hypothesis on the run replaced by: the supervisor's states and actions are the policy program's own
output (`Policy.IsProgramRun`) at the configuration `Policy.designNominalGain50` (period `1/10` s,
move duration `2` s, arrival tolerances `3` degrees and `33/10` rad/s). The plant hypothesis is the
disturbance bound of `cell_assured_measured_right` at `ω = 50` rad/s and `δ = 3/100` rad,
`|(M(x)⁻¹ d)ᵢ| ≤ ω² δ = 75` rad/s², not the nominal-model plant of
`cell_assured_program_nominal_gain50`; the samples are within `1/50` rad and `3/10` rad/s of the
true state.

* `Loop.cell_assured_program_measured_gain50`: the conclusions of
  `cell_assured_program_nominal_gain50`, and the supervisor busy from the admission to the due
  boundary, under the disturbance bound.
* `Loop.cell_assured_program_measured_gain50_exact`: the same for samples equal to the true state.

The supervisor's contract `Supervisor.Contract Instances.params` stays a premise. The arm is
`cellArm` (MLS Example 4.3, printed p. 172) under computed torque (MLS eq. (4.49), p. 191), with
right derivatives only. The configuration, the loop and the bounds are design statements, not from
MLS. Seconds, radians, radians per second. The statements concern the ideal rigid-body model with a
bounded disturbance and the sampled loop with a bounded sample error, not a physical arm, and the
compiled program only through the Lean definitions it is built from.
-/

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- **The assured cell at the gain 50 with every decision taken by the program, on measured
samples, with a bounded disturbance (a design statement, not from MLS; the arm `cellArm` of MLS
Example 4.3, p. 172, under computed torque of MLS eq. (4.49), p. 191).** For every run of the
policy program at the configuration `Policy.designNominalGain50` (`hprog`: the states `st` and
actions `acts` are the program's own output on the requests `reqs` and the samples `smp`), and
every supervisor whose runs meet the contract (`hsup`): if at every boundary `k/10` s each joint
angle of the sample, read in radians, is within `1/50` rad of the true joint angle and each joint
speed estimate is within `3/10` rad/s of the true joint speed (`hsamp`), and under `htrack` (on each
period the arm obeys its equations of motion `M ẍ + C ẋ + N = F + d` with the computed torque `F`
at the gain `50` rad/s tracking the quintic reference of the program's last admitted move, with
right derivatives, and `|(M(x)⁻¹ d)ᵢ| ≤ 75` rad/s² for every joint), `hcont` (`(x, v)` continuous
on `[0, ∞)`) and `h0` (the arm starts in the tube of radius `3/100` rad around home at rest): the
links keep `9/100` m from every obstacle at every `t ≥ 0`; the supervisor never faults and its age
stays below 25; a move admitted at boundary `k₀` keeps the supervisor busy at the boundaries
`k₀ + 1, …, k₀ + 20` and is finished at boundary `k₀ + 20` with the arm at its goal; and at each
finish the tool is within `219/5000` m of the goal's tool position. Proved from
`cell_assured_measured_right` with `δ_a = 3` degrees, `v_a = 33/10` rad/s
(`2 · 50 · 3/100 + 3/10`), `εq = 1/50` rad and `εv = 3/10` rad/s. -/
theorem cell_assured_program_measured_gain50 (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action}
    (hprog : Policy.IsProgramRun Policy.designNominalGain50 reqs smp st acts)
    {x v acc d : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(smp k).toRad Policy.designNominalGain50 i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 3 / 10)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 50 2 (3 / 100) x v acc d (DegPoint.toRad (st (k + 1)).src)
        (DegPoint.toRad (st (k + 1)).goal) ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  have hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad 3) (33 / 10)) Instances.params
      (fun k => (smp k).toRad Policy.designNominalGain50) (fun k => (smp k).velRad)
      (fun k => (st k).toCell) acts := by
    have h := hprog.isMeasuredCellRun
    rw [designNominalGain50_loop] at h
    exact h
  have hδa : (3 : ℝ) / 100 + 1 / 50 ≤ degToRad 3 := by
    have := Real.pi_gt_three
    unfold degToRad
    push_cast
    linarith
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_measured_right (ω := 50) (δ := 3 / 100) (εq := 1 / 50) (εv := 3 / 10)
      (by norm_num) (by norm_num) (by rw [design_steps]; norm_num) (by norm_num) hδa
      (by norm_num) (by norm_num) hsup hrun hsamp htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, h1, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    exact le_of_le_of_eq h4 (by norm_num)

/-- **The assured cell at the gain 50 with every decision taken by the program, on exact samples,
with a bounded disturbance.** As `cell_assured_program_measured_gain50`, with the samples read in
radians and rad/s equal to the true state at every boundary `k/10` s (`hexact`) in place of `hsamp`
(an exact sample is within every nonnegative error). A design statement, not from MLS (computed
torque of MLS eq. (4.49), p. 191). -/
theorem cell_assured_program_measured_gain50_exact (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action}
    (hprog : Policy.IsProgramRun Policy.designNominalGain50 reqs smp st acts)
    {x v acc d : ℝ → Fin 3 → ℝ}
    (hexact : ∀ k : ℕ, x (k * (1 / 10)) = (smp k).toRad Policy.designNominalGain50 ∧
      v (k * (1 / 10)) = (smp k).velRad)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsAccelRightAt 50 2 (3 / 100) x v acc d (DegPoint.toRad (st (k + 1)).src)
        (DegPoint.toRad (st (k + 1)).goal) ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (∀ j, j < 20 → (st (k₀ + 1 + j)).sup.busy = true) ∧
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) :=
  cell_assured_program_measured_gain50 hsup hprog (fun k i => by
    rw [(hexact k).1, (hexact k).2, sub_self, sub_self, abs_zero]; norm_num) htrack hcont h0

end RoboLean.Cell.Loop
