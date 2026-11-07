import RoboLean.Cell.AssuredNominal
import RoboLean.Cell.AssuredProgram
import RoboLean.Cell.AssuredProgramInstance

/-!
# The assured cell with the program's run as its hypothesis, with the nominal model

The assured cell theorem on measured samples with the rotor inertia and the nominal payload in the
controller's model (`RoboLean.Cell.AssuredNominal`), with the hypothesis on the run replaced by:
the supervisor's states and actions are the policy program's own output (`Policy.IsProgramRun`)
on a stream of requests and samples, at a configuration whose arrival tolerances leave room for a
position sample error of `1/50` rad.

* `Policy.designNominal`: the program's configuration (the cell's supervisor parameters,
  `h = 1/10` s, `T = 2` s, position tolerance `3` degrees, speed tolerance `5` rad/s, encoders of
  `2^18` counts per revolution).
* `Loop.cell_assured_program_nominal_design`: the conclusions of the design-point theorem for
  every run of the program whose samples are within `1/50` rad and `1/5` rad/s of the true state.
* `Loop.cell_assured_program_nominal_design_exact`: the same for samples equal to the true state.
* `Loop.program_hold_nominal_assured`: the idle program on encoder samples of the arm at rest at
  home with a mass error of `1` kg held by friction meets every hypothesis.

The supervisor's contract `Supervisor.Contract Instances.params` stays a premise. The controller's
model carries the rotor inertia `J` (kg m²) on every joint and the nominal part mass `mn` (kg) at
the tool point; the plant has the rotor inertia `J' ≥ 3/2` kg m² on every joint and the actual
mass `m` (kg); the unknown is the mass error, the rotor-inertia error and the friction; the
elasticity of the drives is not in the theorem's plant. Computed torque of MLS eq. (4.49), p. 191,
for the robot of p. 303; the plant's equations, MLS eq. (4.47), p. 190, with friction as a joint
force, p. 170. The configuration, the loop and the bounds are design statements, not from MLS.
Seconds, radians, radians per second, kg, kg m², N m. The statements concern the ideal rigid-body
model and the sampled loop with a bounded sample error, not a physical arm, and the compiled
program only through the Lean definitions it is built from.
-/

namespace RoboLean.Cell.Policy

/-- The policy program's configuration with the arrival tolerances of the nominal-model design
point: the cell's supervisor parameters `Instances.params` (three cells, home `(0, -40, 30)`
degrees, age bound 25), the period `1/10` s, the move duration `2` s, the position tolerance `3`
degrees (`π/60 ≈ 0.0524` rad, room for the tube radius `3/100` rad and a position sample error of
`1/50` rad), the speed tolerance `5` rad/s and encoders of `2^18` counts per revolution. A design
definition, not from MLS. -/
def designNominal : Config where
  sup := Supervisor.Instances.params
  period := 1 / 10
  duration := 2
  posTol := 3
  velTol := 5
  countsPerRev := 2 ^ 18

end RoboLean.Cell.Policy

noncomputable section

namespace RoboLean.Cell.Loop

open Set Supervisor

/-- The loop data of the nominal-model configuration: `h = 1/10` s, `T = 2` s, position tolerance
`degToRad 3` rad, speed tolerance `5` rad/s. A design statement, not from MLS. -/
theorem designNominal_loop :
    Policy.designNominal.loop = openCellParams (1 / 10) 2 (degToRad 3) 5 := by
  show openCellParams (((1 / 10 : ℚ)) : ℝ) ((2 : ℚ) : ℝ) (degToRad 3) ((5 : ℚ) : ℝ) = _
  norm_num

/-- **The assured cell with every decision taken by the program, on measured samples, with the
rotor inertia and the nominal payload in the controller's model (a design statement, not from
MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations,
MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).** For every run of the policy
program at the configuration `Policy.designNominal` (`hprog`: the states `st` and actions `acts`
are the program's own output on the requests `reqs` and the samples `smp`), and every supervisor
whose runs meet the contract (`hsup`): let the controller's model carry the rotor inertia `J`
(kg m²) on every joint and the nominal mass `mn ≥ 0` (kg) at the tool point, and the plant the
rotor inertia `J' ≥ 3/2` kg m² on every joint and the actual mass `m ≥ 0` (kg), with
`|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m, N m s) and
`dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`; the unknown is the mass error, the rotor-inertia
error and the friction, and the elasticity of the drives is not in the theorem's plant. If at
every boundary `k/10` s each joint angle of the sample, read in radians, is within `1/50` rad of
the true joint angle and each joint speed estimate is within `1/5` rad/s of the true joint speed
(`hsamp`), and under `htrack` (on each period the plant obeys its equations of motion under a
friction torque `f` with the computed torque of the controller's model tracking the quintic
reference of the program's last admitted move at the gain `80` rad/s, with right derivatives,
`CellArmFollowsNominalRightAt`), `hcont` and `h0`: the links keep `9/100` m from every obstacle at
every `t ≥ 0`; the supervisor never faults and its age stays below 25; a move admitted at boundary
`k₀` is finished at boundary `k₀ + 20` with the arm at its goal; and at each finish the tool is
within `219/5000` m of the goal's tool position. Proved from
`cell_assured_measured_design_nominal_right`. -/
theorem cell_assured_program_nominal_design (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action} (hprog : Policy.IsProgramRun Policy.designNominal reqs smp st acts)
    {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn) (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J')
    (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5)
    {x v acc f : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(smp k).toRad Policy.designNominal i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 1 / 5)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 80 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad (st (k + 1)).src) (DegPoint.toRad (st (k + 1)).goal)
        ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  have hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad 3) 5) Instances.params
      (fun k => (smp k).toRad Policy.designNominal) (fun k => (smp k).velRad)
      (fun k => (st k).toCell) acts := by
    have h := hprog.isMeasuredCellRun
    rw [designNominal_loop] at h
    exact h
  exact cell_assured_measured_design_nominal_right hmn hm hJ' hdm hdJ hfc hfv hcond hsup hrun hsamp
    htrack hcont h0

/-- **The assured cell with every decision taken by the program, on exact samples, with the rotor
inertia and the nominal payload in the controller's model.** As
`cell_assured_program_nominal_design`, with the samples read in radians and rad/s equal to the true
state at every boundary `k/10` s (`hexact`) in place of `hsamp` (an exact sample is within every
nonnegative error). A design statement, not from MLS (computed torque of MLS eq. (4.49), p. 191;
the plant's equations, MLS eq. (4.47), p. 190). -/
theorem cell_assured_program_nominal_design_exact (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action} (hprog : Policy.IsProgramRun Policy.designNominal reqs smp st acts)
    {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn) (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J')
    (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5)
    {x v acc f : ℝ → Fin 3 → ℝ}
    (hexact : ∀ k : ℕ, x (k * (1 / 10)) = (smp k).toRad Policy.designNominal ∧
      v (k * (1 / 10)) = (smp k).velRad)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 80 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad (st (k + 1)).src) (DegPoint.toRad (st (k + 1)).goal)
        ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
      (st (k₀ + 20 + 1)).sup.busy = false ∧ (st (k₀ + 20 + 1)).sup.current = (st (k₀ + 1)).goal) ∧
    (∀ k, (st k).sup.busy = true → (st (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (st k).goal)) ≤
        219 / 5000) := by
  refine cell_assured_program_nominal_design hsup hprog hmn hm hJ' hdm hdJ hfc hfv hcond
    (fun k i => ?_) htrack hcont h0
  rw [(hexact k).1, (hexact k).2, sub_self, sub_self, abs_zero]
  exact ⟨by norm_num, by norm_num⟩

/-- The states of the idle program at the nominal-model configuration: the program's initial state
at every boundary. A design definition, not from MLS. -/
def idleProgramNominal : ℕ → Policy.State := fun _ => Policy.State.init Policy.designNominal

/-- **With no request the program stays idle.** On every stream of samples and no request, the
program at the configuration `Policy.designNominal` sends nothing and keeps its initial state at
every boundary. A design statement, not from MLS. -/
theorem idleProgramNominal_isProgramRun (smp : ℕ → Policy.Sample) :
    Policy.IsProgramRun Policy.designNominal (fun _ => []) smp idleProgramNominal (fun _ => []) :=
  ⟨rfl, fun _ => rfl⟩

/-- **The program on encoder samples of the held run meets every hypothesis.** For a supervisor
whose runs meet the contract (`hsup`), the idle program at the configuration
`Policy.designNominal`, run on the encoder samples (`2^18` counts per revolution, speeds floored to
a multiple of `1/5` rad/s, within `1/2000` rad and `1/5` rad/s of the true state) of the arm at
rest at home, with the controller's model carrying the rotor inertia `17/10` kg m² on every joint
and the nominal mass `1` kg, and the plant the rotor inertia `17/10` kg m² and the actual mass
`2` kg (a mass error of `1` kg) held by the friction torque `(1 − 2) · toolGravity(home)` (at most
`9` N m in every joint; `f_c = 9` N m, `f_v = 0`), meets every hypothesis of
`cell_assured_program_nominal_design`; hence both links keep `9/100` m from every obstacle at every
`t ≥ 0` (s), the supervisor never faults and its age stays below 25, and the statements about
admissions and finishes hold (vacuously here, since nothing is admitted). A design statement, not
from MLS. -/
theorem program_hold_nominal_assured (hsup : Supervisor.Contract Instances.params) :
    (∀ t : ℝ, 0 ≤ t → sceneClear (DegPoint.toRad Instances.params.home)) ∧
    (∀ k, (idleProgramNominal k).sup.faulted = false ∧ (idleProgramNominal k).sup.age < 25) ∧
    (∀ k₀, (idleProgramNominal k₀).sup.busy = false →
      (idleProgramNominal (k₀ + 1)).sup.busy = true →
      (idleProgramNominal (k₀ + 20 + 1)).sup.busy = false ∧
        (idleProgramNominal (k₀ + 20 + 1)).sup.current = (idleProgramNominal (k₀ + 1)).goal) ∧
    (∀ k, (idleProgramNominal k).sup.busy = true →
      (idleProgramNominal (k + 1)).sup.busy = false →
      dist (sceneTool (DegPoint.toRad Instances.params.home))
        (sceneTool (DegPoint.toRad (idleProgramNominal k).goal)) ≤ 219 / 5000) := by
  set θ := DegPoint.toRad Instances.params.home with hθ
  have hg : ∀ i, |((1 - 2 : ℝ) • toolGravity θ) i| ≤ 9 := by
    have hR : |17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)| ≤ 817 / 1000 := by
      have := Real.neg_one_le_cos (θ 1)
      have := Real.cos_le_one (θ 1)
      have := Real.neg_one_le_cos (θ 1 + θ 2)
      have := Real.cos_le_one (θ 1 + θ 2)
      rw [abs_le]; constructor <;> linarith
    have hc := Real.abs_cos_le_one (θ 1 + θ 2)
    intro i
    fin_cases i <;> simp only [toolGravity, Pi.smul_apply, smul_eq_mul] <;> norm_num
    · linarith
    · linarith
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 80 2 (17 / 10) 1 (17 / 10) 2 9 0 (fun _ => θ) 0 0
        (fun _ => (1 - 2 : ℝ) • toolGravity θ)
        (DegPoint.toRad (idleProgramNominal (k + 1)).src)
        (DegPoint.toRad (idleProgramNominal (k + 1)).goal)
        ((idleProgramNominal (k + 1)).start * (1 / 10)) t := by
    intro k t _
    simp only [idleProgramNominal, Policy.State.init, Policy.designNominal]
    refine ⟨hasDerivWithinAt_const _ _ _, hasDerivWithinAt_const _ _ _, fun i => ?_, ?_⟩
    · simpa using hg i
    · simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong]
      rw [moveRef_self, moveRefDeriv_self, moveRefDeriv2_self, ← hθ]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, zero_add, sub_self]
      rw [show (cellLoadedRobot (17 / 10) 2).N θ 0 = cellArm.N θ 0 + (2 : ℝ) • toolGravity θ from
          cellPayloadArm_N (by norm_num) θ 0,
        show (cellLoadedRobot (17 / 10) 1).N θ 0 = cellArm.N θ 0 + (1 : ℝ) • toolGravity θ from
          cellPayloadArm_N (by norm_num) θ 0]
      module
  have hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(encoderSample (fun _ => θ) 0 k).toRad Policy.designNominal i -
          (fun _ => θ) (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(encoderSample (fun _ => θ) 0 k).velRad i - (0 : ℝ → Fin 3 → ℝ) (k * (1 / 10)) i| ≤
          1 / 5 := by
    intro k i
    obtain ⟨h1, h2⟩ := encoderSample_within (fun _ => θ) 0 k i
    exact ⟨h1.trans (by norm_num), h2⟩
  have h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0
      ((fun _ => θ) 0) ((0 : ℝ → Fin 3 → ℝ) 0) := by
    intro i
    simp only [hθ, sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
    exact ⟨by norm_num, by norm_num⟩
  exact cell_assured_program_nominal_design (J := 17 / 10) (mn := 1) (J' := 17 / 10) (m := 2)
    (dm := 1) (dJ := 0) (fc := 9) (fv := 0) hsup
    (idleProgramNominal_isProgramRun (encoderSample (fun _ => θ) 0)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) hsamp htrack
    (by simpa using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (θ, (0 : Fin 3 → ℝ))) (Ici 0))) h0

end RoboLean.Cell.Loop
