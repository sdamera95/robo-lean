import RoboLean.Cell.KnownModelGain50
import RoboLean.Cell.AssuredProgramNominal

/-!
# The assured cell with the nominal model at the gain 50

A second design point of the assured cell with the rotor inertia and the nominal payload in the
controller's model (`RoboLean.Cell.AssuredNominal` is the first, at the gain `80` rad/s): the gain
`ω = 50` rad/s with the tube radius `δ = 3/100` rad, so the plant hypothesis bounds the acceleration
of the disturbance by `ω² δ = 75` rad/s². The controller's model carries the rotor inertia `J`
(kg m²) on every joint and the nominal part mass `mn` (kg) at the tool point
(`cellLoadedRobot J mn`); the plant has the rotor inertia `J' ≥ 3/2` kg m² on every joint and the
actual mass `m` (kg) (`cellLoadedRobot J' m`), under a joint friction torque `f` with
`|fᵢ(t)| ≤ f_c + f_v |ẋᵢ(t)|` (N m, N m s). The unknown is the mass error, the rotor-inertia error
and the friction; the elasticity of the drives is not in the theorem's plant. The disturbance's
bound is derived under `|m − mn| ≤ dm`, `|J' − J| ≤ dJ` and
`dm + (7/2) dJ + (f_c + 4 f_v)/60 ≤ 3/2` while the motion is in the tube of radius `301/10000`
rad, which a first-exit argument shows the motion never leaves.

**Formalized.**

* `CellArmFollowsNominalRightAt.accel_bound_gain50`: inside the tube of radius `301/10000` rad
  around a linked move at the gain `50` rad/s, the disturbance's acceleration is at most `75`
  rad/s² in every joint.
* `Loop.cellArm_moveCorollary_nominal_gain50`: the loop's move corollary at `(50, 3/100)`.
* `Loop.cell_assured_measured_design_nominal_gain50`: the assured cell on samples within `1/50` rad
  and `3/10` rad/s of the true state, with the arrival tolerances `3` degrees and `33/10` rad/s.
* `Policy.designNominalGain50`, `Loop.designNominalGain50_loop`: the program's configuration.
* `Loop.cell_assured_program_nominal_gain50`: the same with the program's run as hypothesis.
* `Loop.idleProgramNominalGain50`, `Loop.idleProgramNominalGain50_isProgramRun`,
  `Loop.program_hold_nominal_gain50_assured`: the idle program on encoder samples of the arm at
  rest at home with a mass error of `1` kg held by friction meets every hypothesis.

Computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations, MLS
eq. (4.47), p. 190, with friction as a joint force, p. 170. Lean joint `k` is the book's joint
`k + 1`; radians, seconds, kg, kg m², N m. The arm's numbers, the rotor model, the payload's
location, the friction model, the scene, the loop, the configuration and the bounds are design
statements, not from MLS. Nothing here concerns a physical arm, and the compiled program only
through the Lean definitions it is built from.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- The model's rotor inertia is nonnegative under the plant hypotheses at the gain 50: the
condition gives `dJ ≤ 3/7` kg m², so `J ≥ J' − dJ ≥ 3/2 − 3/7 > 0`. -/
private theorem rotor_nonneg_gain50 {J mn J' m dm dJ fc fv : ℝ} (hJ' : 3 / 2 ≤ J')
    (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 7 / 2 * dJ + (fc + 4 * fv) / 60 ≤ 3 / 2) : 0 ≤ J := by
  have h1 := abs_nonneg (m - mn)
  have h2 := (abs_le.mp hdJ).2
  linarith

/-- **The acceleration of the disturbance inside the tube at the gain 50 (a design statement, not
from MLS; `cellLoaded_accel_abs_le_gain50`).** At the gain `ω = 50` rad/s and duration `T = 2` s,
let the controller's model carry the rotor inertia `J` (kg m²) on every joint and the nominal mass
`mn ≥ 0` (kg) at the tool point, and the plant the rotor inertia `J' ≥ 3/2` kg m² on every joint
and the actual mass `m ≥ 0` (kg), with `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m,
N m s) and `dm + (7/2) dJ + (f_c + 4 f_v)/60 ≤ 3/2`. If the plant follows the move from `a` to `g`
(linked by the supervisor's link test) at `s` (computed torque of MLS eq. (4.49), p. 191; the
plant's equations, MLS eq. (4.47), p. 190), and its state at `s` is in the tube of radius
`301/10000` rad around the reference, then every `w` with `M̂(x(s)) w = d(s)`,
`d = nominalDisturbance J mn J' m x ẋ ẍ f`, satisfies `|wᵢ| ≤ 75` rad/s² for every joint. -/
theorem CellArmFollowsNominalRightAt.accel_bound_gain50 {J mn J' m dm dJ fc fv : ℝ}
    (hmn : 0 ≤ mn) (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ)
    (hfc : 0 ≤ fc) (hfv : 0 ≤ fv) (hcond : dm + 7 / 2 * dJ + (fc + 4 * fv) / 60 ≤ 3 / 2)
    {h T δa va : ℝ} {a g : Supervisor.Waypoint} (hag : (Loop.openCellParams h T δa va).linked a g)
    {x v acc f : ℝ → Fin 3 → ℝ} {t₀ s : ℝ}
    (hE : CellArmFollowsNominalRightAt 50 2 J mn J' m fc fv x v acc f (DegPoint.toRad a)
      (DegPoint.toRad g) t₀ s)
    (hin : Cell.InTube 50 (301 / 10000) (x s) (v s)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s))
    (w : Fin 3 → ℝ)
    (hMw : (cellLoadedRobot J mn).M (x s) *ᵥ w =
      nominalDisturbance J mn J' m (x s) (v s) (acc s) (f s))
    (i : Fin 3) : |w i| ≤ 75 := by
  obtain ⟨hreach, hu, hv⟩ := Loop.nominal_tube_bounds_gain50 hag hin
  set u : Fin 3 → ℝ := moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s -
    (2 * 50 : ℝ) • (v s - moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s) -
    ((50 : ℝ) ^ 2) • (x s - moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s) with hu_def
  -- the computed torque is `M̂ u + Ĉ v + N̂`
  have hF : (cellLoadedRobot J mn).computedTorque (((50 : ℝ) ^ 2) • 1) ((2 * 50 : ℝ) • 1)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
      (moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2) s (x s) (v s) =
      (cellLoadedRobot J mn).M (x s) *ᵥ u + (cellLoadedRobot J mn).C (x s) (v s) *ᵥ v s +
        (cellLoadedRobot J mn).N (x s) (v s) := by
    simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong,
      Matrix.smul_mulVec, Matrix.one_mulVec, hu_def]
  -- the actual acceleration is `u + w`
  have hM : ((cellLoadedRobot J mn).M (x s)).PosDef :=
    cellLoadedRobot_M_posDef (rotor_nonneg_gain50 hJ' hdm hdJ hfc hfv hcond) hmn (x s)
  have hacc : acc s = u + w := by
    have e := hE.equations
    rw [hF, ← hMw] at e
    have e' : (cellLoadedRobot J mn).M (x s) *ᵥ acc s =
        (cellLoadedRobot J mn).M (x s) *ᵥ (u + w) := by
      rw [Matrix.mulVec_add]
      linear_combination (exp := 1) e
    have := congrArg (fun y => ((cellLoadedRobot J mn).M (x s))⁻¹ *ᵥ y) e'
    rwa [Control.PosDef.inv_mulVec_mulVec hM, Control.PosDef.inv_mulVec_mulVec hM] at this
  rw [hacc] at hMw
  refine cellLoaded_accel_abs_le_gain50 hmn hm hJ' hdm hdJ hfc hfv hcond hreach (fun j => ?_) hv
    (fun j => hE.2.2.1 j) hMw i
  have := hu j
  simp only [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact this

end Cell

namespace Cell.Loop

open Set Supervisor

/-- **The loop's move corollary at the gain 50 for the plant under computed torque with the
controller's model, with joint friction and right derivatives (a design statement, not from MLS;
computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303).** At the gain `ω = 50` rad/s,
tube radius `δ = 3/100` rad and move duration `T = 2` s, for the loop data
`openCellParams h 2 δa va`, the controller's model with the rotor inertia `J` (kg m²) and the
nominal mass `mn ≥ 0` (kg), the plant with the rotor inertia `J' ≥ 3/2` kg m² and the actual mass
`m ≥ 0` (kg), `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m, N m s) with
`dm + (7/2) dJ + (f_c + 4 f_v)/60 ≤ 3/2`, and `(x, v)` continuous on `[0, ∞)`, the arm's motion
satisfies `Loop.MoveCorollary` for the quintic reference and the tracking predicate
`CellArmFollowsNominalRightAt` at the gain 50. The disturbance's bound is required only while the
motion is in the tube of radius `301/10000` rad, which it never leaves (first exit). -/
theorem cellArm_moveCorollary_nominal_gain50 {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn)
    (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : dm + 7 / 2 * dJ + (fc + 4 * fv) / 60 ≤ 3 / 2) (h δa va : ℝ)
    {x v acc f : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    MoveCorollary (openCellParams h 2 δa va) (quinticMoveRef (n := 3) (by norm_num : (0 : ℝ) < 2))
      (3 / 100) 50
      (fun a g t₀ t => CellArmFollowsNominalRightAt 50 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad a) (DegPoint.toRad g) t₀ t) x v := by
  intro a g hag t₀ t₁ ht₀ _ hf hin t ht
  have hin' : Cell.InTube 50 (3 / 100) (x t₀) (v t₀)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 t₀)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 t₀) := by
    rw [moveRef_of_le (by norm_num) le_rfl, moveRefDeriv_of_le (by norm_num) le_rfl]
    exact hin
  have htube := tube_invariant_on_accel_right_of_inTube (η := 301 / 10000)
    (by norm_num : (0 : ℝ) < 50) (by norm_num : (3 : ℝ) / 100 < 301 / 10000)
    (hasDerivAt_moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
    (hasDerivAt_moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
    (Mt := fun s => (cellLoadedRobot J mn).M (x s))
    (Ct := fun s => (cellLoadedRobot J mn).C (x s) (v s))
    (Nt := fun s => (cellLoadedRobot J mn).N (x s) (v s))
    (d := fun s => nominalDisturbance J mn J' m (x s) (v s) (acc s) (f s))
    (hc.mono fun s hs => ht₀.trans hs.1) (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1)
    (fun s hs hnear w hMw i => ?_) (fun s hs => (hf s hs).equations) hin'
  · exact (htube t ht).1
  · have := CellArmFollowsNominalRightAt.accel_bound_gain50 hmn hm hJ' hdm hdJ hfc hfv hcond hag
      (hf s hs) hnear w hMw i
    norm_num
    linarith

/-- The position tolerance `3` degrees, in radians, leaves room for the tube radius `3/100` rad and
the position sample error `1/50` rad: `3/100 + 1/50 ≤ 3π/180`, from `π > 3`. -/
private theorem nominal_radius_add_le_posTol_gain50 : (3 : ℝ) / 100 + 1 / 50 ≤ degToRad 3 := by
  have := Real.pi_gt_three
  unfold degToRad
  push_cast
  linarith

/-- **The assured cell on measured samples at the gain 50 with the rotor inertia and the nominal
payload in the controller's model (a design statement, not from MLS; computed torque of MLS
eq. (4.49), p. 191, for the robot of p. 303; the plant's equations, MLS eq. (4.47), p. 190, with
friction as a joint force, p. 170).** With `h = 1/10` s, `T = 2` s, `ω = 50` rad/s, `δ = 3/100`
rad, the position tolerance `δ_a = 3` degrees (`π/60` rad), the speed tolerance `v_a = 33/10`
rad/s (`2 · 50 · 3/100 + 3/10`), and samples within `εq = 1/50` rad and `εv = 3/10` rad/s of the
true state, let the controller's model carry the rotor inertia `J` (kg m²) on every joint and the
nominal mass `mn ≥ 0` (kg) at the tool point, and the plant the rotor inertia `J' ≥ 3/2` kg m² on
every joint and the actual mass `m ≥ 0` (kg), with `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`,
`f_c, f_v ≥ 0` (N m, N m s) and `dm + (7/2) dJ + (f_c + 4 f_v)/60 ≤ 3/2`. The unknown is the mass
error, the rotor-inertia error and the friction; the elasticity of the drives is not in the
theorem's plant. For every run of the supervisor that meets the contract
`Supervisor.Contract Instances.params` (`hsup`), every timed run `c` of the cell loop on measured
samples `(xm, vm)` (`hrun`: at each boundary the actions sent are queue actions followed by the
policy's action on the measured sample, each accepted by the supervisor), every motion
`(x, v, acc)` of the plant under a friction torque `f` with the sample error bound (`hsamp`), the
tracking hypothesis `CellArmFollowsNominalRightAt` at the gain 50 on each period (`htrack`),
`(x, v)` continuous on `[0, ∞)` (`hcont`) and the arm starting in the tube around home at rest
(`h0`): the links keep `9/100` m from every obstacle at every `t ≥ 0`, the supervisor never faults
and its age stays below 25, a move admitted at boundary `k₀` is finished at boundary `k₀ + 20` at
its goal, and at each finish the tool at the true configuration is within `219/5000` m of the
goal's tool position. -/
theorem cell_assured_measured_design_nominal_gain50 {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn)
    (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : dm + 7 / 2 * dJ + (fc + 4 * fv) / 60 ≤ 3 / 2)
    (hsup : Supervisor.Contract Instances.params)
    {x v acc f : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad 3) (33 / 10)) Instances.params
      xm vm c acts)
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |xm k i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
      |vm k i - v (k * (1 / 10)) i| ≤ 3 / 10)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 50 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad (c (k + 1)).src) (DegPoint.toRad (c (k + 1)).goal)
        ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        219 / 5000) := by
  have H := cell_measured_hyps (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 2)
    (by rw [design_steps]; norm_num) (by norm_num : (0 : ℝ) ≤ 50)
    nominal_radius_add_le_posTol_gain50 (by norm_num) hrun hsamp htrack
    (cellArm_moveCorollary_nominal_gain50 hmn hm hJ' hdm hdJ hfc hfv hcond (1 / 10) (degToRad 3)
      (33 / 10) hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, -⟩ :=
    H.assured hc (openCellParams_certify (1 / 10) 2 (degToRad 3) (33 / 10))
      (by norm_num [cellInflation]) sceneTool_lipschitz
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, h2, h3⟩ := hfin k₀ hidle hbusy
    have h2' : (c (k₀ + ⌈(2 : ℝ) / (1 / 10)⌉₊ + 1)).sup.busy = false := h2
    have h3' : (c (k₀ + ⌈(2 : ℝ) / (1 / 10)⌉₊ + 1)).sup.current = (c (k₀ + 1)).goal := h3
    rw [design_steps] at h2' h3'
    exact ⟨h2', h3'⟩
  · have h4 : dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        73 / 50 * (3 / 100) := htool k hbusy hidle
    linarith

end Cell.Loop

namespace Cell.Policy

/-- The policy program's configuration at the gain-50 design point: the cell's supervisor
parameters `Instances.params` (three cells, home `(0, -40, 30)` degrees, age bound 25), the period
`1/10` s, the move duration `2` s, the position tolerance `3` degrees (`π/60 ≈ 0.0524` rad), the
speed tolerance `33/10` rad/s (`2 · 50 · 3/100 + 3/10`: room for the tube's speed error at the
gain `50` rad/s and a speed sample error of `3/10` rad/s) and encoders of `2^18` counts per
revolution.
A design definition, not from MLS. -/
def designNominalGain50 : Config where
  sup := Supervisor.Instances.params
  period := 1 / 10
  duration := 2
  posTol := 3
  velTol := 33 / 10
  countsPerRev := 2 ^ 18

end Cell.Policy

namespace Cell.Loop

open Set Supervisor

/-- The loop data of the gain-50 configuration: `h = 1/10` s, `T = 2` s, position tolerance
`degToRad 3` rad, speed tolerance `33/10` rad/s. A design statement, not from MLS. -/
theorem designNominalGain50_loop :
    Policy.designNominalGain50.loop = openCellParams (1 / 10) 2 (degToRad 3) (33 / 10) := by
  show openCellParams (((1 / 10 : ℚ)) : ℝ) ((2 : ℚ) : ℝ) (degToRad 3) (((33 / 10 : ℚ)) : ℝ) = _
  norm_num

/-- **The assured cell at the gain 50 with every decision taken by the program, on measured
samples, with the rotor inertia and the nominal payload in the controller's model (a design
statement, not from MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the
plant's equations, MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).** For every run
of the policy program at the configuration `Policy.designNominalGain50` (`hprog`), and every
supervisor whose runs meet the contract (`hsup`): let the controller's model carry the rotor
inertia `J` (kg m²) on every joint and the nominal mass `mn ≥ 0` (kg) at the tool point, and the
plant the rotor inertia `J' ≥ 3/2` kg m² on every joint and the actual mass `m ≥ 0` (kg), with
`|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m, N m s) and
`dm + (7/2) dJ + (f_c + 4 f_v)/60 ≤ 3/2`; the unknown is the mass error, the rotor-inertia error
and the friction, and the elasticity of the drives is not in the theorem's plant. If at every
boundary `k/10` s each joint angle of the sample, read in radians, is within `1/50` rad of the true
joint angle and each joint speed estimate is within `3/10` rad/s of the true joint speed (`hsamp`),
and under `htrack` (on each period the plant obeys its equations of motion under a friction torque
`f` with the computed torque of the controller's model tracking the quintic reference of the
program's last admitted move at the gain `50` rad/s, with right derivatives), `hcont` and `h0`:
the links keep `9/100` m from every obstacle at every `t ≥ 0`; the supervisor never faults and its
age stays below 25; a move admitted at boundary `k₀` is finished at boundary `k₀ + 20` with the
arm at its goal; and at each finish the tool is within `219/5000` m of the goal's tool position.
Proved from `cell_assured_measured_design_nominal_gain50`. -/
theorem cell_assured_program_nominal_gain50 (hsup : Supervisor.Contract Instances.params)
    {reqs : ℕ → List Waypoint} {smp : ℕ → Policy.Sample} {st : ℕ → Policy.State}
    {acts : ℕ → List Action}
    (hprog : Policy.IsProgramRun Policy.designNominalGain50 reqs smp st acts)
    {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn) (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J')
    (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 7 / 2 * dJ + (fc + 4 * fv) / 60 ≤ 3 / 2)
    {x v acc f : ℝ → Fin 3 → ℝ}
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3,
      |(smp k).toRad Policy.designNominalGain50 i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(smp k).velRad i - v (k * (1 / 10)) i| ≤ 3 / 10)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 50 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad (st (k + 1)).src) (DegPoint.toRad (st (k + 1)).goal)
        ((st (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (st k).sup.faulted = false ∧ (st k).sup.age < 25) ∧
    (∀ k₀, (st k₀).sup.busy = false → (st (k₀ + 1)).sup.busy = true →
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
  exact cell_assured_measured_design_nominal_gain50 hmn hm hJ' hdm hdJ hfc hfv hcond hsup hrun
    hsamp htrack hcont h0

/-- The states of the idle program at the gain-50 configuration: the program's initial state at
every boundary. A design definition, not from MLS. -/
def idleProgramNominalGain50 : ℕ → Policy.State :=
  fun _ => Policy.State.init Policy.designNominalGain50

/-- **With no request the program stays idle.** On every stream of samples and no request, the
program at the configuration `Policy.designNominalGain50` sends nothing and keeps its initial state
at every boundary. A design statement, not from MLS. -/
theorem idleProgramNominalGain50_isProgramRun (smp : ℕ → Policy.Sample) :
    Policy.IsProgramRun Policy.designNominalGain50 (fun _ => []) smp idleProgramNominalGain50
      (fun _ => []) :=
  ⟨rfl, fun _ => rfl⟩

/-- **The program at the gain 50 on encoder samples of the held run meets every hypothesis.** For
a supervisor whose runs meet the contract (`hsup`), the idle program at the configuration
`Policy.designNominalGain50`, run on the encoder samples (`2^18` counts per revolution, speeds
floored to a multiple of `1/5` rad/s, so zero at rest and within `1/2000` rad and `1/5 ≤ 3/10`
rad/s of the true state) of the arm at rest at home, with the controller's model carrying the
rotor inertia `17/10` kg m² on every joint and the nominal mass `1` kg, and the plant the rotor
inertia `17/10` kg m² and the actual mass `2` kg (a mass error of `1` kg) held by the friction
torque `(1 − 2) · toolGravity(home)` (at most `9` N m in every joint; `dm = 1` kg, `dJ = 0`,
`f_c = 9` N m, `f_v = 0`, `1 + 9/60 ≤ 3/2`), meets every hypothesis of
`cell_assured_program_nominal_gain50`; hence both links keep `9/100` m from every obstacle at every
`t ≥ 0` (s), the supervisor never faults and its age stays below 25, and the statements about
admissions and finishes hold (vacuously here, since nothing is admitted). A design statement, not
from MLS. -/
theorem program_hold_nominal_gain50_assured (hsup : Supervisor.Contract Instances.params) :
    (∀ t : ℝ, 0 ≤ t → sceneClear (DegPoint.toRad Instances.params.home)) ∧
    (∀ k, (idleProgramNominalGain50 k).sup.faulted = false ∧
      (idleProgramNominalGain50 k).sup.age < 25) ∧
    (∀ k₀, (idleProgramNominalGain50 k₀).sup.busy = false →
      (idleProgramNominalGain50 (k₀ + 1)).sup.busy = true →
      (idleProgramNominalGain50 (k₀ + 20 + 1)).sup.busy = false ∧
        (idleProgramNominalGain50 (k₀ + 20 + 1)).sup.current =
          (idleProgramNominalGain50 (k₀ + 1)).goal) ∧
    (∀ k, (idleProgramNominalGain50 k).sup.busy = true →
      (idleProgramNominalGain50 (k + 1)).sup.busy = false →
      dist (sceneTool (DegPoint.toRad Instances.params.home))
        (sceneTool (DegPoint.toRad (idleProgramNominalGain50 k).goal)) ≤ 219 / 5000) := by
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
      CellArmFollowsNominalRightAt 50 2 (17 / 10) 1 (17 / 10) 2 9 0 (fun _ => θ) 0 0
        (fun _ => (1 - 2 : ℝ) • toolGravity θ)
        (DegPoint.toRad (idleProgramNominalGain50 (k + 1)).src)
        (DegPoint.toRad (idleProgramNominalGain50 (k + 1)).goal)
        ((idleProgramNominalGain50 (k + 1)).start * (1 / 10)) t := by
    intro k t _
    simp only [idleProgramNominalGain50, Policy.State.init, Policy.designNominalGain50]
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
      |(encoderSample (fun _ => θ) 0 k).toRad Policy.designNominalGain50 i -
          (fun _ => θ) (k * (1 / 10)) i| ≤ 1 / 50 ∧
        |(encoderSample (fun _ => θ) 0 k).velRad i - (0 : ℝ → Fin 3 → ℝ) (k * (1 / 10)) i| ≤
          3 / 10 := by
    intro k i
    obtain ⟨h1, h2⟩ := encoderSample_within (fun _ => θ) 0 k i
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num)⟩
  have h0 : InTube (3 / 100) 50 (DegPoint.toRad Instances.params.home) 0
      ((fun _ => θ) 0) ((0 : ℝ → Fin 3 → ℝ) 0) := by
    intro i
    simp only [hθ, sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
    exact ⟨by norm_num, by norm_num⟩
  exact cell_assured_program_nominal_gain50 (J := 17 / 10) (mn := 1) (J' := 17 / 10) (m := 2)
    (dm := 1) (dJ := 0) (fc := 9) (fv := 0) hsup
    (idleProgramNominalGain50_isProgramRun (encoderSample (fun _ => θ) 0)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    hsamp htrack
    (by simpa using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (θ, (0 : Fin 3 → ℝ))) (Ici 0))) h0

end Cell.Loop
end RoboLean
