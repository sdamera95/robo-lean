import RoboLean.Cell.KnownModel
import RoboLean.Cell.PayloadTube
import RoboLean.Cell.AssuredInstanceRightStep
import RoboLean.Cell.AssuredMeasured

/-!
# The assured cell with the rotor inertia and the nominal payload in the controller's model

The plant hypothesis of the assured cell theorem at the design point (gain `ω = 80` rad/s, tube
radius `δ = 3/100` rad) bounds the acceleration that a disturbance torque produces by
`ω² δ = 192` rad/s². Here the controller's model carries what a deployed controller knows: the
rotor inertia `J` (kg m²) on every joint and the nominal part mass `mn` (kg) at the tool point
(`cellLoadedRobot J mn`). The plant has the rotor inertia `J' ≥ 3/2` kg m² on every joint and the
actual mass `m` (kg) at the tool point (`cellLoadedRobot J' m`), under a joint friction torque `f`
of any form with `|fᵢ(t)| ≤ f_c + f_v |ẋᵢ(t)|` (N m, N m s). What the controller does not know is
the mass error `m − mn`, the rotor-inertia error `J' − J` and the friction. The elasticity of the
drives is not in the theorem's plant. The disturbance is not assumed: it is what the plant's
equations add to the controller's model (`nominalDisturbance`), and its bound is derived, under
`|m − mn| ≤ dm`, `|J' − J| ≤ dJ` and `dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`, while the
motion is in a slightly wider tube (radius `301/10000` rad), which a first-exit argument then
shows the motion never leaves.

**Formalized.**

* `CellArmFollowsNominalRightAt`: at time `t` the plant obeys its equations of motion
  `M ẍ + C ẋ + N = F − f` (MLS eq. (4.47), p. 190, for `cellLoadedRobot J' m`) under the computed
  torque `F` of the controller's model `cellLoadedRobot J mn` tracking the move reference, with
  right derivatives, and the friction bound.
* `CellArmFollowsNominalRightAt.equations`: the controller's model with the disturbance.
* `CellArmFollowsNominalRightAt.accel_bound`: while the motion is in the tube of radius
  `301/10000` rad around a linked move, the disturbance's acceleration is at most `192` rad/s² in
  every joint.
* `Loop.cellArm_moveCorollary_nominal_right`: the loop's move corollary for this predicate.
* `Loop.cell_assured_contract_design_nominal_right`: the assured cell at the design point on exact
  samples, with the supervisor's contract as premise.
* `Loop.cell_assured_measured_design_nominal_right`: the same on samples within `1/50` rad and
  `1/5` rad/s of the true state, with the arrival tolerances `3` degrees and `5` rad/s.
* `Loop.demo_assured_contract_nominal_right`, `Loop.hold_assured_contract_nominal_right`: the
  demonstration run with the model equal to the plant, and a run at rest at home with a mass error
  of `1` kg held by friction, meet every hypothesis of the exact-sample theorem.

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); masses in kg, inertias in kg m², torques in N m, speeds in rad/s, accelerations in
rad/s², time in seconds. The arm's numbers, the rotor model, the payload's location, the friction
model, the scene, the loop and the bounds are design statements, not from MLS. Nothing here
concerns a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- **The plant follows the move reference at time `t` under computed torque with the
controller's model, with joint friction and right derivatives (a design statement, not from MLS;
computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations of
motion, MLS eq. (4.47), p. 190, with the friction as a joint force, p. 170).** `x` has right
derivative `v t` and `v` has right derivative `acc t` at `t` (within `[t, ∞)`); the friction
torque satisfies `|fᵢ(t)| ≤ f_c + f_v |vᵢ(t)|` (N m) for every joint; and the plant, the arm with
the rotor inertia `J'` (kg m²) on every joint carrying the actual mass `m` (kg) at the tool point,
obeys `M ẍ + C ẋ + N = F − f` at `t` with `ẍ = acc t` and `F` the computed torque of the
controller's model `cellLoadedRobot J mn` (the rotor inertia `J` on every joint and the nominal
mass `mn` at the tool point) for the gains `ω² I`, `2ω I` and the reference of the move from `a`
to `g` admitted at `t₀` with duration `T` (radians, seconds). The elasticity of the drives is not
in this plant. -/
def CellArmFollowsNominalRightAt (ω T J mn J' m fc fv : ℝ) (x v acc f : ℝ → Fin 3 → ℝ)
    (a g : Fin 3 → ℝ) (t₀ t : ℝ) : Prop :=
  HasDerivWithinAt x (v t) (Ici t) t ∧ HasDerivWithinAt v (acc t) (Ici t) t ∧
    (∀ i, |f t i| ≤ fc + fv * |v t i|) ∧
    (cellLoadedRobot J' m).M (x t) *ᵥ acc t + (cellLoadedRobot J' m).C (x t) (v t) *ᵥ v t +
        (cellLoadedRobot J' m).N (x t) (v t) =
      (cellLoadedRobot J mn).computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a g t₀ T)
        (moveRefDeriv a g t₀ T) (moveRefDeriv2 a g t₀ T) t (x t) (v t) - f t

/-- **The controller's model with the disturbance (a design statement, not from MLS; the plant's
equations, MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).** Along a motion
satisfying `CellArmFollowsNominalRightAt` at `t`, the controller's model `cellLoadedRobot J mn`
obeys `M̂ ẍ + Ĉ ẋ + N̂ = F + d` at `t` with `d = nominalDisturbance J mn J' m x ẋ ẍ f` (N m). -/
theorem CellArmFollowsNominalRightAt.equations {ω T J mn J' m fc fv : ℝ}
    {x v acc f : ℝ → Fin 3 → ℝ} {a g : Fin 3 → ℝ} {t₀ t : ℝ}
    (h : CellArmFollowsNominalRightAt ω T J mn J' m fc fv x v acc f a g t₀ t) :
    (cellLoadedRobot J mn).M (x t) *ᵥ acc t + (cellLoadedRobot J mn).C (x t) (v t) *ᵥ v t +
        (cellLoadedRobot J mn).N (x t) (v t) =
      (cellLoadedRobot J mn).computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a g t₀ T)
        (moveRefDeriv a g t₀ T) (moveRefDeriv2 a g t₀ T) t (x t) (v t) +
        nominalDisturbance J mn J' m (x t) (v t) (acc t) (f t) :=
  nominalDisturbance_spec h.2.2.2

/-- The model's rotor inertia is nonnegative under the plant hypotheses: the condition gives
`dJ ≤ 32/75` kg m², so `J ≥ J' − dJ ≥ 3/2 − 32/75 > 0`. -/
private theorem rotor_nonneg {J mn J' m dm dJ fc fv : ℝ} (hJ' : 3 / 2 ≤ J')
    (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5) : 0 ≤ J := by
  have h1 := abs_nonneg (m - mn)
  have h2 := (abs_le.mp hdJ).2
  linarith

/-- **The acceleration of the disturbance inside the tube (a design statement, not from MLS;
`cellLoaded_accel_abs_le`).** At the design gain `ω = 80` rad/s and duration `T = 2` s, let the
controller's model carry the rotor inertia `J` (kg m²) on every joint and the nominal mass
`mn ≥ 0` (kg) at the tool point, and the plant the rotor inertia `J' ≥ 3/2` kg m² on every joint
and the actual mass `m ≥ 0` (kg), with `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m,
N m s) and `dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`. If the plant follows the move from `a`
to `g` (linked by the supervisor's link test) at `s`, and its state at `s` is in the tube of radius
`301/10000` rad around the reference, then every `w` with `M̂(x(s)) w = d(s)`,
`d = nominalDisturbance J mn J' m x ẋ ẍ f`, satisfies `|wᵢ| ≤ 192` rad/s² for every joint. -/
theorem CellArmFollowsNominalRightAt.accel_bound {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn)
    (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5) {h T δa va : ℝ}
    {a g : Supervisor.Waypoint} (hag : (Loop.openCellParams h T δa va).linked a g)
    {x v acc f : ℝ → Fin 3 → ℝ} {t₀ s : ℝ}
    (hE : CellArmFollowsNominalRightAt 80 2 J mn J' m fc fv x v acc f (DegPoint.toRad a)
      (DegPoint.toRad g) t₀ s)
    (hin : Cell.InTube 80 (301 / 10000) (x s) (v s)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s))
    (w : Fin 3 → ℝ)
    (hMw : (cellLoadedRobot J mn).M (x s) *ᵥ w =
      nominalDisturbance J mn J' m (x s) (v s) (acc s) (f s))
    (i : Fin 3) : |w i| ≤ 192 := by
  obtain ⟨hreach, hu, hv⟩ := Loop.payload_tube_bounds hag hin
  set u : Fin 3 → ℝ := moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s -
    (2 * 80 : ℝ) • (v s - moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s) -
    ((80 : ℝ) ^ 2) • (x s - moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s) with hu_def
  -- the computed torque is `M̂ u + Ĉ v + N̂`
  have hF : (cellLoadedRobot J mn).computedTorque (((80 : ℝ) ^ 2) • 1) ((2 * 80 : ℝ) • 1)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
      (moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2) s (x s) (v s) =
      (cellLoadedRobot J mn).M (x s) *ᵥ u + (cellLoadedRobot J mn).C (x s) (v s) *ᵥ v s +
        (cellLoadedRobot J mn).N (x s) (v s) := by
    simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong,
      Matrix.smul_mulVec, Matrix.one_mulVec, hu_def]
  -- the actual acceleration is `u + w`
  have hM : ((cellLoadedRobot J mn).M (x s)).PosDef :=
    cellLoadedRobot_M_posDef (rotor_nonneg hJ' hdm hdJ hfc hfv hcond) hmn (x s)
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
  refine cellLoaded_accel_abs_le hmn hm hJ' hdm hdJ hfc hfv hcond hreach (fun j => ?_) hv
    (fun j => hE.2.2.1 j) hMw i
  have := hu j
  simp only [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact this

end Cell

namespace Cell.Loop

open Set Supervisor

/-- **The loop's move corollary for the plant under computed torque with the controller's model,
with joint friction and right derivatives (a design statement, not from MLS; computed torque of
MLS eq. (4.49), p. 191, for the robot of p. 303).** At the design gain `ω = 80` rad/s, tube radius
`δ = 3/100` rad and move duration `T = 2` s, for the loop data `openCellParams h 2 δa va`, the
controller's model with the rotor inertia `J` (kg m²) and the nominal mass `mn ≥ 0` (kg), the
plant with the rotor inertia `J' ≥ 3/2` kg m² and the actual mass `m ≥ 0` (kg), `|m − mn| ≤ dm`,
`|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m, N m s) with `dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`,
and `(x, v)` continuous on `[0, ∞)`, the arm's motion satisfies `Loop.MoveCorollary` for the
quintic reference and the tracking predicate `CellArmFollowsNominalRightAt`. The disturbance's
bound is required only while the motion is in the tube of radius `301/10000` rad, which it never
leaves (first exit). -/
theorem cellArm_moveCorollary_nominal_right {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn)
    (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5) (h δa va : ℝ)
    {x v acc f : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    MoveCorollary (openCellParams h 2 δa va) (quinticMoveRef (n := 3) (by norm_num : (0 : ℝ) < 2))
      (3 / 100) 80
      (fun a g t₀ t => CellArmFollowsNominalRightAt 80 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad a) (DegPoint.toRad g) t₀ t) x v := by
  intro a g hag t₀ t₁ ht₀ _ hf hin t ht
  have hin' : Cell.InTube 80 (3 / 100) (x t₀) (v t₀)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 t₀)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 t₀) := by
    rw [moveRef_of_le (by norm_num) le_rfl, moveRefDeriv_of_le (by norm_num) le_rfl]
    exact hin
  have htube := tube_invariant_on_accel_right_of_inTube (η := 301 / 10000)
    (by norm_num : (0 : ℝ) < 80) (by norm_num : (3 : ℝ) / 100 < 301 / 10000)
    (hasDerivAt_moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
    (hasDerivAt_moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
    (Mt := fun s => (cellLoadedRobot J mn).M (x s))
    (Ct := fun s => (cellLoadedRobot J mn).C (x s) (v s))
    (Nt := fun s => (cellLoadedRobot J mn).N (x s) (v s))
    (d := fun s => nominalDisturbance J mn J' m (x s) (v s) (acc s) (f s))
    (hc.mono fun s hs => ht₀.trans hs.1) (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1)
    (fun s hs hnear w hMw i => ?_) (fun s hs => (hf s hs).equations) hin'
  · exact (htube t ht).1
  · have := CellArmFollowsNominalRightAt.accel_bound hmn hm hJ' hdm hdJ hfc hfv hcond hag
      (hf s hs) hnear w hMw i
    norm_num
    linarith

/-- **The assured cell at the design point with the rotor inertia and the nominal payload in the
controller's model, with the supervisor's contract as its premise (a design statement, not from
MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations,
MLS eq. (4.47), p. 190, with friction as a joint force, p. 170).** With `h = 1/10` s, `T = 2` s,
`ω = 80` rad/s, `δ = δ_a = 3/100` rad and `v_a = 24/5` rad/s, let the controller's model carry the
rotor inertia `J` (kg m²) on every joint and the nominal mass `mn ≥ 0` (kg) at the tool point, and
the plant the rotor inertia `J' ≥ 3/2` kg m² on every joint and the actual mass `m ≥ 0` (kg), with
`|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, the Coulomb level `f_c ≥ 0` (N m) and the viscous coefficient
`f_v ≥ 0` (N m s), and `dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`. The unknown is the mass
error, the rotor-inertia error and the friction; the elasticity of the drives is not in the
theorem's plant. For every run of the supervisor that meets the contract
`Supervisor.Contract Instances.params` (`hsup`), every timed run `c` of the cell loop and every
motion `(x, v, acc)` of the plant under a friction torque `f`, under the hypotheses
* (harness, `hrun`) at each boundary the actions sent are queue actions followed by the policy's
  action on the exact sample, each accepted by the supervisor;
* (harness and plant, `htrack`) on each period the plant obeys its equations of motion
  `M ẍ + C ẋ + N = F − f` with the computed torque `F` of the controller's model tracking the
  quintic reference of the last admitted move, with right derivatives, and
  `|fᵢ(t)| ≤ f_c + f_v |vᵢ(t)|` for every joint (`CellArmFollowsNominalRightAt`);
* (plant, `hcont`) `(x, v)` is continuous on `[0, ∞)`;
* (harness, `h0`) the arm starts in the tube around home at rest,
the links keep `9/100` m from every obstacle at every `t ≥ 0`, the supervisor never faults and
its age stays below 25, a move admitted at boundary `k₀` is finished at boundary `k₀ + 20` at its
goal, and at each finish the tool is within `219/5000` m of the goal's tool position. No bound on
the disturbance is assumed: it is derived from `dm`, `dJ`, `f_c` and `f_v`. -/
theorem cell_assured_contract_design_nominal_right {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn)
    (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5)
    (hsup : Supervisor.Contract Instances.params)
    {x v acc f : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 80 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad (c (k + 1)).src) (DegPoint.toRad (c (k + 1)).goal)
        ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        219 / 5000) := by
  have H := cell_open_hyps (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 2)
    (by rw [design_steps]; norm_num) (by norm_num : (0 : ℝ) ≤ 80) le_rfl (by norm_num) hrun htrack
    (cellArm_moveCorollary_nominal_right hmn hm hJ' hdm hdJ hfc hfv hcond (1 / 10) (3 / 100)
      (24 / 5) hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, -⟩ :=
    H.assured hc (openCellParams_certify (1 / 10) 2 (3 / 100) (24 / 5))
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

/-- The position tolerance `3` degrees, in radians, leaves room for the tube radius `3/100` rad and
the position sample error `1/50` rad: `3/100 + 1/50 ≤ 3π/180`, from `π > 3`. -/
private theorem nominal_radius_add_le_posTol : (3 : ℝ) / 100 + 1 / 50 ≤ degToRad 3 := by
  have := Real.pi_gt_three
  unfold degToRad
  push_cast
  linarith

/-- **The assured cell on measured samples at the design point with the rotor inertia and the
nominal payload in the controller's model (a design statement, not from MLS; computed torque of
MLS eq. (4.49), p. 191, for the robot of p. 303; the plant's equations, MLS eq. (4.47), p. 190,
with friction as a joint force, p. 170).** With `h = 1/10` s, `T = 2` s, `ω = 80` rad/s,
`δ = 3/100` rad, the position tolerance `δ_a = 3` degrees (`π/60` rad), the speed tolerance
`v_a = 5` rad/s, and samples within `εq = 1/50` rad and `εv = 1/5` rad/s of the true state, let
the controller's model carry the rotor inertia `J` (kg m²) on every joint and the nominal mass
`mn ≥ 0` (kg) at the tool point, and the plant the rotor inertia `J' ≥ 3/2` kg m² on every joint
and the actual mass `m ≥ 0` (kg), with `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0` (N m,
N m s) and `dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`. The unknown is the mass error, the
rotor-inertia error and the friction; the elasticity of the drives is not in the theorem's plant.
For every run of the supervisor that meets the contract `Supervisor.Contract Instances.params`
(`hsup`), every timed run `c` of the cell loop on measured samples `(xm, vm)` (`hrun`: at each
boundary the actions sent are queue actions followed by the policy's action on the measured
sample, each accepted by the supervisor), every motion `(x, v, acc)` of the plant under a friction
torque `f` with the sample error bound (`hsamp`), the tracking hypothesis
`CellArmFollowsNominalRightAt` on each period (`htrack`), `(x, v)` continuous on `[0, ∞)`
(`hcont`) and the arm starting in the tube around home at rest (`h0`): the links keep `9/100` m
from every obstacle at every `t ≥ 0`, the supervisor never faults and its age stays below 25, a
move admitted at boundary `k₀` is finished at boundary `k₀ + 20` at its goal, and at each finish
the tool at the true configuration is within `219/5000` m of the goal's tool position. -/
theorem cell_assured_measured_design_nominal_right {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn)
    (hm : 0 ≤ m) (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5)
    (hsup : Supervisor.Contract Instances.params)
    {x v acc f : ℝ → Fin 3 → ℝ} {xm vm : ℕ → Fin 3 → ℝ} {c : ℕ → CellState}
    {acts : ℕ → List Action}
    (hrun : IsMeasuredCellRun (openCellParams (1 / 10) 2 (degToRad 3) 5) Instances.params
      xm vm c acts)
    (hsamp : ∀ k : ℕ, ∀ i : Fin 3, |xm k i - x (k * (1 / 10)) i| ≤ 1 / 50 ∧
      |vm k i - v (k * (1 / 10)) i| ≤ 1 / 5)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 80 2 J mn J' m fc fv x v acc f
        (DegPoint.toRad (c (k + 1)).src) (DegPoint.toRad (c (k + 1)).goal)
        ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        219 / 5000) := by
  have H := cell_measured_hyps (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 2)
    (by rw [design_steps]; norm_num) (by norm_num : (0 : ℝ) ≤ 80) nominal_radius_add_le_posTol
    (by norm_num) hrun hsamp htrack
    (cellArm_moveCorollary_nominal_right hmn hm hJ' hdm hdJ hfc hfv hcond (1 / 10) (degToRad 3) 5
      hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, -⟩ :=
    H.assured hc (openCellParams_certify (1 / 10) 2 (degToRad 3) 5)
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

/-- **A moving arm meets the hypotheses of the nominal-model form.** The demonstration run (the
move from home to the waypoint above the pick slot, tracked exactly) with the controller's model
equal to the plant (rotor inertia `J = J' = 17/10` kg m² on every joint, nominal and actual mass
`mn = m = 5` kg, no friction: `f_c = f_v = 0`, `f = 0`, `dm = dJ = 0`) meets every hypothesis of
`cell_assured_contract_design_nominal_right`, with the supervisor's contract given by the
hand-written proof `Supervisor.contract_of_design`: the computed torque of a model at its own
reference has zero tracking error. So the links keep `9/100` m from every obstacle at every
`t ≥ 0` (s), the supervisor never faults, and at the finish the tool is within `219/5000` m of the
goal's tool position. A design statement, not from MLS (computed torque of MLS eq. (4.49),
p. 191). -/
theorem demo_assured_contract_nominal_right :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsNominalRightAt 80 2 (17 / 10) 5 (17 / 10) 5 0 0 demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    refine ⟨(hasDerivAt_moveRef _ _ _ _ t).hasDerivWithinAt,
      (hasDerivAt_moveRefDeriv _ _ _ _ t).hasDerivWithinAt, fun i => by simp, ?_⟩
    simp [Control.RobotSystem.computedTorque, Control.computedTorqueAlong, demoMotion, demoVel,
      demoAcc]
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_contract_design_nominal_right
    (J := 17 / 10) (mn := 5) (J' := 17 / 10) (m := 5) (dm := 0) (dJ := 0) (fc := 0) (fv := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl
    (by norm_num) (Supervisor.contract_of_design Instances.params)
    (demo_isCellRun_of (by norm_num) (by norm_num)).openCellParams_of_cellParams htrack
    demo_continuousOn (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

/-- **A mass error held by friction meets the hypotheses of the nominal-model form.** The idle run
(no request, the supervisor waits at home) with the arm at rest at home, the controller's model
carrying the rotor inertia `J = 17/10` kg m² on every joint and the nominal mass `mn = 1` kg, the
plant the rotor inertia `J' = 17/10` kg m² and the actual mass `m = 2` kg (a mass error of `1`
kg), held by a friction torque equal to the mass error's weight torque,
`f = (1 − 2) · toolGravity(home)` (at most `9` N m in every joint), meets every hypothesis of
`cell_assured_contract_design_nominal_right` with `dm = 1` kg, `dJ = 0`, `f_c = 9` N m and
`f_v = 0` (`1 + 9/150 ≤ 8/5`), with the supervisor's contract given by the hand-written proof
`Supervisor.contract_of_design`. So the links keep `9/100` m from every obstacle at every
`t ≥ 0` (s) and the supervisor never faults. A satisfying instance with a mass error of `1` kg (at
rest); a design statement, not from MLS. -/
theorem hold_assured_contract_nominal_right :
    (∀ t : ℝ, 0 ≤ t → sceneClear (DegPoint.toRad Instances.params.home)) ∧
    (∀ k, (idleState k).sup.faulted = false ∧ (idleState k).sup.age < 25) := by
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
        (DegPoint.toRad (idleState (k + 1)).src) (DegPoint.toRad (idleState (k + 1)).goal)
        ((idleState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    simp only [idleState, CellState.init]
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
  have h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0
      ((fun _ => θ) 0) ((0 : ℝ → Fin 3 → ℝ) 0) := by
    intro i
    simp only [hθ, sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨hclear, hfault, -, -⟩ := cell_assured_contract_design_nominal_right (J := 17 / 10)
    (mn := 1) (J' := 17 / 10) (m := 2) (dm := 1) (dJ := 0) (fc := 9) (fv := 0) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (Supervisor.contract_of_design Instances.params) (idle_isCellRun _ _ _) htrack
    (by simpa using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (θ, (0 : Fin 3 → ℝ))) (Ici 0))) h0
  exact ⟨hclear, hfault⟩

end Cell.Loop
end RoboLean
