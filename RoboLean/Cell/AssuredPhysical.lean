import RoboLean.Cell.Payload
import RoboLean.Cell.PayloadTube
import RoboLean.Cell.AssuredInstanceRightStep

/-!
# The assured cell with the plant described by a payload and joint friction

The plant hypothesis of the assured cell theorem at the design point (gain `ω = 80` rad/s, tube
radius `δ = 3/100` rad) bounds the acceleration that a disturbance torque produces,
`|(M(x)⁻¹ d)ᵢ| ≤ ω² δ = 192` rad/s². Here the plant is described instead by what it is: the cell
arm carrying a point mass `m` (kg) at the tool point that the controller does not know (its model
is the unloaded arm), with a joint friction torque `τ_f` of any form satisfying
`|τ_f,i(t)| ≤ f_c + f_v |ẋᵢ(t)|` (N m, N m s). The disturbance is not assumed: it is what the
loaded arm's equations add to the controller's model (`payloadDisturbance`), and its bound is
derived from `m`, `f_c`, `f_v` while the motion is in a slightly wider tube (radius `301/10000`
rad), which a first-exit argument then shows the motion never leaves.

**Formalized.**

* `CellArmFollowsPayloadRightAt`: at time `t` the loaded arm obeys its equations of motion
  `M_m ẍ + C_m ẋ + N_m = F − τ_f` (MLS eq. (4.47), p. 190, for `cellPayloadArm m`) under the
  computed torque `F` of the unloaded model tracking the move reference, with right derivatives,
  and the friction bound.
* `CellArmFollowsPayloadRightAt.accel_bound`: while the motion is in the tube of radius
  `301/10000` rad around a linked move, the disturbance's acceleration is at most `192` rad/s² in
  every joint, provided `1080 m + (27/2) (f_c + (29/5) f_v) ≤ 192`;
  `CellArmFollowsPayloadRightAt.accel`: there the motion satisfies the acceleration-level
  predicate `CellArmFollowsAccelRightAt 80 2 (3/100)` with that disturbance.
* `cellArm_moveCorollary_payload_right`: the loop's move corollary for the payload predicate.
* `cell_assured_contract_design_physical_right`: the assured cell at the design point with the
  supervisor's contract as premise and the plant hypothesis in payload and friction terms.
* `demo_assured_contract_physical_right`: the demonstration run (no payload, no friction) meets
  every hypothesis of the design-point theorem.

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); masses in kg, torques in N m, speeds in rad/s, accelerations in rad/s², time in seconds.
The arm's numbers, the payload's location, the friction model, the scene, the loop and the bounds
are design statements, not from MLS. Nothing here concerns a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- **The loaded cell arm follows the move reference at time `t`, with joint friction and right
derivatives (a design statement, not from MLS; computed torque of MLS eq. (4.49), p. 191, for the
robot of p. 303; the loaded arm's equations of motion, MLS eq. (4.47), p. 190, with the friction
as a joint force, p. 170).** `x` has right derivative `v t` and `v` has right derivative `acc t`
at `t` (within `[t, ∞)`); the friction torque satisfies `|fᵢ(t)| ≤ f_c + f_v |vᵢ(t)|` (N m) for
every joint; and the arm carrying the point mass `m` (kg) at the tool point obeys
`M_m ẍ + C_m ẋ + N_m = F − f` at `t` with `ẍ = acc t` and `F` the computed torque of the unloaded
model `cellRobot` for the gains `ω² I`, `2ω I` and the reference of the move from `a` to `g`
admitted at `t₀` with duration `T` (radians, seconds). -/
def CellArmFollowsPayloadRightAt (ω T m fc fv : ℝ) (x v acc f : ℝ → Fin 3 → ℝ)
    (a g : Fin 3 → ℝ) (t₀ t : ℝ) : Prop :=
  HasDerivWithinAt x (v t) (Ici t) t ∧ HasDerivWithinAt v (acc t) (Ici t) t ∧
    (∀ i, |f t i| ≤ fc + fv * |v t i|) ∧
    (cellPayloadRobot m).M (x t) *ᵥ acc t + (cellPayloadRobot m).C (x t) (v t) *ᵥ v t +
        (cellPayloadRobot m).N (x t) (v t) =
      cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a g t₀ T)
        (moveRefDeriv a g t₀ T) (moveRefDeriv2 a g t₀ T) t (x t) (v t) - f t

/-- **The controller's model with the payload disturbance (a design statement, not from MLS).**
Along a motion satisfying `CellArmFollowsPayloadRightAt` at `t`, the unloaded model obeys
`M ẍ + C ẋ + N = F + d` at `t` with `d = payloadDisturbance m x ẋ ẍ f` (N m). -/
theorem CellArmFollowsPayloadRightAt.equations {ω T m fc fv : ℝ} {x v acc f : ℝ → Fin 3 → ℝ}
    {a g : Fin 3 → ℝ} {t₀ t : ℝ} (h : CellArmFollowsPayloadRightAt ω T m fc fv x v acc f a g t₀ t) :
    cellRobot.M (x t) *ᵥ acc t + cellRobot.C (x t) (v t) *ᵥ v t + cellRobot.N (x t) (v t) =
      cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a g t₀ T)
        (moveRefDeriv a g t₀ T) (moveRefDeriv2 a g t₀ T) t (x t) (v t) +
        payloadDisturbance m (x t) (v t) (acc t) (f t) :=
  payloadDisturbance_spec h.2.2.2

/-- **The acceleration of the payload disturbance inside the tube (a design statement, not from
MLS; `cellArm_payload_accel_abs_le`).** At the design gain `ω = 80` rad/s and duration `T = 2` s,
let `m ≥ 0` (kg), `f_c, f_v ≥ 0` (N m, N m s) with `1080 m + (27/2) (f_c + (29/5) f_v) ≤ 192`. If
the loaded arm follows the move from `a` to `g` (linked by the supervisor's link test) at `s`, and
its state at `s` is in the tube of radius `301/10000` rad around the reference, then every `w` with
`M(x(s)) w = d(s)`, `d = payloadDisturbance m x ẋ ẍ f`, satisfies `|wᵢ| ≤ 192` rad/s² for every
joint. -/
theorem CellArmFollowsPayloadRightAt.accel_bound {m fc fv : ℝ} (hm : 0 ≤ m) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : 1080 * m + 27 / 2 * (fc + 29 / 5 * fv) ≤ 192) {h T δa va : ℝ}
    {a g : Supervisor.Waypoint} (hag : (Loop.openCellParams h T δa va).linked a g)
    {x v acc f : ℝ → Fin 3 → ℝ}
    {t₀ s : ℝ}
    (hE : CellArmFollowsPayloadRightAt 80 2 m fc fv x v acc f (DegPoint.toRad a)
      (DegPoint.toRad g) t₀ s)
    (hin : Cell.InTube 80 (301 / 10000) (x s) (v s)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s))
    (w : Fin 3 → ℝ) (hMw : cellRobot.M (x s) *ᵥ w = payloadDisturbance m (x s) (v s) (acc s) (f s))
    (i : Fin 3) : |w i| ≤ 192 := by
  obtain ⟨hreach, hu, hv⟩ := Loop.payload_tube_bounds hag hin
  set u : Fin 3 → ℝ := moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s -
    (2 * 80 : ℝ) • (v s - moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s) -
    ((80 : ℝ) ^ 2) • (x s - moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s) with hu_def
  -- the computed torque is `M u + C v + N`
  have hF : cellRobot.computedTorque (((80 : ℝ) ^ 2) • 1) ((2 * 80 : ℝ) • 1)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2)
      (moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2) s (x s) (v s) =
      cellRobot.M (x s) *ᵥ u + cellRobot.C (x s) (v s) *ᵥ v s + cellRobot.N (x s) (v s) := by
    simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong,
      Matrix.smul_mulVec, Matrix.one_mulVec, hu_def]
  -- the actual acceleration is `u + w`
  have hM : (cellRobot.M (x s)).PosDef := cellArm_M_posDef (x s)
  have hacc : acc s = u + w := by
    have e := hE.equations
    rw [hF, ← hMw] at e
    have e' : cellRobot.M (x s) *ᵥ acc s = cellRobot.M (x s) *ᵥ (u + w) := by
      rw [Matrix.mulVec_add]
      linear_combination (exp := 1) e
    have := congrArg (fun y => (cellRobot.M (x s))⁻¹ *ᵥ y) e'
    rwa [Control.PosDef.inv_mulVec_mulVec hM, Control.PosDef.inv_mulVec_mulVec hM] at this
  rw [hacc] at hMw
  refine cellArm_payload_accel_abs_le hm hfc hfv hcond hreach (fun j => ?_) hv
    (fun j => hE.2.2.1 j) hMw i
  have := hu j
  simp only [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact this

/-- **Inside the tube the loaded arm satisfies the acceleration-level predicate (a design
statement, not from MLS).** Under the conditions of
`CellArmFollowsPayloadRightAt.accel_bound`, if the loaded arm follows the move at `s` and its state
is in the tube of radius `301/10000` rad around the reference, then the motion satisfies
`CellArmFollowsAccelRightAt 80 2 (3/100)` at `s` with the disturbance
`d = payloadDisturbance m x ẋ ẍ f` (so `|(M⁻¹ d)ᵢ| ≤ 192` rad/s²). -/
theorem CellArmFollowsPayloadRightAt.accel {m fc fv : ℝ} (hm : 0 ≤ m) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : 1080 * m + 27 / 2 * (fc + 29 / 5 * fv) ≤ 192) {h T δa va : ℝ}
    {a g : Supervisor.Waypoint} (hag : (Loop.openCellParams h T δa va).linked a g)
    {x v acc f : ℝ → Fin 3 → ℝ}
    {t₀ s : ℝ}
    (hE : CellArmFollowsPayloadRightAt 80 2 m fc fv x v acc f (DegPoint.toRad a)
      (DegPoint.toRad g) t₀ s)
    (hin : Cell.InTube 80 (301 / 10000) (x s) (v s)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)) :
    CellArmFollowsAccelRightAt 80 2 (3 / 100) x v acc
      (fun r => payloadDisturbance m (x r) (v r) (acc r) (f r)) (DegPoint.toRad a)
      (DegPoint.toRad g) t₀ s := by
  refine ⟨hE.1, hE.2.1, fun i => ?_, hE.equations⟩
  have hMw : cellRobot.M (x s) *ᵥ ((cellRobot.M (x s))⁻¹ *ᵥ
      payloadDisturbance m (x s) (v s) (acc s) (f s)) =
      payloadDisturbance m (x s) (v s) (acc s) (f s) := by
    have hU : IsUnit (cellRobot.M (x s)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (cellArm_M_posDef (x s)).isUnit
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have := CellArmFollowsPayloadRightAt.accel_bound hm hfc hfv hcond hag hE hin _ hMw i
  norm_num
  linarith

end Cell

namespace Cell.Loop

open Set Supervisor

/-- **The loop's move corollary for the loaded cell arm with joint friction and right
derivatives (a design statement, not from MLS; computed torque of MLS eq. (4.49), p. 191, for the
robot of p. 303).** At the design gain `ω = 80` rad/s, tube radius `δ = 3/100` rad and move
duration `T = 2` s, for the loop data `openCellParams h 2 δa va`, `m ≥ 0` (kg), `f_c, f_v ≥ 0`
(N m, N m s) with `1080 m + (27/2) (f_c + (29/5) f_v) ≤ 192`, and `(x, v)` continuous on
`[0, ∞)`, the arm's motion satisfies `Loop.MoveCorollary` for the quintic reference and the
tracking predicate `CellArmFollowsPayloadRightAt`. The disturbance's bound is required only while
the motion is in the tube of radius `301/10000` rad, which it never leaves (first exit). -/
theorem cellArm_moveCorollary_payload_right {m fc fv : ℝ} (hm : 0 ≤ m) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : 1080 * m + 27 / 2 * (fc + 29 / 5 * fv) ≤ 192) (h δa va : ℝ)
    {x v acc f : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    MoveCorollary (openCellParams h 2 δa va) (quinticMoveRef (n := 3) (by norm_num : (0 : ℝ) < 2))
      (3 / 100) 80
      (fun a g t₀ t => CellArmFollowsPayloadRightAt 80 2 m fc fv x v acc f (DegPoint.toRad a)
        (DegPoint.toRad g) t₀ t) x v := by
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
    (Mt := fun s => cellRobot.M (x s)) (Ct := fun s => cellRobot.C (x s) (v s))
    (Nt := fun s => cellRobot.N (x s) (v s))
    (d := fun s => payloadDisturbance m (x s) (v s) (acc s) (f s))
    (hc.mono fun s hs => ht₀.trans hs.1) (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1)
    (fun s hs hnear w hMw i => ?_) (fun s hs => (hf s hs).equations) hin'
  · exact (htube t ht).1
  · have := CellArmFollowsPayloadRightAt.accel_bound hm hfc hfv hcond hag (hf s hs) hnear w hMw i
    norm_num
    linarith

/-- **The assured cell at the design point with the plant described by a payload and joint
friction, with the supervisor's contract as its premise (a design statement, not from MLS;
computed torque of MLS eq. (4.49), p. 191; the loaded arm's equations, MLS eq. (4.47), p. 190).**
With `h = 1/10` s, `T = 2` s, `ω = 80` rad/s, `δ = δ_a = 3/100` rad and `v_a = 24/5` rad/s, let
the payload `m ≥ 0` (kg), the Coulomb level `f_c ≥ 0` (N m) and the viscous coefficient
`f_v ≥ 0` (N m s) satisfy `1080 m + (27/2) (f_c + (29/5) f_v) ≤ 192`. For every run of the
supervisor that meets the contract `Supervisor.Contract Instances.params` (`hsup`), every timed
run `c` of the cell loop and every motion `(x, v, acc)` of the arm carrying the point mass `m` at
the tool point (unknown to the controller, whose model is the unloaded arm) under a friction
torque `f`, under the hypotheses
* (harness, `hrun`) at each boundary the actions sent are queue actions followed by the policy's
  action on the exact sample, each accepted by the supervisor;
* (harness and plant, `htrack`) on each period the loaded arm obeys its equations of motion
  `M_m ẍ + C_m ẋ + N_m = F − f` with the computed torque `F` of the unloaded model tracking the
  quintic reference of the last admitted move, with right derivatives, and
  `|fᵢ(t)| ≤ f_c + f_v |vᵢ(t)|` for every joint (`CellArmFollowsPayloadRightAt`);
* (plant, `hcont`) `(x, v)` is continuous on `[0, ∞)`;
* (harness, `h0`) the arm starts in the tube around home at rest,
the links keep `9/100` m from every obstacle at every `t ≥ 0`, the supervisor never faults and
its age stays below 25, a move admitted at boundary `k₀` is finished at boundary `k₀ + 20` at its
goal, and at each finish the tool is within `219/5000` m of the goal's tool position. No bound on
the disturbance is assumed: it is derived from `m`, `f_c` and `f_v`. -/
theorem cell_assured_contract_design_physical_right {m fc fv : ℝ} (hm : 0 ≤ m) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : 1080 * m + 27 / 2 * (fc + 29 / 5 * fv) ≤ 192)
    (hsup : Supervisor.Contract Instances.params)
    {x v acc f : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsPayloadRightAt 80 2 m fc fv x v acc f (DegPoint.toRad (c (k + 1)).src)
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
  have H := cell_open_hyps (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 2)
    (by rw [design_steps]; norm_num) (by norm_num : (0 : ℝ) ≤ 80) le_rfl (by norm_num) hrun htrack
    (cellArm_moveCorollary_payload_right hm hfc hfv hcond (1 / 10) (3 / 100) (24 / 5) hcont) h0
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

/-- **A moving arm meets the hypotheses of the payload form.** The demonstration run (the move
from home to the waypoint above the pick slot, tracked exactly) with no payload and no friction
(`m = f_c = f_v = 0`, `f = 0`) meets every hypothesis of
`cell_assured_contract_design_physical_right`, with the supervisor's contract given by the
hand-written proof `Supervisor.contract_of_design`. So the links keep `9/100` m from every obstacle
at every `t ≥ 0` (s), the supervisor never faults, and at the finish the tool is within
`219/5000` m of the goal's tool position. A design statement, not from MLS. -/
theorem demo_assured_contract_physical_right :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsPayloadRightAt 80 2 0 0 0 demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    have h := demoMotion_follows_of (δ := 3 / 100) (by norm_num) t
    refine ⟨h.1.hasDerivWithinAt, h.2.1.hasDerivWithinAt, fun i => by simp, ?_⟩
    have e := h.2.2.2
    simp only [Pi.zero_apply, add_zero] at e
    rw [Pi.zero_apply, sub_zero, cellPayloadRobot, cellPayloadArm_zero]
    simp only [Nat.cast_zero, zero_mul]
    exact e
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_contract_design_physical_right le_rfl le_rfl
    le_rfl (by norm_num) (Supervisor.contract_of_design Instances.params)
    (demo_isCellRun_of (by norm_num) (by norm_num)).openCellParams_of_cellParams htrack
    demo_continuousOn (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

/-- **A payload held by friction meets the hypotheses of the payload form.** The idle run (no
request, the supervisor waits at home) with the arm at rest at home carrying a point mass of
`1/20` kg at the tool point, held by a friction torque equal to the payload's weight torque,
`f = −(1/20) · toolGravity(home)` (at most `1/2` N m in every joint), meets every hypothesis of
`cell_assured_contract_design_physical_right` with `m = 1/20` kg, `f_c = 1/2` N m and `f_v = 0`
(`1080/20 + (27/2)(1/2) ≤ 192`), with the supervisor's contract given by the hand-written proof
`Supervisor.contract_of_design`. So the links keep `9/100` m from every obstacle at every
`t ≥ 0` (s) and the supervisor never faults. A satisfying instance with a positive payload (at
rest); a design statement, not from MLS. -/
theorem hold_assured_contract_physical_right :
    (∀ t : ℝ, 0 ≤ t → sceneClear (DegPoint.toRad Instances.params.home)) ∧
    (∀ k, (idleState k).sup.faulted = false ∧ (idleState k).sup.age < 25) := by
  set θ := DegPoint.toRad Instances.params.home with hθ
  have hg : ∀ i, |((1 / 20 : ℝ) • toolGravity θ) i| ≤ 1 / 2 := by
    have hR : |17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)| ≤ 817 / 1000 := by
      have := Real.neg_one_le_cos (θ 1)
      have := Real.cos_le_one (θ 1)
      have := Real.neg_one_le_cos (θ 1 + θ 2)
      have := Real.cos_le_one (θ 1 + θ 2)
      rw [abs_le]; constructor <;> linarith
    have hc := Real.abs_cos_le_one (θ 1 + θ 2)
    intro i
    fin_cases i <;> simp only [toolGravity, Pi.smul_apply, smul_eq_mul] <;> simp
    · rw [abs_of_pos (by norm_num : (0 : ℝ) < 981 / 100)]
      linarith
    · rw [abs_of_pos (by norm_num : (0 : ℝ) < 981 / 100),
        abs_of_pos (by norm_num : (0 : ℝ) < 49 / 125)]
      linarith
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsPayloadRightAt 80 2 (1 / 20) (1 / 2) 0 (fun _ => θ) 0 0
        (fun _ => -((1 / 20 : ℝ) • toolGravity θ))
        (DegPoint.toRad (idleState (k + 1)).src) (DegPoint.toRad (idleState (k + 1)).goal)
        ((idleState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    simp only [idleState, CellState.init]
    refine ⟨hasDerivWithinAt_const _ _ _, hasDerivWithinAt_const _ _ _, fun i => ?_, ?_⟩
    · simpa [abs_neg] using hg i
    · simp only [Control.RobotSystem.computedTorque, Control.computedTorqueAlong]
      rw [moveRef_self, moveRefDeriv_self, moveRefDeriv2_self, ← hθ]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, zero_add, sub_self, sub_neg_eq_add]
      rw [show (cellPayloadRobot (1 / 20)).N θ 0 = (cellPayloadArm (1 / 20)).N θ 0 from rfl,
        cellPayloadArm_N (by norm_num)]
      rfl
  have h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0
      ((fun _ => θ) 0) ((0 : ℝ → Fin 3 → ℝ) 0) := by
    intro i
    simp only [hθ, sub_self, Pi.zero_apply, mul_zero, add_zero, abs_zero]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨hclear, hfault, -, -⟩ := cell_assured_contract_design_physical_right (m := 1 / 20)
    (fc := 1 / 2) (fv := 0) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (Supervisor.contract_of_design Instances.params) (idle_isCellRun _ _ _) htrack
    (by simpa using (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (θ, (0 : Fin 3 → ℝ))) (Ici 0))) h0
  exact ⟨hclear, hfault⟩

end Cell.Loop
end RoboLean
