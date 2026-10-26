import RoboLean.Control.RobotPDControl

/-!
# The `control` operation on robots (MLS §6.5.2, pp. 305–306, Figure 6.12)

**What MLS states (pp. 303–306).** A *robot* is a dynamical system
`M(q) q̈ + C(q, q̇) q̇ + N(q, q̇) = F` with inputs (the desired position `x_d` and the force `F_d`
to be applied) and outputs (the position `x` and the measured force `F`) (p. 303). "The *control*
operation is responsible for assigning a controller to a robot. It is also responsible for creating
a new robot with attributes that properly represent the controlled robot. The attributes of the
created robot are completely determined by the individual controller. For most controllers, the
current state of the controlled robot is equivalent to the current state of the uncontrolled robot.
Sending a desired trajectory to a controlled robot would cause the controller to buffer the data and
attempt to follow that trajectory" (p. 305). "At one extreme, a controller which compensates for the
inertia of the robot would set the dynamic attributes of the controlled robot to zero ... At the
other end of the spectrum, a controller may make no attempt to compensate for the inertia of a
robot, in which case it should pass the dynamic attributes on to the next higher level" (pp.
305–306). Example 6.7 (pp. 308–310) uses PD control at the lowest level, a feedforward controller
("computed torque with no error correction") in the middle, and computed torque at the top, which
"results in a system with linear error dynamics".

**Formalized.**

* `RobotController R`: a law `u(t, x, ẋ, ẍ, F_c)` giving the force applied to the robot `R` from its
  state, its acceleration and the force command `F_c` arriving from the level above, together with
  the attributes `(M̃, C̃, Ñ)` of the controlled robot at each time, with the defining identity
  (`represents`): the force the environment must supply to keep a motion is the same for `R` driven
  by `u` and for the controlled robot driven by `F_c`. `RobotSystem.control R K t` is the controlled
  robot (`control_equations_iff`: for every external force `F_e`, `R` under the law is the
  controlled robot under the command). Same configuration space and state as `R` (p. 305: "the
  current state of the controlled robot is equivalent to the current state of the uncontrolled
  robot"); the desired trajectory is a parameter of the law.
* The attributes are determined by the law up to the split of `C̃ ẋ + Ñ` between its two terms
  (`control_M_eq_of_law`, `control_CN_eq_of_law`); a law that does not use the acceleration leaves
  the inertia unchanged (`control_M_eq_self`), so the "zero attributes" extreme needs the
  acceleration (or a force measurement) in the law.
* The two extremes of p. 305: `passThrough` (no compensation: the attributes of `R`) and
  `inertiaCompensation` (attributes zero; the law `F = M ẍ + C ẋ + N + F_c` uses the acceleration).
* Feedback laws without acceleration, `feedbackController u` (`F = u(t, x, ẋ) + F_c`, attributes
  `(M, C, N − u)`), which keep `M`, `C` and so the skew property; its closed loop under a command is
  the robot's first-order system under `u + F_c` (`closedLoop_feedbackController`). Instances: PD
  with gravity compensation (`pdController`, attributes `(M, C, K_v ẋ + K_p (x − x_d))`, Proposition
  4.9 for the controlled robot, `globallyAsymptoticallyStableAt_control_pd`) and computed torque
  (`computedTorqueController`: under the command `F_c` the controlled robot obeys
  `M(x)(ë + K_v ė + K_p e) = F_c + F_e`, linear error dynamics for `F_c = F_e = 0` and `M` positive
  definite; Proposition 4.8 for the controlled robot, `computedTorqueController_tracking`).

Inputs and outputs other than the force command are not modeled; nothing here concerns sampling,
model error or actuator limits. Configurations `Fin p → ℝ`, state `(x, ẋ)`.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace Control

namespace RobotSystem

variable {p : ℕ}

/-- **The robot with zero dynamic attributes (MLS p. 305: a controller "would set the dynamic
attributes of the controlled robot to zero"):** `M = 0`, `C = 0`, `N = 0`. -/
instance : Zero (RobotSystem p) :=
  ⟨⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩

/-- The zero robot's inertia is `0` (MLS p. 305). -/
@[simp] theorem zero_M (x : Fin p → ℝ) : (0 : RobotSystem p).M x = 0 :=
  rfl

/-- The zero robot's Coriolis matrix is `0` (MLS p. 305). -/
@[simp] theorem zero_C (x v : Fin p → ℝ) : (0 : RobotSystem p).C x v = 0 :=
  rfl

/-- The zero robot's `N` is `0` (MLS p. 305). -/
@[simp] theorem zero_N (x v : Fin p → ℝ) : (0 : RobotSystem p).N x v = 0 :=
  rfl

/-- **The zero robot has the skew property (MLS p. 300):** along every motion the derivative of the
constant `0` is `0`, and `0 − 2·0` is skew-symmetric. -/
theorem zero_hasSkewProperty : (0 : RobotSystem p).HasSkewProperty := by
  intro x x' t Md _ hMd
  have h0 : Md = 0 := by
    ext i j
    exact (hMd i j).unique (hasDerivAt_const t 0)
  simp [h0]

end RobotSystem

/-- **A controller for a robot and the robot it creates (MLS printed p. 305, Figure 6.12, "The
control operation is responsible for assigning a controller to a robot. It is also responsible for
creating a new robot with attributes that properly represent the controlled robot").** The law
`u(t, x, ẋ, ẍ, F_c)` is the force applied to `R` at time `t` from the state `(x, ẋ)`, the
acceleration `ẍ` and the force command `F_c` of the level above (the desired trajectory, buffered by
the controller, is a parameter of the law); `attributes t` are the dynamic attributes `(M̃, C̃, Ñ)`
of the controlled robot at time `t`. The identity `represents` says that for every motion the force
the environment must supply is the same for `R` driven by `u` and for the controlled robot driven by
`F_c`. -/
structure RobotController {p : ℕ} (R : RobotSystem p) where
  /-- The control law `u(t, x, ẋ, ẍ, F_c)`: the force applied to the robot (MLS Figure 6.12). -/
  law : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ
  /-- The attributes `(M̃, C̃, Ñ)` of the controlled robot at each time (MLS p. 305). -/
  attributes : ℝ → RobotSystem p
  /-- The attributes represent the controlled robot (MLS p. 305): equal residual forces. -/
  represents : ∀ t x v a Fc, R.M x *ᵥ a + R.C x v *ᵥ v + R.N x v - law t x v a Fc =
    (attributes t).M x *ᵥ a + (attributes t).C x v *ᵥ v + (attributes t).N x v - Fc

namespace RobotSystem

variable {p : ℕ} (R : RobotSystem p)

/-- **The `control` operation (MLS printed p. 305):** the robot created by assigning the controller
`K` to the robot `R`, at time `t` (its attributes are "completely determined by the individual
controller"). -/
def control (K : RobotController R) (t : ℝ) : RobotSystem p :=
  K.attributes t

/-- **The controlled robot represents the robot under its controller (MLS p. 305, Figure 6.12).** At
every time, state, acceleration, command `F_c` and external force `F_e`: `R`'s equations of motion
with the force `u + F_e` hold exactly when the controlled robot's equations with the force
`F_c + F_e` hold. -/
theorem control_equations_iff (K : RobotController R) (t : ℝ) (x v a Fc Fe : Fin p → ℝ) :
    R.M x *ᵥ a + R.C x v *ᵥ v + R.N x v = K.law t x v a Fc + Fe ↔
      (R.control K t).M x *ᵥ a + (R.control K t).C x v *ᵥ v + (R.control K t).N x v = Fc + Fe := by
  rw [← sub_eq_iff_eq_add', K.represents t x v a Fc, sub_eq_iff_eq_add']
  rfl

/-- Subtracting the residual identity at zero acceleration isolates the inertia term (MLS p. 305):
`M̃ ẍ = M ẍ − (u(ẍ) − u(0))`. -/
private theorem residual_sub_zero (K : RobotController R) (t : ℝ) (x a : Fin p → ℝ) :
    R.M x *ᵥ a - (K.law t x 0 a 0 - K.law t x 0 0 0) = (R.control K t).M x *ᵥ a := by
  have h1 := K.represents t x 0 a 0
  have h0 := K.represents t x 0 0 0
  simp only [Matrix.mulVec_zero, zero_add, sub_zero] at h1 h0
  rw [control]
  linear_combination (exp := 1) h1 - h0

/-- **The law determines the controlled inertia (MLS p. 305, "completely determined by the
individual controller"):** two controllers with the same law give the same `M̃`. -/
theorem control_M_eq_of_law (K K' : RobotController R) (h : K.law = K'.law) (t : ℝ)
    (x : Fin p → ℝ) : (R.control K t).M x = (R.control K' t).M x := by
  apply Matrix.ext_iff_mulVec.mpr
  intro a
  have key := residual_sub_zero R K t x a
  have key' := residual_sub_zero R K' t x a
  rw [h] at key
  rw [← key, ← key']

/-- **The law determines `C̃ ẋ + Ñ` (MLS p. 305):** two controllers with the same law give the same
`C̃(x, ẋ) ẋ + Ñ(x, ẋ)`; the split between the two terms is not determined (and the skew property of
`(M̃, C̃)` depends on it). -/
theorem control_CN_eq_of_law (K K' : RobotController R) (h : K.law = K'.law) (t : ℝ)
    (x v : Fin p → ℝ) :
    (R.control K t).C x v *ᵥ v + (R.control K t).N x v =
      (R.control K' t).C x v *ᵥ v + (R.control K' t).N x v := by
  have h1 := K.represents t x v 0 0
  have h2 := K'.represents t x v 0 0
  rw [h] at h1
  simp only [Matrix.mulVec_zero, zero_add, sub_zero] at h1 h2
  rw [control, control]
  linear_combination (exp := 1) h2 - h1

/-- **A law that does not use the acceleration cannot change the inertia (MLS pp. 305–306, the
"middle of this range"):** if `u(t, x, ẋ, ẍ, F_c)` does not depend on `ẍ`, the controlled robot has
the inertia of `R`. Setting the attributes to zero (p. 305) therefore needs the acceleration, or a
force measurement, in the law. -/
theorem control_M_eq_self (K : RobotController R)
    (hK : ∀ t x v a a' Fc, K.law t x v a Fc = K.law t x v a' Fc) (t : ℝ) (x : Fin p → ℝ) :
    (R.control K t).M x = R.M x := by
  apply Matrix.ext_iff_mulVec.mpr
  intro a
  rw [← residual_sub_zero R K t x a, hK t x 0 a 0 0, sub_self, sub_zero]

/-- **No compensation (MLS p. 306: a controller that makes "no attempt to compensate for the inertia
of a robot ... should pass the dynamic attributes on to the next higher level"):** the command is
applied as it is and the attributes are those of `R`. -/
def passThrough : RobotController R where
  law := fun _ _ _ _ Fc => Fc
  attributes := fun _ => R
  represents := by
    intro t x v a Fc
    rfl

/-- The robot controlled by `passThrough` is `R` (MLS p. 306). -/
theorem control_passThrough (t : ℝ) : R.control R.passThrough t = R :=
  rfl

/-- **Full compensation (MLS p. 305: "a controller which compensates for the inertia of the robot
would set the dynamic attributes of the controlled robot to zero"):** the law
`F = M(x) ẍ + C(x, ẋ) ẋ + N(x, ẋ) + F_c` uses the acceleration; the controlled robot has zero
attributes, a force generator for the levels above (MLS p. 309, "two Cartesian force generators").
-/
def inertiaCompensation : RobotController R where
  law := fun _ x v a Fc => R.M x *ᵥ a + R.C x v *ᵥ v + R.N x v + Fc
  attributes := fun _ => 0
  represents := by
    intro t x v a Fc
    simp

/-- The robot controlled by `inertiaCompensation` is the zero robot (MLS p. 305). -/
theorem control_inertiaCompensation (t : ℝ) : R.control R.inertiaCompensation t = 0 :=
  rfl

/-- **A feedback law without acceleration (MLS p. 306, controllers in "the middle of this range"):**
`F = u(t, x, ẋ) + F_c`; the controlled robot keeps `M` and `C` and has `Ñ = N − u`. -/
def feedbackController (u : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ) : RobotController R where
  law := fun t x v _ Fc => u t x v + Fc
  attributes := fun t => ⟨R.M, R.C, fun x v => R.N x v - u t x v⟩
  represents := by
    intro t x v a Fc
    show R.M x *ᵥ a + R.C x v *ᵥ v + R.N x v - (u t x v + Fc) =
      R.M x *ᵥ a + R.C x v *ᵥ v + (R.N x v - u t x v) - Fc
    abel

/-- **A feedback law keeps the skew property (MLS p. 300 for the controlled robot):** the controlled
robot of `feedbackController u` has the inertia and Coriolis matrix of `R`, so it has the skew
property when `R` has. -/
theorem control_feedbackController_hasSkewProperty (hR : R.HasSkewProperty)
    (u : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ) (t : ℝ) :
    (R.control (R.feedbackController u) t).HasSkewProperty := by
  exact hR

/-- **The closed loop of a controlled robot under a command law (MLS Figure 6.12):** the first-order
system (MLS eq. (4.31)) of the controlled robot at time `t` under the command `F_c(t, x, ẋ)`. -/
def closedLoop (K : RobotController R) (Fc : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ) :
    ℝ → (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ) :=
  fun t z => (R.control K t).field Fc t z

/-- **The closed loop of a feedback controller is the robot under the law plus the command (MLS pp.
305–306):** `closedLoop (feedbackController u) F_c = field (u + F_c)`. -/
theorem closedLoop_feedbackController (u Fc : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ) :
    R.closedLoop (R.feedbackController u) Fc = R.field fun t x v => u t x v + Fc t x v := by
  funext t z
  simp only [closedLoop, control, feedbackController, field]
  congr 2
  abel

/-- **PD control with gravity compensation as a controller (MLS Example 6.7, p. 308, "simple PD
control laws attached directly to the individual fingers"; Proposition 4.9, p. 193):** the feedback
law `pdCompensatedTorque` (`F = N − K_v ẋ − K_p (x − x_d)`) plus the command. -/
def pdController (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd : Fin p → ℝ) : RobotController R :=
  R.feedbackController (R.pdCompensatedTorque Kp Kv xd)

/-- **The attributes of the PD-controlled robot (MLS p. 308, the PD controllers "mimic the stiffness
provided by muscle coactivation"):** `M̃ = M`, `C̃ = C`, `Ñ = K_v ẋ + K_p (x − x_d)`. -/
theorem control_pdController_N (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd : Fin p → ℝ) (t : ℝ)
    (x v : Fin p → ℝ) :
    (R.control (R.pdController Kp Kv xd) t).N x v = Kv *ᵥ v + Kp *ᵥ (x - xd) := by
  change R.N x v - (R.N x v - Kv *ᵥ v - Kp *ᵥ (x - xd)) = _
  abel

/-- **MLS Proposition 4.9 (p. 193) for the PD-controlled robot under zero command (p. 301 for
robots):** with the hypotheses of `globallyAsymptoticallyStableAt_pdCompensatedTorque`, the set
point `(x_d, 0)` of the controlled robot's closed loop with `F_c = 0` is globally asymptotically
stable at every `t₀ ≥ 0`. -/
theorem globallyAsymptoticallyStableAt_control_pd (hM : ∀ q, (R.M q).PosDef)
    (hMc : Continuous R.M) (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    (hMu : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {xd : Fin p → ℝ}
    {φ : ℝ → (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ)}
    (hφ : Stability.HasFlow (R.pdClosedLoop Kp Kv xd) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt
      (R.closedLoop (R.pdController Kp Kv xd) fun _ _ _ => 0) (xd, 0) t₀ := by
  rw [pdController, closedLoop_feedbackController]
  simp only [add_zero]
  exact R.globallyAsymptoticallyStableAt_pdCompensatedTorque hM hMc hMd hskew hMu hKp hKv hφ ht₀

/-- **Computed torque as a controller (MLS Example 6.7, p. 309, "we use a computed torque controller
at the very highest level"; eq. (4.49), p. 191):** the feedback law `computedTorque` plus the
command. -/
def computedTorqueController (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd xd' xd'' : ℝ → Fin p → ℝ) :
    RobotController R :=
  R.feedbackController (R.computedTorque Kp Kv xd xd' xd'')

/-- **Computed torque "results in a system with linear error dynamics" (MLS p. 310):** the robot
controlled by computed torque obeys, under the command `F_c` and an external force `F_e`,
`M(x)(ë + K_v ė + K_p e) = F_c + F_e` with `e = x − x_d`, `ė = ẋ − ẋ_d`, `ë = ẍ − ẍ_d`; for
`F_c = F_e = 0` and `M(x)` positive definite this is `ë + K_v ė + K_p e = 0`. -/
theorem control_computedTorque_equations_iff (Kp Kv : Matrix (Fin p) (Fin p) ℝ)
    (xd xd' xd'' : ℝ → Fin p → ℝ) (t : ℝ) (x v a Fc Fe : Fin p → ℝ) :
    (R.control (R.computedTorqueController Kp Kv xd xd' xd'') t).M x *ᵥ a +
        (R.control (R.computedTorqueController Kp Kv xd xd' xd'') t).C x v *ᵥ v +
        (R.control (R.computedTorqueController Kp Kv xd xd' xd'') t).N x v = Fc + Fe ↔
      R.M x *ᵥ (a - xd'' t + Kv *ᵥ (v - xd' t) + Kp *ᵥ (x - xd t)) = Fc + Fe := by
  change R.M x *ᵥ a + R.C x v *ᵥ v + (R.N x v - (R.M x *ᵥ (xd'' t - Kv *ᵥ (v - xd' t) -
    Kp *ᵥ (x - xd t)) + R.C x v *ᵥ v + R.N x v)) = Fc + Fe ↔ _
  rw [show R.M x *ᵥ a + R.C x v *ᵥ v + (R.N x v - (R.M x *ᵥ (xd'' t - Kv *ᵥ (v - xd' t) -
    Kp *ᵥ (x - xd t)) + R.C x v *ᵥ v + R.N x v)) =
      R.M x *ᵥ (a - xd'' t + Kv *ᵥ (v - xd' t) + Kp *ᵥ (x - xd t)) by
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
    abel]

/-- **MLS Proposition 4.8 (p. 192) for the robot controlled by computed torque under zero command
(Example 6.7, p. 310):** with `M(x)` positive definite for every `x` and `K_p`, `K_v` positive
definite, there are `m, α > 0` such that for every desired trajectory with `ẋ_d = x_d'`,
`ẍ_d = x_d''` every solution from `t₀ ≥ 0` of the controlled robot's closed loop with `F_c = 0`
satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀`. -/
theorem computedTorqueController_tracking (hM : ∀ q, (R.M q).PosDef)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ z : ℝ → (Fin p → ℝ) × (Fin p → ℝ),
      Stability.IsSolution
        (R.closedLoop (R.computedTorqueController Kp Kv xd xd' xd'') fun _ _ _ => 0) t₀ z →
      ∀ t, t₀ ≤ t → ‖((z t).1 - xd t, (z t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((z t₀).1 - xd t₀, (z t₀).2 - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := R.computedTorque_tracking hM hKp hKv
  refine ⟨m, hm, α, hα, fun {xd xd' xd''} hd hd' t₀ ht₀ z hz => htrack hd hd' t₀ ht₀ z ?_⟩
  rw [computedTorqueController, closedLoop_feedbackController] at hz
  simpa only [add_zero] using hz

end RobotSystem

/-! ### The proportional force loop of MLS p. 302 -/

section ForceLoop

variable {p : ℕ}

/-- **MLS printed p. 302: "For `α ≠ 0`, this controller only satisfies `f = f_d` if
`f = f_d = 0`"**, for the proportional force regulator `f = α(f − f_d)` of a "robot" which only
applies forces; it holds for every `α` (the printed `α ≠ 0` is not needed). -/
theorem proportionalForceLoop_eq_desired_iff (α : ℝ) (f fd : Fin p → ℝ) :
    (f = α • (f - fd) ∧ f = fd) ↔ (f = 0 ∧ fd = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [h2, sub_self, smul_zero] at h1
    exact ⟨h2.trans h1, h1⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

/-- **The solutions of the proportional force loop (MLS p. 302, "an algebraic loop"):** for `α ≠ 1`,
`f = α(f − f_d)` has exactly the solution `f = (α / (α − 1)) f_d`, which differs from `f_d` unless
`f_d = 0`; the loop is solvable, but not by the desired force. -/
theorem proportionalForceLoop_iff {α : ℝ} (hα : α ≠ 1) (f fd : Fin p → ℝ) :
    f = α • (f - fd) ↔ f = (α / (α - 1)) • fd := by
  have h1 : α - 1 ≠ 0 := sub_ne_zero.mpr hα
  constructor
  · intro h
    have h2 : (α - 1) • f = α • fd := by
      rw [sub_smul, one_smul]
      nth_rewrite 2 [h]
      rw [smul_sub]
      abel
    rw [← smul_right_inj h1, h2, smul_smul, mul_div_cancel₀ _ h1]
  · intro h
    subst h
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring

/-- **The proportional force loop with `α = 1` has no solution for `f_d ≠ 0` (MLS p. 302, "an
algebraic loop which is never satisfied"):** `f = f − f_d` holds exactly when `f_d = 0`. -/
theorem proportionalForceLoop_one_iff (f fd : Fin p → ℝ) :
    f = (1 : ℝ) • (f - fd) ↔ fd = 0 := by
  rw [one_smul]
  constructor
  · intro h
    have h' : f - (f - fd) = 0 := by rw [← h, sub_self]
    simpa using h'
  · intro h
    simp [h]

end ForceLoop

end Control
end RoboLean
