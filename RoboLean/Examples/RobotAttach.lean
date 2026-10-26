import RoboLean.Control.RobotAttach

/-!
# The hierarchical controller of a two-fingered hand, as a toy (MLS Example 6.7, pp. 308–310)

MLS Example 6.7 (pp. 308–310, Figures 6.14–6.15) builds the controller of a two-fingered hand
grasping a box from the `attach` and `control` operations (pp. 303–306): PD control at each
finger, the fingers attached as a Cartesian unit, a feedforward controller that turns them into
"two Cartesian force generators" (p. 309), the force generators attached to the box, which gives
"a robot with the dynamic properties of the box, but capable of motion due to the actuation in the
fingers" (p. 309), and computed torque at the top, which "results in a system with linear error
dynamics" (p. 310).

**The toy here is one-dimensional.** Each finger is a prismatic robot with one joint, inertia
`[m]`, no Coriolis or gravity terms, whose joint coordinate is already its Cartesian fingertip
position (`prismaticFinger`); the box is a robot with one coordinate and inertia `[m_b]`
(`boxRobot`). Both fingertips touch the box at its coordinate, `h(θ, x) = θ − (x, x) = 0`. The
levels:

1. PD control at each finger (`pdFinger`);
2. the two controlled fingers as one robot, `RobotSystem.stack`, with inertia `diag(m₁, m₂)`
   (`fingerStack`, `fingerStack_M`);
3. the fingers attached to the zero payload as a Cartesian unit (`J = G = I`), which is the stack
   again (`cartesianFingers`, `cartesianFingers_eq`);
4. full inertia compensation: the zero robot, "two Cartesian force generators" (`forceGenerators`,
   `forceGenerators_eq_zero`);
5. the force generators attached to the box (`handTop`), which is the box robot (`handTop_eq`);
   the constraint is holonomic (`boxAttach_isHolonomic`), a box force `F` is commanded as
   `(F/2, F/2)` and produced (`boxAttach_torqueCommand`, `boxAttach_effectiveForce_torqueCommand`),
   and the box velocity read from the fingers is `(ẋ₁ + ẋ₂)/2` (`box_velocity_of_constraint`);
6. computed torque at the top: exponential tracking (`handTop_computedTorque_tracking`), with the
   positive definiteness and the skew property of the top robot obtained from those of its parts
   (`handTop_M_posDef`, `handTop_hasSkewProperty`).

These are instances of the general operations, not separate results; nothing here models a
physical hand, a physical box or contact. Lean index `0` is the book's first finger.
-/

noncomputable section

open Matrix Filter Topology
open RoboLean.MapJacobian RoboLean.Composite

namespace RoboLean.Examples

open Control

/-- **A finger of the toy hand of MLS Example 6.7 (pp. 308–310): a prismatic robot with one joint
(MLS p. 303),** inertia `M = [m]`, `C = 0`, `N = 0`; its joint coordinate is the Cartesian position
of its fingertip. -/
def prismaticFinger (m : ℝ) : RobotSystem 1 :=
  ⟨fun _ => !![m], fun _ _ => 0, fun _ _ => 0⟩

/-- **The box of the toy hand of MLS Example 6.7 (pp. 308–310), as a robot with one coordinate
(MLS p. 303):** inertia `M = [m_b]`, `C = 0`, `N = 0`. -/
def boxRobot (mb : ℝ) : RobotSystem 1 :=
  ⟨fun _ => !![mb], fun _ _ => 0, fun _ _ => 0⟩

/-- **Level 1 of MLS Example 6.7 (p. 308, "simple PD control laws attached directly to the
individual fingers"; the `control` operation, p. 305):** the finger controlled by PD with gravity
compensation, gains `K_p`, `K_v` (`1 × 1` matrices) and set point `x_d`, at time `0` (the
attributes do not depend on time). -/
def pdFinger (m : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd : Fin 1 → ℝ) : RobotSystem 1 :=
  (prismaticFinger m).control ((prismaticFinger m).pdController Kp Kv xd) 0

/-- **The relabeling of the two one-joint fingers' joints as `Fin 2` (MLS p. 276, eq. (6.16)):**
finger `i`'s joint is joint `i`. -/
def fingerEquiv : (Σ _ : Fin 2, Fin 1) ≃ Fin 2 :=
  Equiv.sigmaUnique (Fin 2) fun _ => Fin 1

/-- **Level 2 of MLS Example 6.7 (p. 308): the two PD-controlled fingers as one robot**, the list
of fingers of the `attach` operation (p. 304) stacked block-diagonally (eq. (6.16), p. 276), finger
`0` with mass `m₁` and set point `x_{d1}`, finger `1` with `m₂` and `x_{d2}`, both with gains
`K_p`, `K_v`. -/
def fingerStack (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ) :
    RobotSystem 2 :=
  RobotSystem.stack fingerEquiv fun i : Fin 2 => pdFinger (![m₁, m₂] i) Kp Kv (![xd₁, xd₂] i)

/-- **The stacked fingers have the inertia `diag(m₁, m₂)` (MLS p. 276,
`M_f = diag(M_{f₁}, M_{f₂})`)**
at every configuration; PD control leaves each finger's inertia unchanged (p. 306). -/
theorem fingerStack_M (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ)
    (θ : Fin 2 → ℝ) : (fingerStack m₁ m₂ Kp Kv xd₁ xd₂).M θ = !![m₁, 0; 0, m₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fingerStack, RobotSystem.stack, stackMat, fingerEquiv, pdFinger, RobotSystem.control,
      RobotSystem.pdController, RobotSystem.feedbackController, prismaticFinger,
      Matrix.blockDiagonal'_apply]

/-- **The Cartesian constraint of level 3 of MLS Example 6.7 (p. 308, the fingers attached "as a
Cartesian unit"; the `attach` operation, pp. 304–305):** the fingertip coordinates are the payload
coordinates, `θ = x`, `J = I`, `G = I`, `Bd = 0`. -/
def cartesianAttach : AttachConstraint 2 2 :=
  ⟨id, fun _ => 1, fun _ => 1, fun _ _ => 0⟩

/-- **Attaching a robot with two joints to the zero payload through the Cartesian constraint gives
the robot back (MLS p. 305 with `J = G = I`):** `M̃ = M`, `C̃ = C`, `Ñ = N`. -/
theorem attach_cartesianAttach (F : RobotSystem 2) : F.attach 0 cartesianAttach = F := by
  obtain ⟨M, C, N⟩ := F
  simp only [RobotSystem.attach, cartesianAttach, AttachConstraint.fingerVelocity, effectiveMass,
    effectiveCoriolis, effectiveN, RobotSystem.zero_M, RobotSystem.zero_C, RobotSystem.zero_N,
    inv_one, transpose_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mulVec, id]

/-- **Level 3 of MLS Example 6.7 (p. 308): the fingers attached as a Cartesian unit**, the stack
attached to the zero payload through `cartesianAttach` (the `attach` operation, pp. 304–305). -/
def cartesianFingers (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ) :
    RobotSystem 2 :=
  (fingerStack m₁ m₂ Kp Kv xd₁ xd₂).attach 0 cartesianAttach

/-- **The Cartesian unit of the toy is the stack itself (MLS p. 305):** the fingertip coordinates
are the joint coordinates. -/
theorem cartesianFingers_eq (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ)
    (xd₁ xd₂ : Fin 1 → ℝ) :
    cartesianFingers m₁ m₂ Kp Kv xd₁ xd₂ = fingerStack m₁ m₂ Kp Kv xd₁ xd₂ :=
  attach_cartesianAttach _

/-- **Level 4 of MLS Example 6.7 (p. 309, "a feedforward controller ... computed torque with no
error correction"; the `control` operation, p. 305):** the Cartesian unit under full inertia
compensation, at time `0`. -/
def forceGenerators (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ) :
    RobotSystem 2 :=
  (cartesianFingers m₁ m₂ Kp Kv xd₁ xd₂).control
    (cartesianFingers m₁ m₂ Kp Kv xd₁ xd₂).inertiaCompensation 0

/-- **The fingers become "two Cartesian force generators" (MLS p. 309):** the robot of level 4 has
zero dynamic attributes (p. 305). -/
theorem forceGenerators_eq_zero (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ)
    (xd₁ xd₂ : Fin 1 → ℝ) : forceGenerators m₁ m₂ Kp Kv xd₁ xd₂ = 0 :=
  rfl

/-- **The grasp map of the toy box, `G = [1 1]` (MLS p. 305, `Gᵀ = −∂h/∂x`):** each fingertip
pushes the box along its coordinate. -/
def boxG : Matrix (Fin 1) (Fin 2) ℝ :=
  !![1, 1]

/-- **The constraint of level 5 of MLS Example 6.7 (p. 309, the force generators attached to the
box; the `attach` operation, pp. 304–305):** both fingertips at the box coordinate, `θ = σ(x) =
(x, x)`, from `h(θ, x) = θ − (x, x)`: `J = ∂h/∂θ = I`, `G = [1 1]` (`Gᵀ = −∂h/∂x`), and `Bd = 0`
since `J⁻¹ Gᵀ` is constant. -/
def boxAttach : AttachConstraint 2 1 :=
  ⟨fun x => ![x 0, x 0], fun _ => 1, fun _ => boxG, fun _ _ => 0⟩

/-- **Level 5 of MLS Example 6.7 (p. 309): the force generators attached to the box.** -/
def handTop (mb m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ) :
    RobotSystem 1 :=
  (forceGenerators m₁ m₂ Kp Kv xd₁ xd₂).attach (boxRobot mb) boxAttach

/-- **The top robot has the attributes of the box (MLS p. 309, "a robot with the dynamic properties
of the box, but capable of motion due to the actuation in the fingers"):** level 5 is `boxRobot`,
for every finger mass and gain. -/
theorem handTop_eq (mb m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ) :
    handTop mb m₁ m₂ Kp Kv xd₁ xd₂ = boxRobot mb := by
  simp only [handTop, forceGenerators_eq_zero, RobotSystem.attach, boxRobot, effectiveMass,
    effectiveCoriolis, effectiveN, RobotSystem.zero_M, RobotSystem.zero_C, RobotSystem.zero_N,
    boxAttach, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mulVec_zero]

/-- The constraint function `h(θ, x) = θ − (x, x)` of the toy box as a matrix on the composite
configuration `q = (x, θ₁, θ₂)` (MLS p. 304): `h(q) = A q`, `A = [[−1, 1, 0], [−1, 0, 1]]`. -/
def boxConstraintMatrix : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-1, 1, 0; -1, 0, 1]

/-- **The constraint of level 5 is holonomic (MLS p. 304, `h(θ, x) = 0`; p. 305, `J = ∂h/∂θ`,
`Gᵀ = −∂h/∂x`):** with the composite configuration `q = (x, θ)` relabeled by `finSumFinEquiv`
(payload first) and `h(q) = A q`, `A = [[−1, 1, 0], [−1, 0, 1]]`. -/
theorem boxAttach_isHolonomic :
    boxAttach.IsHolonomic finSumFinEquiv fun q => boxConstraintMatrix *ᵥ q := by
  have e0 : finSumFinEquiv (Sum.inl (0 : Fin 1)) = (0 : Fin (1 + 2)) := by decide
  have e1 : finSumFinEquiv (Sum.inr (0 : Fin 2)) = (1 : Fin (1 + 2)) := by decide
  have e2 : finSumFinEquiv (Sum.inr (1 : Fin 2)) = (2 : Fin (1 + 2)) := by decide
  have s0 : finSumFinEquiv.symm (0 : Fin (1 + 2)) = Sum.inl (0 : Fin 1) :=
    finSumFinEquiv.symm_apply_eq.mpr e0.symm
  have s1 : finSumFinEquiv.symm (1 : Fin (1 + 2)) = Sum.inr (0 : Fin 2) :=
    finSumFinEquiv.symm_apply_eq.mpr e1.symm
  have s2 : finSumFinEquiv.symm (2 : Fin (1 + 2)) = Sum.inr (1 : Fin 2) :=
    finSumFinEquiv.symm_apply_eq.mpr e2.symm
  intro x
  rw [jac_linear]
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;>
      simp [boxConstraintMatrix, boxAttach, Constrained.splitJoin, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, s0, s1, s2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boxConstraintMatrix, boxAttach, Constrained.colsSnd, e1, e2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boxConstraintMatrix, boxAttach, boxG, Constrained.colsFst, e0]

/-- `G Gᵀ = [2]` for the toy box (MLS p. 301). -/
private lemma boxG_mul_transpose : boxG * boxGᵀ = !![2] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [boxG, Matrix.mul_apply, Fin.sum_univ_two]

/-- The right pseudo-inverse of `G = [1 1]` is `[1/2; 1/2]` (MLS p. 301, `G⁺ = Gᵀ(GGᵀ)⁻¹`). -/
private lemma rightPinv_boxG : rightPinv boxG = !![1 / 2; 1 / 2] := by
  have hinv : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![1 / 2] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i
    fin_cases j
    norm_num
  rw [rightPinv, boxG_mul_transpose, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boxG, Matrix.mul_apply]

/-- **The force command of Figure 6.11 for the toy box (MLS p. 306, `τ_d = Jᵀ G⁺ F_d`, eq. (6.36),
p. 301, with `f_N = 0`):** a box force `F` is commanded as `F/2` at each finger. -/
theorem boxAttach_torqueCommand (x F : Fin 1 → ℝ) :
    boxAttach.torqueCommand x F = ![F 0 / 2, F 0 / 2] := by
  simp only [AttachConstraint.torqueCommand, graspTorque, boxAttach, rightPinv_boxG,
    transpose_one, Matrix.one_mulVec, add_zero]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct] <;> ring

/-- `G = [1 1]` is onto (MLS p. 301). -/
private lemma boxG_surjective : Function.Surjective boxG.mulVec := fun y =>
  ⟨![y 0, 0], by ext i; fin_cases i; simp [boxG, Matrix.mulVec, dotProduct]⟩

/-- **The commanded box force is produced (MLS Figure 6.11, p. 306):** `G J⁻ᵀ τ_d = F` for the toy
box, from `effectiveForce_torqueCommand`. -/
theorem boxAttach_effectiveForce_torqueCommand (x F : Fin 1 → ℝ) :
    effectiveForce (boxAttach.J x) (boxAttach.G x) (boxAttach.torqueCommand x F) = F :=
  boxAttach.effectiveForce_torqueCommand (by simp [boxAttach]) boxG_surjective F

/-- **Reading the box velocity from the fingers (MLS p. 310, `ẋ_b ← G⁺ᵀ ẋ_f`):** if the fingertip
velocities `θ'` and the box velocity `v` obey the grasp constraint `θ' = Gᵀ v` (`J = I`), then
`v = (θ'₁ + θ'₂)/2`, from `velocity_eq_of_constraint`. -/
theorem box_velocity_of_constraint {v : Fin 1 → ℝ} {θ' : Fin 2 → ℝ}
    (h : (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ θ' = boxGᵀ *ᵥ v) : v 0 = (θ' 0 + θ' 1) / 2 := by
  have hv := AttachConstraint.velocity_eq_of_constraint boxG_surjective h
  rw [hv, rightPinv_boxG, Matrix.one_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The finger velocity of the toy box constraint is `(ẋ, ẋ)` (MLS p. 278, `θ̇ = J⁻¹ Gᵀ ẋ`). -/
private lemma boxAttach_fingerVelocity (x v : Fin 1 → ℝ) :
    boxAttach.fingerVelocity x v = ![v 0, v 0] := by
  ext i
  fin_cases i <;> simp [AttachConstraint.fingerVelocity, boxAttach, boxG, Matrix.mulVec,
    dotProduct]

/-- The box robot's inertia is positive definite for `m_b > 0` (MLS Lemma 4.2(1), p. 171). -/
private lemma boxRobot_M_posDef {mb : ℝ} (hmb : 0 < mb) (x : Fin 1 → ℝ) :
    ((boxRobot mb).M x).PosDef := by
  have e : (boxRobot mb).M x = Matrix.diagonal fun _ => mb := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [e]
  exact Matrix.PosDef.diagonal fun _ => hmb

/-- A robot with constant inertia has the derivative `0` along every motion (MLS p. 300). -/
private lemma eq_zero_of_hasDerivAt_const {k : ℕ} {M₀ : Matrix (Fin k) (Fin k) ℝ}
    {Md : Matrix (Fin k) (Fin k) ℝ} {t : ℝ}
    (hMd : ∀ i j, HasDerivAt (fun _ : ℝ => M₀ i j) (Md i j) t) :
    Md = 0 := by
  ext i j
  exact (hMd i j).unique (hasDerivAt_const t _)

/-- The box robot has the skew property: constant `M`, `C = 0` (MLS p. 300). -/
private lemma boxRobot_hasSkewProperty (mb : ℝ) : (boxRobot mb).HasSkewProperty := by
  intro x x' t Md _ hMd
  have h0 := eq_zero_of_hasDerivAt_const (M₀ := !![mb]) hMd
  subst h0
  simp [boxRobot]

/-- **The top robot's inertia is positive definite (MLS Lemma 6.1(1), p. 279, for `attach`, from
the payload):** for `m_b > 0`, by `attach_M_posDef` with the box's inertia positive definite and
the force generators' inertia `0` positive semidefinite. -/
theorem handTop_M_posDef {mb : ℝ} (hmb : 0 < mb) (m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ)
    (xd₁ xd₂ : Fin 1 → ℝ) (x : Fin 1 → ℝ) : ((handTop mb m₁ m₂ Kp Kv xd₁ xd₂).M x).PosDef :=
  RobotSystem.attach_M_posDef boxAttach (boxRobot_M_posDef hmb) (fun _ => Matrix.PosSemidef.zero) x

/-- **The top robot has the skew property (MLS Lemma 6.1(2), p. 279, for `attach`; p. 300):** by
`attach_hasSkewProperty`, with the force generators' inertia `0`, the box's constant inertia, the
finger motion `σ(x(s)) = (x(s), x(s))` with velocity `J⁻¹ Gᵀ ẋ`, and `Bd = 0` the rate of the
constant `J⁻¹ Gᵀ`. -/
theorem handTop_hasSkewProperty (mb m₁ m₂ : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ)
    (xd₁ xd₂ : Fin 1 → ℝ) : (handTop mb m₁ m₂ Kp Kv xd₁ xd₂).HasSkewProperty := by
  refine RobotSystem.attach_hasSkewProperty (F := forceGenerators m₁ m₂ Kp Kv xd₁ xd₂)
    (P := boxRobot mb) (A := boxAttach) (fun _ => Matrix.isSymm_zero)
    (fun _ => ⟨0, fun _ _ => hasDerivAt_const _ _⟩) (fun _ => ⟨0, fun _ _ => hasDerivAt_const _ _⟩)
    (boxRobot_hasSkewProperty mb) RobotSystem.zero_hasSkewProperty ?_ ?_
  · intro x x' t hx
    rw [boxAttach_fingerVelocity]
    refine hasDerivAt_pi.mpr fun i => ?_
    have h0 := hasDerivAt_pi.mp hx 0
    fin_cases i <;> simpa [boxAttach] using h0
  · intro x x' t _ i j
    show HasDerivAt (fun _ => ((1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * boxGᵀ) i j) 0 t
    exact hasDerivAt_const t _

/-- **Level 6 of MLS Example 6.7 (p. 309, "we use a computed torque controller at the very highest
level"; p. 310, "linear error dynamics"): exponential tracking of the box, every hypothesis
discharged.** For `m_b > 0`, any finger masses, gains and set points, and the top-level gains
`K_p = K_v = I`, there are `m, α > 0` such that for every desired box trajectory with
`ẋ_d = x_d'`, `ẍ_d = x_d''` every solution from `t₀ ≥ 0` of the top robot's closed loop under
computed torque with zero command satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖`
for `t ≥ t₀` (Proposition 4.8, p. 192, via `computedTorqueController_tracking`). -/
theorem handTop_computedTorque_tracking {mb : ℝ} (hmb : 0 < mb) (m₁ m₂ : ℝ)
    (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ) (xd₁ xd₂ : Fin 1 → ℝ) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin 1 → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ),
      Stability.IsSolution ((handTop mb m₁ m₂ Kp Kv xd₁ xd₂).closedLoop
        ((handTop mb m₁ m₂ Kp Kv xd₁ xd₂).computedTorqueController 1 1 xd xd' xd'')
          fun _ _ _ => 0) t₀ z →
      ∀ t, t₀ ≤ t → ‖((z t).1 - xd t, (z t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((z t₀).1 - xd t₀, (z t₀).2 - xd' t₀)‖ :=
  (handTop mb m₁ m₂ Kp Kv xd₁ xd₂).computedTorqueController_tracking
    (handTop_M_posDef hmb m₁ m₂ Kp Kv xd₁ xd₂) Matrix.PosDef.one Matrix.PosDef.one

end RoboLean.Examples
