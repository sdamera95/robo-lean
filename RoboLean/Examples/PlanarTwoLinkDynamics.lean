import RoboLean.Dynamics.Christoffel
import RoboLean.Examples.RigidTransform

/-!
# Dynamics of the planar two-link arm (MLS §2.3, Figure 4.4)

MLS Chapter 4, §2.3, printed pp. 164–165, Figure 4.4 and eqs. (4.10)–(4.11). Two revolute
joints about `+z`; at `θ = 0` the arm lies along `+x` (the book's `x̄₁ = r₁ c₁`); joint 1 is at
the base origin and joint 2 at `(l₁, 0, 0)`. Link `i` is a bar with mass `mᵢ` and principal
inertia tensor `diag(I_xi, I_yi, I_zi)` about its mass center, which lies at distance `rᵢ` from
its joint along the link. The book derives

`M(θ) = [[α + 2β c₂, δ + β c₂], [δ + β c₂, δ]]`, `α = I_z1 + I_z2 + m₁r₁² + m₂(l₁² + r₂²)`,
`β = m₂ l₁ r₂`, `δ = I_z2 + m₂ r₂²`,

and the Coriolis matrix `[[-β s₂ θ̇₂, -β s₂ (θ̇₁ + θ̇₂)], [β s₂ θ̇₁, 0]]` (eq. (4.11)).

Here the same arm is an `InertialChain 2`, and `M(θ)` is computed from the general
construction `M(θ) = ∑ Jᵢᵀ 𝓜ᵢ Jᵢ` of eq. (4.19), p. 168, through the link body Jacobians; it is
not taken from the book. The Coriolis matrix is the Christoffel matrix of eq. (4.23) computed
from the partial derivatives of that `M`. This instance shows the hypotheses of the general
positivity theorem (`InertialChain.massMatrix_posDef_of_joints`) and of the trajectory form of
Lemma 4.2(2) (`InertialChain.skew_deriv_massMatrix_sub_two_coriolisMatrix`) satisfiable.

Lean joint `0` is the book's joint 1, so `θ 0 = θ₁` and `θ 1 = θ₂`. The inertia diagonals are
`I₁ = ![I_x1, I_y1, I_z1]`, `I₂ = ![I_x2, I_y2, I_z2]`, so `I_zi = Iᵢ 2`. The tool pose of the
chain is not used and is set to the identity. All parameters are arbitrary reals unless a
theorem states a sign; nothing here concerns a physical arm.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

/-! ### Small coordinate helpers -/

private theorem norm_zAxis' : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem revolute_angular' (ω q : Vec3) : (Twist.revolute ω q).angular = ω := rfl

private theorem revolute_linear' (ω q : Vec3) :
    (Twist.revolute ω q).linear = -Vec3.cross ω q := rfl

private theorem vec_add' (a b c a' b' c' : ℝ) :
    vec a b c + vec a' b' c' = vec (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem vec_sub' (a b c a' b' c' : ℝ) :
    vec a b c - vec a' b' c' = vec (a - a') (b - b') (c - c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem vec_eq' {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem zRotation_act_vec (t x y z : ℝ) :
    (Rotation.zRotation t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem zAxis_eq : Rotation.zAxis = vec 0 0 1 := rfl

/-- A revolute joint motion about `+z` through `(a, b, 0)`, acting on a point
(MLS p. 47, eq. (2.40) with zero pitch). -/
private theorem exp_revolute_z_applyPoint (a b t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec a b 0)) t).applyPoint x =
      (Rotation.zRotation t).act (x - vec a b 0) + vec a b 0 :=
  Twist.exp_revolute_applyPoint _ _ norm_zAxis' t x

/-- A revolute joint motion about `+z` fixes the direction `+z`. -/
private theorem exp_revolute_z_applyVector (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyVector Rotation.zAxis =
      Rotation.zAxis := by
  rw [RigidTransform.applyVector, Twist.exp_rotation, revolute_angular']
  change (Rotation.zRotation t).act Rotation.zAxis = Rotation.zAxis
  rw [zAxis_eq, zRotation_act_vec]
  simp

private theorem translation_applyPoint (p x : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyPoint x = x + p := by
  simp [RigidTransform.applyPoint]

private theorem translation_applyVector (p v : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyVector v = v := by
  simp [RigidTransform.applyVector]

private theorem inv_applyPoint_of {g : RigidTransform} {x y : Vec3} (h : g.applyPoint x = y) :
    g⁻¹.applyPoint y = x := by
  rw [← h, RigidTransform.inv_applyPoint_applyPoint]

private theorem inv_applyVector_of {g : RigidTransform} {v w : Vec3}
    (h : g.applyVector v = w) : g⁻¹.applyVector w = v := by
  rw [← h, ← RigidTransform.mul_applyVector, inv_mul_cancel, RigidTransform.one_applyVector]

/-! ### The arm as an inertial chain -/

/-- The joints of MLS Figure 4.4 (p. 164): revolute about `+z` through the base origin and
through `(l₁, 0, 0)`, base-frame twists at `θ = 0` in the order `(v, ω)` (MLS p. 87). The tool
pose is not used by the dynamics and is set to the identity. -/
def twoLinkDynamicsChain (l₁ : ℝ) : SerialChain 2 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 0 0),
    Twist.revolute Rotation.zAxis (vec l₁ 0 0)]
  toolRef := 1

/-- **The planar two-link arm of MLS Figure 4.4 (pp. 164–165) with inertial data.** Link
frames at the mass centers `(r₁, 0, 0)` and `(l₁ + r₂, 0, 0)` with the base orientation at
`θ = 0` (aligned with the principal axes), and generalized inertias
`[[mᵢ I, 0], [0, diag(Iᵢ)]]` (MLS eq. (4.9), p. 162). -/
def planarTwoLinkArm (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ) : InertialChain 2 where
  chain := twoLinkDynamicsChain l₁
  linkRef := ![⟨1, vec r₁ 0 0⟩, ⟨1, vec (l₁ + r₂) 0 0⟩]
  linkInertia := ![RigidBody.generalizedInertia m₁ (Matrix.diagonal I₁),
    RigidBody.generalizedInertia m₂ (Matrix.diagonal I₂)]

variable (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)

/-! ### Link body Jacobians (MLS p. 168) -/

/-- The only nonzero column of the body Jacobian of link 1 (MLS p. 168): joint 1's twist in
the frame `L₁`, a revolute twist about `+z` through `(-r₁, 0, 0)`, at every configuration. -/
theorem planarTwoLinkArm_linkBodyJacobian_zero_zero (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkBodyJacobian 0 θ 0 =
      Twist.revolute Rotation.zAxis (vec (-r₁) 0 0) := by
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ le_rfl]
  have ht : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).chain.twist 0 =
      Twist.revolute Rotation.zAxis (vec 0 0 0) := rfl
  have hl : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkRef 0 = ⟨1, vec r₁ 0 0⟩ := rfl
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
    zero_add, List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons,
    List.prod_nil, mul_one]
  rw [ht, hl, Twist.adjoint_revolute]
  congr 1
  · apply inv_applyVector_of
    rw [RigidTransform.mul_applyVector, translation_applyVector, exp_revolute_z_applyVector]
  · apply inv_applyPoint_of
    rw [RigidTransform.mul_applyPoint, translation_applyPoint, exp_revolute_z_applyPoint,
      vec_add', vec_sub', zRotation_act_vec, vec_add']
    apply vec_eq' <;> ring

/-- The second column of the body Jacobian of link 1 vanishes (MLS p. 168,
`J^b_{sl₁} = [ξ₁† 0]`). -/
theorem planarTwoLinkArm_linkBodyJacobian_zero_one (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkBodyJacobian 0 θ 1 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

/-- The second column of the body Jacobian of link 2 (MLS p. 168): joint 2's twist in the
frame `L₂`, a revolute twist about `+z` through `(-r₂, 0, 0)`, at every configuration. -/
theorem planarTwoLinkArm_linkBodyJacobian_one_one (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkBodyJacobian 1 θ 1 =
      Twist.revolute Rotation.zAxis (vec (-r₂) 0 0) := by
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ le_rfl]
  have ht : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).chain.twist 1 =
      Twist.revolute Rotation.zAxis (vec l₁ 0 0) := rfl
  have hl : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkRef 1 = ⟨1, vec (l₁ + r₂) 0 0⟩ := rfl
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
    List.prod_nil, mul_one, Fin.succ_zero_eq_one]
  rw [ht, hl, Twist.adjoint_revolute]
  congr 1
  · apply inv_applyVector_of
    rw [RigidTransform.mul_applyVector, translation_applyVector, exp_revolute_z_applyVector]
  · apply inv_applyPoint_of
    rw [RigidTransform.mul_applyPoint, translation_applyPoint, exp_revolute_z_applyPoint,
      vec_add', vec_sub', zRotation_act_vec, vec_add']
    apply vec_eq' <;> ring

/-- The first column of the body Jacobian of link 2 (MLS p. 168): joint 1's twist in the
frame `L₂`, a revolute twist about `+z` through `(-(r₂ + l₁ cos θ₂), l₁ sin θ₂, 0)`, the base
origin in `L₂` coordinates. -/
theorem planarTwoLinkArm_linkBodyJacobian_one_zero (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkBodyJacobian 1 θ 0 =
      Twist.revolute Rotation.zAxis
        (vec (-(r₂ + l₁ * Real.cos (θ 1))) (l₁ * Real.sin (θ 1)) 0) := by
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  have ht0 : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).chain.twist 0 =
      Twist.revolute Rotation.zAxis (vec 0 0 0) := rfl
  have ht1 : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).chain.twist 1 =
      Twist.revolute Rotation.zAxis (vec l₁ 0 0) := rfl
  have hl : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkRef 1 = ⟨1, vec (l₁ + r₂) 0 0⟩ := rfl
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one,
    Fin.val_zero, List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons,
    List.prod_nil, mul_one, Fin.succ_zero_eq_one]
  rw [ht0, ht1, hl, Twist.adjoint_revolute]
  congr 1
  · apply inv_applyVector_of
    rw [RigidTransform.mul_applyVector, RigidTransform.mul_applyVector,
      translation_applyVector, exp_revolute_z_applyVector, exp_revolute_z_applyVector]
  · apply inv_applyPoint_of
    rw [RigidTransform.mul_applyPoint, RigidTransform.mul_applyPoint, translation_applyPoint,
      exp_revolute_z_applyPoint, exp_revolute_z_applyPoint, vec_add', vec_sub',
      zRotation_act_vec, vec_add', vec_sub', zRotation_act_vec, vec_add']
    have hsc := Real.sin_sq_add_cos_sq (θ 1)
    apply vec_eq'
    · linear_combination (-(Real.cos (θ 0) * l₁)) * hsc
    · linear_combination (-(Real.sin (θ 0) * l₁)) * hsc
    · ring

/-! ### The manipulator inertia matrix (MLS eqs. (4.10), (4.19)) -/

/-- The generalized-inertia pairing of two in-plane revolute twists about `+z`
(MLS eq. (4.9), p. 162): the axes through `(a, b, 0)` and `(a', b', 0)` give
`m (a a' + b b') + I_z`. -/
private theorem pairing_revolute_z (m : ℝ) (I : Fin 3 → ℝ) (a b a' b' : ℝ) :
    (Twist.revolute Rotation.zAxis (vec a b 0)).coordinates ⬝ᵥ
      (RigidBody.generalizedInertia m (Matrix.diagonal I) *ᵥ
        (Twist.revolute Rotation.zAxis (vec a' b' 0)).coordinates) =
      m * (a * a' + b * b') + I 2 := by
  have hv (x y : ℝ) : WithLp.ofLp (-Vec3.cross Rotation.zAxis (vec x y 0)) = ![y, -x, 0] := by
    ext i
    fin_cases i <;> simp [Vec3.cross, cross_apply, Rotation.zAxis, vec]
  have hz : WithLp.ofLp Rotation.zAxis = ![0, 0, 1] := rfl
  rw [RigidBody.coordinates_dotProduct_generalizedInertia_mulVec, revolute_linear',
    revolute_linear', revolute_angular', revolute_angular', hv, hv, hz]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.mulVec_diagonal, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem pairing_zero_left (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (V : Twist) :
    (0 : Twist).coordinates ⬝ᵥ (𝓜 *ᵥ V.coordinates) = 0 := by
  simp

private theorem pairing_zero_right (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (V : Twist) :
    V.coordinates ⬝ᵥ (𝓜 *ᵥ (0 : Twist).coordinates) = 0 := by
  simp

/-- **MLS eq. (4.10), p. 165: the inertia matrix of the planar two-link arm.** The general
construction `M(θ) = ∑ Jᵢᵀ 𝓜ᵢ Jᵢ` of eq. (4.19) gives, at every configuration,
`M(θ) = [[α + 2β cos θ₂, δ + β cos θ₂], [δ + β cos θ₂, δ]]` with
`α = I_z1 + I_z2 + m₁ r₁² + m₂ (l₁² + r₂²)`, `β = m₂ l₁ r₂`, `δ = I_z2 + m₂ r₂²`
(`I_zi = Iᵢ 2`, `θ₂ = θ 1`). -/
theorem planarTwoLinkArm_massMatrix (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix θ =
      !![I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2) +
          2 * (m₂ * l₁ * r₂) * Real.cos (θ 1),
        I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos (θ 1);
        I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos (θ 1),
        I₂ 2 + m₂ * r₂ ^ 2] := by
  have hM0 : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkInertia 0 =
      RigidBody.generalizedInertia m₁ (Matrix.diagonal I₁) := rfl
  have hM1 : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkInertia 1 =
      RigidBody.generalizedInertia m₂ (Matrix.diagonal I₂) := rfl
  have hsc := Real.sin_sq_add_cos_sq (θ 1)
  ext i j
  rw [InertialChain.massMatrix_apply, Fin.sum_univ_two, hM0, hM1]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, planarTwoLinkArm_linkBodyJacobian_zero_zero,
      planarTwoLinkArm_linkBodyJacobian_one_zero, pairing_revolute_z, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.empty_val']
    linear_combination m₂ * l₁ ^ 2 * hsc
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      planarTwoLinkArm_linkBodyJacobian_zero_zero, planarTwoLinkArm_linkBodyJacobian_zero_one,
      planarTwoLinkArm_linkBodyJacobian_one_zero, planarTwoLinkArm_linkBodyJacobian_one_one,
      pairing_revolute_z, pairing_zero_right, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      planarTwoLinkArm_linkBodyJacobian_zero_zero, planarTwoLinkArm_linkBodyJacobian_zero_one,
      planarTwoLinkArm_linkBodyJacobian_one_zero, planarTwoLinkArm_linkBodyJacobian_one_one,
      pairing_revolute_z, pairing_zero_left, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    ring
  · simp only [Fin.isValue, Fin.mk_one, planarTwoLinkArm_linkBodyJacobian_zero_one,
      planarTwoLinkArm_linkBodyJacobian_one_one, pairing_revolute_z, pairing_zero_left,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    ring

/-! ### Positive definiteness (MLS Lemma 4.2(1), p. 171) -/

/-- **MLS Lemma 4.2(1) for the two-link arm.** With positive masses and positive principal
moments of both links, the inertia matrix `M(θ)` of the arm is positive definite at every
configuration, for all real `r₁, r₂, l₁`. This is the general
`InertialChain.massMatrix_posDef_of_joints` (positive definite link inertias, unit-axis
revolute joints); the moments `I_xi, I_yi` do not appear in `M(θ)` but enter the hypothesis
that each link inertia is positive definite. -/
theorem planarTwoLinkArm_massMatrix_posDef (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (θ : Fin 2 → ℝ) :
    ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix θ).PosDef := by
  refine InertialChain.massMatrix_posDef_of_joints _ (fun k => ?_) (fun j => Or.inl ?_) θ
  · fin_cases k
    · exact RigidBody.generalizedInertia_posDef hm₁ (Matrix.PosDef.diagonal hI₁)
    · exact RigidBody.generalizedInertia_posDef hm₂ (Matrix.PosDef.diagonal hI₂)
  · fin_cases j
    · exact ⟨Rotation.zAxis, vec 0 0 0, norm_zAxis', rfl⟩
    · exact ⟨Rotation.zAxis, vec l₁ 0 0, norm_zAxis', rfl⟩

/-- The printed matrix of MLS eq. (4.10), p. 165, is positive definite for positive masses and
principal moments (a corollary of `planarTwoLinkArm_massMatrix_posDef` and
`planarTwoLinkArm_massMatrix`). -/
theorem planarTwoLinkArm_printedMassMatrix_posDef (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (θ₂ : ℝ) :
    (!![I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2) + 2 * (m₂ * l₁ * r₂) * Real.cos θ₂,
        I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos θ₂;
        I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos θ₂,
        I₂ 2 + m₂ * r₂ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have h := planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂ ![0, θ₂]
  rw [planarTwoLinkArm_massMatrix] at h
  simpa using h

/-! ### Christoffel symbols and the Coriolis matrix (MLS eqs. (4.11), (4.22)–(4.23)) -/

/-- Fréchet derivatives of the entries of the arm's inertia matrix at `θ` (from MLS
eq. (4.10)): only `θ₂ = θ 1` enters, with `∂M₁₁/∂θ₂ = -2β sin θ₂`,
`∂M₁₂/∂θ₂ = ∂M₂₁/∂θ₂ = -β sin θ₂`, `∂M₂₂/∂θ₂ = 0`, `β = m₂ l₁ r₂`. -/
def planarTwoLinkArmMassDeriv (θ : Fin 2 → ℝ) : Fin 2 → Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
  ![![(-(2 * (m₂ * l₁ * r₂) * Real.sin (θ 1))) •
        (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ),
      (-(m₂ * l₁ * r₂ * Real.sin (θ 1))) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)],
    ![(-(m₂ * l₁ * r₂ * Real.sin (θ 1))) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ),
      0]]

/-- The entries of the arm's inertia matrix have the Fréchet derivatives
`planarTwoLinkArmMassDeriv` at every configuration, so the derivative hypothesis of the
trajectory form of MLS Lemma 4.2(2) holds for this arm. -/
theorem hasFDerivAt_planarTwoLinkArm_massMatrix (θ : Fin 2 → ℝ) (i j : Fin 2) :
    HasFDerivAt (fun q => (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q i j)
      (planarTwoLinkArmMassDeriv m₂ r₂ l₁ θ i j) θ := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 θ
  simp only [planarTwoLinkArm_massMatrix]
  fin_cases i <;> fin_cases j
  · refine ((hc.cos.const_mul (2 * (m₂ * l₁ * r₂))).const_add
      (I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2))).congr_fderiv ?_
    ext v
    simp [planarTwoLinkArmMassDeriv]
    ring
  · refine ((hc.cos.const_mul (m₂ * l₁ * r₂)).const_add (I₂ 2 + m₂ * r₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [planarTwoLinkArmMassDeriv]
    ring
  · refine ((hc.cos.const_mul (m₂ * l₁ * r₂)).const_add (I₂ 2 + m₂ * r₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [planarTwoLinkArmMassDeriv]
    ring
  · convert hasFDerivAt_const (𝕜 := ℝ) (I₂ 2 + m₂ * r₂ ^ 2) θ using 1 <;> rfl

/-- **MLS eq. (4.11), p. 165: the Coriolis matrix of the two-link arm.** The Christoffel
Coriolis matrix of eq. (4.23), computed from the partial derivatives of the arm's inertia
matrix at `θ`, is `[[-β s₂ θ̇₂, -β s₂ (θ̇₁ + θ̇₂)], [β s₂ θ̇₁, 0]]` with `β = m₂ l₁ r₂`,
`s₂ = sin θ₂`. -/
theorem planarTwoLinkArm_coriolisMatrix (θ θ' : Fin 2 → ℝ) :
    Christoffel.coriolisMatrix
        (Christoffel.partials (planarTwoLinkArmMassDeriv m₂ r₂ l₁ θ)) θ' =
      !![-(m₂ * l₁ * r₂) * Real.sin (θ 1) * θ' 1,
          -(m₂ * l₁ * r₂) * Real.sin (θ 1) * (θ' 0 + θ' 1);
        m₂ * l₁ * r₂ * Real.sin (θ 1) * θ' 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials,
      planarTwoLinkArmMassDeriv, Fin.sum_univ_two, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  all_goals ring

/-- The actual derivative of the arm's inertia matrix along a joint trajectory (chain rule,
MLS p. 169): this shows the hypothesis `hMdot` of `planarTwoLinkArm_skew` satisfiable. -/
theorem hasDerivAt_planarTwoLinkArm_massMatrix {θ : ℝ → Fin 2 → ℝ} {θ' : Fin 2 → ℝ} {t : ℝ}
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t) (i j : Fin 2) :
    HasDerivAt (fun s => (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix (θ s) i j)
      (Christoffel.rate (Christoffel.partials (planarTwoLinkArmMassDeriv m₂ r₂ l₁ (θ t))) θ'
        i j) t :=
  Christoffel.hasDerivAt_comp
    (fun i j => hasFDerivAt_planarTwoLinkArm_massMatrix m₁ m₂ r₁ r₂ l₁ I₁ I₂ (θ t) i j) hθ i j

/-- `Ṁ − 2C` for the two-link arm, computed: `[[0, β s₂ (2θ̇₁ + θ̇₂)], [-β s₂ (2θ̇₁ + θ̇₂), 0]]`,
visibly skew-symmetric (MLS Lemma 4.2(2), p. 171, with eqs. (4.10)–(4.11)). -/
theorem planarTwoLinkArm_rate_sub_two_coriolisMatrix (θ θ' : Fin 2 → ℝ) :
    Christoffel.rate (Christoffel.partials (planarTwoLinkArmMassDeriv m₂ r₂ l₁ θ)) θ' -
        (2 : ℝ) • Christoffel.coriolisMatrix
          (Christoffel.partials (planarTwoLinkArmMassDeriv m₂ r₂ l₁ θ)) θ' =
      !![0, m₂ * l₁ * r₂ * Real.sin (θ 1) * (2 * θ' 0 + θ' 1);
        -(m₂ * l₁ * r₂ * Real.sin (θ 1) * (2 * θ' 0 + θ' 1)), 0] := by
  rw [planarTwoLinkArm_coriolisMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Christoffel.rate, Christoffel.partials, planarTwoLinkArmMassDeriv, Fin.sum_univ_two,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  all_goals ring

/-- **MLS Lemma 4.2(2), p. 171, for the two-link arm along any differentiable joint
trajectory**, an instance of `InertialChain.skew_deriv_massMatrix_sub_two_coriolisMatrix`:
for every actual derivative `Mdot` of `s ↦ M(θ(s))` (one exists by
`hasDerivAt_planarTwoLinkArm_massMatrix`), `Mdot − 2C` is skew-symmetric, with `C` the printed
Coriolis matrix of eq. (4.11). -/
theorem planarTwoLinkArm_skew {θ : ℝ → Fin 2 → ℝ} {θ' : Fin 2 → ℝ} {t : ℝ}
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t) {Mdot : Matrix (Fin 2) (Fin 2) ℝ}
    (hMdot : ∀ i j,
      HasDerivAt (fun s => (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix (θ s) i j)
        (Mdot i j) t) :
    (Mdot - (2 : ℝ) • !![-(m₂ * l₁ * r₂) * Real.sin (θ t 1) * θ' 1,
          -(m₂ * l₁ * r₂) * Real.sin (θ t 1) * (θ' 0 + θ' 1);
        m₂ * l₁ * r₂ * Real.sin (θ t 1) * θ' 0, 0])ᵀ =
      -(Mdot - (2 : ℝ) • !![-(m₂ * l₁ * r₂) * Real.sin (θ t 1) * θ' 1,
          -(m₂ * l₁ * r₂) * Real.sin (θ t 1) * (θ' 0 + θ' 1);
        m₂ * l₁ * r₂ * Real.sin (θ t 1) * θ' 0, 0]) := by
  rw [← planarTwoLinkArm_coriolisMatrix]
  refine InertialChain.skew_deriv_massMatrix_sub_two_coriolisMatrix _ (fun k => ?_)
    (fun i j => hasFDerivAt_planarTwoLinkArm_massMatrix m₁ m₂ r₁ r₂ l₁ I₁ I₂ (θ t) i j) hθ hMdot
  fin_cases k
  · exact RigidBody.generalizedInertia_isSymm m₁ (Matrix.isSymm_diagonal I₁)
  · exact RigidBody.generalizedInertia_isSymm m₂ (Matrix.isSymm_diagonal I₂)

end RoboLean.Examples
