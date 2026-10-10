import RoboLean.Dynamics.MassMatrixDerivative
import RoboLean.Examples.ThreeLinkGravity

/-!
# Inertia matrix and Christoffel symbols of the three-link manipulator (MLS Example 4.3)

MLS Chapter 4, Example 4.3, printed pp. 172–174, Figure 4.5. The arm is
`Examples.threeLinkArm` (`RoboLean.Examples.ThreeLinkGravity`): the printed joint twists of
p. 172, link frames at the mass centers with the base orientation at `θ = 0`, and generalized
inertias `[[mᵢ I, 0], [0, diag(I_xi, I_yi, I_zi)]]`. Everything below is computed from the
general constructions of the library and compared with the printed displays; nothing is taken
from the book:

* the columns of the link body Jacobians `J₁, J₂, J₃` (p. 173) from the E009 body Jacobian of
  the link chains (`InertialChain.linkBodyJacobian`);
* the inertia matrix `M(θ) = ∑ Jᵢᵀ 𝓜ᵢ Jᵢ` of eq. (4.19), which equals the printed `M₁₁, …, M₃₃`
  of p. 173;
* the Christoffel symbols of eq. (4.22) from the actual partial derivatives of that `M`
  (`InertialChain.massMatrixDeriv`), which equal the printed nonzero `Γᵢⱼₖ` of p. 174, with
  every other symbol zero.

Source observation (a consistency check, not an errata judgment): the first column of the
printed `J₃` on p. 173 has first entry `−l₂ c₂ − r₂ c₂₃`; the computed entry is
`−l₁ c₂ − r₂ c₂₃` (`threeLinkArm_linkBodyJacobian_two_zero`), and the printed `M₁₁` on the same
page, with its term `m₃ (l₁ c₂ + r₂ c₂₃)²`, agrees with the computed value.

Notation: Lean joint `k` is the book's joint `k + 1`, so `θ 1 = θ₂`, `θ 2 = θ₃`;
`cᵢ = cos θᵢ`, `sᵢ = sin θᵢ`, `c₂₃ = cos(θ₂ + θ₃)`, `s₂₃ = sin(θ₂ + θ₃)`; the inertia diagonals
are `Iᵢ = ![I_xi, I_yi, I_zi]`, so `I_xi = Iᵢ 0`, `I_yi = Iᵢ 1`, `I_zi = Iᵢ 2`. Twist
coordinates are linear first. This is one instance (a convention check on one chain, not a
general theorem); nothing here concerns a physical manipulator.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

variable (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ)

/-! ### Private coordinate helpers -/

private theorem tl_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem tl_norm_neg_xAxis : ‖-Rotation.xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem tl_zAxis_eq : Rotation.zAxis = vec 0 0 1 := rfl

private theorem tl_neg_xAxis_eq : -Rotation.xAxis = vec (-1) 0 0 := by
  ext i
  fin_cases i <;> simp [Rotation.xAxis, vec]

private theorem tl_exp_zAxis_act (t x y z : ℝ) :
    (Rotation.exp Rotation.zAxis t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  change (Rotation.zRotation t).act (vec x y z) = _
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem tl_exp_neg_xAxis_act (t x y z : ℝ) :
    (Rotation.exp (-Rotation.xAxis) t).act (vec x y z) =
      vec x (Real.cos t * y + Real.sin t * z) (-(Real.sin t * y) + Real.cos t * z) := by
  rw [show -Rotation.xAxis = (-1 : ℝ) • Rotation.xAxis by simp, Rotation.exp_smul,
    Rotation.exp_xAxis]
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.xRotation_val, Rotation.xMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, vec]

private theorem tl_vec_add (a b c a' b' c' : ℝ) :
    vec a b c + vec a' b' c' = vec (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem tl_vec_sub (a b c a' b' c' : ℝ) :
    vec a b c - vec a' b' c' = vec (a - a') (b - b') (c - c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem tl_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem tl_translation_applyPoint (p x : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyPoint x = x + p := by
  simp [RigidTransform.applyPoint]

private theorem tl_translation_applyVector (p v : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyVector v = v := by
  simp [RigidTransform.applyVector]

private theorem tl_exp_revolute_applyVector (ω q v : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  rw [RigidTransform.applyVector, Twist.exp_rotation]
  rfl

private theorem tl_inv_applyPoint_of {g : RigidTransform} {x y : Vec3}
    (h : g.applyPoint x = y) : g⁻¹.applyPoint y = x := by
  rw [← h, RigidTransform.inv_applyPoint_applyPoint]

private theorem tl_inv_applyVector_of {g : RigidTransform} {v w : Vec3}
    (h : g.applyVector v = w) : g⁻¹.applyVector w = v := by
  rw [← h, ← RigidTransform.mul_applyVector, inv_mul_cancel, RigidTransform.one_applyVector]

/-- Six coordinates (linear first) of the revolute twist `(-ω × q, ω)` (MLS p. 87). -/
private theorem tl_revolute_coordinates (a b c x y z : ℝ) :
    (Twist.revolute (vec a b c) (vec x y z)).coordinates =
      Sum.elim ![c * y - b * z, a * z - c * x, b * x - a * y] ![a, b, c] := by
  funext r
  rcases r with i | i <;> fin_cases i <;>
    simp [Twist.coordinates, Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem tl_sum_elim_eq {a b c d e f a' b' c' d' e' f' : ℝ} (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') (he : e = e') (hf : f = f') :
    (Sum.elim ![a, b, c] ![d, e, f] : Fin 3 ⊕ Fin 3 → ℝ) =
      Sum.elim ![a', b', c'] ![d', e', f'] := by
  rw [ha, hb, hc, hd, he, hf]

/-- The generalized-inertia pairing (MLS eq. (4.9), p. 162) of two six-vectors written by their
linear and angular coordinates, for a diagonal inertia tensor. -/
private theorem tl_pairing (m : ℝ) (I : Fin 3 → ℝ) (a b c d e f a' b' c' d' e' f' : ℝ) :
    (Sum.elim ![a, b, c] ![d, e, f] : Fin 3 ⊕ Fin 3 → ℝ) ⬝ᵥ
      (RigidBody.generalizedInertia m (Matrix.diagonal I) *ᵥ Sum.elim ![a', b', c'] ![d', e', f']) =
      m * (a * a' + b * b' + c * c') + (I 0 * d * d' + I 1 * e * e' + I 2 * f * f') := by
  rw [RigidBody.dotProduct_generalizedInertia_mulVec]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.mulVec_diagonal, Function.comp_apply,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Joint 1 in the frame of link 1 (MLS p. 173): the axis `+z` through `(0, 0, -r₀)`. -/
private theorem tl_jac_zero_zero (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 0 θ 0 =
      Twist.revolute (vec 0 0 1)
        (vec 0 0 (-r₀)) := by
  have h0 : ∀ t x, (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - vec 0 0 0) + vec 0 0 0 :=
    Twist.exp_revolute_applyPoint _ _ tl_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [threeLinkArm, elbowChain, Matrix.cons_val_zero, Twist.adjoint_revolute]
  congr 1
  · apply tl_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, tl_translation_applyVector,
        tl_exp_revolute_applyVector, tl_exp_zAxis_act]
    simp only [tl_zAxis_eq]
    apply tl_vec_eq <;> ring
  · apply tl_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, tl_translation_applyPoint, h0, tl_vec_add, tl_vec_sub,
        tl_exp_zAxis_act]
    apply tl_vec_eq <;> ring

/-- Joint 1 in the frame of link 2 (MLS p. 173), the base `+z` axis seen from link 2. -/
private theorem tl_jac_one_zero (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 1 θ 0 =
      Twist.revolute (vec 0 (-Real.sin (θ 1)) (Real.cos (θ 1)))
        (vec 0 (l₀ * Real.sin (θ 1) - r₁) (-(Real.cos (θ 1) * l₀))) := by
  have h0 : ∀ t x, (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - vec 0 0 0) + vec 0 0 0 :=
    Twist.exp_revolute_applyPoint _ _ tl_norm_zAxis
  have h1 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute (-Rotation.xAxis) q) t).applyPoint x =
      (Rotation.exp (-Rotation.xAxis) t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q tl_norm_neg_xAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_one,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [threeLinkArm, elbowChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Twist.adjoint_revolute]
  congr 1
  · apply tl_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, tl_translation_applyVector,
        tl_exp_revolute_applyVector, tl_exp_neg_xAxis_act, tl_exp_zAxis_act]
    simp only [tl_zAxis_eq]
    apply tl_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)
  · apply tl_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, tl_translation_applyPoint, h0, h1, tl_vec_add,
        tl_vec_sub, tl_exp_neg_xAxis_act, tl_exp_zAxis_act]
    apply tl_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 2 in the frame of link 2 (MLS p. 173): the axis `-x` through `(0, -r₁, 0)`. -/
private theorem tl_jac_one_one (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 1 θ 1 =
      Twist.revolute (vec (-1) 0 0)
        (vec 0 (-r₁) 0) := by
  have h1 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute (-Rotation.xAxis) q) t).applyPoint x =
      (Rotation.exp (-Rotation.xAxis) t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q tl_norm_neg_xAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [threeLinkArm, elbowChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Twist.adjoint_revolute]
  congr 1
  · apply tl_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, tl_translation_applyVector,
        tl_exp_revolute_applyVector, tl_exp_neg_xAxis_act]
    simp only [tl_neg_xAxis_eq]
    apply tl_vec_eq <;> ring
  · apply tl_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, tl_translation_applyPoint, h1, tl_vec_add, tl_vec_sub,
        tl_exp_neg_xAxis_act]
    apply tl_vec_eq <;> ring

/-- Joint 1 in the frame of link 3 (MLS p. 173), the base `+z` axis seen from link 3. -/
private theorem tl_jac_two_zero (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 2 θ 0 =
      Twist.revolute (vec 0 (-(Real.cos (θ 1) * Real.sin (θ 2) + Real.cos (θ 2) * Real.sin (θ 1)))
          (Real.cos (θ 1) * Real.cos (θ 2) - Real.sin (θ 1) * Real.sin (θ 2)))
        (vec 0 (Real.cos (θ 1) * l₀ * Real.sin (θ 2) + Real.cos (θ 2) * l₀ * Real.sin (θ 1) -
            Real.cos (θ 2) * l₁ - r₂)
          (-(Real.cos (θ 1) * Real.cos (θ 2) * l₀) + l₀ * Real.sin (θ 1) * Real.sin (θ 2) -
            l₁ * Real.sin (θ 2))) := by
  have h0 : ∀ t x, (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - vec 0 0 0) + vec 0 0 0 :=
    Twist.exp_revolute_applyPoint _ _ tl_norm_zAxis
  have h1 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute (-Rotation.xAxis) q) t).applyPoint x =
      (Rotation.exp (-Rotation.xAxis) t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q tl_norm_neg_xAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_two,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [threeLinkArm, elbowChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply tl_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, tl_translation_applyVector,
        tl_exp_revolute_applyVector, tl_exp_neg_xAxis_act, tl_exp_zAxis_act]
    simp only [tl_zAxis_eq]
    apply tl_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)
  · apply tl_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, tl_translation_applyPoint, h0, h1, tl_vec_add,
        tl_vec_sub, tl_exp_neg_xAxis_act, tl_exp_zAxis_act]
    apply tl_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 2 in the frame of link 3 (MLS p. 173): the axis `-x` through
`(0, -l₁ c₃ - r₂, -l₁ s₃)`. -/
private theorem tl_jac_two_one (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 2 θ 1 =
      Twist.revolute (vec (-1) 0 0)
        (vec 0 (-(Real.cos (θ 2) * l₁) - r₂) (-(l₁ * Real.sin (θ 2)))) := by
  have h1 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute (-Rotation.xAxis) q) t).applyPoint x =
      (Rotation.exp (-Rotation.xAxis) t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q tl_norm_neg_xAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one, Fin.val_two,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [threeLinkArm, elbowChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply tl_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, tl_translation_applyVector,
        tl_exp_revolute_applyVector, tl_exp_neg_xAxis_act]
    simp only [tl_neg_xAxis_eq]
    apply tl_vec_eq <;> ring
  · apply tl_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, tl_translation_applyPoint, h1, tl_vec_add, tl_vec_sub,
        tl_exp_neg_xAxis_act]
    apply tl_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 3 in the frame of link 3 (MLS p. 173): the axis `-x` through `(0, -r₂, 0)`. -/
private theorem tl_jac_two_two (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 2 θ 2 =
      Twist.revolute (vec (-1) 0 0)
        (vec 0 (-r₂) 0) := by
  have h1 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute (-Rotation.xAxis) q) t).applyPoint x =
      (Rotation.exp (-Rotation.xAxis) t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q tl_norm_neg_xAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_two,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [threeLinkArm, elbowChain, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Twist.adjoint_revolute]
  congr 1
  · apply tl_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, tl_translation_applyVector,
        tl_exp_revolute_applyVector, tl_exp_neg_xAxis_act]
    simp only [tl_neg_xAxis_eq]
    apply tl_vec_eq <;> ring
  · apply tl_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, tl_translation_applyPoint, h1, tl_vec_add, tl_vec_sub,
        tl_exp_neg_xAxis_act]
    apply tl_vec_eq <;> ring

/-! ### Link body Jacobians (MLS p. 173) -/

/-- **The column of `J₁` (MLS p. 173):** joint 1's twist in the frame of link 1 is the pure
rotation `(0, 0, 0, 0, 0, 1)`. -/
theorem threeLinkArm_linkBodyJacobian_zero_zero (θ : Fin 3 → ℝ) :
    ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 0 θ 0).coordinates =
      Sum.elim ![0, 0, 0] ![0, 0, 1] := by
  rw [tl_jac_zero_zero, tl_revolute_coordinates]
  refine tl_sum_elim_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

/-- **The first column of `J₂` (MLS p. 173):** `(−r₁ c₂, 0, 0, 0, −s₂, c₂)`. -/
theorem threeLinkArm_linkBodyJacobian_one_zero (θ : Fin 3 → ℝ) :
    ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 1 θ 0).coordinates =
      Sum.elim ![-(r₁ * Real.cos (θ 1)), 0, 0] ![0, -Real.sin (θ 1), Real.cos (θ 1)] := by
  rw [tl_jac_one_zero, tl_revolute_coordinates]
  refine tl_sum_elim_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

/-- **The second column of `J₂` (MLS p. 173):** `(0, 0, −r₁, −1, 0, 0)`. -/
theorem threeLinkArm_linkBodyJacobian_one_one (θ : Fin 3 → ℝ) :
    ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 1 θ 1).coordinates =
      Sum.elim ![0, 0, -r₁] ![-1, 0, 0] := by
  rw [tl_jac_one_one, tl_revolute_coordinates]
  refine tl_sum_elim_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

/-- **The first column of `J₃` (MLS p. 173), as computed:**
`(−(l₁ c₂ + r₂ c₂₃), 0, 0, 0, −s₂₃, c₂₃)`. The printed first entry is `−l₂ c₂ − r₂ c₂₃`
(observation in the module docstring). -/
theorem threeLinkArm_linkBodyJacobian_two_zero (θ : Fin 3 → ℝ) :
    ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 2 θ 0).coordinates =
      Sum.elim ![-(l₁ * Real.cos (θ 1) + r₂ * Real.cos (θ 1 + θ 2)), 0, 0]
        ![0, -Real.sin (θ 1 + θ 2), Real.cos (θ 1 + θ 2)] := by
  rw [tl_jac_two_zero, tl_revolute_coordinates]
  simp only [Real.cos_add, Real.sin_add]
  refine tl_sum_elim_eq ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- **The second column of `J₃` (MLS p. 173):** `(0, l₁ s₃, −r₂ − l₁ c₃, −1, 0, 0)`. -/
theorem threeLinkArm_linkBodyJacobian_two_one (θ : Fin 3 → ℝ) :
    ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 2 θ 1).coordinates =
      Sum.elim ![0, l₁ * Real.sin (θ 2), -r₂ - l₁ * Real.cos (θ 2)] ![-1, 0, 0] := by
  rw [tl_jac_two_one, tl_revolute_coordinates]
  refine tl_sum_elim_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

/-- **The third column of `J₃` (MLS p. 173):** `(0, 0, −r₂, −1, 0, 0)`. -/
theorem threeLinkArm_linkBodyJacobian_two_two (θ : Fin 3 → ℝ) :
    ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 2 θ 2).coordinates =
      Sum.elim ![0, 0, -r₂] ![-1, 0, 0] := by
  rw [tl_jac_two_two, tl_revolute_coordinates]
  refine tl_sum_elim_eq ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

/-! ### The inertia matrix (MLS p. 173) -/

private theorem tl_jac_zero_one (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 0 θ 1 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem tl_jac_zero_two (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 0 θ 2 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem tl_jac_one_two (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkBodyJacobian 1 θ 2 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

/-- **The inertia matrix of MLS Example 4.3, as printed on p. 173.** The general construction
`M(θ) = ∑ Jᵢᵀ 𝓜ᵢ Jᵢ` of eq. (4.19) gives, at every configuration,
`M₁₁ = I_y2 s₂² + I_y3 s₂₃² + I_z1 + I_z2 c₂² + I_z3 c₂₃² + m₂ r₁² c₂² + m₃ (l₁ c₂ + r₂ c₂₃)²`,
`M₁₂ = M₁₃ = M₂₁ = M₃₁ = 0`, `M₂₂ = I_x2 + I_x3 + m₃ l₁² + m₂ r₁² + m₃ r₂² + 2 m₃ l₁ r₂ c₃`,
`M₂₃ = M₃₂ = I_x3 + m₃ r₂² + m₃ l₁ r₂ c₃`, `M₃₃ = I_x3 + m₃ r₂²`. -/
theorem threeLinkArm_massMatrix (θ : Fin 3 → ℝ) :
    (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).massMatrix θ =
      !![I₂ 1 * Real.sin (θ 1) ^ 2 + I₃ 1 * Real.sin (θ 1 + θ 2) ^ 2 + I₁ 2 +
            I₂ 2 * Real.cos (θ 1) ^ 2 + I₃ 2 * Real.cos (θ 1 + θ 2) ^ 2 +
            m₂ * r₁ ^ 2 * Real.cos (θ 1) ^ 2 +
            m₃ * (l₁ * Real.cos (θ 1) + r₂ * Real.cos (θ 1 + θ 2)) ^ 2, 0, 0;
        0, I₂ 0 + I₃ 0 + m₃ * l₁ ^ 2 + m₂ * r₁ ^ 2 + m₃ * r₂ ^ 2 +
            2 * m₃ * l₁ * r₂ * Real.cos (θ 2),
          I₃ 0 + m₃ * r₂ ^ 2 + m₃ * l₁ * r₂ * Real.cos (θ 2);
        0, I₃ 0 + m₃ * r₂ ^ 2 + m₃ * l₁ * r₂ * Real.cos (θ 2), I₃ 0 + m₃ * r₂ ^ 2] := by
  have hM0 : (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkInertia 0 =
      RigidBody.generalizedInertia m₁ (Matrix.diagonal I₁) := rfl
  have hM1 : (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkInertia 1 =
      RigidBody.generalizedInertia m₂ (Matrix.diagonal I₂) := rfl
  have hM2 : (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).linkInertia 2 =
      RigidBody.generalizedInertia m₃ (Matrix.diagonal I₃) := rfl
  have hsc := Real.sin_sq_add_cos_sq (θ 2)
  ext i j
  rw [InertialChain.massMatrix_apply, Fin.sum_univ_three, hM0, hM1, hM2]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      threeLinkArm_linkBodyJacobian_zero_zero, threeLinkArm_linkBodyJacobian_one_zero,
      threeLinkArm_linkBodyJacobian_one_one, threeLinkArm_linkBodyJacobian_two_zero,
      threeLinkArm_linkBodyJacobian_two_one, threeLinkArm_linkBodyJacobian_two_two,
      tl_jac_zero_one, tl_jac_zero_two, tl_jac_one_two, tl_pairing, RigidBody.coordinates_zero,
      Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct, Matrix.of_apply, Matrix.cons_val]
  · ring
  · ring
  · ring
  · ring
  · linear_combination m₃ * l₁ ^ 2 * hsc
  · ring
  · ring
  · ring
  · ring

/-! ### Christoffel symbols (MLS p. 174) -/

/-- Fréchet derivatives of the entries of the printed inertia matrix of MLS Example 4.3
(p. 173) at `θ`; `θ 1 = θ₂` and `θ 2 = θ₃` are the only coordinates that enter. -/
private def tlMassDeriv (m₂ m₃ r₁ r₂ l₁ : ℝ) (I₂ I₃ : Fin 3 → ℝ) (θ : Fin 3 → ℝ) :
    Fin 3 → Fin 3 → ((Fin 3 → ℝ) →L[ℝ] ℝ) :=
  let c₂ := Real.cos (θ 1)
  let s₂ := Real.sin (θ 1)
  let s₃ := Real.sin (θ 2)
  let c₂₃ := Real.cos (θ 1 + θ 2)
  let s₂₃ := Real.sin (θ 1 + θ 2)
  let P₁ : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  let P₂ : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  ![![(2 * ((I₂ 1 - I₂ 2 - m₂ * r₁ ^ 2) * c₂ * s₂ + (I₃ 1 - I₃ 2) * c₂₃ * s₂₃ -
          m₃ * (l₁ * c₂ + r₂ * c₂₃) * (l₁ * s₂ + r₂ * s₂₃))) • P₁ +
        (2 * ((I₃ 1 - I₃ 2) * c₂₃ * s₂₃ - m₃ * r₂ * s₂₃ * (l₁ * c₂ + r₂ * c₂₃))) • P₂, 0, 0],
    ![0, (-(2 * m₃ * l₁ * r₂ * s₃)) • P₂, (-(m₃ * l₁ * r₂ * s₃)) • P₂],
    ![0, (-(m₃ * l₁ * r₂ * s₃)) • P₂, 0]]

/-- The entries of the inertia matrix of `threeLinkArm` have the Fréchet derivatives
`tlMassDeriv` at every configuration (from `threeLinkArm_massMatrix`, MLS p. 173). -/
private theorem tl_hasFDerivAt_massMatrix (θ : Fin 3 → ℝ) (i j : Fin 3) :
    HasFDerivAt (fun q => (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).massMatrix q i j)
      (tlMassDeriv m₂ m₃ r₁ r₂ l₁ I₂ I₃ θ i j) θ := by
  have hc1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 θ
  have hc2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 θ
  have h12 := hc1.fun_add hc2
  simp only [threeLinkArm_massMatrix]
  fin_cases i <;> fin_cases j
  · refine ((((((((hc1.sin.pow 2).const_mul (I₂ 1)).fun_add
      ((h12.sin.pow 2).const_mul (I₃ 1))).add_const (I₁ 2)).fun_add
      ((hc1.cos.pow 2).const_mul (I₂ 2))).fun_add ((h12.cos.pow 2).const_mul (I₃ 2))).fun_add
      ((hc1.cos.pow 2).const_mul (m₂ * r₁ ^ 2))).fun_add
      ((((hc1.cos.const_mul l₁).fun_add (h12.cos.const_mul r₂)).pow 2).const_mul m₃)).congr_fderiv
      ?_
    ext v
    simp [tlMassDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · refine ((hc2.cos.const_mul (2 * m₃ * l₁ * r₂)).const_add
      (I₂ 0 + I₃ 0 + m₃ * l₁ ^ 2 + m₂ * r₁ ^ 2 + m₃ * r₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [tlMassDeriv]
    ring
  · refine ((hc2.cos.const_mul (m₃ * l₁ * r₂)).const_add (I₃ 0 + m₃ * r₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [tlMassDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · refine ((hc2.cos.const_mul (m₃ * l₁ * r₂)).const_add (I₃ 0 + m₃ * r₂ ^ 2)).congr_fderiv ?_
    ext v
    simp [tlMassDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (I₃ 0 + m₃ * r₂ ^ 2) θ

/-- **The Christoffel symbols of MLS Example 4.3 as printed on p. 174**, indexed by Lean
indices (`threeLinkArmChristoffel … θ i j k` is the book's `Γ_{(i+1)(j+1)(k+1)}`): the printed
nonzero values

* `Γ₁₁₂ = Γ₁₂₁ = (I_y2 − I_z2 − m₂ r₁²) c₂ s₂ + (I_y3 − I_z3) c₂₃ s₂₃`
  `− m₃ (l₁ c₂ + r₂ c₂₃)(l₁ s₂ + r₂ s₂₃)`,
* `Γ₁₁₃ = Γ₁₃₁ = (I_y3 − I_z3) c₂₃ s₂₃ − m₃ r₂ s₂₃ (l₁ c₂ + r₂ c₂₃)`,
* `Γ₂₁₁ = (I_z2 − I_y2 + m₂ r₁²) c₂ s₂ + (I_z3 − I_y3) c₂₃ s₂₃`
  `+ m₃ (l₁ c₂ + r₂ c₂₃)(l₁ s₂ + r₂ s₂₃)`,
* `Γ₂₂₃ = Γ₂₃₂ = Γ₂₃₃ = −l₁ m₃ r₂ s₃`,
* `Γ₃₁₁ = (I_z3 − I_y3) c₂₃ s₂₃ + m₃ r₂ s₂₃ (l₁ c₂ + r₂ c₂₃)`, `Γ₃₂₂ = l₁ m₃ r₂ s₃`,

and `0` for every other index triple. -/
def threeLinkArmChristoffel (θ : Fin 3 → ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  let c₂ := Real.cos (θ 1)
  let s₂ := Real.sin (θ 1)
  let s₃ := Real.sin (θ 2)
  let c₂₃ := Real.cos (θ 1 + θ 2)
  let s₂₃ := Real.sin (θ 1 + θ 2)
  let Γ₁₁₂ := (I₂ 1 - I₂ 2 - m₂ * r₁ ^ 2) * c₂ * s₂ + (I₃ 1 - I₃ 2) * c₂₃ * s₂₃ -
    m₃ * (l₁ * c₂ + r₂ * c₂₃) * (l₁ * s₂ + r₂ * s₂₃)
  let Γ₁₁₃ := (I₃ 1 - I₃ 2) * c₂₃ * s₂₃ - m₃ * r₂ * s₂₃ * (l₁ * c₂ + r₂ * c₂₃)
  let Γ₂₁₁ := (I₂ 2 - I₂ 1 + m₂ * r₁ ^ 2) * c₂ * s₂ + (I₃ 2 - I₃ 1) * c₂₃ * s₂₃ +
    m₃ * (l₁ * c₂ + r₂ * c₂₃) * (l₁ * s₂ + r₂ * s₂₃)
  let Γ₃₁₁ := (I₃ 2 - I₃ 1) * c₂₃ * s₂₃ + m₃ * r₂ * s₂₃ * (l₁ * c₂ + r₂ * c₂₃)
  ![![![0, Γ₁₁₂, Γ₁₁₃], ![Γ₁₁₂, 0, 0], ![Γ₁₁₃, 0, 0]],
    ![![Γ₂₁₁, 0, 0], ![0, 0, -(l₁ * m₃ * r₂ * s₃)],
      ![0, -(l₁ * m₃ * r₂ * s₃), -(l₁ * m₃ * r₂ * s₃)]],
    ![![Γ₃₁₁, 0, 0], ![0, l₁ * m₃ * r₂ * s₃, 0], ![0, 0, 0]]]

/-- **The Christoffel symbols of MLS Example 4.3 (p. 174) from the general definitions.** For
the inertia matrix of `threeLinkArm`, the Christoffel symbols of eq. (4.22), computed from the
actual partial derivatives `InertialChain.massMatrixDeriv` of the general `M(θ)`, equal the
printed table `threeLinkArmChristoffel` at every configuration and for every index triple (the
printed list of nonzero symbols is complete). -/
theorem threeLinkArm_christoffel (θ : Fin 3 → ℝ) (i j k : Fin 3) :
    Christoffel.symbol
        (Christoffel.partials ((threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).massMatrixDeriv θ))
        i j k =
      threeLinkArmChristoffel m₂ m₃ r₁ r₂ l₁ I₂ I₃ θ i j k := by
  have hD : (threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃).massMatrixDeriv θ =
      tlMassDeriv m₂ m₃ r₁ r₂ l₁ I₂ I₃ θ := by
    funext i j
    exact (tl_hasFDerivAt_massMatrix m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃ θ i j).fderiv
  rw [hD]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Christoffel.symbol, Christoffel.partials, tlMassDeriv, threeLinkArmChristoffel,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

end RoboLean.Examples
