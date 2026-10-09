import RoboLean.Geometry.TwistExp
import RoboLean.Geometry.Rodrigues

/-!
# Closed forms for actual twist matrix exponentials

MLS printed pp. 40–42, equations (2.28), (2.32), and (2.36). The angular
norm-one premise used in the derivation on p. 41 is explicit below. Scaling
an arbitrary nonzero angular component rescales the full twist `(v, ω)`.
-/

open Matrix
open scoped Matrix.Norms.Operator

noncomputable section

namespace RoboLean.Twist

private theorem hat_vec3_zero : Vec3.hat (0 : Vec3) = 0 := by
  change (Vec3.hatLinearEquiv (0 : Vec3)).val = 0
  rw [map_zero]
  rfl

private theorem exp_eq_of_hasDerivAt (A : HomogeneousMatrix)
    (P : ℝ → HomogeneousMatrix)
    (hP : ∀ s, HasDerivAt P (A * P s) s) (h0 : P 0 = 1) (t : ℝ) :
    NormedSpace.exp (t • A) = P t := by
  have hF (s : ℝ) :
      HasDerivAt (fun r ↦ NormedSpace.exp (r • (-A)) * P r) 0 s := by
    have h := (hasDerivAt_exp_smul_const (-A) s).mul (hP s)
    convert! h using 1
    simp [mul_assoc]
  have hconst := is_const_of_deriv_eq_zero
    (fun s ↦ (hF s).differentiableAt) (fun s ↦ (hF s).deriv) t 0
  have hprod : NormedSpace.exp (t • (-A)) * P t = 1 := by
    simpa [h0] using hconst
  have hcancel : NormedSpace.exp (t • A) * NormedSpace.exp (t • (-A)) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • A)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have h := congrArg (fun M ↦ NormedSpace.exp (t • A) * M) hprod
  rw [← mul_assoc, hcancel, one_mul, mul_one] at h
  exact h.symm

/-- Positive powers have an explicit upper triangular block form. -/
theorem hat_pow_succ (ξ : Twist) (n : ℕ) :
    ξ.hat ^ (n + 1) = Matrix.fromBlocks
      (Vec3.hat ξ.angular ^ (n + 1))
      (Vec3.hat ξ.angular ^ n * Matrix.of (fun i (_ : Fin 1) ↦ ξ.linear i))
      0 0 := by
  induction n with
  | zero => simp [hat]
  | succ n ih =>
    rw [pow_succ, ih, hat, Matrix.fromBlocks_multiply]
    simp [← pow_succ]

/-- The pure translation generator is nilpotent of index at most two. -/
theorem hat_pure_translation_sq (v : Vec3) : hat ⟨v, 0⟩ ^ 2 = 0 := by
  rw [hat_pow_succ ⟨v, 0⟩ 1]
  simp [hat_vec3_zero]

/-- MLS equation (2.32); `v` need not be a unit vector, and zero is allowed. -/
theorem exp_hat_pure_translation (v : Vec3) (t : ℝ) :
    NormedSpace.exp (t • hat ⟨v, 0⟩) =
      (⟨1, t • v⟩ : RigidTransform).toHomogeneous := by
  let A := hat ⟨v, 0⟩
  have hA : A * A = 0 := by
    simpa only [A, pow_two] using hat_pure_translation_sq v
  have hP (s : ℝ) : HasDerivAt (fun r : ℝ ↦ 1 + r • A) (A * (1 + s • A)) s := by
    convert! ((hasDerivAt_id s).smul_const A).const_add
      (1 : HomogeneousMatrix) using 1
    simp [mul_add, hA]
  rw [exp_eq_of_hasDerivAt A _ hP (by simp) t]
  change (1 : HomogeneousMatrix) + t • Matrix.fromBlocks (Vec3.hat 0)
    (Matrix.of fun i (_ : Fin 1) ↦ v i) 0 0 =
    Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) ↦ (t • v) i) 0 1
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  simp only [hat_vec3_zero, smul_zero, add_zero, zero_add]
  rfl

/-- The fourth-power relation underlying the unit-angular closed form. -/
theorem hat_pow_four_of_angular_norm_eq_one (ξ : Twist) (hω : ‖ξ.angular‖ = 1) :
    ξ.hat ^ 4 = -(ξ.hat ^ 2) := by
  have hcube := Vec3.hat_cube_of_norm_eq_one ξ.angular hω
  have hfour : Vec3.hat ξ.angular ^ 4 = -(Vec3.hat ξ.angular ^ 2) := by
    rw [show 4 = 3 + 1 from rfl, pow_succ, hcube, neg_mul, ← pow_two]
  rw [hat_pow_succ ξ 3, hat_pow_succ ξ 1, Matrix.fromBlocks_neg]
  simp [hcube, hfour]

/-- The actual exponential is a cubic polynomial for a unit angular component. -/
theorem exp_hat_polynomial_of_angular_norm_eq_one
    (ξ : Twist) (hω : ‖ξ.angular‖ = 1) (t : ℝ) :
    NormedSpace.exp (t • ξ.hat) =
      1 + t • ξ.hat + (1 - Real.cos t) • ξ.hat ^ 2 +
        (t - Real.sin t) • ξ.hat ^ 3 := by
  let A := ξ.hat
  let P : ℝ → HomogeneousMatrix := fun s ↦
    1 + s • A + (1 - Real.cos s) • A ^ 2 + (s - Real.sin s) • A ^ 3
  have hfour : A * A ^ 3 = -(A ^ 2) := by
    simpa only [← pow_succ', A] using hat_pow_four_of_angular_norm_eq_one ξ hω
  have hP (s : ℝ) : HasDerivAt P (A * P s) s := by
    have hlin := ((hasDerivAt_id s).smul_const A).const_add
      (1 : HomogeneousMatrix)
    have hcos := ((Real.hasDerivAt_cos s).const_sub 1).smul_const (A ^ 2)
    have hsin := ((hasDerivAt_id s).sub (Real.hasDerivAt_sin s)).smul_const (A ^ 3)
    convert! (hlin.add hcos).add hsin using 1
    dsimp [P]
    rw [mul_add, mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, hfour, ← pow_two, ← pow_succ']
    module
  exact exp_eq_of_hasDerivAt A P hP (by simp [P]) t

/-- MLS equation (2.36), retaining the unit-axis premise from its derivation.

The translation column is `((I-R) hat(ω) + t ωωᵀ) v`.
-/
theorem exp_hat_of_angular_norm_eq_one
    (ξ : Twist) (hω : ‖ξ.angular‖ = 1) (t : ℝ) :
    NormedSpace.exp (t • ξ.hat) = Matrix.fromBlocks
      (NormedSpace.exp (t • Vec3.hat ξ.angular))
      (((1 - NormedSpace.exp (t • Vec3.hat ξ.angular)) * Vec3.hat ξ.angular +
          t • Vec3.outer ξ.angular ξ.angular) *
        Matrix.of (fun i (_ : Fin 1) ↦ ξ.linear i)) 0 1 := by
  let W := Vec3.hat ξ.angular
  let V : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun i _ ↦ ξ.linear i
  have hcube : W ^ 3 = -W := Vec3.hat_cube_of_norm_eq_one ξ.angular hω
  have houter : Vec3.outer ξ.angular ξ.angular = W ^ 2 + 1 := by
    rw [Vec3.hat_sq_of_norm_eq_one ξ.angular hω]
    module
  have hR : NormedSpace.exp (t • W) =
      1 + Real.sin t • W + (1 - Real.cos t) • W ^ 2 :=
    Vec3.exp_hat_of_norm_eq_one ξ.angular hω t
  have hJ : t • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
      (1 - Real.cos t) • W + (t - Real.sin t) • W ^ 2 =
      (1 - NormedSpace.exp (t • W)) * W + t • Vec3.outer ξ.angular ξ.angular := by
    rw [hR, houter, sub_mul, add_mul, add_mul, one_mul,
      Matrix.smul_mul, Matrix.smul_mul, ← pow_two, ← pow_succ, hcube]
    module
  rw [exp_hat_polynomial_of_angular_norm_eq_one ξ hω t,
    hat_pow_succ ξ 1, hat_pow_succ ξ 2]
  simp only [pow_one]
  change (1 : HomogeneousMatrix) + t • Matrix.fromBlocks W V 0 0 +
      (1 - Real.cos t) • Matrix.fromBlocks (W ^ 2) (W * V) 0 0 +
      (t - Real.sin t) • Matrix.fromBlocks (W ^ 3) (W ^ 2 * V) 0 0 = _
  rw [← Matrix.fromBlocks_one]
  simp only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, smul_zero,
    add_zero, zero_add]
  congr 1
  · rw [hR, hcube]
    module
  · rw [← hJ]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    rfl

/-- Nonzero-angular normalization divides both linear and angular coordinates. -/
theorem exp_hat_normalize_angular (ξ : Twist) (hω : ξ.angular ≠ 0) (t : ℝ) :
    NormedSpace.exp (t • ξ.hat) =
      NormedSpace.exp ((‖ξ.angular‖ * t) • hat (‖ξ.angular‖⁻¹ • ξ)) := by
  have hn : ‖ξ.angular‖ ≠ 0 := norm_ne_zero_iff.mpr hω
  rw [hat_smul, smul_smul]
  congr 2
  field_simp [hn]

/-- Full-twist normalization produces a unit angular component. -/
theorem angular_norm_normalize (ξ : Twist) (hω : ξ.angular ≠ 0) :
    ‖(‖ξ.angular‖⁻¹ • ξ : Twist).angular‖ = 1 := by
  change ‖‖ξ.angular‖⁻¹ • ξ.angular‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hω)]

/-- Explicit zero-angular branch for an arbitrary twist. -/
theorem exp_hat_of_angular_eq_zero (ξ : Twist) (hω : ξ.angular = 0) (t : ℝ) :
    NormedSpace.exp (t • ξ.hat) =
      (⟨1, t • ξ.linear⟩ : RigidTransform).toHomogeneous := by
  rcases ξ with ⟨v, ω⟩
  change ω = 0 at hω
  subst ω
  exact exp_hat_pure_translation v t

/-- The rigid transform generated by any pure translation, including zero. -/
@[simp] theorem exp_pure_translation (v : Vec3) (t : ℝ) :
    exp ⟨v, 0⟩ t = (⟨1, t • v⟩ : RigidTransform) := by
  apply RigidTransform.toHomogeneous_injective
  rw [toHomogeneous_exp, exp_hat_pure_translation]

/-- Coordinate-vector version of the unit-angular translation block in (2.36). -/
theorem exp_translation_of_angular_norm_eq_one
    (ξ : Twist) (hω : ‖ξ.angular‖ = 1) (t : ℝ) :
    (exp ξ t).translation = WithLp.toLp 2
      (((1 - NormedSpace.exp (t • Vec3.hat ξ.angular)) * Vec3.hat ξ.angular +
          t • Vec3.outer ξ.angular ξ.angular) *ᵥ WithLp.ofLp ξ.linear) := by
  apply WithLp.ofLp_injective
  funext i
  have h := congrArg (fun M : HomogeneousMatrix ↦ M (Sum.inl i) (Sum.inr 0))
    (exp_hat_of_angular_norm_eq_one ξ hω t)
  rw [← toHomogeneous_exp] at h
  exact h

/-- Group-level normalization, scaling both components and the parameter. -/
theorem exp_normalize_angular (ξ : Twist) (hω : ξ.angular ≠ 0) (t : ℝ) :
    exp ξ t = exp (‖ξ.angular‖⁻¹ • ξ) (‖ξ.angular‖ * t) := by
  apply RigidTransform.toHomogeneous_injective
  simpa only [toHomogeneous_exp] using exp_hat_normalize_angular ξ hω t

end RoboLean.Twist
