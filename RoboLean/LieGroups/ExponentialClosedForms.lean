import RoboLean.Geometry.HatPowers
import RoboLean.Geometry.TwistExpClosedForm
import RoboLean.Geometry.TwistExpJacobian

/-!
# The closed forms of Examples A.12 and A.15 for the exponential of `se(3)`

MLS Appendix A, §2.3, printed pp. 413–414, for a twist `ξ = (v, ω)` with a nonunit angular part.

* Example A.12 (p. 413): `exp ξ̂ = [[e^{ω̂}, A v], [0, 1]]` for `ω ≠ 0`, with
  `A = I + ω̂ (1 - cos ‖ω‖) / ‖ω‖² + ω̂² (‖ω‖ - sin ‖ω‖) / ‖ω‖³`, and `exp ξ̂ = [[I, v], [0, 1]]`
  for `ω = 0`. The library's exponential (`Twist.exp ξ 1`, the matrix exponential of `ξ̂`) is
  shown to have the translation `A v`; its rotation is `e^{ω̂}` by `Twist.exp_rotation`, and the
  `ω = 0` branch is `Twist.exp_pure_translation`.
* Example A.15 (p. 414): `A⁻¹ = I - ω̂ / 2 + ω̂² (2 sin ‖ω‖ - ‖ω‖ (1 + cos ‖ω‖)) / (2 ‖ω‖² sin ‖ω‖)`.
  Corrected printing: the display is printed under the condition `ω ≠ 0`, but its denominator
  `2 ‖ω‖² sin ‖ω‖` vanishes when `‖ω‖` is a nonzero multiple of `π`; the statement here assumes
  `sin ‖ω‖ ≠ 0` (which implies `ω ≠ 0`), and proves the display is a two-sided inverse of `A`.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Twist

/-- The matrix `A = I + ω̂ (1 - cos ‖ω‖) / ‖ω‖² + ω̂² (‖ω‖ - sin ‖ω‖) / ‖ω‖³` of MLS Example A.12,
printed p. 413, multiplying the linear part `v` in the translation of `exp ξ̂`. -/
def expTranslationMatrix (ω : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + ((1 - Real.cos ‖ω‖) / ‖ω‖ ^ 2) • Vec3.hat ω +
    ((‖ω‖ - Real.sin ‖ω‖) / ‖ω‖ ^ 3) • Vec3.hat ω ^ 2

/-- The matrix
`I - ω̂ / 2 + ω̂² (2 sin ‖ω‖ - ‖ω‖ (1 + cos ‖ω‖)) / (2 ‖ω‖² sin ‖ω‖)` of MLS Example A.15, printed
p. 414, printed as `A⁻¹`. -/
def expTranslationMatrixInv (ω : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 - (1 / 2 : ℝ) • Vec3.hat ω +
    ((2 * Real.sin ‖ω‖ - ‖ω‖ * (1 + Real.cos ‖ω‖)) / (2 * ‖ω‖ ^ 2 * Real.sin ‖ω‖)) •
      Vec3.hat ω ^ 2

/-- Product of two quadratic polynomials in a matrix `W` with `W³ = -θ² W` (MLS equation (2.13),
printed p. 28, for `W = ω̂`, `θ = ‖ω‖`). Supporting lemma. -/
private theorem quadratic_mul (W : Matrix (Fin 3) (Fin 3) ℝ) (θ a b c d : ℝ)
    (hW : W ^ 3 = -(θ ^ 2) • W) :
    (1 + a • W + b • W ^ 2) * (1 + d • W + c • W ^ 2) =
      1 + (a + d - θ ^ 2 * (a * c + b * d)) • W + (b + c + a * d - θ ^ 2 * (b * c)) • W ^ 2 := by
  have h4 : W ^ 4 = -(θ ^ 2) • W ^ 2 := by
    rw [show W ^ 4 = W * W ^ 3 by rw [pow_succ'], hW, Matrix.mul_smul, ← pow_two]
  have e1 : W * W = W ^ 2 := (pow_two W).symm
  have e2 : W * W ^ 2 = W ^ 3 := (pow_succ' W 2).symm
  have e3 : W ^ 2 * W = W ^ 3 := (pow_succ W 2).symm
  have e4 : W ^ 2 * W ^ 2 = W ^ 4 := by rw [← pow_add]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, e1, e2, e3, e4, hW, h4, smul_smul]
  module

/-- Two quadratic polynomials in `W` with `W³ = -θ² W` commute (supporting lemma for MLS
Example A.15, printed p. 414). -/
private theorem quadratic_commute (W : Matrix (Fin 3) (Fin 3) ℝ) (θ a b c d : ℝ)
    (hW : W ^ 3 = -(θ ^ 2) • W) :
    Commute (1 + a • W + b • W ^ 2) (1 + d • W + c • W ^ 2) := by
  unfold Commute SemiconjBy
  rw [quadratic_mul W θ a b c d hW, quadratic_mul W θ d c b a hW,
    show d + a - θ ^ 2 * (d * b + c * a) = a + d - θ ^ 2 * (a * c + b * d) by ring,
    show c + b + d * a - θ ^ 2 * (c * b) = b + c + a * d - θ ^ 2 * (b * c) by ring]

/-- The printed `A⁻¹` of Example A.15 as a quadratic polynomial in `ω̂` (MLS printed p. 414).
Supporting lemma. -/
private theorem expTranslationMatrixInv_eq (ω : Vec3) :
    expTranslationMatrixInv ω = 1 + (-(1 / 2) : ℝ) • Vec3.hat ω +
      ((2 * Real.sin ‖ω‖ - ‖ω‖ * (1 + Real.cos ‖ω‖)) / (2 * ‖ω‖ ^ 2 * Real.sin ‖ω‖)) •
        Vec3.hat ω ^ 2 := by
  rw [expTranslationMatrixInv, neg_smul, ← sub_eq_add_neg]

/-- The scalar identities behind Example A.15 (MLS printed p. 414): with `S = sin θ ≠ 0`,
`C = cos θ`, the coefficients of `ω̂` and `ω̂²` in `A A⁻¹ - I` vanish. Supporting lemma. -/
private theorem coefficients_eq_zero (θ S C : ℝ) (hθ : θ ≠ 0) (hS : S ≠ 0)
    (h : S ^ 2 + C ^ 2 = 1) :
    (1 - C) / θ ^ 2 + -(1 / 2) -
        θ ^ 2 * ((1 - C) / θ ^ 2 * ((2 * S - θ * (1 + C)) / (2 * θ ^ 2 * S)) +
          (θ - S) / θ ^ 3 * -(1 / 2)) = 0 ∧
      (θ - S) / θ ^ 3 + (2 * S - θ * (1 + C)) / (2 * θ ^ 2 * S) + (1 - C) / θ ^ 2 * -(1 / 2) -
        θ ^ 2 * ((θ - S) / θ ^ 3 * ((2 * S - θ * (1 + C)) / (2 * θ ^ 2 * S))) = 0 := by
  constructor
  · field_simp
    linear_combination (-θ) * h
  · field_simp
    linear_combination 0 * h

/-- MLS Example A.12, printed p. 413: for `ω ≠ 0` the translation of `exp ξ̂` is `A v`, with `A`
the matrix `expTranslationMatrix ω`. Coordinates `(v, ω)`; column vectors. -/
theorem exp_one_translation (ξ : Twist) (hω : ξ.angular ≠ 0) :
    (exp ξ 1).translation =
      WithLp.toLp 2 (expTranslationMatrix ξ.angular *ᵥ WithLp.ofLp ξ.linear) := by
  set θ := ‖ξ.angular‖ with hθdef
  have hθ : θ ≠ 0 := norm_ne_zero_iff.mpr hω
  have hu := angular_norm_normalize ξ hω
  rw [exp_normalize_angular ξ hω 1, mul_one, exp_translation_of_angular_norm_eq_one _ hu θ]
  congr 1
  have hM := translationJacobian_eq_trig _ hu θ
  rw [translationJacobian] at hM
  rw [hM]
  have hout (c : ℝ) (v : Vec3) : Vec3.outer (c • v) (c • v) = (c * c) • Vec3.outer v v := by
    ext i j
    simp only [Vec3.outer_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
    ring
  have key : θ⁻¹ • (Real.sin θ • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
      (1 - Real.cos θ) • Vec3.hat (θ⁻¹ • ξ.angular) +
      (θ - Real.sin θ) • Vec3.outer (θ⁻¹ • ξ.angular) (θ⁻¹ • ξ.angular)) =
      expTranslationMatrix ξ.angular := by
    rw [expTranslationMatrix, Vec3.hat_sq, hout, Vec3.hat_smul, ← hθdef]
    rw [smul_add, smul_add, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul,
      smul_smul]
    match_scalars
    all_goals field_simp
    all_goals ring
  change _ = expTranslationMatrix ξ.angular *ᵥ WithLp.ofLp ξ.linear
  rw [← key, Matrix.smul_mulVec]
  change _ *ᵥ WithLp.ofLp (θ⁻¹ • ξ.linear) = _
  rw [WithLp.ofLp_smul, Matrix.mulVec_smul]
  rfl

/-- MLS Example A.15, printed p. 414, corrected printing: when `sin ‖ω‖ ≠ 0` the printed `A⁻¹` is
a right inverse of the matrix `A` of Example A.12. -/
theorem expTranslationMatrix_mul_inv (ω : Vec3) (hs : Real.sin ‖ω‖ ≠ 0) :
    expTranslationMatrix ω * expTranslationMatrixInv ω = 1 := by
  have hθ : ‖ω‖ ≠ 0 := by
    intro h0
    rw [h0, Real.sin_zero] at hs
    exact hs rfl
  have hW : Vec3.hat ω ^ 3 = -(‖ω‖ ^ 2) • Vec3.hat ω := Vec3.hat_cube ω
  rw [expTranslationMatrix, expTranslationMatrixInv_eq, quadratic_mul _ ‖ω‖ _ _ _ _ hW]
  obtain ⟨h1, h2⟩ := coefficients_eq_zero ‖ω‖ (Real.sin ‖ω‖) (Real.cos ‖ω‖) hθ hs
    (Real.sin_sq_add_cos_sq ‖ω‖)
  rw [h1, h2, zero_smul, zero_smul, add_zero, add_zero]

/-- MLS Example A.15, printed p. 414, corrected printing: when `sin ‖ω‖ ≠ 0` the printed `A⁻¹` is
a left inverse of the matrix `A` of Example A.12. -/
theorem expTranslationMatrixInv_mul (ω : Vec3) (hs : Real.sin ‖ω‖ ≠ 0) :
    expTranslationMatrixInv ω * expTranslationMatrix ω = 1 := by
  have hc : Commute (expTranslationMatrixInv ω) (expTranslationMatrix ω) := by
    rw [expTranslationMatrix, expTranslationMatrixInv_eq]
    exact quadratic_commute _ ‖ω‖ _ _ _ _ (Vec3.hat_cube ω)
  rw [hc.eq, expTranslationMatrix_mul_inv ω hs]

end Twist

end RoboLean
