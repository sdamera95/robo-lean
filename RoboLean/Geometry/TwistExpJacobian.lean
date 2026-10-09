import RoboLean.Geometry.TwistExpClosedForm

/-!
# Nonsingularity of the unit-axis translation coefficient

MLS printed p. 43, equation (2.38), requires solving the translation equation
for a unit angular axis and `0 < θ < 2π`. The determinant is computed here
from the actual rotation exponential. This does not prove rotation or rigid
exponential surjectivity, or define a global logarithm.
-/

open Matrix
open scoped Matrix.Norms.Operator

noncomputable section

namespace RoboLean.Twist

/-- Translation coefficient multiplying `v` in the unit-angular exponential. -/
def translationJacobian (ω : Vec3) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - NormedSpace.exp (t • Vec3.hat ω)) * Vec3.hat ω + t • Vec3.outer ω ω

private theorem det_smul_one_add_hat_add_outer (ω : Vec3) (a b c : ℝ) :
    (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • Vec3.hat ω +
      c • Vec3.outer ω ω).det =
      (a + c * ‖ω‖ ^ 2) * (a ^ 2 + b ^ 2 * ‖ω‖ ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.det_fin_three, Vec3.hat, Vec3.outer, Matrix.vecMulVec,
    Fin.sum_univ_succ]
  ring

/-- A polynomial expression for the actual-exponential coefficient. -/
theorem translationJacobian_eq_trig (ω : Vec3) (hω : ‖ω‖ = 1) (t : ℝ) :
    translationJacobian ω t =
      Real.sin t • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
        (1 - Real.cos t) • Vec3.hat ω +
        (t - Real.sin t) • Vec3.outer ω ω := by
  rw [translationJacobian, Vec3.exp_hat_of_norm_eq_one ω hω t,
    sub_mul, add_mul, add_mul, one_mul, Matrix.smul_mul, Matrix.smul_mul,
    ← pow_two, ← pow_succ, Vec3.hat_cube_of_norm_eq_one ω hω,
    Vec3.hat_sq_of_norm_eq_one ω hω]
  module

/-- Exact determinant of the translation coefficient, with no restriction on `t`. -/
theorem det_translationJacobian (ω : Vec3) (hω : ‖ω‖ = 1) (t : ℝ) :
    (translationJacobian ω t).det = 2 * t * (1 - Real.cos t) := by
  rw [translationJacobian_eq_trig ω hω t, det_smul_one_add_hat_add_outer, hω]
  simp only [one_pow, mul_one]
  have htrig : Real.sin t ^ 2 + (1 - Real.cos t) ^ 2 = 2 * (1 - Real.cos t) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [htrig]
  ring

/-- The interval from MLS equation (2.38) excludes zero and full turns. -/
theorem det_translationJacobian_ne_zero (ω : Vec3) (hω : ‖ω‖ = 1)
    (t : ℝ) (ht0 : 0 < t) (ht2π : t < 2 * Real.pi) :
    (translationJacobian ω t).det ≠ 0 := by
  have hcos : Real.cos t ≠ 1 := by
    intro h
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [Real.pi_pos] : -(2 * Real.pi) < t) ht2π).mp h
    exact (ne_of_gt ht0) hz
  rw [det_translationJacobian ω hω t]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt ht0))
    (sub_ne_zero.mpr (Ne.symm hcos))

/-- Actual matrix invertibility, derived from the interval and unit-axis premises. -/
theorem isUnit_translationJacobian (ω : Vec3) (hω : ‖ω‖ = 1)
    (t : ℝ) (ht0 : 0 < t) (ht2π : t < 2 * Real.pi) :
    IsUnit (translationJacobian ω t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (det_translationJacobian_ne_zero ω hω t ht0 ht2π)

/-- The translation equation has at most one solution on the stated interval. -/
theorem translationJacobian_mulVec_injective (ω : Vec3) (hω : ‖ω‖ = 1)
    (t : ℝ) (ht0 : 0 < t) (ht2π : t < 2 * Real.pi) :
    Function.Injective (Matrix.mulVec (translationJacobian ω t)) :=
  Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_translationJacobian ω hω t ht0 ht2π)

/-- The inverse coefficient supplies a solution for every translation column. -/
theorem translationJacobian_mulVec_inv_mulVec (ω : Vec3) (hω : ‖ω‖ = 1)
    (t : ℝ) (ht0 : 0 < t) (ht2π : t < 2 * Real.pi) (p : Fin 3 → ℝ) :
    translationJacobian ω t *ᵥ ((translationJacobian ω t)⁻¹ *ᵥ p) = p := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (det_translationJacobian_ne_zero ω hω t ht0 ht2π)),
    Matrix.one_mulVec]

/-- A full turn is singular; merely assuming a nonzero angle is insufficient. -/
theorem det_translationJacobian_two_pi (ω : Vec3) (hω : ‖ω‖ = 1) :
    (translationJacobian ω (2 * Real.pi)).det = 0 := by
  simp [det_translationJacobian ω hω]

end RoboLean.Twist
