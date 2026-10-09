import RoboLean.Geometry.HatPowers
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module

/-!
# Rodrigues formulas for the actual matrix exponential

The unit-axis formula is identified with Mathlib's exponential by differentiating
an integrating factor. The general nonzero-axis formula follows by normalization;
the zero axis is stated separately. The vector norm is Euclidean throughout.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean.Vec3

/-- MLS equation (2.14), as an equality with the matrix exponential. -/
theorem exp_hat_of_norm_eq_one (v : Vec3) (hv : ‖v‖ = 1) (t : ℝ) :
    NormedSpace.exp (t • hat v) =
      1 + Real.sin t • hat v + (1 - Real.cos t) • hat v ^ 2 := by
  let A := hat v
  let P : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun s ↦ 1 + Real.sin s • A + (1 - Real.cos s) • A ^ 2
  have hcube : A * A ^ 2 = -A := by
    simpa only [← pow_succ'] using hat_cube_of_norm_eq_one v hv
  have hP (s : ℝ) : HasDerivAt P (A * P s) s := by
    have hsin := ((Real.hasDerivAt_sin s).smul_const A).const_add
      (1 : Matrix (Fin 3) (Fin 3) ℝ)
    have hcos := ((Real.hasDerivAt_cos s).const_sub 1).smul_const (A ^ 2)
    convert! hsin.add hcos using 1
    rw [mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul,
      ← pow_two, hcube]
    module
  have hF (s : ℝ) :
      HasDerivAt (fun r ↦ NormedSpace.exp (r • (-A)) * P r) 0 s := by
    have h := (hasDerivAt_exp_smul_const (-A) s).mul (hP s)
    convert! h using 1
    simp [mul_assoc]
  have hconst := is_const_of_deriv_eq_zero
    (fun s ↦ (hF s).differentiableAt) (fun s ↦ (hF s).deriv) t 0
  have hprod : NormedSpace.exp (t • (-A)) * P t = 1 := by
    simpa [P] using hconst
  have hcancel : NormedSpace.exp (t • A) * NormedSpace.exp (t • (-A)) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • A)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have h := congrArg (fun M ↦ NormedSpace.exp (t • A) * M) hprod
  rw [← mul_assoc, hcancel, one_mul, mul_one] at h
  exact h.symm

/-- The nonzero-axis formula below MLS equation (2.14), with its denominator condition. -/
theorem exp_hat_of_ne_zero (v : Vec3) (hv : v ≠ 0) (t : ℝ) :
    NormedSpace.exp (t • hat v) =
      1 + (Real.sin (‖v‖ * t) / ‖v‖) • hat v +
        ((1 - Real.cos (‖v‖ * t)) / ‖v‖ ^ 2) • hat v ^ 2 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖NormedSpace.normalize v‖ = 1 := NormedSpace.norm_normalize hv
  have h := exp_hat_of_norm_eq_one (NormedSpace.normalize v) hu (‖v‖ * t)
  have hscale : (‖v‖ * t) • hat (NormedSpace.normalize v) = t • hat v := by
    rw [NormedSpace.normalize, hat_smul, smul_smul]
    congr 1
    field_simp [hn]
  rw [hscale, NormedSpace.normalize, hat_smul, smul_pow, smul_smul, smul_smul] at h
  simpa only [div_eq_mul_inv, inv_pow] using h

/-- The zero axis gives the identity for every parameter value. -/
@[simp] theorem exp_hat_zero (t : ℝ) :
    NormedSpace.exp (t • hat (0 : Vec3)) = 1 := by
  have hzero : hat (0 : Vec3) = 0 := by
    change (hatLinearEquiv (0 : Vec3)).val = 0
    rw [map_zero]
    rfl
  simp [hzero]

end RoboLean.Vec3
