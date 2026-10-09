import RoboLean.Geometry.Hat
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Rotation exponentials and constant-axis trajectories

`Rotation.exp ω t` uses Mathlib's actual matrix exponential `exp (t • hat ω)`.
The axis is arbitrary, including zero. Only for a unit axis does the parameter
`t` itself have the angle in radians and unit angular-rate interpretation of MLS equations
(2.8)–(2.9). The proofs of membership in `SO(3)` do not use Rodrigues' formula.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Rotation

/-- The exponential of a real skew matrix is orthogonal. -/
theorem matrix_exp_transpose_mul (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A) :
    (NormedSpace.exp A)ᵀ * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_transpose, hA,
    ← Matrix.exp_add_of_commute (-A) A (Commute.refl A).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

/-- MLS Proposition 2.4: an arbitrary real skew matrix exponentiates into `SO(3)`.
The determinant is nonnegative because the exponential is the square of the
half-parameter exponential; orthogonality then makes it equal to one. -/
theorem matrix_exp_mem (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A) :
    NormedSpace.exp A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have horth := matrix_exp_transpose_mul A hA
  refine ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr horth, ?_⟩
  have hdet := congrArg Matrix.det horth
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hhalf : NormedSpace.exp A =
      NormedSpace.exp ((1 / 2 : ℝ) • A) * NormedSpace.exp ((1 / 2 : ℝ) • A) := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  have hnonneg : 0 ≤ (NormedSpace.exp A).det := by
    rw [hhalf, Matrix.det_mul]
    exact mul_self_nonneg _
  change (NormedSpace.exp A).det = 1
  nlinarith

/-- The exponential map from real skew matrices with an explicit real parameter. -/
noncomputable def expSkew (A : SkewMatrix3) (t : ℝ) : Rotation :=
  ⟨NormedSpace.exp (t • A.val), matrix_exp_mem _ (by
    rw [Matrix.transpose_smul, (mem_skewMatrix3_iff _).mp A.property, smul_neg])⟩

@[simp] theorem expSkew_val (A : SkewMatrix3) (t : ℝ) :
    (expSkew A t).val = NormedSpace.exp (t • A.val) := rfl

@[simp] theorem expSkew_zero (A : SkewMatrix3) : expSkew A 0 = 1 := by
  apply Subtype.ext
  simp

/-- A constant-axis rotation, defined by the power-series matrix exponential. -/
noncomputable def exp (ω : Vec3) (t : ℝ) : Rotation :=
  expSkew (Vec3.hatLinearEquiv ω) t

@[simp] theorem exp_val (ω : Vec3) (t : ℝ) :
    (exp ω t).val = NormedSpace.exp (t • Vec3.hat ω) := rfl

/-- Matrix coordinates of the exponential action on the initial point. -/
theorem exp_act_coordinates (ω q : Vec3) (t : ℝ) :
    WithLp.ofLp ((exp ω t).act q) =
      NormedSpace.exp (t • Vec3.hat ω) *ᵥ WithLp.ofLp q := rfl

@[simp] theorem exp_zero (ω : Vec3) : exp ω 0 = 1 :=
  expSkew_zero _

@[simp] theorem exp_zero_axis (t : ℝ) : exp 0 t = 1 := by
  apply Subtype.ext
  have hz : Vec3.hat (0 : Vec3) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Vec3.hat]
  change NormedSpace.exp (t • Vec3.hat 0) = 1
  rw [hz, smul_zero, NormedSpace.exp_zero]

/-- The one-parameter composition law for a fixed, possibly nonunit, axis. -/
theorem exp_add (ω : Vec3) (s t : ℝ) : exp ω (s + t) = exp ω s * exp ω t := by
  apply Subtype.ext
  change NormedSpace.exp ((s + t) • Vec3.hat ω) =
    NormedSpace.exp (s • Vec3.hat ω) * NormedSpace.exp (t • Vec3.hat ω)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Vec3.hat ω)).smul_left s).smul_right t)

@[simp] theorem exp_neg (ω : Vec3) (t : ℝ) : exp ω (-t) = (exp ω t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← exp_add, neg_add_cancel, exp_zero]

/-- Rescaling the axis rescales its parameter; there is no normalization premise. -/
theorem exp_smul (c : ℝ) (ω : Vec3) (t : ℝ) : exp (c • ω) t = exp ω (t * c) := by
  apply Subtype.ext
  simp [Vec3.hat_smul, smul_smul]

/-- The matrix-coordinate derivative of the actual exponential path. -/
theorem hasDerivAt_exp_val (ω : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (exp ω s).val)
      (Vec3.hat ω * (exp ω t).val) t :=
  hasDerivAt_exp_smul_const' (Vec3.hat ω) t

/-- MLS (2.8): the exponential action solves `q̇ = ω × q` for a constant axis. -/
theorem hasDerivAt_exp_act (ω q : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (exp ω s).act q)
      (Vec3.cross ω ((exp ω t).act q)) t := by
  let L : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Vec3 :=
    (LinearMap.applyₗ (R := ℝ) (M₂ := Vec3) q).comp Matrix.toEuclideanLin.toLinearMap
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_val ω t)
  change HasDerivAt (fun s : ℝ ↦ (exp ω s).act q)
    (Matrix.toEuclideanLin (Vec3.hat ω * (exp ω t).val) q) t at h
  convert h using 1
  apply WithLp.ofLp_injective
  change WithLp.ofLp (Vec3.cross ω ((exp ω t).act q)) =
    (Vec3.hat ω * (exp ω t).val) *ᵥ WithLp.ofLp q
  rw [← Matrix.mulVec_mulVec, Vec3.hat_mulVec]
  rfl

/-- The initial condition for every initial point and every constant axis. -/
@[simp] theorem exp_zero_act (ω q : Vec3) : (exp ω 0).act q = q := by
  rw [exp_zero, act_one]

end Rotation
end RoboLean
