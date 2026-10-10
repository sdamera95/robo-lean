import RoboLean.Geometry.ElementaryRotations
import RoboLean.Geometry.RotationSurjectivity

/-!
# Ordered ZYZ Euler rotations

MLS printed p. 32, equation (2.19). The expanded matrix is an independent
component specification, compared with the ordered product `Rz(α) Ry(β) Rz(γ)`.
The inverse uses an explicit argument branch and a strictly positive middle-angle
sine. It makes no global-coordinate or singular-branch reconstruction claim.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Rotation

/-- The independently displayed ZYZ component formula in MLS (2.19). -/
def zyzMatrix (α β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos α * Real.cos β * Real.cos γ - Real.sin α * Real.sin γ,
      -Real.cos α * Real.cos β * Real.sin γ - Real.sin α * Real.cos γ,
      Real.cos α * Real.sin β;
    Real.sin α * Real.cos β * Real.cos γ + Real.cos α * Real.sin γ,
      -Real.sin α * Real.cos β * Real.sin γ + Real.cos α * Real.cos γ,
      Real.sin α * Real.sin β;
    -Real.sin β * Real.cos γ, Real.sin β * Real.sin γ, Real.cos β]

/-- The ordered ZYZ group product. The right factor acts first on column coordinates. -/
def zyz (α β γ : ℝ) : Rotation := zRotation α * yRotation β * zRotation γ

/-- The actual product of elementary rotations agrees with all nine independently
specified components in MLS equation (2.19), for all real angles. -/
theorem zyz_val (α β γ : ℝ) : (zyz α β γ).val = zyzMatrix α β γ := by
  change (zRotation α).val * (yRotation β).val * (zRotation γ).val = zyzMatrix α β γ
  rw [zRotation_matrix, yRotation_val, zRotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yMatrix, zMatrix, zyzMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Every displayed ZYZ matrix is a proper rotation. -/
theorem zyzMatrix_mem (α β γ : ℝ) :
    zyzMatrix α β γ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [← zyz_val]
  exact (zyz α β γ).property

@[simp] theorem det_zyzMatrix (α β γ : ℝ) : (zyzMatrix α β γ).det = 1 :=
  (zyzMatrix_mem α β γ).2

/-- The identity family explicitly noted after MLS (2.20). This witnesses
parameter nonuniqueness at a singular middle angle; it is not an inverse theorem. -/
theorem zyz_identity_family (α : ℝ) : zyz α 0 (-α) = 1 := by
  rw [zyz, ← exp_yAxis, exp_zero, mul_one]
  change exp zAxis α * exp zAxis (-α) = 1
  rw [← exp_add, add_neg_cancel, exp_zero]

/-- `atan2(y,x)` with the explicit complex-argument branch `(-π,π]`.
The inverse theorem below ensures that every input pair lies on the unit circle. -/
def atan2 (y x : ℝ) : ℝ := Complex.arg ⟨x, y⟩

private theorem atan2_unit_trig (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    Real.cos (atan2 y x) = x ∧ Real.sin (atan2 y x) = y := by
  let z : ℂ := ⟨x, y⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    change Real.sqrt (x * x + y * y) = 1
    rw [show x * x + y * y = 1 by simpa only [pow_two] using h, Real.sqrt_one]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hc := Complex.cos_arg hz
  have hs := Complex.sin_arg z
  rw [hn, div_one] at hc hs
  exact ⟨by simpa only [atan2, z] using hc, by simpa only [atan2, z] using hs⟩

/-- Polar form of the first argument of `atan2` (MLS p. 100, Subproblem 1; MLS p. 98,
eq. (3.16) and the formula for `θ₁`): `√(x² + y²) cos(atan2(y, x)) = x`, including the origin,
where this `atan2` is `0`. -/
theorem sqrt_mul_cos_atan2 (y x : ℝ) :
    √(x ^ 2 + y ^ 2) * Real.cos (atan2 y x) = x := by
  have hn : ‖(⟨x, y⟩ : ℂ)‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    ring_nf
  by_cases hz : (⟨x, y⟩ : ℂ) = 0
  · have hx : x = 0 := congrArg Complex.re hz
    have hy : y = 0 := congrArg Complex.im hz
    simp [hx, hy]
  · have hn0 : ‖(⟨x, y⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [atan2, Complex.cos_arg hz, ← hn]
    field_simp

/-- Polar form of the second argument of `atan2` (MLS p. 100, Subproblem 1; MLS p. 98,
eq. (3.16) and the formula for `θ₁`): `√(x² + y²) sin(atan2(y, x)) = y`, including the
origin. -/
theorem sqrt_mul_sin_atan2 (y x : ℝ) :
    √(x ^ 2 + y ^ 2) * Real.sin (atan2 y x) = y := by
  have hn : ‖(⟨x, y⟩ : ℂ)‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    ring_nf
  by_cases hz : (⟨x, y⟩ : ℂ) = 0
  · have hx : x = 0 := congrArg Complex.re hz
    have hy : y = 0 := congrArg Complex.im hz
    simp [hx, hy]
  · have hn0 : ‖(⟨x, y⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [atan2, Complex.sin_arg, ← hn]
    field_simp

/-- The nonnegative radial quantity in the first line of MLS (2.20). -/
def zyzRadial (R : Rotation) : ℝ := Real.sqrt (R.val 2 0 ^ 2 + R.val 2 1 ^ 2)

/-- The middle-angle branch chosen in MLS (2.20). -/
def zyzBeta (R : Rotation) : ℝ := atan2 (zyzRadial R) (R.val 2 2)

/-- First Euler angle on the branch where `zyzRadial R = sin β > 0`. -/
def zyzAlpha (R : Rotation) : ℝ := atan2 (R.val 1 2 / zyzRadial R) (R.val 0 2 / zyzRadial R)

/-- Last Euler angle on the same branch; the first argument retains the printed sign. -/
def zyzGamma (R : Rotation) : ℝ := atan2 (R.val 2 1 / zyzRadial R) (-R.val 2 0 / zyzRadial R)

private theorem row_two_sq (R : Rotation) :
    R.val 2 0 ^ 2 + R.val 2 1 ^ 2 + R.val 2 2 ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) R.mul_transpose
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h

private theorem col_two_sq (R : Rotation) :
    R.val 0 2 ^ 2 + R.val 1 2 ^ 2 + R.val 2 2 ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) R.transpose_mul
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h

private theorem zyzRadial_sq (R : Rotation) :
    zyzRadial R ^ 2 = R.val 2 0 ^ 2 + R.val 2 1 ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The chosen beta has exactly the third diagonal entry as its cosine. -/
theorem cos_zyzBeta (R : Rotation) : Real.cos (zyzBeta R) = R.val 2 2 := by
  exact (atan2_unit_trig (R.val 2 2) (zyzRadial R)
    (by nlinarith [row_two_sq R, zyzRadial_sq R])).1

/-- The chosen beta has the nonnegative radial quantity as its sine. -/
theorem sin_zyzBeta (R : Rotation) : Real.sin (zyzBeta R) = zyzRadial R := by
  exact (atan2_unit_trig (R.val 2 2) (zyzRadial R)
    (by nlinarith [row_two_sq R, zyzRadial_sq R])).2

/-- A positive radial quantity places the chosen beta strictly between zero and pi. -/
theorem zyzBeta_mem_Ioo (R : Rotation) (hr : 0 < zyzRadial R) :
    0 < zyzBeta R ∧ zyzBeta R < Real.pi := by
  have h0 : 0 ≤ zyzBeta R := Complex.arg_nonneg_iff.mpr (le_of_lt hr)
  have hπ : zyzBeta R ≤ Real.pi := Complex.arg_le_pi _
  have hn0 : zyzBeta R ≠ 0 := by
    intro h
    have hs := sin_zyzBeta R
    rw [h, Real.sin_zero] at hs
    linarith
  have hnπ : zyzBeta R ≠ Real.pi := by
    intro h
    have hs := sin_zyzBeta R
    rw [h, Real.sin_pi] at hs
    linarith
  exact ⟨lt_of_le_of_ne h0 (Ne.symm hn0), lt_of_le_of_ne hπ hnπ⟩

/-- MLS (2.20), on its nonsingular positive-sine branch: the computed Euler
angles reconstruct an arbitrary proper rotation. Both zero-sine endpoints are
excluded by the explicit radial premise. -/
theorem zyz_inverse (R : Rotation) (hr : 0 < zyzRadial R) :
    zyz (zyzAlpha R) (zyzBeta R) (zyzGamma R) = R := by
  have hr0 : zyzRadial R ≠ 0 := ne_of_gt hr
  have hαunit : (R.val 0 2 / zyzRadial R) ^ 2 + (R.val 1 2 / zyzRadial R) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div]
    have hn : R.val 0 2 ^ 2 + R.val 1 2 ^ 2 = zyzRadial R ^ 2 := by
      nlinarith [row_two_sq R, col_two_sq R, zyzRadial_sq R]
    rw [hn, div_self (pow_ne_zero 2 hr0)]
  obtain ⟨hca, hsa⟩ := atan2_unit_trig (R.val 0 2 / zyzRadial R)
    (R.val 1 2 / zyzRadial R) hαunit
  change Real.cos (zyzAlpha R) = _ at hca
  change Real.sin (zyzAlpha R) = _ at hsa
  let T := zRotation (zyzAlpha R) * yRotation (zyzBeta R)
  have hcol : T.act zAxis = R.act zAxis := by
    apply WithLp.ofLp_injective
    change ((zRotation (zyzAlpha R)).val * (yRotation (zyzBeta R)).val) *ᵥ WithLp.ofLp zAxis =
      R.val *ᵥ WithLp.ofLp zAxis
    rw [zRotation_matrix, yRotation_val]
    ext i
    fin_cases i <;>
      simp [zMatrix, yMatrix, zAxis, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, hca, hsa, cos_zyzBeta, sin_zyzBeta, hr0]
  let S := T⁻¹ * R
  have hsfix : S.act zAxis = zAxis := by
    change (T⁻¹ * R).act zAxis = zAxis
    rw [act_mul, ← hcol, inv_act_act]
  have hz : ‖zAxis‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [zAxis, Fin.sum_univ_succ]
  obtain ⟨γ, _, _, hγ⟩ := exists_angle_exp_eq_of_fixed_axis S zAxis hz hsfix
  have hrep : zyz (zyzAlpha R) (zyzBeta R) γ = R := by
    change T * exp zAxis γ = R
    rw [hγ]
    simp only [S, mul_inv_cancel_left]
  have hrow0 : -zyzRadial R * Real.cos γ = R.val 2 0 := by
    have h := congrArg (fun Q : Rotation => Q.val 2 0) hrep
    simpa [zyz_val, zyzMatrix, sin_zyzBeta] using h
  have hrow1 : zyzRadial R * Real.sin γ = R.val 2 1 := by
    have h := congrArg (fun Q : Rotation => Q.val 2 1) hrep
    simpa [zyz_val, zyzMatrix, sin_zyzBeta] using h
  have hcg : -R.val 2 0 / zyzRadial R = Real.cos γ := by
    apply (div_eq_iff hr0).mpr
    nlinarith [hrow0]
  have hsg : R.val 2 1 / zyzRadial R = Real.sin γ := by
    apply (div_eq_iff hr0).mpr
    nlinarith [hrow1]
  obtain ⟨hcγ, hsγ⟩ := atan2_unit_trig (-R.val 2 0 / zyzRadial R)
    (R.val 2 1 / zyzRadial R) (by rw [hcg, hsg]; nlinarith [Real.sin_sq_add_cos_sq γ])
  change Real.cos (zyzGamma R) = _ at hcγ
  change Real.sin (zyzGamma R) = _ at hsγ
  have hzg : zRotation (zyzGamma R) = zRotation γ := by
    apply Subtype.ext
    simp only [zRotation_val, hcγ, hsγ, hcg, hsg]
  simpa only [zyz, hzg] using hrep

end Rotation
end RoboLean
