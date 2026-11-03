import RoboLean.Dynamics.PseudoInverse

/-!
# The left pseudo-inverse `A⁺ = (Aᵀ A)⁻¹ Aᵀ` of MLS Chapter 6

MLS Chapter 6, §3.2, printed p. 291: for a nonmanipulable grasp whose hand Jacobian `J_h` is "full
column rank" (p. 290), "`J_h` is not necessarily square so we must use the pseudo-inverse
`J_h⁺ = (J_hᵀ J_h)⁻¹ J_hᵀ` in place of `J_h⁻¹`". This file defines the formula (`leftPinv`, with
Mathlib's `Matrix.inv`) beside the right pseudo-inverse `rightPinv` of `Dynamics/PseudoInverse`,
and proves what (6.33) needs, under the rank hypothesis the book states: `A` injective (full
column rank).

* `Aᵀ A` is invertible exactly when `A` is injective (`isUnit_det_transpose_mul_iff_injective`);
* `A⁺ A = I` (`leftPinv_mul`), so `A⁺ (A x) = x`;
* `A (A⁺ b) = b` for `b` in the range of `A` (`mulVec_leftPinv_mulVec_of_eq`), the step "we can solve
  for `θ̇` given `w`" of p. 291;
* `A⁺` is the transpose of the right pseudo-inverse of `Aᵀ` (`leftPinv_eq_transpose_rightPinv`) and
  is `A⁻¹` for an invertible square `A` (`leftPinv_eq_inv`), so (6.33) reduces to (6.22) there.

Matrices are real, indexed by `Fin`. Nothing here concerns a physical hand.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Composite

variable {m n : ℕ}

/-- **The left pseudo-inverse `A⁺ = (Aᵀ A)⁻¹ Aᵀ` (MLS printed p. 291, `J_h⁺ = (J_hᵀ J_h)⁻¹ J_hᵀ`).**
`Matrix.inv` is Mathlib's inverse (zero for a singular `Aᵀ A`); every theorem using it assumes `A`
injective (full column rank, p. 290). -/
def leftPinv (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  (Aᵀ * A)⁻¹ * Aᵀ

/-- **`Aᵀ A` is invertible exactly when `A` is injective (MLS printed p. 290, "We assume that the
hand Jacobian is full column rank").** -/
theorem isUnit_det_transpose_mul_iff_injective (A : Matrix (Fin m) (Fin n) ℝ) :
    IsUnit (Aᵀ * A).det ↔ Function.Injective A.mulVec := by
  constructor
  · intro h a b hab
    have hu : Function.Injective (Aᵀ * A).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr h)
    apply hu
    rw [← Matrix.mulVec_mulVec, hab, Matrix.mulVec_mulVec]
  · intro hA
    have hinj : Function.Injective (Aᵀ * A).mulVec := by
      intro a b hab
      have h0 : (Aᵀ * A) *ᵥ (a - b) = 0 := by
        rw [Matrix.mulVec_sub, hab, sub_self]
      have h1 : A *ᵥ (a - b) = 0 := by
        have h2 : (A *ᵥ (a - b)) ⬝ᵥ (A *ᵥ (a - b)) = 0 := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h0,
            zero_dotProduct]
        exact dotProduct_self_eq_zero.mp h2
      have h3 : A *ᵥ a = A *ᵥ b := by
        rw [← sub_eq_zero, ← Matrix.mulVec_sub, h1]
      exact hA h3
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)

/-- **`A⁺ A = I` for `A` injective (MLS printed p. 291: `J_h⁺` is used "in place of `J_h⁻¹`").** -/
theorem leftPinv_mul {A : Matrix (Fin m) (Fin n) ℝ} (hA : Function.Injective A.mulVec) :
    leftPinv A * A = 1 := by
  rw [leftPinv, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((isUnit_det_transpose_mul_iff_injective A).mpr hA)]

/-- **`A⁺ (A x) = x` for `A` injective (MLS printed p. 291).** -/
theorem leftPinv_mulVec_mulVec {A : Matrix (Fin m) (Fin n) ℝ} (hA : Function.Injective A.mulVec)
    (x : Fin n → ℝ) : leftPinv A *ᵥ (A *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, leftPinv_mul hA, Matrix.one_mulVec]

/-- **The unique solution of `A x = b` is `A⁺ b` (MLS printed p. 291, "we can solve for `θ̇` given
`w`"):** for `A` injective and `A x = b`, `x = A⁺ b`. -/
theorem eq_leftPinv_mulVec_of_eq {A : Matrix (Fin m) (Fin n) ℝ} (hA : Function.Injective A.mulVec)
    {x : Fin n → ℝ} {b : Fin m → ℝ} (h : A *ᵥ x = b) : x = leftPinv A *ᵥ b := by
  rw [← h, leftPinv_mulVec_mulVec hA]

/-- **`A⁺ b` solves `A x = b` whenever `b` is in the range of `A` (MLS printed p. 291, "`J_h` is
surjective onto the range of `Ḡᵀ` and hence we can solve for `θ̇`"):** for `A` injective and
`b = A x₀`, `A (A⁺ b) = b`. -/
theorem mulVec_leftPinv_mulVec_of_eq {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : Function.Injective A.mulVec) {x₀ : Fin n → ℝ} {b : Fin m → ℝ} (h : A *ᵥ x₀ = b) :
    A *ᵥ (leftPinv A *ᵥ b) = b := by
  rw [← eq_leftPinv_mulVec_of_eq hA h, h]

/-- **The left pseudo-inverse of `A` is the transpose of the right pseudo-inverse of `Aᵀ` (MLS
printed pp. 287, 291):** `(Aᵀ A)⁻¹ Aᵀ = ((Aᵀ)ᵀ ((Aᵀ)(Aᵀ)ᵀ)⁻¹)ᵀ`, with no rank hypothesis. -/
theorem leftPinv_eq_transpose_rightPinv (A : Matrix (Fin m) (Fin n) ℝ) :
    leftPinv A = (rightPinv Aᵀ)ᵀ := by
  rw [leftPinv, rightPinv, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **For an invertible square `A`, `A⁺ = A⁻¹` (MLS printed p. 291, the pseudo-inverse used "in
place of `J_h⁻¹`"),** so the nonmanipulable dynamics (6.33) contain the invertible case (6.22). -/
theorem leftPinv_eq_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) : leftPinv A = A⁻¹ := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  rw [leftPinv, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAt, Matrix.mul_one]

end Composite
end RoboLean
