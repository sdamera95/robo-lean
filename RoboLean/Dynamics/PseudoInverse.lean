import RoboLean.Dynamics.CompositeDynamics

/-!
# The right pseudo-inverse `A⁺ = Aᵀ (A Aᵀ)⁻¹` of MLS Chapter 6

MLS uses one explicit formula three times: the right pseudo-inverse `J⁺ = Jᵀ (J Jᵀ)⁻¹` of a
manipulator Jacobian of full row rank (§3.1, printed p. 287, "the least-squares right (pseudo-)
inverse of `J`"), the coupling-matrix pseudo-inverse `P⁺ = Pᵀ (P Pᵀ)⁻¹` of a tendon network (§4.3,
p. 299) and the grasp-map pseudo-inverse `G⁺ = Gᵀ (G Gᵀ)⁻¹` of the general solution (6.36) (§5.1, p.
301). This file defines the formula (`rightPinv`, with Mathlib's `Matrix.inv`) and proves what the
three uses need, under the rank hypothesis the book states: `A` onto (full row rank).

* `A Aᵀ` is invertible exactly when `A` is onto (`isUnit_det_mul_transpose_iff_surjective`);
* `A A⁺ = I` (`mul_rightPinv`), so `A⁺ b` solves `A x = b`;
* the general solution of `A x = b` is `A⁺ b + x_N` with `A x_N = 0`
  (`mulVec_eq_iff_exists_rightPinv`, the form of (6.36) and of `f = P⁺ τ + f_N`, p. 299);
* `A⁺ b` is orthogonal to the null space of `A` and has the least Euclidean norm among the solutions
  (`dotProduct_rightPinv_mulVec_le`, the book's "least-squares").

Mathlib has no Moore–Penrose inverse at the pin (`Matrix.inv` only); none is needed. Matrices are
real, indexed by `Fin`; the dot product is `⬝ᵥ`.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Composite

variable {p n : ℕ}

/-- **The right pseudo-inverse `A⁺ = Aᵀ (A Aᵀ)⁻¹` (MLS printed pp. 287, 299, 301).** `Matrix.inv` is
Mathlib's inverse (zero for a singular `A Aᵀ`); every theorem using it assumes `A` onto. -/
def rightPinv (A : Matrix (Fin p) (Fin n) ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  Aᵀ * (A * Aᵀ)⁻¹

/-- **`A Aᵀ` is invertible exactly when `A` is onto (full row rank; MLS printed p. 287, "we assume
that `J(θ)` is full row rank").** -/
theorem isUnit_det_mul_transpose_iff_surjective (A : Matrix (Fin p) (Fin n) ℝ) :
    IsUnit (A * Aᵀ).det ↔ Function.Surjective A.mulVec := by
  constructor
  · intro h b
    refine ⟨rightPinv A *ᵥ b, ?_⟩
    rw [rightPinv, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h,
      Matrix.one_mulVec]
  · intro hA
    have hinj : Function.Injective (A * Aᵀ).mulVec := by
      intro a b hab
      have h0 : (A * Aᵀ) *ᵥ (a - b) = 0 := by
        rw [Matrix.mulVec_sub, hab, sub_self]
      have h1 : Aᵀ *ᵥ (a - b) = 0 := by
        have h2 : (Aᵀ *ᵥ (a - b)) ⬝ᵥ (Aᵀ *ᵥ (a - b)) = 0 := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h0,
            zero_dotProduct]
        exact dotProduct_self_eq_zero.mp h2
      have h3 := transpose_mulVec_injective_of_surjective hA (h1.trans (Matrix.mulVec_zero _).symm)
      exact sub_eq_zero.mp h3
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)

/-- **`A A⁺ = I` for `A` onto (MLS printed p. 287: `J⁺` is a right inverse of `J`).** -/
theorem mul_rightPinv {A : Matrix (Fin p) (Fin n) ℝ} (hA : Function.Surjective A.mulVec) :
    A * rightPinv A = 1 := by
  rw [rightPinv, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((isUnit_det_mul_transpose_iff_surjective A).mpr hA)]

/-- **`A⁺ b` solves `A x = b` for `A` onto (MLS printed pp. 287, 299, 301).** -/
theorem mulVec_rightPinv_mulVec {A : Matrix (Fin p) (Fin n) ℝ} (hA : Function.Surjective A.mulVec)
    (b : Fin p → ℝ) : A *ᵥ (rightPinv A *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, mul_rightPinv hA, Matrix.one_mulVec]

/-- **The general solution of `A x = b` (MLS eq. (6.36), p. 301, and `f = P⁺ τ + f_N`, p. 299):**
for `A` onto, `A x = b` exactly when `x = A⁺ b + x_N` with `x_N` in the null space of `A`. -/
theorem mulVec_eq_iff_exists_rightPinv {A : Matrix (Fin p) (Fin n) ℝ}
    (hA : Function.Surjective A.mulVec) (x : Fin n → ℝ) (b : Fin p → ℝ) :
    A *ᵥ x = b ↔ ∃ xN, A *ᵥ xN = 0 ∧ x = rightPinv A *ᵥ b + xN := by
  constructor
  · intro h
    refine ⟨x - rightPinv A *ᵥ b, ?_, by abel⟩
    rw [Matrix.mulVec_sub, h, mulVec_rightPinv_mulVec hA, sub_self]
  · rintro ⟨xN, hN, rfl⟩
    rw [Matrix.mulVec_add, mulVec_rightPinv_mulVec hA, hN, add_zero]

/-- **`A⁺ b` is orthogonal to the null space of `A` (MLS printed p. 287, "least-squares").** -/
theorem dotProduct_rightPinv_mulVec_eq_zero (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    {xN : Fin n → ℝ} (hN : A *ᵥ xN = 0) : (rightPinv A *ᵥ b) ⬝ᵥ xN = 0 := by
  rw [rightPinv, ← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, hN, zero_dotProduct]

/-- **`A⁺ b` is the solution of least Euclidean norm (MLS printed p. 287, "the least-squares right
(pseudo-) inverse of `J`")**: for `A` onto and every `x` with `A x = b`, `(A⁺ b) ⬝ (A⁺ b) ≤ x ⬝ x`.
-/
theorem dotProduct_rightPinv_mulVec_le {A : Matrix (Fin p) (Fin n) ℝ}
    (hA : Function.Surjective A.mulVec) {x : Fin n → ℝ} {b : Fin p → ℝ} (hx : A *ᵥ x = b) :
    (rightPinv A *ᵥ b) ⬝ᵥ (rightPinv A *ᵥ b) ≤ x ⬝ᵥ x := by
  obtain ⟨xN, hN, rfl⟩ := (mulVec_eq_iff_exists_rightPinv hA x b).mp hx
  have h0 := dotProduct_rightPinv_mulVec_eq_zero A b hN
  have h1 : 0 ≤ xN ⬝ᵥ xN := dotProduct_self_star_nonneg xN
  rw [add_dotProduct, dotProduct_add, dotProduct_add, h0, dotProduct_comm xN, h0]
  linarith

end Composite
end RoboLean
