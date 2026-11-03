import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import RoboLean.LieGroups.LeftInvariantFields

/-!
# The exponential map of `ℝⁿ` and of `GL(n, ℝ)`

MLS Appendix A, §2.3, printed pp. 412–413. For `ξ` in the Lie algebra, `φ_ξ` is the integral curve
of the left invariant field `X_ξ` through `e`, a one-parameter subgroup, and `exp(ξ) = φ_ξ(1)`.

* Example A.9 (`ℝⁿ`): the integral curve of the constant field `X_v` through `x` is `t ↦ x + v t`,
  so `exp : ℝⁿ → ℝⁿ` is the identity.
* Example A.10 (`GL(n, ℝ)`): `Φ_A(t) = Σ tⁿ Aⁿ / n!`, Mathlib's `NormedSpace.exp (t • A)`, satisfies
  `Φ_A(0) = I` and `Φ̇_A(t) = Φ_A(t) A = X_A(Φ_A(t))`; it is a one-parameter subgroup with values in
  `GL(n, ℝ)`, and `exp(A) = Φ_A(1)`. Derivatives of matrix-valued curves use the operator norm
  (`Matrix.Norms.Operator`), as in the library's exponential coordinates.

The general statements of p. 412 (existence and uniqueness of integral curves on a Lie group,
`T_e exp = id`, the local diffeomorphism and surjectivity for compact `G`) need a manifold
structure and are not stated here.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace LieGroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- MLS Example A.9, printed p. 412: the curve `t ↦ x + v t` is an integral curve of the constant
(left invariant) field `X_v`, so the exponential map of `(ℝⁿ, +)` is `v ↦ 0 + v · 1 = v`, the
identity. Stated on a real normed space `E`. -/
theorem hasDerivAt_add_smul (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

section GeneralLinear

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- MLS Example A.10, printed p. 412: `Φ_A(0) = I`. -/
theorem exp_zero_smul (A : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp ((0 : ℝ) • A) = 1 := by
  rw [zero_smul, NormedSpace.exp_zero]

/-- MLS Example A.10, printed pp. 412–413: `d/dt Φ_A(t) = Φ_A(t) A`, so `Φ_A(t) = exp(t A)` is an
integral curve of the left invariant field `X_A(g) = g A` (operator norm on matrices). -/
theorem hasDerivAt_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A))
      (leftInvariantField A (NormedSpace.exp (t • A))) t := by
  exact hasDerivAt_exp_smul_const A t

/-- MLS Example A.10, printed p. 413 (with p. 412, `φ_ξ(s + t) = φ_ξ(s) φ_ξ(t)`): `Φ_A` is a
one-parameter subgroup, `exp((s + t) A) = exp(s A) exp(t A)`. -/
theorem exp_add_smul (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) = NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left s |>.smul_right t)]

/-- MLS Example A.10, printed p. 412: `Φ_A(t)` takes values in `GL(n, ℝ)`. -/
theorem isUnit_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    IsUnit (NormedSpace.exp (t • A)) := by
  exact Matrix.isUnit_exp _

/-- MLS Example A.10, printed p. 413: `exp(A) = Φ_A(1) = Σ Aⁿ / n!`. -/
theorem exp_eq_exp_one_smul (A : Matrix (Fin n) (Fin n) ℝ) :
    NormedSpace.exp A = NormedSpace.exp ((1 : ℝ) • A) := by
  rw [one_smul]

end GeneralLinear

end LieGroup

end RoboLean
