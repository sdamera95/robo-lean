import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The exponential near the identity of `GL(n, ℝ)`: `T_e exp = id`, canonical coordinates of the
first kind, and the logarithm series

MLS Appendix A, §2.3–§2.4, printed pp. 412–414, for `G = GL(n, ℝ)`, an open subset of `ℝⁿˣⁿ`, so
that no further manifold structure is needed. Matrices carry the `L^∞` operator norm
(`Matrix.Norms.Operator`), a submultiplicative norm; the book does not name the norm in
Example A.13.

* p. 412: `T_e exp = id` (the derivative of `exp` at `0` is the identity of `gl(n, ℝ)`).
* (A.4), p. 414: for a basis `X₁, …, X_N` of `gl(n, ℝ)`, `σ ↦ exp(X₁ σ₁ + ⋯ + X_N σ_N)` has an
  invertible strict derivative at `0`, so it restricts to a homeomorphism from an open
  neighbourhood of `0 ∈ ℝᴺ` onto an open neighbourhood of `I` (the inverse function theorem),
  with differentiable inverse at `I`. The atlas by left translation and the general Lie group
  statement need a manifold structure and are not stated.
* Example A.13, p. 413: the series `Σ (-1)ⁿ⁺¹ (A - I)ⁿ / n` converges for `‖A - I‖ < 1`. That its
  sum is a logarithm (`exp ∘ log = id`) is not stated.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace LieGroup

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- MLS printed p. 412, `T_e exp = id`, for `GL(n, ℝ)`: the matrix exponential has the identity
as its strict derivative at `0` (operator norm on matrices). -/
theorem hasStrictFDerivAt_exp_zero_matrix :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) 0 := by
  exact hasStrictFDerivAt_exp_zero

/-- Canonical coordinates of the first kind on `GL(n, ℝ)`, MLS equation (A.4), printed p. 414:
for a basis `X` of `gl(n, ℝ) = ℝⁿˣⁿ`, the map `σ ↦ exp(Σᵢ σᵢ Xᵢ)` has at `0` the strict
derivative `σ ↦ Σᵢ σᵢ Xᵢ`, a linear isomorphism. -/
theorem hasStrictFDerivAt_exp_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Module.Basis ι ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    HasStrictFDerivAt (fun σ : ι → ℝ => NormedSpace.exp (∑ i, σ i • X i))
      ((X.equivFun.symm.toContinuousLinearEquiv : (ι → ℝ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ) :
        (ι → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ) 0 := by
  set L : (ι → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (X.equivFun.symm.toContinuousLinearEquiv : (ι → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ)
  have hL : ∀ σ : ι → ℝ, L σ = ∑ i, σ i • X i := fun σ => by
    simp [L, Module.Basis.equivFun_symm_apply]
  have h0 : L 0 = 0 := map_zero L
  have hexp : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → _)
      (1 : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ) (L 0) := by
    rw [h0]; exact hasStrictFDerivAt_exp_zero
  have := hexp.comp (0 : ι → ℝ) L.hasStrictFDerivAt
  have hfun : (fun σ : ι → ℝ => NormedSpace.exp (∑ i, σ i • X i)) =
      fun σ => NormedSpace.exp (L σ) := funext fun σ => by rw [hL]
  rw [hfun]
  exact this

/-- MLS equation (A.4), printed p. 414: canonical coordinates of the first kind are a local
homeomorphism near the identity. For a basis `X` of `gl(n, ℝ)` there is a homeomorphism `e` between
open sets, `0 ∈ e.source`, which is `σ ↦ exp(Σᵢ σᵢ Xᵢ)` on its source (inverse function theorem). -/
theorem exists_openPartialHomeomorph_exp_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Module.Basis ι ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    ∃ e : OpenPartialHomeomorph (ι → ℝ) (Matrix (Fin n) (Fin n) ℝ),
      (0 : ι → ℝ) ∈ e.source ∧ ⇑e = fun σ => NormedSpace.exp (∑ i, σ i • X i) := by
  have hf := hasStrictFDerivAt_exp_sum X
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, rfl⟩

/-- MLS Example A.13, printed p. 413: the logarithm series `Σ_{k ≥ 1} (-1)^{k+1} (A - I)^k / k`
converges when `‖A - I‖ < 1` (operator norm). Written with `k = m + 1`. -/
theorem summable_log_series (A : Matrix (Fin n) (Fin n) ℝ) (hA : ‖A - 1‖ < 1) :
    Summable fun m : ℕ => ((-1 : ℝ) ^ (m + 2) / (m + 1 : ℝ)) • (A - 1) ^ (m + 1) := by
  have hg : Summable fun m : ℕ => ‖A - 1‖ ^ (m + 1) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hA).comp_injective (add_left_injective 1)
  refine Summable.of_norm_bounded hg fun m => ?_
  rw [norm_smul]
  have h1 : ‖(-1 : ℝ) ^ (m + 2) / (m + 1 : ℝ)‖ ≤ 1 := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < m + 1)]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (by positivity)
  calc ‖(-1 : ℝ) ^ (m + 2) / (m + 1 : ℝ)‖ * ‖(A - 1) ^ (m + 1)‖ ≤ 1 * ‖A - 1‖ ^ (m + 1) :=
        mul_le_mul h1 (norm_pow_le' _ (Nat.succ_pos m)) (norm_nonneg _) zero_le_one
    _ = ‖A - 1‖ ^ (m + 1) := one_mul _

end LieGroup

end RoboLean
