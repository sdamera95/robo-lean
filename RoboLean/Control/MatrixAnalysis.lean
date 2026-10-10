import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix and derivative lemmas shared by the control modules

Small facts about dot products, matrix–vector products, positive definite matrices and the norm
of a pair, used in MLS Chapter 4, Section 5 (printed pp. 189–195): the derivative of the energy
`½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e` along motions (p. 193), the inverse of the positive definite inertia
matrix in the closed loop (pp. 190–191), and comparisons of `‖(e, ė)‖²` with `‖e‖² + ‖ė‖²`.

Conventions: vectors are `Fin n → ℝ` with Mathlib's dot product `⬝ᵥ` and matrix–vector product
`*ᵥ`; the norm on `Fin n → ℝ` and on products is Mathlib's sup norm (maximum of the components);
"positive definite" is Mathlib's `Matrix.PosDef`, which includes symmetry.

These lemmas were collected here in E019 from `ManipulatorSystem` and `PDControl` (E016); their
names are unchanged.
-/

open Matrix

namespace RoboLean
namespace Control

variable {n : ℕ}

/-- **Product rule for the dot product of two curves in `ℝⁿ`**, used for `V̇` in the proof of
MLS Proposition 4.9 (p. 193) and for the skewed energy of Example 4.5 (p. 186). -/
theorem hasDerivAt_dotProduct {a b : ℝ → Fin n → ℝ} {a' b' : Fin n → ℝ} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => a s ⬝ᵥ b s) (a' ⬝ᵥ b t + a t ⬝ᵥ b') t := by
  have ha' := hasDerivAt_pi.mp ha
  have hb' := hasDerivAt_pi.mp hb
  have h : HasDerivAt (fun s => ∑ i, a s i * b s i) (∑ i, (a' i * b t i + a t i * b' i)) t :=
    HasDerivAt.fun_sum fun i _ => (ha' i).mul (hb' i)
  convert h using 1
  · funext s
    simp only [dotProduct]
  · simp only [dotProduct, Finset.sum_add_distrib]

/-- **A constant matrix applied to a differentiable curve in `ℝⁿ`**, used for the derivative of
`eᵀ K_p e` in the proof of MLS Proposition 4.9 (p. 193). -/
theorem hasDerivAt_mulVec_const (A : Matrix (Fin n) (Fin n) ℝ) {a : ℝ → Fin n → ℝ}
    {a' : Fin n → ℝ} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => A *ᵥ a s) (A *ᵥ a') t := by
  have ha' := hasDerivAt_pi.mp ha
  refine hasDerivAt_pi.mpr fun i => ?_
  have h : HasDerivAt (fun s => ∑ j, A i j * a s j) (∑ j, A i j * a' j) t :=
    HasDerivAt.fun_sum fun j _ => (ha' j).const_mul (A i j)
  simpa [Matrix.mulVec, dotProduct] using h

/-- **A positive definite matrix cancels against its inverse on vectors: `M (M⁻¹ w) = w`**
(MLS pp. 190–191: "since `M(θ)` is always positive definite"). The inverse is Mathlib's
`Matrix.inv`. -/
theorem PosDef.mulVec_inv_mulVec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (w : Fin n → ℝ) : A *ᵥ (A⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hA.isUnit), Matrix.one_mulVec]

/-- **A positive definite matrix cancels against its inverse on vectors: `M⁻¹ (M w) = w`**
(MLS pp. 190–191: "since `M(θ)` is always positive definite"). The inverse is Mathlib's
`Matrix.inv`. -/
theorem PosDef.inv_mulVec_mulVec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (w : Fin n → ℝ) : A⁻¹ *ᵥ (A *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hA.isUnit), Matrix.one_mulVec]

/-- **For a symmetric real matrix, `x ⬝ A y = y ⬝ A x`** (used for `K_p` in the proof of MLS
Proposition 4.9, p. 193, and for the skewed energy of Example 4.5, p. 186). -/
theorem dotProduct_mulVec_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]

/-- **The square of the norm of a pair is at most the sum of the squares of the norms of its
components** (the norm of a product is the maximum, `Prod.norm_def`); used to compare Lyapunov
functions on the state `(θ, θ̇)` with `‖(θ, θ̇)‖²` (MLS Definition 4.4, p. 182). -/
theorem sq_norm_prod_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (z : E × F) :
    ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases max_choice ‖z.1‖ ‖z.2‖ with h | h <;> rw [h] <;> nlinarith [sq_nonneg ‖z.1‖,
    sq_nonneg ‖z.2‖]

end Control
end RoboLean
