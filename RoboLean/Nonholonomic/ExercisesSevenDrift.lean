import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

/-!
# Constraints with constants and the drift field: MLS Chapter 7, Exercise 16

MLS Chapter 7, Exercise 16, printed p. 353: "Consider what would happen if the constraints were of
the form `ωᵢ(q)q̇ = cᵢ`, `i = 1, …, k`, for constants `cᵢ`. Dualize these constraints to get an
associated control system of the form `q̇ = f(q) + Σ_{i=1}^{n−k} gᵢ(q)uᵢ`. What is the formula for
`f(q)`?"

**What is formalized.** At a point `q`, with the constraint rows stacked as `A = A(q) ∈ ℝ^{k×n}`
and `A Aᵀ` invertible (the rows independent; MLS assumes independent constraints, p. 318): the
drift `f = Aᵀ(AAᵀ)⁻¹c` satisfies `Af = c` (the least-norm choice; any solution of `Af = c` would
do, which the exercise leaves open: this formula is a choice); the velocities allowed by the
constraints are exactly `f + w` with `Aw = 0`; and if the fields `g₁, …, g_r` span the kernel of
`A` (the drift-free dualization of p. 318), the allowed velocities are exactly
`f + Σ gᵢuᵢ`. The space robot with nonzero angular momentum and the path-planning discussion are not
formalized.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Nonholonomic

variable {k n r : ℕ}

/-- **MLS Chapter 7, Exercise 16, p. 353: the drift `f = Aᵀ(AAᵀ)⁻¹c`** of the constraints
`A q̇ = c` at a point (the least-norm solution of `Af = c`). -/
def constraintDrift (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → ℝ) : Fin n → ℝ :=
  Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ c)

/-- **MLS Chapter 7, Exercise 16, p. 353: the drift satisfies the constraints,** `Af = c`, when
`AAᵀ` is invertible. -/
theorem mulVec_constraintDrift {A : Matrix (Fin k) (Fin n) ℝ} (hA : IsUnit (A * Aᵀ).det)
    (c : Fin k → ℝ) : A *ᵥ constraintDrift A c = c := by
  rw [constraintDrift, mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, one_mulVec]

/-- **MLS Chapter 7, Exercise 16, p. 353: the allowed velocities are the drift plus the kernel:**
`Aq̇ = c` exactly when `A(q̇ − f) = 0`. -/
theorem mulVec_eq_iff_sub_constraintDrift {A : Matrix (Fin k) (Fin n) ℝ}
    (hA : IsUnit (A * Aᵀ).det) (v : Fin n → ℝ) (c : Fin k → ℝ) :
    A *ᵥ v = c ↔ A *ᵥ (v - constraintDrift A c) = 0 := by
  rw [mulVec_sub, mulVec_constraintDrift hA, sub_eq_zero]

/-- **MLS Chapter 7, Exercise 16, p. 353: the control system with drift.** If `A gᵢ = 0` for
fields `g₁, …, g_r` spanning the kernel of `A`, the velocities with `Aq̇ = c` are exactly
`q̇ = f + Σ gᵢuᵢ` for some input `u`. -/
theorem mulVec_eq_iff_exists_input {A : Matrix (Fin k) (Fin n) ℝ} (hA : IsUnit (A * Aᵀ).det)
    {g : Fin r → Fin n → ℝ} (hg : ∀ i, A *ᵥ g i = 0)
    (hspan : ∀ w, A *ᵥ w = 0 → w ∈ Submodule.span ℝ (Set.range g)) (c : Fin k → ℝ)
    (v : Fin n → ℝ) :
    A *ᵥ v = c ↔ ∃ u : Fin r → ℝ, v = constraintDrift A c + ∑ i, u i • g i := by
  constructor
  · intro hv
    have hw := hspan _ ((mulVec_eq_iff_sub_constraintDrift hA v c).1 hv)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
    exact ⟨u, by rw [hu]; abel⟩
  · rintro ⟨u, rfl⟩
    rw [mulVec_add, mulVec_constraintDrift hA, mulVec_sum]
    simp [mulVec_smul, hg]

end Nonholonomic
end RoboLean
