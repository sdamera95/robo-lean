import RoboLean.Nonholonomic.VectorField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The disk rolling on a plane: MLS Examples 7.4 and 7.9

MLS Chapter 7: Example 7.4, printed p. 336, eq. (7.13); Example 7.9, pp. 342–343.

**What MLS states.** With `q = (x, y, θ, φ)` and radius `ρ > 0`, rolling without slipping gives
the Pfaffian constraint `[[1, 0, 0, −ρ cos θ], [0, 1, 0, −ρ sin θ]] q̇ = 0` and the control system
(7.13) `q̇ = (ρ cos θ, ρ sin θ, 0, 1) u₁ + (0, 0, 1, 0) u₂`. Example 7.9 prints
`g₃ = [g₁, g₂] = (ρ sin θ, −ρ cos θ, 0, 0)`, `g₄ = [g₂, g₃] = (ρ cos θ, ρ sin θ, 0, 0)`, and "for all
`q`, span{g₁, g₂, g₃, g₄} is full rank".

**Corrected printing.** p. 336 names `θ̇ = u₁` "the rate of rolling" and `φ̇ = u₂`, but the
columns of (7.13) give `φ̇ = u₁` and `θ̇ = u₂`; the fields below are the printed columns.

**Formalized.** Coordinates `q 0 = x`, `q 1 = y`, `q 2 = θ`, `q 3 = φ`; the brackets with
Mathlib's `VectorField.lieBracket` (the book's sign, p. 324), the constraint applied to the fields,
and the determinant `−ρ²` of the four fields. These are convention checks of the printed formulas
on one system; they say nothing about a physical disk.
-/

noncomputable section

open Real VectorField Matrix
open scoped ContDiff

namespace RoboLean
namespace Examples

/-- **MLS eq. (7.13), p. 336, first column: `g₁(q) = (ρ cos θ, ρ sin θ, 0, 1)`** for the rolling
disk with `q = (x, y, θ, φ)`. -/
def diskG1 (ρ : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![ρ * cos (q 2), ρ * sin (q 2), 0, 1]

/-- **MLS eq. (7.13), p. 336, second column: `g₂ = (0, 0, 1, 0)`.** -/
def diskG2 (_q : Fin 4 → ℝ) : Fin 4 → ℝ := ![0, 0, 1, 0]

/-- **MLS Example 7.9, p. 342: `g₃ = (ρ sin θ, −ρ cos θ, 0, 0)`.** -/
def diskG3 (ρ : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![ρ * sin (q 2), -(ρ * cos (q 2)), 0, 0]

/-- **MLS Example 7.9, p. 342: `g₄ = (ρ cos θ, ρ sin θ, 0, 0)`.** -/
def diskG4 (ρ : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![ρ * cos (q 2), ρ * sin (q 2), 0, 0]

/-- **MLS Example 7.4, p. 336: the rolling constraint**
`[[1, 0, 0, −ρ cos θ], [0, 1, 0, −ρ sin θ]] q̇ = 0`. -/
def diskConstraint (ρ : ℝ) (q : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, 0, 0, -(ρ * cos (q 2)); 0, 1, 0, -(ρ * sin (q 2))]

/-- The derivative of `t ↦ G(q + t v)` at `0`, assembled from its components (supporting lemma
for MLS p. 342). -/
private theorem deriv_line {n : ℕ} (G : (Fin n → ℝ) → Fin n → ℝ) (q v w : Fin n → ℝ)
    (h : ∀ i, HasDerivAt (fun t : ℝ => G (q + t • v) i) (w i) 0) :
    deriv (fun t : ℝ => G (q + t • v)) 0 = w := by
  have hd : HasDerivAt (fun t : ℝ => G (q + t • v)) w 0 := by
    rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_pi']
    intro i
    convert (h i).hasFDerivAt using 1
    ext
    simp
  exact hd.deriv

/-- **MLS p. 322 for (7.13):** `g₁` is smooth. -/
theorem diskG1_contDiff (ρ : ℝ) : ContDiff ℝ ∞ (diskG1 ρ) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [diskG1] <;> fun_prop

/-- **MLS p. 322 for (7.13):** `g₂` is smooth. -/
theorem diskG2_contDiff : ContDiff ℝ ∞ diskG2 := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [diskG2] <;> fun_prop

-- helpers begin

/-- **MLS Example 7.9, p. 342: `[g₁, g₂] = g₃`** at every `q`. -/
theorem disk_lieBracket_g1_g2 (ρ : ℝ) (q : Fin 4 → ℝ) :
    lieBracket ℝ (diskG1 ρ) diskG2 q = diskG3 ρ q := by
  have h1 := ((diskG1_contDiff ρ).differentiable (by simp)) q
  have h2 := (diskG2_contDiff.differentiable (by simp)) q
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h2,
    deriv_line diskG2 q (diskG1 ρ q) 0 ?_, deriv_line (diskG1 ρ) q (diskG2 q) (-diskG3 ρ q) ?_]
  · simp
  · intro i
    fin_cases i <;> simp [diskG1, diskG2, diskG3]
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (q 2)).cos.const_mul ρ
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (q 2)).sin.const_mul ρ
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
  · intro i
    fin_cases i <;> simp [diskG2] <;> exact hasDerivAt_const _ _

/-- **MLS Example 7.9, p. 342: `[g₂, g₃] = g₄`** at every `q`. -/
theorem disk_lieBracket_g2_g3 (ρ : ℝ) (q : Fin 4 → ℝ) :
    lieBracket ℝ diskG2 (diskG3 ρ) q = diskG4 ρ q := by
  have h3 : ContDiff ℝ ∞ (diskG3 ρ) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [diskG3] <;> fun_prop
  have h2 := (diskG2_contDiff.differentiable (by simp)) q
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h2 (h3.differentiable (by simp) q),
    deriv_line diskG2 q (diskG3 ρ q) 0 ?_, deriv_line (diskG3 ρ) q (diskG2 q) (diskG4 ρ q) ?_]
  · simp
  · intro i
    fin_cases i <;> simp [diskG3, diskG2, diskG4]
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (q 2)).sin.const_mul ρ
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (q 2)).cos.const_mul (-ρ)
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
  · intro i
    fin_cases i <;> simp [diskG2] <;> exact hasDerivAt_const _ _

/-- **MLS Example 7.4, p. 336:** the constraint annihilates `g₁`. -/
theorem diskConstraint_mulVec_g1 (ρ : ℝ) (q : Fin 4 → ℝ) :
    diskConstraint ρ q *ᵥ diskG1 ρ q = 0 := by
  ext i
  fin_cases i <;> simp [diskConstraint, diskG1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **MLS Example 7.4, p. 336:** the constraint annihilates `g₂`. -/
theorem diskConstraint_mulVec_g2 (ρ : ℝ) (q : Fin 4 → ℝ) :
    diskConstraint ρ q *ᵥ diskG2 q = 0 := by
  ext i
  fin_cases i <;> simp [diskConstraint, diskG2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **MLS Examples 7.4 and 7.9, pp. 336 and 342:** the constraint applied to `g₃ = [g₁, g₂]` is
`(ρ sin θ, −ρ cos θ)`, which is nonzero for `ρ ≠ 0`. -/
theorem diskConstraint_mulVec_g3 (ρ : ℝ) (q : Fin 4 → ℝ) :
    diskConstraint ρ q *ᵥ diskG3 ρ q = ![ρ * sin (q 2), -(ρ * cos (q 2))] := by
  ext i
  fin_cases i <;> simp [diskConstraint, diskG3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **MLS Example 7.9, p. 343, "for all `q`, span{g₁, g₂, g₃, g₄} is full rank":** the matrix with
rows `g₁, …, g₄` has determinant `−ρ²`. -/
theorem disk_det (ρ : ℝ) (q : Fin 4 → ℝ) :
    (Matrix.of ![diskG1 ρ q, diskG2 q, diskG3 ρ q, diskG4 ρ q]).det = -ρ ^ 2 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, diskG1, diskG2, diskG3, diskG4, Fin.succAbove]
  linear_combination (-ρ ^ 2) * sin_sq_add_cos_sq (q 2)

/-- **MLS Example 7.9, p. 343:** for `ρ ≠ 0` the four fields are linearly independent at every
`q`. -/
theorem disk_linearIndependent {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    LinearIndependent ℝ ![diskG1 ρ q, diskG2 q, diskG3 ρ q, diskG4 ρ q] := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![diskG1 ρ q, diskG2 q, diskG3 ρ q, diskG4 ρ q])
    (by rw [disk_det]; exact neg_ne_zero.2 (pow_ne_zero 2 hρ))
  exact h

end Examples
end RoboLean
