import RoboLean.Nonholonomic.VectorField
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The hopping robot in flight: MLS Examples 7.2 and 7.7

MLS Chapter 7: Example 7.2, printed pp. 333–334, eq. (7.11); Example 7.7, pp. 341–342.

**What MLS states.** With `q = (ψ, l, θ)` (leg angle, leg extension, body angle), body inertia
`I`, leg mass `m` at the foot and upper leg length `d`, conservation of zero angular momentum
`I θ̇ + m (l + d)² (θ̇ + ψ̇) = 0` (7.11) gives `g₁ = (1, 0, −m(l + d)²/(I + m(l + d)²))`,
`g₂ = (0, 1, 0)` (p. 334). Example 7.7 prints
`g₃ = [g₁, g₂] = (0, 0, 2 I m (l + d)/(I + m(l + d)²)²)` and "in a neighborhood of `l = 0`,
span{g₁, g₂, g₃} is full rank".

**Corrected printing.** p. 341 prints `g₁` with denominator `I + (l + d)²`; p. 334 and the printed
`g₃` have `I + m(l + d)²`, used here. The rank at `l = 0` needs `d ≠ 0`, a hypothesis the example
does not print: the determinant of `g₁, g₂, g₃` is `2 I m (l + d)/(I + m(l + d)²)²`.

**Formalized.** Coordinates `q 0 = ψ`, `q 1 = l`, `q 2 = θ`; `0 < I` and `0 ≤ m`, so that
`I + m(l + d)² > 0`. These are convention checks of the printed formulas; they say nothing about a
physical robot.
-/

noncomputable section

open VectorField Matrix
open scoped ContDiff

namespace RoboLean
namespace Examples

/-- **MLS Example 7.2, p. 334: `g₁(q) = (1, 0, −m(l + d)²/(I + m(l + d)²))`** for the hopper with
`q = (ψ, l, θ)`. -/
def hopperG1 (I m d : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![1, 0, -(m * (q 1 + d) ^ 2 / (I + m * (q 1 + d) ^ 2))]

/-- **MLS Example 7.2, p. 334: `g₂ = (0, 1, 0)`.** -/
def hopperG2 (_q : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 1, 0]

/-- **MLS Example 7.7, p. 341: `g₃ = (0, 0, 2 I m (l + d)/(I + m(l + d)²)²)`.** -/
def hopperG3 (I m d : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0, 0, 2 * I * m * (q 1 + d) / (I + m * (q 1 + d) ^ 2) ^ 2]

/-- **MLS eq. (7.11), p. 333: the angular momentum constraint**
`m(l + d)² ψ̇ + (I + m(l + d)²) θ̇ = 0`, a single Pfaffian row. -/
def hopperConstraint (I m d : ℝ) (q : Fin 3 → ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  !![m * (q 1 + d) ^ 2, 0, I + m * (q 1 + d) ^ 2]

/-- The derivative of `t ↦ G(q + t v)` at `0`, assembled from its components (supporting lemma
for MLS p. 341). -/
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

/-- **MLS p. 322 for Example 7.2:** `g₁` is smooth when `0 < I` and `0 ≤ m`. -/
theorem hopperG1_contDiff {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (d : ℝ) :
    ContDiff ℝ ∞ (hopperG1 I m d) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [hopperG1]
  · fun_prop
  · fun_prop
  · fun_prop (disch := intro x; positivity)

/-- **MLS p. 322 for Example 7.2:** `g₂` is smooth. -/
theorem hopperG2_contDiff : ContDiff ℝ ∞ hopperG2 := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [hopperG2] <;> fun_prop

/-- **MLS Example 7.7, p. 341: `[g₁, g₂] = g₃`** at every `q`, for `0 < I` and `0 ≤ m`. -/
theorem hopper_lieBracket_g1_g2 {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (d : ℝ) (q : Fin 3 → ℝ) :
    lieBracket ℝ (hopperG1 I m d) hopperG2 q = hopperG3 I m d q := by
  have h1 := ((hopperG1_contDiff hI hm d).differentiable (by simp)) q
  have h2 := (hopperG2_contDiff.differentiable (by simp)) q
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h2,
    deriv_line hopperG2 q (hopperG1 I m d q) 0 ?_,
    deriv_line (hopperG1 I m d) q (hopperG2 q) (-hopperG3 I m d q) ?_]
  · simp
  · intro i
    fin_cases i <;> simp [hopperG1, hopperG2, hopperG3]
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · have hD : ∀ t : ℝ, I + m * (q 1 + t + d) ^ 2 ≠ 0 := fun t => by positivity
      have hdiff : DifferentiableAt ℝ
          (fun t : ℝ => m * (q 1 + t + d) ^ 2 / (I + m * (q 1 + t + d) ^ 2)) 0 :=
        by fun_prop (disch := exact hD 0)
      have hh := hdiff.hasDerivAt
      have hx : HasDerivAt (fun t : ℝ => q 1 + t + d) 1 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add (q 1)).add_const d
      have hN : HasDerivAt (fun t : ℝ => m * (q 1 + t + d) ^ 2) (m * (2 * (q 1 + d))) 0 := by
        simpa using (hx.fun_pow 2).const_mul m
      have hprod := hh.fun_mul (hN.const_add I)
      have heq : (fun t : ℝ => m * (q 1 + t + d) ^ 2 / (I + m * (q 1 + t + d) ^ 2) *
          (I + m * (q 1 + t + d) ^ 2)) = fun t : ℝ => m * (q 1 + t + d) ^ 2 :=
        funext fun t => div_mul_cancel₀ _ (hD t)
      rw [heq] at hprod
      have key := hprod.unique hN
      have hk := div_mul_cancel₀ (m * (q 1 + d) ^ 2) (hD 0)
      simp only [add_zero] at key hk
      have hval : deriv (fun t : ℝ => m * (q 1 + t + d) ^ 2 / (I + m * (q 1 + t + d) ^ 2)) 0 =
          2 * I * m * (q 1 + d) / (I + m * (q 1 + d) ^ 2) ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 (by simpa using hD 0))]
        linear_combination (I + m * (q 1 + d) ^ 2) * key - m * (2 * (q 1 + d)) * hk
      rw [← hval]
      exact hh.neg
  · intro i
    fin_cases i <;> simp [hopperG2] <;> exact hasDerivAt_const _ _

/-- **MLS eq. (7.11), p. 333:** the constraint annihilates `g₁`. -/
theorem hopperConstraint_mulVec_g1 {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (d : ℝ)
    (q : Fin 3 → ℝ) : hopperConstraint I m d q *ᵥ hopperG1 I m d q = 0 := by
  have hden : I + m * (q 1 + d) ^ 2 ≠ 0 := by positivity
  ext i
  fin_cases i
  simp [hopperConstraint, hopperG1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp
  ring

/-- **MLS eq. (7.11), p. 333:** the constraint annihilates `g₂`. -/
theorem hopperConstraint_mulVec_g2 (I m d : ℝ) (q : Fin 3 → ℝ) :
    hopperConstraint I m d q *ᵥ hopperG2 q = 0 := by
  ext i
  fin_cases i
  simp [hopperConstraint, hopperG2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **MLS Examples 7.2 and 7.7, pp. 333 and 341:** the constraint applied to `g₃ = [g₁, g₂]` is
`2 I m (l + d)/(I + m(l + d)²)`. -/
theorem hopperConstraint_mulVec_g3 {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (d : ℝ)
    (q : Fin 3 → ℝ) :
    hopperConstraint I m d q *ᵥ hopperG3 I m d q =
      ![2 * I * m * (q 1 + d) / (I + m * (q 1 + d) ^ 2)] := by
  have hden : I + m * (q 1 + d) ^ 2 ≠ 0 := by positivity
  ext i
  fin_cases i
  simp [hopperConstraint, hopperG3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp

/-- **MLS Example 7.7, p. 342:** the matrix with rows `g₁, g₂, g₃` has determinant
`2 I m (l + d)/(I + m(l + d)²)²`. -/
theorem hopper_det (I m d : ℝ) (q : Fin 3 → ℝ) :
    (Matrix.of ![hopperG1 I m d q, hopperG2 q, hopperG3 I m d q]).det =
      2 * I * m * (q 1 + d) / (I + m * (q 1 + d) ^ 2) ^ 2 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, hopperG1, hopperG2, hopperG3, Fin.succAbove]

/-- **MLS Example 7.7, p. 342, with the unprinted hypothesis `l + d ≠ 0` (at `l = 0`: `d ≠ 0`):**
for `0 < I` and `0 < m` the three fields are linearly independent at `q`. -/
theorem hopper_linearIndependent {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ) {q : Fin 3 → ℝ}
    (hq : q 1 + d ≠ 0) :
    LinearIndependent ℝ ![hopperG1 I m d q, hopperG2 q, hopperG3 I m d q] := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![hopperG1 I m d q, hopperG2 q, hopperG3 I m d q])
    (by
      rw [hopper_det]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hI.ne') hm.ne') hq)
        (by positivity))
  exact h

end Examples
end RoboLean
