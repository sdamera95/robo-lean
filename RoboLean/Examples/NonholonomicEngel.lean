import RoboLean.Nonholonomic.TwoInputs
import RoboLean.Nonholonomic.Controllability
import RoboLean.Nonholonomic.OptimalInputs

/-!
# Engel's system: MLS Example 8.4

MLS Chapter 8, Example 8.4, printed p. 374: Engel's system
`q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₁ u₂ − q₂ u₁, q̇₄ = q₁² u₂`, "growth vector (2, 3, 4)",
`[g₁, g₂] = (0, 0, 2, 2q₁)`, and the specialization (8.18) of (8.16):
`u̇₁ = 2(p₃ + q₁ p₄) u₂`, `u̇₂ = −2(p₃ + q₁ p₄) u₁`.

**What is formalized.** Coordinates `q 0 = q₁`, …, `q 3 = q₄`; fields `g₁ = (1, 0, −q₂, 0)`,
`g₂ = (0, 1, q₁, q₁²)` read from the system. The third-level bracket
`[g₁, [g₁, g₂]] = (0, 0, 0, 2)` (not printed) gives `Δ₃ = ℝ⁴`, hence the growth vector, the degree
of nonholonomy `3` and the controllability rank condition at every point. The matrix `Ω(q, p)` of
(8.16) has the entry `2(p₃ + q₁ p₄)` with `pᵢ = p(eᵢ)`. The elliptic-function solution of p. 374 is
not formalized.
-/

noncomputable section

open Set VectorField Matrix
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Example 8.4, p. 374: `g₁ = (1, 0, −q₂, 0)`** of Engel's system. -/
def engelG1 (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![1, 0, -q 1, 0]

/-- **MLS Example 8.4, p. 374: `g₂ = (0, 1, q₁, q₁²)`** of Engel's system. -/
def engelG2 (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![0, 1, q 0, q 0 ^ 2]

/-- **MLS Example 8.4, p. 374: the input fields `(g₁, g₂)` of Engel's system.** -/
def engelFields : Fin 2 → (Fin 4 → ℝ) → Fin 4 → ℝ := ![engelG1, engelG2]

/-- **MLS Example 8.4, p. 374: `q̇ = (u₁, u₂, q₁ u₂ − q₂ u₁, q₁² u₂)`.** -/
theorem engel_driftFree (q : Fin 4 → ℝ) (u : Fin 2 → ℝ) :
    driftFree engelFields q u = ![u 0, u 1, q 0 * u 1 - q 1 * u 0, q 0 ^ 2 * u 1] := by
  ext i
  fin_cases i <;> simp [driftFree, Fin.sum_univ_two, engelFields, engelG1, engelG2] <;> ring

/-- The derivative of `t ↦ G(q + t v)` at `0`, assembled from its components (supporting lemma
for MLS p. 374). -/
private theorem deriv_line {n : ℕ} (G : (Fin n → ℝ) → Fin n → ℝ) (q v w : Fin n → ℝ)
    (h : ∀ i, HasDerivAt (fun t : ℝ => G (q + t • v) i) (w i) 0) :
    deriv (fun t : ℝ => G (q + t • v)) 0 = w := by
  have hd : HasDerivAt (fun t : ℝ => G (q + t • v)) w 0 := by
    rw [hasDerivAt_pi]
    exact h
  exact hd.deriv

/-- The line `t ↦ a + t c` has derivative `c` at `0` (supporting lemma for MLS p. 374). -/
private theorem hasDerivAt_line (a c : ℝ) : HasDerivAt (fun t : ℝ => a + t * c) c 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add a

/-- `g₁` is differentiable (supporting lemma for MLS p. 374). -/
private theorem engelG1_differentiable : Differentiable ℝ engelG1 := by
  intro q
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [engelG1]
  fun_prop

/-- `g₂` is differentiable (supporting lemma for MLS p. 374). -/
private theorem engelG2_differentiable : Differentiable ℝ engelG2 := by
  intro q
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [engelG2] <;> fun_prop

/-- **MLS Example 8.4, p. 374: `[g₁, g₂] = (0, 0, 2, 2q₁)`.** -/
theorem engel_lieBracket (q : Fin 4 → ℝ) :
    lieBracket ℝ engelG1 engelG2 q = ![0, 0, 2, 2 * q 0] := by
  rw [lieBracket_eq_deriv (engelG1_differentiable q) (engelG2_differentiable q),
    deriv_line engelG2 q (engelG1 q) ![0, 0, 1, 2 * q 0] ?_,
    deriv_line engelG1 q (engelG2 q) ![0, 0, -1, 0] ?_]
  · ext i
    fin_cases i <;> simp
    norm_num
  all_goals
    intro i
    fin_cases i <;> simp [engelG1, engelG2] <;>
      first
      | exact hasDerivAt_const _ _
      | exact hasDerivAt_neg _
      | exact hasDerivAt_id _
      | simpa using hasDerivAt_line (q 0) 1
      | simpa using (hasDerivAt_line (q 0) 1).fun_pow 2

/-- **MLS Example 8.4, p. 374 (growth vector `(2, 3, 4)`): `[g₁, [g₁, g₂]] = (0, 0, 0, 2)`** (not
printed). -/
theorem engel_lieBracket_g1_lieBracket (q : Fin 4 → ℝ) :
    lieBracket ℝ engelG1 (lieBracket ℝ engelG1 engelG2) q = ![0, 0, 0, 2] := by
  have hb : lieBracket ℝ engelG1 engelG2 = fun x : Fin 4 → ℝ => ![0, 0, 2, 2 * x 0] :=
    funext engel_lieBracket
  have hd : Differentiable ℝ fun x : Fin 4 → ℝ => (![0, 0, 2, 2 * x 0] : Fin 4 → ℝ) := by
    intro x
    refine differentiableAt_pi.2 fun i => ?_
    fin_cases i <;> simp
    fun_prop
  rw [hb, lieBracket_eq_deriv (engelG1_differentiable q) (hd q),
    deriv_line (fun x : Fin 4 → ℝ => ![0, 0, 2, 2 * x 0]) q (engelG1 q) ![0, 0, 0, 2] ?_,
    deriv_line engelG1 q ![0, 0, 2, 2 * q 0] 0 ?_]
  · simp
  all_goals
    intro i
    fin_cases i <;> simp [engelG1] <;>
      first
      | exact hasDerivAt_const _ _
      | simpa using (hasDerivAt_line (2 * q 0) 2)
      | simpa using ((hasDerivAt_line (q 0) 1).const_mul 2)

/-- `g₁(q), g₂(q), [g₁, g₂](q), [g₁, [g₁, g₂]](q)` are independent (supporting lemma for MLS
p. 374). -/
private theorem engel_four (q : Fin 4 → ℝ) :
    LinearIndependent ℝ ![engelFields 0 q, engelFields 1 q,
      lieBracket ℝ (engelFields 0) (engelFields 1) q,
      lieBracket ℝ (engelFields 0) (lieBracket ℝ (engelFields 0) (engelFields 1)) q] := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![engelG1 q, engelG2 q, ![0, 0, 2, 2 * q 0], ![0, 0, 0, 2]])
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, engelG1, engelG2, Fin.succAbove])
  convert h using 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact engel_lieBracket q
  · exact engel_lieBracket_g1_lieBracket q

/-- `g₁(q), g₂(q), [g₁, g₂](q)` are independent (supporting lemma for MLS p. 374). -/
private theorem engel_triple (q : Fin 4 → ℝ) :
    LinearIndependent ℝ ![engelFields 0 q, engelFields 1 q,
      lieBracket ℝ (engelFields 0) (engelFields 1) q] := by
  have hc := (engel_four q).comp Fin.castSucc (Fin.castSucc_injective 3)
  convert hc using 1
  funext j
  fin_cases j <;> rfl

/-- `Δ₃(q) = ℝ⁴` (supporting lemma for MLS p. 374). -/
private theorem engel_filtrationAt_three (q : Fin 4 → ℝ) : filtrationAt engelFields 3 q = ⊤ := by
  refine filtrationAt_eq_top_of_linearIndependent engelFields (Module.finrank_fin_fun ℝ)
    (engel_four q) ?_
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt engelFields 0 (by norm_num) q
  · exact generator_mem_filtrationAt engelFields 1 (by norm_num) q
  · exact lieBracket_mem_filtrationAt_two engelFields (by norm_num) q
  · exact lieBracket_lieBracket_mem_filtrationAt_three engelFields 0 le_rfl q

/-- **MLS Example 8.4, p. 374: growth vector `(2, 3, 4)`** (relative growth vector `(2, 1, 1)`) at
every point. -/
theorem engel_growthVector (q : Fin 4 → ℝ) :
    growthVector engelFields 3 q = ![2, 3, 4] ∧
      relativeGrowthVector engelFields 3 q = ![2, 1, 1] := by
  have h := growthVector_three engelFields (engel_triple q) (engel_filtrationAt_three q)
  simpa using h

/-- **MLS Example 8.4, p. 374, and Definition 7.2, p. 340: degree of nonholonomy `3`** at every
point. -/
theorem engel_isDegreeOfNonholonomy (q : Fin 4 → ℝ) : IsDegreeOfNonholonomy engelFields q 3 := by
  exact isDegreeOfNonholonomy_three engelFields (by simp) (engel_triple q)
    (engel_filtrationAt_three q)

/-- **MLS Example 8.4, p. 374, and Theorem 7.5, p. 329: the controllability rank condition** for
Engel's system, `L(g₁, g₂)` has rank `4` at every point. -/
theorem engel_lieAlgebraAt (q : Fin 4 → ℝ) : lieAlgebraAt engelFields q = ⊤ := by
  exact lieAlgebraAt_eq_top_of_filtrationAt engelFields (engel_filtrationAt_three q)

/-- **MLS eq. (8.18), p. 374: `Ω(q, p)` for Engel's system,** `Ω₁₂ = pᵀ[g₁, g₂] = 2(p₃ + q₁ p₄)`
with `pᵢ = p(eᵢ)`, so (8.16) reads `u̇₁ = 2(p₃ + q₁ p₄) u₂`, `u̇₂ = −2(p₃ + q₁ p₄) u₁`. -/
theorem engel_optimalOmega (q : Fin 4 → ℝ) (p : (Fin 4 → ℝ) →L[ℝ] ℝ) (u : Fin 2 → ℝ) :
    optimalOmega engelFields q p *ᵥ u =
      ![2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1)) * u 1,
        -(2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1))) * u 0] := by
  have hv : (![0, 0, 2, 2 * q 0] : Fin 4 → ℝ) =
      (2 : ℝ) • Pi.single 2 1 + (2 * q 0) • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  have h01 : p (lieBracket ℝ (engelFields 0) (engelFields 1) q) =
      2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1)) := by
    rw [show engelFields 0 = engelG1 from rfl, show engelFields 1 = engelG2 from rfl,
      engel_lieBracket, hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have h10 : p (lieBracket ℝ (engelFields 1) (engelFields 0) q) =
      -(2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1))) := by
    rw [lieBracket_swap, map_neg, h01]
  ext i
  fin_cases i <;>
    simp [optimalOmega, Matrix.mulVec, dotProduct, Fin.sum_univ_two, lieBracket_self, h01, h10]

end Examples
end RoboLean
