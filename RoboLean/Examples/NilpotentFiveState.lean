import RoboLean.Nonholonomic.Nilpotent
import RoboLean.Nonholonomic.TwoInputs
import RoboLean.Nonholonomic.Controllability
import RoboLean.Nonholonomic.OptimalInputs

/-!
# A five-state nilpotent system: MLS Chapter 8, Exercise 2

MLS Chapter 8, Exercise 2, printed p. 391: "Show that the following system is controllable and
nilpotent: `q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₁u₂ − q₂u₁, q̇₄ = q₁²u₂, q̇₅ = q₂²u₁`."

**What is formalized.** Coordinates `q 0 = q₁`, …, `q 4 = q₅`; input fields
`g₁ = (1, 0, −q₂, 0, q₂²)`, `g₂ = (0, 1, q₁, q₁², 0)` read from the system, as fields of `(q₁, q₂)`.
The brackets `[g₁, g₂] = (0, 0, 2, 2q₁, −2q₂)`, `[g₁, [g₁, g₂]] = (0, 0, 0, 2, 0)` and
`[g₂, [g₁, g₂]] = (0, 0, 0, 0, −2)` give `Δ₃ = ℝ⁵` at every point: the controllability rank
condition (Theorem 7.5, p. 329, the reading of "controllable" used by the library), the growth
vector `(2, 3, 5)` and the degree of nonholonomy `3`. Nilpotent in the sense of p. 344: every Lie
product of the generators of length greater than `3` is zero, and `[g₁, [g₁, g₂]] ≠ 0`, so the order
of nilpotency is `3`. For Exercise 10 (p. 393), the matrix `Ω(q, p)` of (8.16) has the entry
`p[g₁, g₂] = 2(p₃ + q₁p₄ − q₂p₅)`; the optimal inputs themselves are not formalized.
-/

noncomputable section

open Set VectorField Matrix
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Chapter 8, Exercise 2, p. 391: `g₁ = (1, 0, −q₂, 0, q₂²)`** as a function of `(q₁, q₂)`. -/
def fiveG1 (_a b : ℝ) : Fin 5 → ℝ := ![1, 0, -b, 0, b ^ 2]

/-- **MLS Chapter 8, Exercise 2, p. 391: `g₂ = (0, 1, q₁, q₁², 0)`** as a function of `(q₁, q₂)`. -/
def fiveG2 (a _b : ℝ) : Fin 5 → ℝ := ![0, 1, a, a ^ 2, 0]

/-- **MLS Chapter 8, Exercise 2, p. 391: the input fields `(g₁, g₂)`.** -/
def fiveFields : Fin 2 → (Fin 5 → ℝ) → Fin 5 → ℝ := ![baseField fiveG1, baseField fiveG2]

/-- **MLS Chapter 8, Exercise 2, p. 391: `[g₁, g₂] = (0, 0, 2, 2q₁, −2q₂)`** as a function of
`(q₁, q₂)`. -/
def fiveC (a b : ℝ) : Fin 5 → ℝ := ![0, 0, 2, 2 * a, -2 * b]

/-- **MLS Chapter 8, Exercise 2, p. 391: `[g₁, [g₁, g₂]] = (0, 0, 0, 2, 0)`.** -/
def fiveD1 : Fin 5 → ℝ := ![0, 0, 0, 2, 0]

/-- **MLS Chapter 8, Exercise 2, p. 391: `[g₂, [g₁, g₂]] = (0, 0, 0, 0, −2)`.** -/
def fiveD2 : Fin 5 → ℝ := ![0, 0, 0, 0, -2]

/-- **MLS Chapter 8, Exercise 2, p. 391: the system
`q̇ = (u₁, u₂, q₁u₂ − q₂u₁, q₁²u₂, q₂²u₁)`.** -/
theorem five_driftFree (q : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    driftFree fiveFields q u = ![u 0, u 1, q 0 * u 1 - q 1 * u 0, q 0 ^ 2 * u 1, q 1 ^ 2 * u 0] := by
  ext i
  fin_cases i <;> simp [driftFree, Fin.sum_univ_two, fiveFields, baseField, fiveG1, fiveG2] <;> ring

private theorem diff_g1 (q : Fin 5 → ℝ) : DifferentiableAt ℝ (baseField fiveG1) q := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [baseField, fiveG1] <;> fun_prop

private theorem diff_g2 (q : Fin 5 → ℝ) : DifferentiableAt ℝ (baseField fiveG2) q := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [baseField, fiveG2] <;> fun_prop

private theorem diff_c (q : Fin 5 → ℝ) : DifferentiableAt ℝ (baseField fiveC) q := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [baseField, fiveC] <;> fun_prop

/-- **MLS Chapter 8, Exercise 2, p. 391: `[g₁, g₂] = (0, 0, 2, 2q₁, −2q₂)`.** -/
theorem five_lieBracket : lieBracket ℝ (fiveFields 0) (fiveFields 1) = baseField fiveC := by
  funext q
  have hFa : HasDerivAt (fun a => fiveG1 a (q 1)) 0 (q 0) := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveG1] <;> poly_hasDerivAt
  have hFb : HasDerivAt (fun b => fiveG1 (q 0) b) ![0, 0, -1, 0, 2 * q 1] (q 1) := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveG1] <;> poly_hasDerivAt
  have hGa : HasDerivAt (fun a => fiveG2 a (q 1)) ![0, 0, 1, 2 * q 0, 0] (q 0) := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveG2] <;> poly_hasDerivAt
  have hGb : HasDerivAt (fun b => fiveG2 (q 0) b) 0 (q 1) := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveG2] <;> poly_hasDerivAt
  show lieBracket ℝ (baseField fiveG1) (baseField fiveG2) q = _
  rw [lieBracket_baseField (diff_g1 q) (diff_g2 q) hFa hFb hGa hGb]
  ext i
  fin_cases i <;> simp [fiveG1, fiveG2, fiveC, baseField]
  ring

/-- `[gⱼ, [g₁, g₂]]` through the partial derivatives of `[g₁, g₂]` (supporting lemma for MLS
p. 391). -/
private theorem five_lieBracket_c (j : Fin 2) :
    lieBracket ℝ (fiveFields j) (baseField fiveC) = fun _ => ![fiveD1, fiveD2] j := by
  funext q
  have hCa : HasDerivAt (fun a => fiveC a (q 1)) fiveD1 (q 0) := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveC, fiveD1] <;> poly_hasDerivAt
  have hCb : HasDerivAt (fun b => fiveC (q 0) b) fiveD2 (q 1) := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveC, fiveD2] <;> poly_hasDerivAt
  fin_cases j
  · have hFa : HasDerivAt (fun a => fiveG1 a (q 1)) 0 (q 0) := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i <;> simp [fiveG1] <;> poly_hasDerivAt
    have hFb : HasDerivAt (fun b => fiveG1 (q 0) b) ![0, 0, -1, 0, 2 * q 1] (q 1) := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i <;> simp [fiveG1] <;> poly_hasDerivAt
    show lieBracket ℝ (baseField fiveG1) (baseField fiveC) q = _
    rw [lieBracket_baseField (diff_g1 q) (diff_c q) hFa hFb hCa hCb]
    ext i
    fin_cases i <;> simp [fiveG1, fiveC, fiveD1]
  · have hGa : HasDerivAt (fun a => fiveG2 a (q 1)) ![0, 0, 1, 2 * q 0, 0] (q 0) := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i <;> simp [fiveG2] <;> poly_hasDerivAt
    have hGb : HasDerivAt (fun b => fiveG2 (q 0) b) 0 (q 1) := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i <;> simp [fiveG2] <;> poly_hasDerivAt
    show lieBracket ℝ (baseField fiveG2) (baseField fiveC) q = _
    rw [lieBracket_baseField (diff_g2 q) (diff_c q) hGa hGb hCa hCb]
    ext i
    fin_cases i <;> simp [fiveG2, fiveC, fiveD2]

/-- **MLS Chapter 8, Exercise 2, p. 391: `[g₁, [g₁, g₂]] = (0, 0, 0, 2, 0)`.** -/
theorem five_lieBracket_g1_lieBracket :
    lieBracket ℝ (fiveFields 0) (lieBracket ℝ (fiveFields 0) (fiveFields 1)) = fun _ => fiveD1 := by
  rw [five_lieBracket, five_lieBracket_c 0]
  rfl

/-- **MLS Chapter 8, Exercise 2, p. 391: `[g₂, [g₁, g₂]] = (0, 0, 0, 0, −2)`.** -/
theorem five_lieBracket_g2_lieBracket :
    lieBracket ℝ (fiveFields 1) (lieBracket ℝ (fiveFields 0) (fiveFields 1)) = fun _ => fiveD2 := by
  rw [five_lieBracket, five_lieBracket_c 1]
  rfl

/-- The five vectors `g₁, g₂, [g₁, g₂], [g₁, [g₁, g₂]], [g₂, [g₁, g₂]]` at `q` are independent
(supporting lemma for MLS p. 391). -/
private theorem five_five (q : Fin 5 → ℝ) :
    LinearIndependent ℝ ![fiveFields 0 q, fiveFields 1 q,
      lieBracket ℝ (fiveFields 0) (fiveFields 1) q,
      lieBracket ℝ (fiveFields 0) (lieBracket ℝ (fiveFields 0) (fiveFields 1)) q,
      lieBracket ℝ (fiveFields 1) (lieBracket ℝ (fiveFields 0) (fiveFields 1)) q] := by
  rw [five_lieBracket_g1_lieBracket, five_lieBracket_g2_lieBracket, five_lieBracket]
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![fiveG1 (q 0) (q 1), fiveG2 (q 0) (q 1), fiveC (q 0) (q 1), fiveD1, fiveD2])
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, fiveG1, fiveG2, fiveC, fiveD1, fiveD2,
      Fin.succAbove])
  convert h using 1
  funext j
  fin_cases j <;> rfl

/-- `g₁(q), g₂(q), [g₁, g₂](q)` are independent (supporting lemma for MLS p. 391). -/
private theorem five_triple (q : Fin 5 → ℝ) :
    LinearIndependent ℝ ![fiveFields 0 q, fiveFields 1 q,
      lieBracket ℝ (fiveFields 0) (fiveFields 1) q] := by
  have hc := (five_five q).comp (fun i : Fin 3 => (⟨i.val, by omega⟩ : Fin 5))
    (fun i j h => Fin.ext (by simpa using congrArg Fin.val h))
  convert hc using 1
  funext j
  fin_cases j <;> rfl

/-- `Δ₃(q) = ℝ⁵` (supporting lemma for MLS p. 391). -/
private theorem five_filtrationAt_three (q : Fin 5 → ℝ) : filtrationAt fiveFields 3 q = ⊤ := by
  refine filtrationAt_eq_top_of_linearIndependent fiveFields (Module.finrank_fin_fun ℝ)
    (five_five q) ?_
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt fiveFields 0 (by norm_num) q
  · exact generator_mem_filtrationAt fiveFields 1 (by norm_num) q
  · exact lieBracket_mem_filtrationAt_two fiveFields (by norm_num) q
  · exact lieBracket_lieBracket_mem_filtrationAt_three fiveFields 0 le_rfl q
  · exact lieBracket_lieBracket_mem_filtrationAt_three fiveFields 1 le_rfl q

/-- **MLS Chapter 8, Exercise 2, p. 391 ("controllable"), with Theorem 7.5, p. 329: the
controllability rank condition** at every point, `L(g₁, g₂)` has rank `5`. -/
theorem five_lieAlgebraAt (q : Fin 5 → ℝ) : lieAlgebraAt fiveFields q = ⊤ :=
  lieAlgebraAt_eq_top_of_filtrationAt fiveFields (five_filtrationAt_three q)

/-- **MLS Chapter 8, Exercise 2, p. 391, with Definition 7.3, p. 341: growth vector `(2, 3, 5)`**
(relative growth vector `(2, 1, 2)`) at every point. -/
theorem five_growthVector (q : Fin 5 → ℝ) :
    growthVector fiveFields 3 q = ![2, 3, 5] ∧ relativeGrowthVector fiveFields 3 q = ![2, 1, 2] := by
  have h := growthVector_three fiveFields (five_triple q) (five_filtrationAt_three q)
  simpa using h

/-- **MLS Chapter 8, Exercise 2, p. 391, with Definition 7.2, p. 340: degree of nonholonomy `3`**
at every point. -/
theorem five_isDegreeOfNonholonomy (q : Fin 5 → ℝ) : IsDegreeOfNonholonomy fiveFields q 3 :=
  isDegreeOfNonholonomy_three fiveFields (by simp) (five_triple q) (five_filtrationAt_three q)

/-- The negative of a field of `q₁, q₂` is one (supporting lemma for MLS p. 391). -/
private theorem isBase_neg {X : (Fin 5 → ℝ) → Fin 5 → ℝ} (hX : IsBase X) : IsBase (-X) := by
  intro q v h0 h1
  simp [hX q v h0 h1]

/-- The classification of the Lie products by length (supporting statement for MLS p. 391). -/
private def FiveClass (l : ℕ) (A : (Fin 5 → ℝ) → Fin 5 → ℝ) : Prop :=
  (l = 1 → A = fiveFields 0 ∨ A = fiveFields 1) ∧
    (l = 2 → A = 0 ∨ A = baseField fiveC ∨ A = -baseField fiveC) ∧
    (2 ≤ l → IsBase A ∧ ∀ q, A q 0 = 0 ∧ A q 1 = 0) ∧
    (3 ≤ l → ∃ v : Fin 5 → ℝ, v 0 = 0 ∧ v 1 = 0 ∧ A = fun _ => v) ∧
    (4 ≤ l → A = 0)

private theorem fiveClass_const {l : ℕ} (hl : 3 ≤ l) {v : Fin 5 → ℝ} (h0 : v 0 = 0) (h1 : v 1 = 0)
    (h4 : 4 ≤ l → v = 0) : FiveClass l (fun _ => v) := by
  refine ⟨fun h => by omega, fun h => by omega, fun _ => ⟨isBase_const v, fun _ => ⟨h0, h1⟩⟩,
    fun _ => ⟨v, h0, h1, rfl⟩, fun h => ?_⟩
  funext q
  simp [h4 h]

private theorem fiveClass_zero {l : ℕ} (hl : 4 ≤ l) : FiveClass l 0 := by
  have h := fiveClass_const (l := l) (by omega) (v := 0) rfl rfl (fun _ => rfl)
  exact h

private theorem fiveFields_isBase (j : Fin 2) : IsBase (fiveFields j) := by
  fin_cases j
  · exact isBase_baseField fiveG1
  · exact isBase_baseField fiveG2

private theorem five_lieBracket_gen_c (i : Fin 2) (B : (Fin 5 → ℝ) → Fin 5 → ℝ)
    (hB : B = 0 ∨ B = baseField fiveC ∨ B = -baseField fiveC) :
    FiveClass 3 (lieBracket ℝ (fiveFields i) B) := by
  rcases hB with rfl | rfl | rfl
  · rw [lieBracket_zero_right]
    exact fiveClass_const (v := 0) le_rfl rfl rfl (fun h => by omega)
  · rw [five_lieBracket_c i]
    fin_cases i
    · exact fiveClass_const le_rfl (by simp [fiveD1]) (by simp [fiveD1]) (fun h => by omega)
    · exact fiveClass_const le_rfl (by simp [fiveD2]) (by simp [fiveD2]) (fun h => by omega)
  · have hneg : lieBracket ℝ (fiveFields i) (-baseField fiveC) =
        fun _ => -![fiveD1, fiveD2] i := by
      rw [lieBracket_neg_right, five_lieBracket_c i]
      rfl
    rw [hneg]
    fin_cases i
    · exact fiveClass_const le_rfl (by simp [fiveD1]) (by simp [fiveD1]) (fun h => by omega)
    · exact fiveClass_const le_rfl (by simp [fiveD2]) (by simp [fiveD2]) (fun h => by omega)

private theorem fiveClass_bracket {a b : ℕ} {A B : (Fin 5 → ℝ) → Fin 5 → ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : FiveClass a A) (hB : FiveClass b B) : FiveClass (a + b) (lieBracket ℝ A B) := by
  obtain ⟨hA1, hA2, hAv, hA3, hA4⟩ := hA
  obtain ⟨hB1, hB2, hBv, hB3, hB4⟩ := hB
  by_cases h4 : 4 ≤ a + b
  · suffices hz : lieBracket ℝ A B = 0 by
      rw [hz]
      exact fiveClass_zero h4
    by_cases ha4 : 4 ≤ a
    · rw [hA4 ha4, lieBracket_zero_left]
    by_cases hb4 : 4 ≤ b
    · rw [hB4 hb4, lieBracket_zero_right]
    by_cases ha1 : a = 1
    · obtain ⟨v, h0, h1, rfl⟩ := hB3 (by omega)
      rcases hA1 ha1 with rfl | rfl
      · exact lieBracket_const_eq_zero_of_isBase (fiveFields_isBase 0) h0 h1
      · exact lieBracket_const_eq_zero_of_isBase (fiveFields_isBase 1) h0 h1
    by_cases hb1 : b = 1
    · obtain ⟨v, h0, h1, rfl⟩ := hA3 (by omega)
      rw [lieBracket_antisymm]
      rcases hB1 hb1 with rfl | rfl
      · rw [lieBracket_const_eq_zero_of_isBase (fiveFields_isBase 0) h0 h1, neg_zero]
      · rw [lieBracket_const_eq_zero_of_isBase (fiveFields_isBase 1) h0 h1, neg_zero]
    obtain ⟨hAb, hAq⟩ := hAv (by omega)
    obtain ⟨hBb, hBq⟩ := hBv (by omega)
    funext q
    exact lieBracket_eq_zero_of_isBase hAb hBb q (hAq q).1 (hAq q).2 (hBq q).1 (hBq q).2
  · rcases (show (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h2 : lieBracket ℝ A B = 0 ∨ lieBracket ℝ A B = baseField fiveC ∨
          lieBracket ℝ A B = -baseField fiveC := by
        rcases hA1 rfl with rfl | rfl <;> rcases hB1 rfl with rfl | rfl
        · exact Or.inl (lieBracket_self)
        · exact Or.inr (Or.inl five_lieBracket)
        · refine Or.inr (Or.inr ?_)
          rw [lieBracket_antisymm, five_lieBracket]
        · exact Or.inl (lieBracket_self)
      refine ⟨fun h => by omega, fun _ => h2, fun _ => ?_, fun h => by omega, fun h => by omega⟩
      rcases h2 with h | h | h <;> rw [h]
      · exact ⟨isBase_const 0, fun _ => ⟨rfl, rfl⟩⟩
      · exact ⟨isBase_baseField fiveC, fun q => by simp [baseField, fiveC]⟩
      · exact ⟨isBase_neg (isBase_baseField fiveC), fun q => by simp [baseField, fiveC]⟩
    · rcases hA1 rfl with rfl | rfl
      · exact five_lieBracket_gen_c 0 B (hB2 rfl)
      · exact five_lieBracket_gen_c 1 B (hB2 rfl)
    · have hneg : lieBracket ℝ A B = -lieBracket ℝ B A := lieBracket_antisymm A B
      have hc : FiveClass 3 (lieBracket ℝ B A) := by
        rcases hB1 rfl with rfl | rfl
        · exact five_lieBracket_gen_c 0 A (hA2 rfl)
        · exact five_lieBracket_gen_c 1 A (hA2 rfl)
      obtain ⟨-, -, -, hc3, -⟩ := hc
      obtain ⟨v, h0, h1, hv⟩ := hc3 le_rfl
      rw [hneg, hv]
      exact fiveClass_const le_rfl (by simp [h0]) (by simp [h1]) (fun h => by omega)

private theorem fiveClass_of_isLieProduct {l : ℕ} {A : (Fin 5 → ℝ) → Fin 5 → ℝ}
    (h : IsLieProduct fiveFields l A) : FiveClass l A := by
  induction h with
  | gen j =>
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  | bracket hA hB ihA ihB => exact fiveClass_bracket hA.one_le hB.one_le ihA ihB

/-- **MLS Chapter 8, Exercise 2, p. 391 ("nilpotent"), in the sense of p. 344: order of
nilpotency `3`.** Every Lie product of `g₁, g₂` of length greater than `3` is zero, and the product
`[g₁, [g₁, g₂]]` of length `3` is not. -/
theorem five_isNilpotencyOrder : IsNilpotencyOrder fiveFields 3 := by
  refine ⟨fun l A hA hl => (fiveClass_of_isLieProduct hA).2.2.2.2 hl, ?_⟩
  refine ⟨lieBracket ℝ (fiveFields 0) (lieBracket ℝ (fiveFields 0) (fiveFields 1)),
    IsLieProduct.bracket (IsLieProduct.gen 0) (IsLieProduct.bracket (IsLieProduct.gen 0)
      (IsLieProduct.gen 1)), ?_⟩
  rw [five_lieBracket_g1_lieBracket]
  intro h
  have := congrFun (congrFun h 0) 3
  simp [fiveD1] at this

/-- **MLS Chapter 8, Exercise 10, p. 393, with (8.16), p. 373: `Ω(q, p)` for the system of
Exercise 2,** `Ω₁₂ = p[g₁, g₂] = 2(p₃ + q₁p₄ − q₂p₅)` with `pᵢ = p(eᵢ)`, so (8.16) reads
`u̇₁ = Ω₁₂ u₂`, `u̇₂ = −Ω₁₂ u₁`. -/
theorem five_optimalOmega (q : Fin 5 → ℝ) (p : (Fin 5 → ℝ) →L[ℝ] ℝ) (u : Fin 2 → ℝ) :
    optimalOmega fiveFields q p *ᵥ u =
      ![2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1) - q 1 * p (Pi.single 4 1)) * u 1,
        -(2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1) - q 1 * p (Pi.single 4 1))) * u 0] := by
  have hv : baseField fiveC q =
      (2 : ℝ) • Pi.single 2 1 + (2 * q 0) • Pi.single 3 1 + (-2 * q 1) • Pi.single 4 1 := by
    ext i
    fin_cases i <;> simp [baseField, fiveC]
  have h01 : p (lieBracket ℝ (fiveFields 0) (fiveFields 1) q) =
      2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1) - q 1 * p (Pi.single 4 1)) := by
    rw [five_lieBracket, hv, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring
  have h10 : p (lieBracket ℝ (fiveFields 1) (fiveFields 0) q) =
      -(2 * (p (Pi.single 2 1) + q 0 * p (Pi.single 3 1) - q 1 * p (Pi.single 4 1))) := by
    rw [lieBracket_swap, map_neg, h01]
  ext i
  fin_cases i <;>
    simp [optimalOmega, Matrix.mulVec, dotProduct, Fin.sum_univ_two, lieBracket_self, h01, h10]

end Examples
end RoboLean
