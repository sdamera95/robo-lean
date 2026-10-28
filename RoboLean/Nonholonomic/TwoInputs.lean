import RoboLean.Nonholonomic.Filtration
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Growth vectors of two-input systems

MLS Chapter 7, printed pp. 340–341 (the filtration, Definitions 7.2–7.3), as used in Examples
7.7, 7.9, 7.10 and 7.11 (pp. 341–344): for two inputs `g₁, g₂`, the levels of the filtration and
the growth vector are read from the linear independence of `g₁(q), g₂(q), [g₁, g₂](q)` and of the
third-level brackets. Generators are `g 0 = g₁`, `g 1 = g₂`.

**Formalized.** Independence of `g₁(q), g₂(q), [g₁, g₂](q)` gives `r₁ = 2`, `r₂ = 3` and shows
that `Δ = span{g₁, g₂}` violates the generator criterion of p. 325 at `q` (it is not involutive);
with `dim E = 3` it gives degree of nonholonomy `2` and growth vector `(2, 3)`; with
`Δ₃(q) = T_q E` and `dim E > 3` it gives degree `3` and growth vector `(2, 3, dim E)`; the same
hypotheses on a set `U` give a regular filtration on `U`. The brackets `[gₐ, [g₁, g₂]]` span `Δ₃`.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS p. 340:** a generator lies in every level `Δᵢ(q)`, `i ≥ 1`. -/
theorem generator_mem_filtrationAt {m : ℕ} (g : Fin m → E → E) (j : Fin m) {i : ℕ} (hi : 1 ≤ i)
    (q : E) : g j q ∈ filtrationAt g i q := by
  have h1 : g j ∈ filtrationFields g 1 := by
    rw [filtrationFields_one]
    exact Set.mem_range_self j
  exact mem_spanAt (filtrationFields_mono g hi h1) q

/-- **MLS p. 340:** `[g₁, g₂](q) ∈ Δᵢ(q)` for `i ≥ 2`. -/
theorem lieBracket_mem_filtrationAt_two (g : Fin 2 → E → E) {i : ℕ} (hi : 2 ≤ i) (q : E) :
    lieBracket ℝ (g 0) (g 1) q ∈ filtrationAt g i q := by
  have h1 : g 1 ∈ filtrationFields g 1 := by
    rw [filtrationFields_one]
    exact Set.mem_range_self 1
  exact mem_spanAt (filtrationFields_mono g hi (lieBracket_mem_filtrationFields g 0 h1)) q

/-- **MLS p. 340:** `[gₐ, [g₁, g₂]](q) ∈ Δᵢ(q)` for `i ≥ 3`. -/
theorem lieBracket_lieBracket_mem_filtrationAt_three (g : Fin 2 → E → E) (a : Fin 2) {i : ℕ}
    (hi : 3 ≤ i) (q : E) :
    lieBracket ℝ (g a) (lieBracket ℝ (g 0) (g 1)) q ∈ filtrationAt g i q := by
  have h1 : g 1 ∈ filtrationFields g 1 := by
    rw [filtrationFields_one]
    exact Set.mem_range_self 1
  exact mem_spanAt (filtrationFields_mono g hi
    (lieBracket_mem_filtrationFields g a (lieBracket_mem_filtrationFields g 0 h1))) q

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **MLS p. 341:** the values of two generators at `q` as a vector. -/
private theorem values_eq_vec (g : Fin 2 → E → E) (q : E) :
    (fun j => g j q) = ![g 0 q, g 1 q] := by
  funext j
  fin_cases j <;> rfl

/-- **MLS Definition 7.3, p. 341: `r₁ = 2`** when `g₁(q), g₂(q)` are independent. -/
theorem growth_one_eq_two (g : Fin 2 → E → E) {q : E}
    (h : LinearIndependent ℝ ![g 0 q, g 1 q]) : growth g 1 q = 2 := by
  rw [growth, filtrationAt_one, spanAt_range, values_eq_vec, finrank_span_eq_card h,
    Fintype.card_fin]

/-- **MLS Definition 7.3, p. 341: `r₂ = 3`** when `g₁(q), g₂(q), [g₁, g₂](q)` are independent. -/
theorem growth_two_eq_three (g : Fin 2 → E → E) {q : E}
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) :
    growth g 2 q = 3 := by
  have hs : ({g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q} : Set E) =
      Set.range ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union, Set.singleton_union]
  rw [growth, filtrationAt_two, hs, finrank_span_eq_card h, Fintype.card_fin]

/-- **MLS pp. 340–341:** once a level is the whole space, every later level has rank `dim E`. -/
theorem growth_eq_finrank_of_filtrationAt_eq_top [FiniteDimensional ℝ E] {m : ℕ}
    (g : Fin m → E → E) {i j : ℕ} {q : E} (h : filtrationAt g i q = ⊤) (hij : i ≤ j) :
    growth g j q = Module.finrank ℝ E := by
  have hj : filtrationAt g j q = ⊤ := top_le_iff.mp (h ▸ filtrationAt_mono g hij q)
  rw [growth, hj, finrank_top]

/-- **MLS p. 325:** if `g₁(q), g₂(q), [g₁, g₂](q)` are independent at some `q ∈ U`, the
distribution `span{g₁, g₂}` violates the generator criterion on `U`: it is not involutive. -/
theorem not_generatorsInvolutiveOn_of_linearIndependent (g : Fin 2 → E → E) {U : Set E} {q : E}
    (hq : q ∈ U) (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) :
    ¬ GeneratorsInvolutiveOn (Set.range g) U := by
  intro hI
  have hmem := hI q hq (g 0) (Set.mem_range_self 0) (g 1) (Set.mem_range_self 1)
  rw [spanAt_range] at hmem
  refine h.notMem_span_image (s := {0, 1}) (x := 2) (by decide) ?_
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact ⟨0, by simp, rfl⟩
  · exact ⟨1, by simp, rfl⟩

/-- **MLS p. 341:** independence of `g₁(q), g₂(q), [g₁, g₂](q)` gives independence of
`g₁(q), g₂(q)`. -/
private theorem linearIndependent_pair_of_triple (g : Fin 2 → E → E) {q : E}
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) :
    LinearIndependent ℝ ![g 0 q, g 1 q] := by
  have hc := h.comp Fin.castSucc (Fin.castSucc_injective 2)
  have he : ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q] ∘ Fin.castSucc = ![g 0 q, g 1 q] := by
    funext j
    fin_cases j <;> rfl
  rwa [he] at hc

/-- **MLS pp. 340–341:** in dimension `3`, independence of `g₁(q), g₂(q), [g₁, g₂](q)` gives
`Δ₂(q) = T_q E`. -/
private theorem filtrationAt_two_eq_top [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {q : E}
    (hn : Module.finrank ℝ E = 3)
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) :
    filtrationAt g 2 q = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [hn]
  exact growth_two_eq_three g h

/-- **MLS Definition 7.3, p. 341:** the ranks `r₀ = 0`, `r₁ = 2`, `r₂ = 3` and `rᵢ = dim E` for
`i ≥ 3` when `g₁(q), g₂(q), [g₁, g₂](q)` are independent and `Δ₃(q) = T_q E`. -/
private theorem growth_eq_of_three [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {q : E}
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q])
    (h3 : filtrationAt g 3 q = ⊤) :
    ∀ i, growth g i q =
      if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else Module.finrank ℝ E
  | 0 => by simp [growth_zero]
  | 1 => by simp [growth_one_eq_two g (linearIndependent_pair_of_triple g h)]
  | 2 => by simp [growth_two_eq_three g h]
  | i + 3 => by
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ite_false,
      show i + 3 ≠ 1 by omega, show i + 3 ≠ 2 by omega]
    exact growth_eq_finrank_of_filtrationAt_eq_top g h3 (by omega)

/-- **MLS Definition 7.2, p. 340, degree `2`:** in a space of dimension `3`, independence of
`g₁(q), g₂(q), [g₁, g₂](q)` gives degree of nonholonomy `2` at `q`. -/
theorem isDegreeOfNonholonomy_two [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {q : E}
    (hn : Module.finrank ℝ E = 3)
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) :
    IsDegreeOfNonholonomy g q 2 := by
  have h2 := filtrationAt_two_eq_top g hn h
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [growth_eq_finrank_of_filtrationAt_eq_top g h2 le_rfl,
      growth_eq_finrank_of_filtrationAt_eq_top g h2 (by norm_num)]
  · intro i hi1 hi2
    obtain rfl : i = 1 := by omega
    rw [growth_one_eq_two g (linearIndependent_pair_of_triple g h), growth_two_eq_three g h]
    norm_num

/-- **MLS Definition 7.3, p. 341, growth vector `(2, 3)` and relative growth vector `(2, 1)`:** the
first two entries for independent `g₁(q), g₂(q), [g₁, g₂](q)`; they are the whole vectors when the
degree is `2` (`isDegreeOfNonholonomy_two`, `dim E = 3`). -/
theorem growthVector_two (g : Fin 2 → E → E) {q : E}
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) :
    growthVector g 2 q = ![2, 3] ∧ relativeGrowthVector g 2 q = ![2, 1] := by
  have h1 := growth_one_eq_two g (linearIndependent_pair_of_triple g h)
  have h2 := growth_two_eq_three g h
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i
    · simpa [growthVector] using h1
    · simpa [growthVector] using h2
  · funext i
    fin_cases i
    · simp [relativeGrowthVector, h1, growth_zero]
    · simp [relativeGrowthVector, h1, h2]

/-- **MLS Definition 7.2, p. 340, degree `3`:** if `g₁(q), g₂(q), [g₁, g₂](q)` are independent,
`Δ₃(q) = T_q E` and `dim E > 3`, the degree of nonholonomy at `q` is `3`. -/
theorem isDegreeOfNonholonomy_three [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {q : E}
    (hn : 3 < Module.finrank ℝ E)
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q])
    (h3 : filtrationAt g 3 q = ⊤) : IsDegreeOfNonholonomy g q 3 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [growth_eq_finrank_of_filtrationAt_eq_top g h3 le_rfl,
      growth_eq_finrank_of_filtrationAt_eq_top g h3 (by norm_num)]
  · intro i hi1 hi2
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · rw [growth_one_eq_two g (linearIndependent_pair_of_triple g h), growth_two_eq_three g h]
      norm_num
    · rw [growth_two_eq_three g h, growth_eq_finrank_of_filtrationAt_eq_top g h3 le_rfl]
      exact hn

/-- **MLS Definition 7.3, p. 341, growth vector `(2, 3, n)` and relative growth vector
`(2, 1, n − 3)`** with `n = dim E`, under the hypotheses of `isDegreeOfNonholonomy_three`. -/
theorem growthVector_three [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {q : E}
    (h : LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q])
    (h3 : filtrationAt g 3 q = ⊤) :
    growthVector g 3 q = ![2, 3, Module.finrank ℝ E] ∧
      relativeGrowthVector g 3 q = ![2, 1, (Module.finrank ℝ E : ℤ) - 3] := by
  have h1 := growth_one_eq_two g (linearIndependent_pair_of_triple g h)
  have h2 := growth_two_eq_three g h
  have h3' := growth_eq_finrank_of_filtrationAt_eq_top g h3 le_rfl
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i
    · simpa [growthVector] using h1
    · simpa [growthVector] using h2
    · simpa [growthVector] using h3'
  · funext i
    fin_cases i
    · simp [relativeGrowthVector, h1, growth_zero]
    · simp [relativeGrowthVector, h1, h2]
    · simp [relativeGrowthVector, h2, h3']

/-- **MLS p. 340: a regular filtration, degree `2`:** if `dim E = 3` and `g₁, g₂, [g₁, g₂]` are
independent at every point of `U`, the filtration is regular on `U` around any `q₀ ∈ U`. -/
theorem isRegularFiltrationOn_two [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {U : Set E}
    (hn : Module.finrank ℝ E = 3)
    (h : ∀ q ∈ U, LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q]) {q₀ : E}
    (hq₀ : q₀ ∈ U) : IsRegularFiltrationOn g U q₀ := by
  have h3 : ∀ q ∈ U, filtrationAt g 3 q = ⊤ := fun q hq =>
    top_le_iff.mp (filtrationAt_two_eq_top g hn (h q hq) ▸ filtrationAt_mono g (by norm_num) q)
  intro i q hq
  rw [growth_eq_of_three g (h q hq) (h3 q hq), growth_eq_of_three g (h q₀ hq₀) (h3 q₀ hq₀)]

/-- **MLS p. 340: a regular filtration, degree `3`:** if at every point of `U` the fields
`g₁, g₂, [g₁, g₂]` are independent and `Δ₃ = T E`, the filtration is regular on `U` around any
`q₀ ∈ U`. -/
theorem isRegularFiltrationOn_three [FiniteDimensional ℝ E] (g : Fin 2 → E → E) {U : Set E}
    (h : ∀ q ∈ U, LinearIndependent ℝ ![g 0 q, g 1 q, lieBracket ℝ (g 0) (g 1) q])
    (h3 : ∀ q ∈ U, filtrationAt g 3 q = ⊤) {q₀ : E} (hq₀ : q₀ ∈ U) :
    IsRegularFiltrationOn g U q₀ := by
  intro i q hq
  rw [growth_eq_of_three g (h q hq) (h3 q hq), growth_eq_of_three g (h q₀ hq₀) (h3 q₀ hq₀)]

end Nonholonomic
end RoboLean
