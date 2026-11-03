import RoboLean.Nonholonomic.ExercisesSeven
import RoboLean.Nonholonomic.VectorField
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The third stage of Exercise 17 of MLS Chapter 7 and the count of p. 362

MLS Chapter 7, Exercise 17, printed p. 353: the relative growth of a regular system is bounded by
`σ̄ᵢ = (1/i)((σ̄₁)^i − Σ_{j | i, j < i} jσ̄ⱼ)`; at `i = 3`, `σ̄₃ = (σ̄₁³ − σ̄₁)/3`. MLS p. 362: "the
maximum number of controllable `qᵢⱼₖ` is `(m + 1)m(m − 1)/3`" (from Exercise 17).

**What is formalized.** For `m` input fields of class `C²` at a point `q` of a finite-dimensional
space, `r₃ − r₂ ≤ (m³ − m)/3 = σ̄₃` at `q`: `Δ₃` adds to `Δ₂` at most the brackets
`[gᵢ, [gⱼ, gₖ]]` with `j < k` and `i ≥ j` (the Philip Hall products of length three), since
`[gᵢ, [gⱼ, gₖ]] = [gⱼ, [gᵢ, gₖ]] − [gₖ, [gᵢ, gⱼ]]` for `i < j < k` (Jacobi, Proposition 7.1) and
skew-symmetry handles the rest; there are `Σ_{j<k} (m − j) = (m³ − m)/3` of them. This is the
upper bound behind p. 362's count; that it is attained (for the free nilpotent system (8.6)) is not
formalized.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

/-- `Σ_{t<m} (m − t) = m(m + 1)/2` (supporting lemma for MLS p. 353). -/
private theorem sum_range_sub (m : ℕ) :
    ∑ t ∈ Finset.range m, ((m : ℚ) - t) = (m : ℚ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ t ∈ Finset.range m, (((m + 1 : ℕ) : ℚ) - t) =
        ∑ t ∈ Finset.range m, ((m : ℚ) - t) + m := by
      have h1 : ∀ t ∈ Finset.range m, (((m + 1 : ℕ) : ℚ) - t) = ((m : ℚ) - t) + 1 :=
        fun t _ => by push_cast; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      simp
    rw [h, ih]
    push_cast
    ring

/-- `Σ_{t<m} (m − t)(m − 1 − t) = (m³ − m)/3` (supporting lemma for MLS pp. 353 and 362). -/
private theorem sum_range_sub_mul (m : ℕ) :
    ∑ t ∈ Finset.range m, ((m : ℚ) - t) * ((m : ℚ) - 1 - t) = ((m : ℚ) ^ 3 - m) / 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ t ∈ Finset.range m, (((m + 1 : ℕ) : ℚ) - t) * (((m + 1 : ℕ) : ℚ) - 1 - t) =
        ∑ t ∈ Finset.range m, ((m : ℚ) - t) * ((m : ℚ) - 1 - t) +
          2 * ∑ t ∈ Finset.range m, ((m : ℚ) - t) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by push_cast; ring
    rw [h, ih, sum_range_sub]
    push_cast
    ring

/-- The number of Philip Hall products `[gᵢ, [gⱼ, gₖ]]`, `j < k`, `i ≥ j`, of length three is
`(m³ − m)/3` (supporting lemma for MLS pp. 353 and 362). -/
private theorem card_hallThree (m : ℕ) :
    ((((Finset.univ ×ˢ Finset.univ).filter fun x : Fin m × Fin m => x.1 < x.2).sigma
      fun x => Finset.Ici x.1).card : ℚ) = ((m : ℚ) ^ 3 - m) / 3 := by
  rw [Finset.card_sigma]
  push_cast
  simp only [Fin.card_Ici]
  rw [Finset.sum_filter, Finset.sum_product]
  have h : ∀ j : Fin m, (∑ k : Fin m, if j < k then (((m - j : ℕ) : ℕ) : ℚ) else 0) =
      ((m : ℚ) - j) * ((m : ℚ) - 1 - j) := by
    intro j
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter fun k : Fin m => j < k).card : ℚ) = (m : ℚ) - 1 - j := by
      have h1 : (Finset.univ.filter fun k : Fin m => j < k) = Finset.Ioi j := by
        ext k
        simp
      rw [h1, Fin.card_Ioi]
      have hj := j.isLt
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    rw [hc, Nat.cast_sub j.isLt.le]
    ring
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun t => ((m : ℚ) - t) * ((m : ℚ) - 1 - t)), sum_range_sub_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS Chapter 7, Exercise 17, p. 353, third stage, and p. 362: `σ₃ = r₃ − r₂ ≤ (m³ − m)/3 =
σ̄₃`** for `m` input fields of class `C²` at `q` on a finite-dimensional space, with `σ̄₁ = m`: the
Philip Hall products of length three span `Δ₃(q)` modulo `Δ₂(q)`. -/
theorem relativeGrowth_three_le_maxGrowth [FiniteDimensional ℝ E] (g : Fin m → E → E) (q : E)
    (hg : ∀ j, ContDiffAt ℝ 2 (g j) q) :
    ((growth g 3 q : ℚ) - growth g 2 q) ≤ maxGrowth m 3 := by
  classical
  set H := ((Finset.univ ×ˢ Finset.univ).filter fun x : Fin m × Fin m => x.1 < x.2).sigma
    fun x => Finset.Ici x.1
  set b : (Σ _ : Fin m × Fin m, Fin m) → E := fun x =>
    lieBracket ℝ (g x.2) (lieBracket ℝ (g x.1.1) (g x.1.2)) q
  set W := Submodule.span ℝ ((H.image b : Finset E) : Set E)
  have hW : ∀ x ∈ H, b x ∈ W := fun x hx =>
    Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem b hx))
  have hH : ∀ i j k : Fin m, j < k → j ≤ i → lieBracket ℝ (g i) (lieBracket ℝ (g j) (g k)) q ∈ W := by
    intro i j k hjk hji
    exact hW ⟨(j, k), i⟩ (by simp [H, hjk, hji])
  have hlt : ∀ i j k : Fin m, j < k → lieBracket ℝ (g i) (lieBracket ℝ (g j) (g k)) q ∈ W := by
    intro i j k hjk
    by_cases hji : j ≤ i
    · exact hH i j k hjk hji
    · rw [not_le] at hji
      have hjac := lieBracket_jacobi (hg i) (hg j) (hg k)
      have hsw : lieBracket ℝ (g j) (lieBracket ℝ (g k) (g i)) q =
          -lieBracket ℝ (g j) (lieBracket ℝ (g i) (g k)) q := by
        rw [lieBracket_antisymm (g k) (g i), lieBracket_neg_right]
        rfl
      have heq : lieBracket ℝ (g i) (lieBracket ℝ (g j) (g k)) q =
          lieBracket ℝ (g j) (lieBracket ℝ (g i) (g k)) q -
            lieBracket ℝ (g k) (lieBracket ℝ (g i) (g j)) q := by
        rw [hsw] at hjac
        calc lieBracket ℝ (g i) (lieBracket ℝ (g j) (g k)) q
            = (lieBracket ℝ (g i) (lieBracket ℝ (g j) (g k)) q +
                lieBracket ℝ (g k) (lieBracket ℝ (g i) (g j)) q +
                -lieBracket ℝ (g j) (lieBracket ℝ (g i) (g k)) q) -
                lieBracket ℝ (g k) (lieBracket ℝ (g i) (g j)) q +
                lieBracket ℝ (g j) (lieBracket ℝ (g i) (g k)) q := by abel
          _ = lieBracket ℝ (g j) (lieBracket ℝ (g i) (g k)) q -
                lieBracket ℝ (g k) (lieBracket ℝ (g i) (g j)) q := by rw [hjac]; abel
      rw [heq]
      exact W.sub_mem (hH j i k (hji.trans hjk) hji.le) (hH k i j hji (hji.trans hjk).le)
  have hall : ∀ i j k : Fin m, lieBracket ℝ (g i) (lieBracket ℝ (g j) (g k)) q ∈ W := by
    intro i j k
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact hlt i j k hjk
    · rw [lieBracket_self, lieBracket_zero_right]
      exact W.zero_mem
    · rw [lieBracket_antisymm (g j) (g k), lieBracket_neg_right]
      exact W.neg_mem (hlt i k j hkj)
  have h1 : ∀ j, g j ∈ filtrationFields g 1 := fun j => by
    rw [filtrationFields_one]
    exact ⟨j, rfl⟩
  have hle : filtrationAt g 3 q ≤ filtrationAt g 2 q ⊔ W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    rcases hf with ⟨j, rfl⟩ | ⟨i, w, hw, rfl⟩
    · exact Submodule.mem_sup_left (mem_spanAt (filtrationFields_mono g (by norm_num) (h1 j)) q)
    · rcases hw with ⟨k, rfl⟩ | ⟨j, w', hw', rfl⟩
      · exact Submodule.mem_sup_left
          (mem_spanAt (lieBracket_mem_filtrationFields g i (h1 k)) q)
      · rw [filtrationFields_one] at hw'
        obtain ⟨k, rfl⟩ := hw'
        exact Submodule.mem_sup_right (hall i j k)
  have hWr : Module.finrank ℝ W ≤ H.card :=
    (finrank_span_finset_le_card _).trans Finset.card_image_le
  have hfin : growth g 3 q ≤ growth g 2 q + H.card := by
    calc growth g 3 q ≤ Module.finrank ℝ ↥(filtrationAt g 2 q ⊔ W) := Submodule.finrank_mono hle
      _ ≤ Module.finrank ℝ (filtrationAt g 2 q) + Module.finrank ℝ W :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ growth g 2 q + H.card := by
          rw [growth]
          omega
  have hq : (growth g 3 q : ℚ) ≤ growth g 2 q + (H.card : ℚ) := by exact_mod_cast hfin
  rw [maxGrowth_three]
  have := card_hallThree m
  linarith

end Nonholonomic
end RoboLean
