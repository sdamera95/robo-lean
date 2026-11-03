import RoboLean.Nonholonomic.Integrability
import RoboLean.Nonholonomic.Filtration
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Exercises 2 and 17 of MLS Chapter 7

MLS Chapter 7, printed p. 349, Exercise 2: "Show that the differential constraint in `ℝ⁵` given by
`(0  1  ρ sin q₅  ρ cos q₃  cos q₅) q̇ = 0` is nonholonomic." Printed p. 353, Exercise 17
("Hard"): "Show that for a regular system the growth vector is bounded above by
`σ̄ᵢ = (1/i)((σ̄₁)^i − Σ_{j | i, j < i} j σ̄ⱼ)`, `i > 1`, where `σ̄ᵢ` is the maximum relative growth
at the `i`th stage."

**What is formalized.**
* Exercise 2, for `ρ ≠ 0` (for `ρ = 0` the constraint is `q̇₂ + cos q₅ q̇₅ = 0`, exact, hence
  integrable): on no nonempty open set are the constraints integrable with a `C²` map, by the
  library's necessity half of Proposition 7.4 (p. 328) applied to `f₃ = e₃ − ρ sin q₅ e₂` and
  `f₅ = e₅ − cos q₅ e₂`, both annihilated by the constraint, with
  `[f₃, f₅] = ρ cos q₅ e₂` and `ω · [f₃, f₅] = ρ cos q₅`; every nonempty open set contains a point
  with `cos q₅ ≠ 0`.
* Exercise 17: the bound `σ̄ᵢ` as a function of `σ̄₁` (`maxGrowth`, by the printed recursion), its
  values `σ̄₂ = (σ̄₁² − σ̄₁)/2` and `σ̄₃ = (σ̄₁³ − σ̄₁)/3`; the first two stages of the bound for `m`
  input fields on a finite-dimensional space at every point, `r₁ ≤ m` and `r₂ − r₁ ≤ m(m − 1)/2`
  (`σ̄₁ = m`), by skew-symmetry of the bracket; and the count of p. 362 that rests on it: the
  `m · m(m − 1)/2` coordinates `qᵢⱼₖ` of (8.6) (`i < j`) less one Jacobi relation for each triple
  `i < j < k` number `(m + 1)m(m − 1)/3 = σ̄₃` (an arithmetic identity). The bound at stages
  `i ≥ 3` (the dimension of the free Lie algebra, Witt's formula) is not formalized.

Coordinates: `q 0 = q₁`, …, `q 4 = q₅`.
-/

noncomputable section

open Set Filter Topology VectorField Matrix Real

namespace RoboLean
namespace Nonholonomic

/-- **MLS Chapter 7, Exercise 2, p. 349: the constraint `(0, 1, ρ sin q₅, ρ cos q₃, cos q₅) q̇ = 0`**
as a `1 × 5` matrix. -/
def exerciseTwoConstraint (ρ : ℝ) (q : Fin 5 → ℝ) : Matrix (Fin 1) (Fin 5) ℝ :=
  !![0, 1, ρ * sin (q 4), ρ * cos (q 2), cos (q 4)]

/-- **MLS Chapter 7, Exercise 2, p. 349: the field `f₃ = e₃ − ρ sin q₅ e₂`** annihilated by the
constraint. -/
def exerciseTwoF3 (ρ : ℝ) (q : Fin 5 → ℝ) : Fin 5 → ℝ := ![0, -(ρ * sin (q 4)), 1, 0, 0]

/-- **MLS Chapter 7, Exercise 2, p. 349: the field `f₅ = e₅ − cos q₅ e₂`** annihilated by the
constraint. -/
def exerciseTwoF5 (q : Fin 5 → ℝ) : Fin 5 → ℝ := ![0, -cos (q 4), 0, 0, 1]

/-- **MLS Chapter 7, Exercise 2, p. 349:** `f₃` and `f₅` satisfy the constraint. -/
theorem exerciseTwo_annihilates (ρ : ℝ) (q : Fin 5 → ℝ) :
    exerciseTwoConstraint ρ q *ᵥ exerciseTwoF3 ρ q = 0 ∧
      exerciseTwoConstraint ρ q *ᵥ exerciseTwoF5 q = 0 := by
  refine ⟨?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [exerciseTwoConstraint, exerciseTwoF3, exerciseTwoF5, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

private theorem exerciseTwoF3_differentiable (ρ : ℝ) (q : Fin 5 → ℝ) :
    DifferentiableAt ℝ (exerciseTwoF3 ρ) q := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [exerciseTwoF3]
  fun_prop

private theorem exerciseTwoF5_differentiable (q : Fin 5 → ℝ) :
    DifferentiableAt ℝ exerciseTwoF5 q := by
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [exerciseTwoF5]
  fun_prop

/-- **MLS Chapter 7, Exercise 2, p. 349: `[f₃, f₅] = ρ cos q₅ e₂`.** -/
theorem exerciseTwo_lieBracket (ρ : ℝ) (q : Fin 5 → ℝ) :
    lieBracket ℝ (exerciseTwoF3 ρ) exerciseTwoF5 q = ![0, ρ * cos (q 4), 0, 0, 0] := by
  rw [lieBracket_eq_deriv (exerciseTwoF3_differentiable ρ q) (exerciseTwoF5_differentiable q)]
  have h1 : (fun t : ℝ => exerciseTwoF5 (q + t • exerciseTwoF3 ρ q)) =
      fun _ => exerciseTwoF5 q := by
    funext t
    simp [exerciseTwoF5, exerciseTwoF3]
  have h2 : HasDerivAt (fun t : ℝ => exerciseTwoF3 ρ (q + t • exerciseTwoF5 q))
      ![0, -(ρ * cos (q 4)), 0, 0, 0] 0 := by
    have hs : HasDerivAt (fun t : ℝ => q 4 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (q 4)
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [exerciseTwoF3, exerciseTwoF5] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · have h : HasDerivAt (fun t : ℝ => -(ρ * sin (q 4 + t))) (-(ρ * (cos (q 4 + 0) * 1))) 0 :=
        (hs.sin.const_mul ρ).neg
      simp only [add_zero, mul_one] at h
      simpa [exerciseTwoF3, exerciseTwoF5] using h
    · simpa [exerciseTwoF3, exerciseTwoF5] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa [exerciseTwoF3, exerciseTwoF5] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [exerciseTwoF3, exerciseTwoF5] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  rw [h1, deriv_const, h2.deriv]
  ext i
  fin_cases i <;> simp

/-- Every nonempty open set of `ℝ⁵` contains a point with `cos q₅ ≠ 0` (supporting lemma for MLS
p. 349). -/
private theorem exists_cos_ne_zero {U : Set (Fin 5 → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, cos (q 4) ≠ 0 := by
  obtain ⟨q, hq⟩ := hne
  by_cases hc : cos (q 4) = 0
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU q hq
    set δ := min (ε / 2) 1 with hδ
    have hδpos : 0 < δ := lt_min (by linarith) one_pos
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ1 : δ ≤ 1 := min_le_right _ _
    refine ⟨q + Pi.single 4 δ, hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single, Real.norm_eq_abs,
        abs_of_pos hδpos]
      exact hδε
    · have hs : sin (q 4) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (q 4)]
      have hsδ : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδpos (by linarith [Real.two_le_pi])
      simp only [Pi.add_apply, Pi.single_eq_same, cos_add, hc, zero_mul, zero_sub, neg_ne_zero]
      intro h
      rcases mul_eq_zero.1 h with h' | h'
      · rw [h'] at hs
        norm_num at hs
      · linarith
  · exact ⟨q, hq, hc⟩

/-- **MLS Chapter 7, Exercise 2, p. 349: the constraint is nonholonomic** for `ρ ≠ 0`: on no
nonempty open set `U ⊆ ℝ⁵` is it integrable with a `C²` map (Proposition 7.4, p. 328, necessity,
with `ω · [f₃, f₅] = ρ cos q₅`). -/
theorem exerciseTwo_not_isC2IntegrableOn {ρ : ℝ} (hρ : ρ ≠ 0) {U : Set (Fin 5 → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty) : ¬ IsC2IntegrableOn (exerciseTwoConstraint ρ) U := by
  obtain ⟨q, hq, hc⟩ := exists_cos_ne_zero hU hne
  refine not_isC2IntegrableOn_of_lieBracket hU (fun x _ => exerciseTwoF3_differentiable ρ x)
    (fun x _ => exerciseTwoF5_differentiable x) (fun x _ => (exerciseTwo_annihilates ρ x).1)
    (fun x _ => (exerciseTwo_annihilates ρ x).2) hq ?_
  rw [exerciseTwo_lieBracket]
  intro h
  have h0 := congrFun h 0
  simp [exerciseTwoConstraint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0
  rcases h0 with h0 | h0
  · exact hρ h0
  · exact hc h0

/-- **MLS Chapter 7, Exercise 17, p. 353: the bound `σ̄ᵢ`** as a function of `σ̄₁`, by the printed
recursion `σ̄ᵢ = (1/i)((σ̄₁)^i − Σ_{j | i, j < i} j σ̄ⱼ)` (for `i = 1` the sum is empty and
`σ̄₁` is returned; `σ̄₀ = 0`). -/
def maxGrowth (s : ℚ) (i : ℕ) : ℚ :=
  (s ^ i - ∑ j ∈ (Nat.properDivisors i).attach, (j : ℚ) * maxGrowth s j) / i
termination_by i
decreasing_by exact (Nat.mem_properDivisors.1 j.2).2

/-- **MLS Chapter 7, Exercise 17, p. 353:** the recursion returns `σ̄₁` at the first stage. -/
theorem maxGrowth_one (s : ℚ) : maxGrowth s 1 = s := by
  rw [maxGrowth, Finset.sum_attach (Nat.properDivisors 1) (fun j => (j : ℚ) * maxGrowth s j)]
  simp

/-- **MLS Chapter 7, Exercise 17, p. 353: `σ̄₂ = (σ̄₁² − σ̄₁)/2`.** -/
theorem maxGrowth_two (s : ℚ) : maxGrowth s 2 = (s ^ 2 - s) / 2 := by
  have h : Nat.properDivisors 2 = {1} := by decide
  rw [maxGrowth, Finset.sum_attach (Nat.properDivisors 2) (fun j => (j : ℚ) * maxGrowth s j), h,
    Finset.sum_singleton, maxGrowth_one]
  push_cast
  ring

/-- **MLS Chapter 7, Exercise 17, p. 353, and p. 362: `σ̄₃ = (σ̄₁³ − σ̄₁)/3`,** which is
`(m + 1)m(m − 1)/3` for `σ̄₁ = m`. -/
theorem maxGrowth_three (s : ℚ) : maxGrowth s 3 = (s ^ 3 - s) / 3 := by
  have h : Nat.properDivisors 3 = {1} := by decide
  rw [maxGrowth, Finset.sum_attach (Nat.properDivisors 3) (fun j => (j : ℚ) * maxGrowth s j), h,
    Finset.sum_singleton, maxGrowth_one]
  push_cast
  ring

/-- **MLS p. 362 with Chapter 7, Exercise 17, p. 353: the count of second-order coordinates.** The
`m · m(m − 1)/2` coordinates `qᵢⱼₖ` (`i < j`, any `k`) of (8.6), less one Jacobi relation for each
triple `i < j < k`, number `(m + 1)m(m − 1)/3 = σ̄₃` with `σ̄₁ = m` (arithmetic identity). -/
theorem secondOrder_count (m : ℕ) :
    ((m * m.choose 2 - m.choose 3 : ℕ) : ℚ) = maxGrowth m 3 ∧
      maxGrowth m 3 = ((m + 1) * m * (m - 1) / 3 : ℚ) := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;> norm_num [maxGrowth_three, Nat.choose]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have h6 : 6 * (k + 3).choose 3 = (k + 3) * (k + 2) * (k + 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (k + 3) 3
    simp [Nat.descFactorial_succ, Nat.factorial] at h
    rw [← h]
    ring
  have h2 : 2 * (k + 3).choose 2 = (k + 3) * (k + 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (k + 3) 2
    simp [Nat.descFactorial_succ, Nat.factorial] at h
    rw [← h]
    ring
  have hle : (k + 3).choose 3 ≤ (k + 3) * (k + 3).choose 2 := by nlinarith
  have h6q : (6 : ℚ) * ((k + 3).choose 3 : ℕ) = (k + 3) * (k + 2) * (k + 1) := by exact_mod_cast h6
  have h2q : (2 : ℚ) * ((k + 3).choose 2 : ℕ) = (k + 3) * (k + 2) := by exact_mod_cast h2
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_sub hle, maxGrowth_three]
    push_cast
    linear_combination (k + 3 : ℚ) / 2 * h2q - h6q / 6
  · rw [maxGrowth_three]
    push_cast
    ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS Chapter 7, Exercise 17, p. 353, first stage:** `r₁ = rank Δ₁ ≤ m`, the number of input
fields (`σ̄₁ = m`). -/
theorem growth_one_le (g : Fin m → E → E) (q : E) : growth g 1 q ≤ m := by
  rw [growth, filtrationAt_one, spanAt_range]
  calc Module.finrank ℝ (Submodule.span ℝ (Set.range fun j => g j q)) ≤ Fintype.card (Fin m) :=
        finrank_range_le_card _
    _ = m := Fintype.card_fin m

/-- **MLS Chapter 7, Exercise 17, p. 353, second stage: `σ₂ = r₂ − r₁ ≤ m(m − 1)/2 = σ̄₂`** for `m`
input fields on a finite-dimensional space, at every point: `Δ₂` adds at most the brackets
`[gⱼ, gₖ]`, `j < k`, by skew-symmetry. -/
theorem growth_two_le [FiniteDimensional ℝ E] (g : Fin m → E → E) (q : E) :
    growth g 2 q ≤ growth g 1 q + m.choose 2 := by
  classical
  set P : Finset (Fin m × Fin m) := (Finset.univ ×ˢ Finset.univ).filter fun x => x.1 < x.2
  set W := Submodule.span ℝ ((fun x : Fin m × Fin m => lieBracket ℝ (g x.1) (g x.2) q) '' P)
  have hle : filtrationAt g 2 q ≤ filtrationAt g 1 q ⊔ W := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    rcases hf with ⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩
    · exact Submodule.mem_sup_left (mem_spanAt (by rw [filtrationFields_one]; exact ⟨j, rfl⟩) q)
    · rw [filtrationFields_one] at hw
      obtain ⟨k, rfl⟩ := hw
      refine Submodule.mem_sup_right ?_
      rcases lt_trichotomy j k with hjk | rfl | hkj
      · exact Submodule.subset_span ⟨(j, k), by simp [P, hjk], rfl⟩
      · show lieBracket ℝ (g j) (g j) q ∈ W
        rw [lieBracket_self]
        exact W.zero_mem
      · show lieBracket ℝ (g j) (g k) q ∈ W
        rw [lieBracket_swap]
        exact W.neg_mem (Submodule.subset_span ⟨(k, j), by simp [P, hkj], rfl⟩)
  have hW : Module.finrank ℝ W ≤ m.choose 2 := by
    calc Module.finrank ℝ W ≤
          (P.image fun x : Fin m × Fin m => lieBracket ℝ (g x.1) (g x.2) q).card := by
          rw [show W = Submodule.span ℝ
            ↑(P.image fun x : Fin m × Fin m => lieBracket ℝ (g x.1) (g x.2) q) by simp [W]]
          exact finrank_span_finset_le_card _
      _ ≤ P.card := Finset.card_image_le
      _ = m.choose 2 := by
          rw [Finset.card_product_filter_lt, Finset.card_univ, Fintype.card_fin]
  calc growth g 2 q ≤ Module.finrank ℝ ↥(filtrationAt g 1 q ⊔ W) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ (filtrationAt g 1 q) + Module.finrank ℝ W :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ growth g 1 q + m.choose 2 := by
        rw [growth]
        omega

/-- **MLS Chapter 7, Exercise 17, p. 353, the second stage in the printed form:**
`σ₂ ≤ σ̄₂ = (σ̄₁² − σ̄₁)/2` with `σ̄₁ = m`. -/
theorem relativeGrowth_two_le_maxGrowth [FiniteDimensional ℝ E] (g : Fin m → E → E) (q : E) :
    ((growth g 2 q : ℚ) - growth g 1 q) ≤ maxGrowth m 2 := by
  have h := growth_two_le g q
  rw [maxGrowth_two]
  have hc : ((m.choose 2 : ℕ) : ℚ) = ((m : ℚ) ^ 2 - m) / 2 := by
    rw [Nat.cast_choose_two]
    ring
  have h' : (growth g 2 q : ℚ) ≤ growth g 1 q + (m.choose 2 : ℕ) := by exact_mod_cast h
  linarith

end Nonholonomic
end RoboLean
