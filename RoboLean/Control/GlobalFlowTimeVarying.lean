import RoboLean.Control.GlobalFlow

/-!
# Global solutions of time-varying globally Lipschitz fields (MLS p. 179)

MLS assumes, for `ẋ = f(x, t)` (eq. (4.31), p. 179), "the standard conditions for the existence
and uniqueness of solutions", for instance that `f(x, t)` is Lipschitz continuous in `x`, uniformly
in `t`. This module proves global existence of solutions for a time-varying field `f(t, x)` (time
first) on a real Banach space that is `K`-Lipschitz in `x` for every `t` and continuous in `t` for
every `x`: from every initial time `s` and state `x₀` there is a solution forward in time
(`exists_forward_solution_of_lipschitzWith`) and a solution on the whole real line
(`exists_global_solution_of_lipschitzWith`).

Route: Mathlib's Picard–Lindelöf theorem on intervals of a uniform length `T` depending only on
`K`, on a closed ball about the initial state whose radius bounds the field over the interval by
compactness, glued at overlaps by Mathlib's uniqueness theorem `ODE_solution_unique`, as in
`exists_isSolution_of_lipschitzWith` (autonomous fields) and `exists_forall_hasDerivAt_linear`
(linear time-varying fields). The solution backward in time is the forward solution of the
reversed field `(t, x) ↦ −f(−t, x)`.

**Conventions.** Time first, as in `RoboLean.Stability`; continuity in `t` for every `x` and the
Lipschitz bound hold for all real `t` (a field given for `t ≥ 0` is extended by `f(0, x)` to
negative times by the consumers of this module). MLS allows piecewise continuity in `t`; the
continuity asked here gives an actual derivative at every time.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Uniform local existence for a time-varying globally Lipschitz field (the local step behind
`exists_forward_solution_of_lipschitzWith`; MLS's standing existence assumption, p. 179): if
`f(t, ·)` is `K`-Lipschitz for every `t`, `t ↦ f(t, x)` is continuous for every `x`, and
`T (2 (K + 1)) ≤ 1`, then from every initial time `τ` and state `y` a solution of `u' = f(t, u)`
with `σ τ = y` exists on `[τ, τ + T]` (one-sided derivatives at the end points). From Mathlib's
Picard–Lindelöf theorem on the closed ball of radius `2 C T + 1` about `y`, where `C` bounds
`‖f(t, y)‖` on `[τ, τ + T]`. Time first. -/
private theorem exists_local_of_lipschitzWith {f : ℝ → E → E} {K : NNReal}
    (hf : ∀ t, LipschitzWith K (f t)) (hc : ∀ x, Continuous fun t => f t x) {T : ℝ} (hT : 0 ≤ T)
    (hTK : T * (2 * ((K : ℝ) + 1)) ≤ 1) (τ : ℝ) (y : E) :
    ∃ σ : ℝ → E, σ τ = y ∧
      ∀ t ∈ Icc τ (τ + T), HasDerivWithinAt σ (f t (σ t)) (Icc τ (τ + T)) t := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := τ) (b := τ + T)).exists_bound_of_continuousOn
    (hc y).continuousOn
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ t ∈ Icc τ (τ + T), ‖f t y‖ ≤ C := fun t ht => (hC₀ t ht).trans (le_max_left _ _)
  have ha0 : 0 ≤ 2 * C * T + 1 := by positivity
  set a : NNReal := ⟨2 * C * T + 1, ha0⟩ with ha
  set L : NNReal := ⟨C + K * (2 * C * T + 1), by positivity⟩ with hL
  have hτ : τ ∈ Icc τ (τ + T) := ⟨le_rfl, by linarith⟩
  have hP : IsPicardLindelof f (⟨τ, hτ⟩ : Icc τ (τ + T)) y a 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (hf t).lipschitzOnWith
    · intro x _
      exact (hc x).continuousOn
    · intro t ht x hx
      rw [Metric.mem_closedBall] at hx
      have h1 := (hf t).dist_le_mul x y
      rw [dist_eq_norm] at h1
      have h2 : ‖f t x‖ ≤ ‖f t y‖ + ‖f t x - f t y‖ := norm_le_norm_add_norm_sub' _ _
      have h3 : (K : ℝ) * dist x y ≤ K * (2 * C * T + 1) :=
        mul_le_mul_of_nonneg_left hx K.2
      have h4 := hC t ht
      show ‖f t x‖ ≤ C + K * (2 * C * T + 1)
      linarith
    · show (C + K * (2 * C * T + 1)) * max (τ + T - τ) (τ - τ) ≤ 2 * C * T + 1 - 0
      rw [add_sub_cancel_left, sub_self, max_eq_left hT, sub_zero]
      nlinarith [mul_nonneg (sub_nonneg.2 hTK) ha0, mul_nonneg hT ha0, mul_nonneg hC0 hT]
  obtain ⟨σ, hσ0, hσ⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨σ, hσ0, hσ⟩

/-- **Global forward existence for a time-varying globally Lipschitz field** (the existence half of
MLS's standing assumption, p. 179, for `f(x, t)` Lipschitz in `x` uniformly in `t`): if `f(t, ·)` is
`K`-Lipschitz for every `t` and `t ↦ f(t, x)` is continuous for every `x`, then from every initial
time `s` and state `x₀` there is a curve `u` with `u s = x₀`, the right derivative `f(s, x₀)` at
`s`, and the derivative `f(t, u t)` at every `t > s`. Time first. -/
theorem exists_forward_solution_of_lipschitzWith {f : ℝ → E → E} {K : NNReal}
    (hf : ∀ t, LipschitzWith K (f t)) (hc : ∀ x, Continuous fun t => f t x) (s : ℝ) (x₀ : E) :
    ∃ u : ℝ → E, u s = x₀ ∧ HasDerivWithinAt u (f s x₀) (Ici s) s ∧
      ∀ t, s < t → HasDerivAt u (f t (u t)) t := by
  set h : ℝ := 1 / (4 * ((K : ℝ) + 1)) with hh
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hpos : 0 < h := by positivity
  have hTM : 2 * h * (2 * ((K : ℝ) + 1)) ≤ 1 := by
    rw [hh]; field_simp; norm_num
  choose σ hσ0 hσ using fun τ y =>
    exists_local_of_lipschitzWith hf hc (by positivity : (0 : ℝ) ≤ 2 * h) hTM τ y
  have hcont : ∀ τ z, ContinuousOn (σ τ z) (Icc τ (τ + 2 * h)) := fun τ z t ht =>
    (hσ τ z t ht).continuousWithinAt
  -- the restart points and the glued curve
  let p : ℕ → E := fun n => Nat.rec x₀ (fun k pk => σ (s + k * h) pk (s + (k + 1) * h)) n
  have hp0 : p 0 = x₀ := rfl
  have hpsucc : ∀ k : ℕ, p (k + 1) = σ (s + k * h) (p k) (s + (k + 1) * h) := fun k => rfl
  -- consecutive pieces agree on their overlap
  have hagree : ∀ k : ℕ, ∀ t ∈ Icc (s + (k + 1) * h) (s + (k + 2) * h),
      σ (s + (k + 1) * h) (p (k + 1)) t = σ (s + k * h) (p k) t := by
    intro k
    refine ODE_solution_unique (v := f) hf ?_ ?_ ?_ ?_ ?_
    · exact (hcont _ _).mono (Icc_subset_Icc le_rfl (by linarith))
    · intro t ht
      exact ((hσ _ _ t ⟨ht.1, by linarith [ht.2]⟩).mono
        (Icc_subset_Icc ht.1 le_rfl)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE (by linarith [ht.2]))
    · exact (hcont _ _).mono (Icc_subset_Icc (by nlinarith) (by linarith))
    · intro t ht
      exact ((hσ _ _ t ⟨by nlinarith [ht.1], by linarith [ht.2]⟩).mono
        (Icc_subset_Icc (by nlinarith [ht.1]) le_rfl)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE (by linarith [ht.2]))
    · rw [hσ0, hpsucc]
  set u : ℝ → E := fun t => σ (s + ⌊(t - s) / h⌋₊ * h) (p ⌊(t - s) / h⌋₊) t with hu
  -- on `[s + n h, s + (n + 2) h)` the glued curve is the `n`-th piece
  have hkey : ∀ n : ℕ, ∀ t ∈ Ico (s + n * h) (s + (n + 2) * h),
      u t = σ (s + n * h) (p n) t := by
    intro n t ht
    have ht0 : 0 ≤ t - s := by nlinarith [ht.1, (by positivity : (0 : ℝ) ≤ n * h)]
    set m := ⌊(t - s) / h⌋₊ with hm
    have hm1 : (m : ℝ) * h ≤ t - s :=
      (le_div_iff₀ hpos).1 (Nat.floor_le (div_nonneg ht0 hpos.le))
    have hm2 : t - s < ((m : ℝ) + 1) * h := (div_lt_iff₀ hpos).1 (Nat.lt_floor_add_one _)
    have hnm : (n : ℝ) < m + 1 :=
      lt_of_mul_lt_mul_right (by linarith [ht.1] : (n : ℝ) * h < (m + 1) * h) hpos.le
    have hmn : (m : ℝ) < n + 2 :=
      lt_of_mul_lt_mul_right (by linarith [ht.2] : (m : ℝ) * h < (n + 2) * h) hpos.le
    have hnm' : n < m + 1 := by exact_mod_cast hnm
    have hmn' : m < n + 2 := by exact_mod_cast hmn
    rcases (by omega : m = n ∨ m = n + 1) with h1 | h1
    · simp only [hu, ← hm, h1]
    · simp only [hu, ← hm, h1]
      push_cast
      apply hagree
      rw [h1] at hm1
      push_cast at hm1
      exact ⟨by linarith, by linarith [ht.2]⟩
  have hex : ∀ t, s < t → ∃ n : ℕ, s + n * h < t ∧ t < s + (n + 2) * h := by
    intro t ht
    refine ⟨⌊(t - s) / h - 1 / 2⌋₊, ?_, ?_⟩
    · rcases le_or_gt 0 ((t - s) / h - 1 / 2) with h1 | h1
      · have := Nat.floor_le h1
        have : (⌊(t - s) / h - 1 / 2⌋₊ : ℝ) + 1 / 2 ≤ (t - s) / h := by linarith
        rw [le_div_iff₀ hpos] at this
        nlinarith
      · rw [Nat.floor_of_nonpos h1.le]; simpa using ht
    · have := Nat.lt_floor_add_one ((t - s) / h - 1 / 2)
      have : (t - s) / h < (⌊(t - s) / h - 1 / 2⌋₊ : ℝ) + 2 := by linarith
      have := (div_lt_iff₀ hpos).1 this
      linarith
  have hu0 : ∀ t ∈ Ico s (s + 2 * h), u t = σ s x₀ t := by
    intro t ht
    simpa [hp0] using hkey 0 t ⟨by simpa using ht.1, by simpa using ht.2⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu0 s ⟨le_rfl, by linarith⟩, hσ0]
  · have hd := (hσ s x₀ s ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE (by linarith : s < s + 2 * h))
    rw [hσ0] at hd
    refine hd.congr_of_eventuallyEq ?_ (hu0 s ⟨le_rfl, by linarith⟩)
    filter_upwards [Ico_mem_nhdsGE (by linarith : s < s + 2 * h)] with t ht using hu0 t ht
  · intro t ht
    obtain ⟨n, h1, h2⟩ := hex t ht
    have hd := (hσ (s + n * h) (p n) t ⟨h1.le, by linarith⟩).hasDerivAt
      (Icc_mem_nhds h1 (by linarith))
    have heq : u =ᶠ[𝓝 t] σ (s + n * h) (p n) := by
      filter_upwards [Ioo_mem_nhds h1 h2] with r hr using hkey n r ⟨hr.1.le, hr.2⟩
    rw [hkey n t ⟨h1.le, h2⟩]
    exact hd.congr_of_eventuallyEq heq

/-- **Global existence on the whole time axis for a time-varying globally Lipschitz field** (MLS's
standing assumption, p. 179): under the hypotheses of `exists_forward_solution_of_lipschitzWith`,
from every initial time `s` and state `x₀` there is a curve `u` with `u s = x₀` and the derivative
`f(t, u t)` at every real `t`. The part before `s` is the forward solution of the reversed field
`(t, x) ↦ −f(−t, x)`. Time first. -/
theorem exists_global_solution_of_lipschitzWith {f : ℝ → E → E} {K : NNReal}
    (hf : ∀ t, LipschitzWith K (f t)) (hc : ∀ x, Continuous fun t => f t x) (s : ℝ) (x₀ : E) :
    ∃ u : ℝ → E, u s = x₀ ∧ ∀ t, HasDerivAt u (f t (u t)) t := by
  obtain ⟨w, hw0, hwd0, hwd⟩ := exists_forward_solution_of_lipschitzWith hf hc s x₀
  have hg : ∀ t, LipschitzWith K (fun x => -f (-t) x) := fun t => (hf (-t)).neg
  have hgc : ∀ x, Continuous fun t => -f (-t) x := fun x => ((hc x).comp continuous_neg).neg
  obtain ⟨v, hv0, hvd0, hvd⟩ :=
    exists_forward_solution_of_lipschitzWith (f := fun t x => -f (-t) x) hg hgc (-s) x₀
  set u : ℝ → E := fun t => if s ≤ t then w t else v (-t) with hu
  have hus : u s = x₀ := by simp [hu, hw0]
  refine ⟨u, hus, fun t => ?_⟩
  rcases lt_trichotomy t s with hts | rfl | hts
  · have hd := HasDerivAt.scomp t (hvd (-t) (by linarith)) (hasDerivAt_neg t)
    have heq : u =ᶠ[𝓝 t] v ∘ Neg.neg := by
      filter_upwards [Iio_mem_nhds hts] with r hr
      simp [hu, not_le.2 (mem_Iio.1 hr)]
    have hut : u t = v (-t) := by simp [hu, not_le.2 hts]
    rw [hut]
    convert hd.congr_of_eventuallyEq heq using 1
    simp
  · have h1 : HasDerivWithinAt u (f t x₀) (Ici t) t :=
      hwd0.congr (fun r hr => by simp [hu, mem_Ici.1 hr]) (by rw [hus, hw0])
    have h2 : HasDerivWithinAt u (f t x₀) (Iic t) t := by
      have hd := HasDerivWithinAt.scomp t hvd0 (hasDerivWithinAt_neg t (Iic t))
        (fun r hr => neg_le_neg (mem_Iic.1 hr))
      have hd' : HasDerivWithinAt (v ∘ Neg.neg) (f t x₀) (Iic t) t := by
        convert hd using 1
        simp
      refine hd'.congr (fun r hr => ?_) (by simp [hus, hv0])
      rcases eq_or_lt_of_le (mem_Iic.1 hr) with rfl | hrt
      · simp [hus, hv0]
      · simp [hu, not_le.2 hrt]
    rw [hus]
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have heq : u =ᶠ[𝓝 t] w := by
      filter_upwards [Ioi_mem_nhds hts] with r hr
      simp [hu, (mem_Ioi.1 hr).le]
    have hut : u t = w t := by simp [hu, hts.le]
    rw [hut]
    exact (hwd t hts).congr_of_eventuallyEq heq

end Stability
end RoboLean
