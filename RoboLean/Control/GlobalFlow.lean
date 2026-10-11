import RoboLean.Control.SolutionFlow

/-!
# Global forward existence for globally Lipschitz autonomous fields (MLS p. 179)

MLS assumes, for the system `ẋ = f(x, t)` of eq. (4.31), "the standard conditions for the
existence and uniqueness of solutions" (p. 179), and names as an instance that `f(x, t)` is
Lipschitz continuous in `x`, uniformly in `t`. The flow interface `HasFlow` of
`RoboLean.Control.SolutionFlow` takes forward existence as a hypothesis; for a globally Lipschitz
field, `HasFlow.of_lipschitzWith` already reduces it to that existence field. This module
discharges the existence field for a globally Lipschitz autonomous field `F` on a complete normed
space, with the system written `fun _ => F` (time first, ignored) and solutions taken from time
`0` in the sense of `IsSolution` (continuous on `[0, ∞)`, actual derivative `F(x(t))` at every
`t > 0`).

Route: Mathlib's Picard–Lindelöf theorem gives, from every initial state `y`, a solution on
`[0, 2h]`, where the step `h = 1 / (2 (K + 1))` depends only on the Lipschitz constant `K` (on the
closed ball of radius `‖F y‖ + 1` about `y` the field is bounded by `L = ‖F y‖ + K (‖F y‖ + 1)`,
and `L · 2h` does not exceed the radius). Restarting at time `h` from the state reached there,
the successive pieces overlap on intervals of length `h`, agree there by Mathlib's uniqueness
theorem `ODE_solution_unique`, and glue to one curve on `[0, ∞)`. The pinned Mathlib's ODE files
(`Mathlib/Analysis/ODE/`) do not extend local solutions to maximal or global ones; its one
uniform-time extension lemma, `exists_isMIntegralCurve_of_isMIntegralCurveOn` for integral curves
on manifolds, assumes a `C¹` vector field, which a Lipschitz field need not be. Hence the gluing
is done here.

Limits: global Lipschitz continuity is essential to the uniform step. For a field that is only
locally Lipschitz (for example a nonlinear spring, or the closed loop of a manipulator under a
nonlinear control law) nothing here applies; for such fields global existence can fail in general
(`ẋ = x²` escapes in finite time).
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Uniform local existence (the local step behind MLS p. 179's standing assumption): if `F` is
`K`-Lipschitz and `T (K + 1) ≤ 1`, then from every `y` a solution of `ẋ = F(x)` with `σ 0 = y`
exists on `[0, T]` (one-sided derivatives at the end points). From Mathlib's Picard–Lindelöf
theorem on the closed ball of radius `‖F y‖ + 1` about `y`. -/
private theorem exists_local {F : E → E} {K : NNReal} (hF : LipschitzWith K F) {T : ℝ}
    (hT : 0 ≤ T) (hTK : T * ((K : ℝ) + 1) ≤ 1) (y : E) :
    ∃ σ : ℝ → E, σ 0 = y ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt σ (F (σ t)) (Icc 0 T) t := by
  set a : NNReal := ‖F y‖₊ + 1 with ha
  set L : NNReal := ‖F y‖₊ + K * a with hL
  have hb : ∀ x ∈ Metric.closedBall y a, ‖F x‖ ≤ L := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    have h1 := hF.dist_le_mul x y
    rw [dist_eq_norm] at h1
    have h2 := norm_le_norm_add_norm_sub' (F x) (F y)
    have h3 : (K : ℝ) * dist x y ≤ K * a := mul_le_mul_of_nonneg_left hx K.2
    simp only [hL, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm]
    linarith
  have hm : (L : ℝ) * max (T - ((⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) : ℝ))
      (((⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) : ℝ) - 0) ≤ a - ((0 : NNReal) : ℝ) := by
    simp only [hL, ha, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one,
      NNReal.coe_zero, sub_zero, max_eq_left hT]
    nlinarith [mul_nonneg (sub_nonneg.2 hTK) (norm_nonneg (F y)), K.2]
  obtain ⟨σ, hσ0, hσ⟩ := (IsPicardLindelof.of_time_independent hb hF.lipschitzOnWith
    hm).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨σ, hσ0, hσ⟩

/-- **Global forward existence for a globally Lipschitz autonomous field** (the existence half of
MLS's standing assumption, p. 179, for `f(x, t) = F(x)` Lipschitz in `x`): if `F` is `K`-Lipschitz
on a complete normed space, then from every initial state `x₀` there is a curve `γ` with
`γ 0 = x₀` that solves `ẋ = F(x)` from time `0`. The system is `fun _ => F`; `IsSolution` asks
continuity on `[0, ∞)` and the actual derivative `F(γ t)` at every `t > 0`. -/
theorem exists_isSolution_of_lipschitzWith {F : E → E} {K : NNReal} (hF : LipschitzWith K F)
    (x₀ : E) : ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsSolution (fun _ => F) 0 γ := by
  set h : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hh
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hpos : 0 < h := by positivity
  have hTK : 2 * h * ((K : ℝ) + 1) ≤ 1 := by
    rw [hh]; field_simp; rfl
  choose σ hσ0 hσ using fun y => exists_local hF (by positivity : (0 : ℝ) ≤ 2 * h) hTK y
  have hcont : ∀ z, ContinuousOn (σ z) (Icc 0 (2 * h)) := fun z t ht =>
    (hσ z t ht).continuousWithinAt
  -- consecutive pieces agree on their overlap
  have hagree : ∀ y, ∀ s ∈ Icc 0 h, σ (σ y h) s = σ y (s + h) := by
    intro y
    refine ODE_solution_unique (v := fun _ => F) (fun _ => hF) ?_ ?_ ?_ ?_ ?_
    · exact (hcont _).mono (Icc_subset_Icc le_rfl (by linarith))
    · intro t ht
      exact ((hσ _ t ⟨ht.1, by linarith [ht.2]⟩).mono
        (Icc_subset_Icc ht.1 le_rfl)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith [ht.2]))
    · exact (hcont y).comp (continuous_id.add continuous_const).continuousOn
        (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    · intro t ht
      exact (((hσ y (t + h) ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))).comp_add_const t
        h).hasDerivWithinAt
    · simp [hσ0]
  -- the restart points `p (n + 1) = σ (p n) h` and the glued curve
  set p : ℕ → E := fun n => (fun z => σ z h)^[n] x₀
  have hp0 : p 0 = x₀ := rfl
  have hpsucc : ∀ n, p (n + 1) = σ (p n) h := fun n => Function.iterate_succ_apply' _ _ _
  set γ : ℝ → E := fun t => σ (p ⌊t / h⌋₊) (t - ⌊t / h⌋₊ * h) with hγ
  -- on `[n h, (n + 2) h)` the glued curve is the `n`-th piece
  have hkey : ∀ n : ℕ, ∀ t ∈ Ico (n * h) ((n + 2) * h), γ t = σ (p n) (t - n * h) := by
    intro n t ht
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
    set m := ⌊t / h⌋₊ with hm
    have hm1 : (m : ℝ) * h ≤ t := (le_div_iff₀ hpos).1 (Nat.floor_le (div_nonneg ht0 hpos.le))
    have hm2 : t < ((m : ℝ) + 1) * h := (div_lt_iff₀ hpos).1 (Nat.lt_floor_add_one _)
    have hnm : (n : ℝ) < m + 1 := lt_of_mul_lt_mul_right (ht.1.trans_lt hm2) hpos.le
    have hmn : (m : ℝ) < n + 2 := lt_of_mul_lt_mul_right (hm1.trans_lt ht.2) hpos.le
    have hnm' : n < m + 1 := by exact_mod_cast hnm
    have hmn' : m < n + 2 := by exact_mod_cast hmn
    rcases (by omega : m = n ∨ m = n + 1) with h1 | h1
    · simp only [hγ, ← hm, h1]
    · simp only [hγ, ← hm, h1, hpsucc]
      rw [hagree]
      · congr 1; push_cast; ring
      · rw [h1] at hm1
        push_cast at hm1 ⊢
        refine ⟨by linarith, by linarith [ht.2]⟩
  have hex : ∀ t, 0 < t → ∃ n : ℕ, n * h < t ∧ t < (n + 2) * h := by
    intro t ht
    refine ⟨⌊t / h - 1 / 2⌋₊, ?_, ?_⟩
    · rcases le_or_gt 0 (t / h - 1 / 2) with h1 | h1
      · have := Nat.floor_le h1
        have : (⌊t / h - 1 / 2⌋₊ : ℝ) + 1 / 2 ≤ t / h := by linarith
        rw [le_div_iff₀ hpos] at this
        nlinarith
      · rw [Nat.floor_of_nonpos h1.le]; simpa using ht
    · have := Nat.lt_floor_add_one (t / h - 1 / 2)
      have : t / h < (⌊t / h - 1 / 2⌋₊ : ℝ) + 2 := by linarith
      exact (div_lt_iff₀ hpos).1 this
  have hderiv : ∀ t, 0 < t → HasDerivAt γ (F (γ t)) t := by
    intro t ht
    obtain ⟨n, h1, h2⟩ := hex t ht
    have hd : HasDerivAt (fun s => σ (p n) (s - n * h)) (F (σ (p n) (t - n * h))) t := by
      apply HasDerivAt.comp_sub_const
      exact (hσ (p n) (t - n * h) ⟨by linarith, by linarith⟩).hasDerivAt
        (Icc_mem_nhds (by linarith) (by linarith))
    have heq : γ =ᶠ[𝓝 t] fun s => σ (p n) (s - n * h) := by
      filter_upwards [Ioo_mem_nhds h1 h2] with s hs using hkey n s ⟨hs.1.le, hs.2⟩
    rw [hkey n t ⟨h1.le, h2⟩]
    exact hd.congr_of_eventuallyEq heq
  refine ⟨γ, ?_, ?_, fun t ht => hderiv t ht⟩
  · simp [hγ, hp0, hσ0]
  · intro t ht
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0 | h0
    · subst h0
      have hc : ContinuousWithinAt (σ x₀) (Ici 0) 0 :=
        (hcont x₀ 0 ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))
      refine hc.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Icc_mem_nhdsGE hpos] with s hs
        simpa [hp0] using hkey 0 s ⟨by simpa using hs.1, by simp; linarith [hs.2]⟩
      · simpa [hp0] using hkey 0 0 ⟨by simp, by simp; linarith⟩
    · exact (hderiv t h0).continuousAt.continuousWithinAt

/-- **A globally Lipschitz autonomous field has a solution flow** (MLS's standing existence and
uniqueness assumption, p. 179, as used for eq. (4.46), p. 188): if `F` is `K`-Lipschitz on a
complete normed space, there is `φ` with `HasFlow F φ`. Existence is
`exists_isSolution_of_lipschitzWith`; uniqueness and continuous dependence come from
`HasFlow.of_lipschitzWith`. The system is `fun _ => F`, solutions from time `0`. -/
theorem exists_hasFlow_of_lipschitzWith {F : E → E} {K : NNReal} (hF : LipschitzWith K F) :
    ∃ φ : ℝ → E → E, HasFlow F φ := by
  choose γ hγ0 hγ using exists_isSolution_of_lipschitzWith hF
  exact ⟨fun t x => γ x t, HasFlow.of_lipschitzWith hF hγ0 hγ⟩

end Stability
end RoboLean
