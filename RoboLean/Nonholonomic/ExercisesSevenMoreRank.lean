import RoboLean.Nonholonomic.Controllability
import RoboLean.Nonholonomic.LocalFramesFiltration
import RoboLean.Nonholonomic.FrobeniusFrame
import RoboLean.Nonholonomic.Integrability2
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Chapter 7, Exercise 1: the rank condition is necessary (MLS p. 349)

MLS Chapter 7, Exercise 1, printed p. 349: "Show that the controllability rank condition is also a
necessary condition for local controllability under the usual smoothness and regularity
assumptions."

**The hypotheses, which the book does not state.** "The usual smoothness and regularity
assumptions" are read as: the state space is a finite-dimensional real space, the input fields are
smooth (`C^∞`), and the filtration `Δ₁ ⊂ Δ₂ ⊂ ⋯` is regular in a neighbourhood `U` of the point
(`IsRegularFiltrationOn`, the regularity of p. 340 under which the degree of nonholonomy is
defined). Without regularity the necessity fails for smooth fields (for instance `g₁ = ∂/∂x`,
`g₂ = e^{−1/x²} ∂/∂y` on `ℝ²` near `x = 0`), so a hypothesis of this kind is needed.

**What is formalized.** Under these hypotheses, small-time local controllability at `q₀` (p. 329,
for any input set) implies the rank condition in its filtration form, `Δᵢ(q₀) = ℝⁿ` for some `i`
(p. 341). The proof: if the filtration never fills the space, its rank stops growing at some
stage `i` with `Δᵢ(q₀) ≠ ℝⁿ`; by Exercise 11 (the library's `isInvolutiveOn_filtrationAt_of_growth`)
`Δᵢ` is involutive and regular near `q₀`, so by Frobenius' theorem (the library's `C¹` form) it is
the kernel of the derivative of a map `h` with onto derivative; every trajectory staying near `q₀`
keeps `h` constant, since its velocity lies in `Δ₁ ⊂ Δᵢ`; so the reachable set lies in a level set
of `h`, which is not a neighbourhood of `q₀`.

**Conventions.** The library's `IsLocallyControllableAt` (reachable sets with piecewise constant
inputs, trajectories of `IsTrajectory`), `filtrationAt` and `growth` (p. 340).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS p. 340: the rank of the filtration stops growing at some stage** (it is nondecreasing and
bounded by `n`) (supporting lemma for MLS Exercise 1, p. 349). -/
theorem exists_growth_succ_eq [FiniteDimensional ℝ E] (g : Fin m → E → E) (q : E) :
    ∃ i, growth g (i + 1) q = growth g i q := by
  by_contra h
  push Not at h
  have hlt : ∀ i, growth g i q < growth g (i + 1) q := fun i =>
    lt_of_le_of_ne (growth_mono g (Nat.le_succ i) q) (h i).symm
  have hge : ∀ i, i ≤ growth g i q := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hlt i))
  have := hge (Module.finrank ℝ E + 1)
  have := growth_le_finrank g (Module.finrank ℝ E + 1) q
  omega

/-- **MLS Chapter 7, Exercise 1, p. 349: the rank condition is necessary for local
controllability,** under the hypotheses the book leaves unstated (finite dimension, smooth input
fields, a filtration regular near `q₀`): if the system is small-time locally controllable at `q₀`
for some input set, then `Δᵢ(q₀)` is the whole space for some `i`. -/
theorem exists_filtrationAt_eq_top_of_isLocallyControllableAt [FiniteDimensional ℝ E]
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {q₀ : E}
    (hq₀ : q₀ ∈ U) (hreg : IsRegularFiltrationOn g U q₀) {Uc : Set (Fin m → ℝ)}
    (hlc : IsLocallyControllableAt g Uc q₀) : ∃ i, filtrationAt g i q₀ = ⊤ := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := exists_growth_succ_eq g q₀
  have hsmooth : ∀ {n : ℕ} {f : E → E}, f ∈ filtrationFields g n → ContDiff ℝ ∞ f :=
    fun hf => contDiff_of_mem_filtrationFields hg hf
  have hinv := isInvolutiveOn_filtrationAt_of_growth hg hU hreg hi
  have hregD : IsRegularOn (filtrationAt g i) U := ⟨growth g i q₀, fun y hy => hreg i y hy⟩
  obtain ⟨k, v, hvS, -, V, hV, -, hframe⟩ := exists_localFrame_of_set hU hregD hq₀
    fun f hf => (hsmooth hf).continuous.continuousAt
  have hspan : ∀ᶠ y in 𝓝 q₀, filtrationAt g i y = spanAt (Set.range v) y :=
    Filter.mem_of_superset hV fun y hy => by
      show spanAt (filtrationFields g i) y = _
      rw [spanAt_range]
      exact (hframe y hy).2
  obtain ⟨W, hW, hq₀W, p, h, hhc, hker⟩ := isIntegrableAtOfClass_one_of_isInvolutiveOn hU hregD
    hinv hq₀ (fun b => (hsmooth (hvS b)).of_le (by simp)) hspan
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exfalso
      apply hne i
      rw [(hker q₀ hq₀W).2]
      ext w
      simp [Subsingleton.elim ((fderiv ℝ h q₀) w) 0]
    · exact hp
  have hsub : ∀ y ∈ U, filtrationAt g 1 y ≤ filtrationAt g i y := by
    intro y hy
    have h1 := filtrationAt_add_eq_of_growth hg hU hreg hi 1 y hy
    rw [← h1]
    exact filtrationAt_mono g (by omega) y
  have hR := hlc (W ∩ U) (inter_mem (hW.mem_nhds hq₀W) (hU.mem_nhds hq₀)) 1 one_pos
  have hconst : ∀ y ∈ reachableSetLE g Uc (W ∩ U) q₀ 1, h y = h q₀ := by
    intro y hy
    simp only [reachableSetLE, mem_iUnion] at hy
    obtain ⟨τ, hτ, u, x, -, ⟨hxc, S, hS⟩, hx0, hxτ, hxV⟩ := hy
    have hcont : ContinuousOn (fun t => h (x t)) (Icc 0 τ) := fun t ht =>
      ((hhc (x t) (hxV t ht).1).continuousAt).comp_continuousWithinAt (hxc t ht)
    have hder : ∀ t ∈ Ioo 0 τ, t ∉ S → HasDerivAt (fun s => h (x s)) 0 t := by
      intro t ht htS
      have hT : t ∈ Icc 0 τ := Ioo_subset_Icc_self ht
      have hd := ((hhc (x t) (hxV t hT).1).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        t (hS t ht htS)
      convert hd using 1
      · rfl
      have hmem : driftFree g (x t) (u t) ∈ filtrationAt g i (x t) := by
        apply hsub (x t) (hxV t hT).2
        rw [filtrationAt_one, spanAt_range]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      rw [(hker (x t) (hxV t hT).1).2] at hmem
      exact (LinearMap.mem_ker.1 hmem).symm
    have hint := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => h (x s))
      (fun _ => (0 : Fin p → ℝ)) hτ.1.le S.countable_toSet hcont
      (fun s hs => hder s hs.1 hs.2) intervalIntegrable_const
    simp only [intervalIntegral.integral_zero] at hint
    rw [← hxτ, ← hx0]
    exact (sub_eq_zero.1 hint.symm)
  have hloc : h =ᶠ[𝓝 q₀] fun _ => h q₀ := Filter.mem_of_superset hR fun y hy => hconst y hy
  have hzero : fderiv ℝ h q₀ = 0 := by
    rw [hloc.fderiv_eq, fderiv_const_apply]
  obtain ⟨w, hw⟩ := (hker q₀ hq₀W).1 (Pi.single ⟨0, hp⟩ 1)
  rw [hzero, zero_apply] at hw
  have := congrFun hw ⟨0, hp⟩
  simp at this

end Nonholonomic
end RoboLean
