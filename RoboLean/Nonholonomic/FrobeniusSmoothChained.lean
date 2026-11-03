import RoboLean.Nonholonomic.ChainedConversionProof
import RoboLean.Nonholonomic.FrobeniusSmooth

/-!
# The chained-form conversion with a smooth second function (MLS p. 370)

**What MLS prints.** For `q̇ = g₁(q)u₁ + g₂(q)u₂` on `ℝⁿ` under the conditions of p. 370 (the
distributions `Δ₀, Δ₁, Δ₂` of constant rank and involutive, `h₁` with `dh₁ · Δ₁ = 0` and
`dh₁ · g₁ = 1`), "the existence of a function `h₂` independent of `h₁` such that `dh₂ · Δ₂ = 0` is
guaranteed by Frobenius' theorem", and the coordinates `z₁ = h₁`, `z_k = L^{n−k}_{g₁}h₂` with
`v = β(q)u` yield the one-chain form (8.7) (p. 370).

**Proved here.** On a finite-dimensional space of dimension `n` (MLS: `q ∈ ℝⁿ`), under the printed
conditions on an open set `U`, every point of `U` has an open neighbourhood `V ⊂ U` and a smooth
`h₂ : E → ℝ` with `dh₂ · Δ₂ = 0` on `V` and `dh₁, dh₂` independent on `V`
(`exists_chainedConversion_smooth`): this is the conclusion of the named statement
`ChainedConversionStatement` with the dimension hypothesis added
(`chainedConversionStatement_of_finrank`). With it the conversion yields (8.7)
(`hasDerivAt_chainedCoordinates_of_finrank`).

**Route.** As in `Nonholonomic/ChainedConversionProof`, with Frobenius' theorem for smooth
defining functions (`isIntegrableAt_of_spanAt`, `Nonholonomic/FrobeniusSmooth`) in place of the
`C¹` form; the component of the defining map independent of `dh₁` is smooth near the point and is
multiplied by a smooth bump equal to `1` near it, which makes it smooth on the whole space.

**Hypotheses against MLS.** `Module.finrank ℝ E = n`, printed only as `q ∈ ℝⁿ`; the named
statement does not carry it, and without it the statement is false
(`Examples/ChainedConversionCounterexample`, `n = 4` on `ℝ³`).

**Conventions.** Those of `Nonholonomic/ChainedConversion` and `Nonholonomic/Integrability`.
-/

noncomputable section

open Set Filter Topology VectorField Metric
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The existence step of MLS p. 370 with a defining function smooth at every point of `V`
(supporting lemma for `exists_chainedConversion_smooth`). -/
private theorem exists_chainedConversion_contDiffAt [FiniteDimensional ℝ E] {g₁ g₂ : E → E} {n : ℕ}
    {h₁ : E → ℝ} {U : Set E} (hdim : Module.finrank ℝ E = n) (hg₁ : ContDiff ℝ ∞ g₁)
    (hg₂ : ContDiff ℝ ∞ g₂) (hh₁ : ContDiff ℝ ∞ h₁) (hU : IsOpen U)
    (hc : ChainedConversionConditions g₁ g₂ n h₁ U) {q₀ : E} (hq₀ : q₀ ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, (∀ q ∈ V, ContDiffAt ℝ ∞ h₂ q) ∧
      (∀ q ∈ V, ∀ f ∈ conversionDelta2 g₁ g₂ n, lieDerivative f h₂ q = 0) ∧
      ∀ q ∈ V, LinearIndependent ℝ ![fderiv ℝ h₁ q, fderiv ℝ h₂ q] := by
  set F : Fin (n - 2) → E → E := fun k => adIter g₁ k g₂ with hF
  have hFc : ∀ k, ContDiff ℝ ∞ (F k) := fun k => contDiff_adIter_of_contDiff hg₁ hg₂ k
  obtain ⟨V₀, hV₀, hq₀V₀, p, H, hHc, hH⟩ :=
    isIntegrableAt_of_spanAt hU hFc hc.regular2 hc.involutive2 hq₀
  obtain ⟨hsurj₀, hker₀⟩ := hH q₀ hq₀V₀
  -- counting dimensions at `q₀`
  have hn2 : 2 ≤ n := by
    have h := (hc.linearIndependent q₀ hq₀).fintype_card_le_finrank
    simpa [hdim] using h
  have hrank : Module.finrank ℝ (spanAt (Set.range F) q₀) ≤ n - 2 := by
    have h : spanAt (Set.range F) q₀ = Submodule.span ℝ (Set.range fun k => F k q₀) := by
      rw [spanAt, ← Set.range_comp]
      rfl
    rw [h]
    exact (finrank_range_le_card _).trans (by simp)
  have hp : 2 ≤ p := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ H q₀ : E →ₗ[ℝ] Fin p → ℝ)
    rw [LinearMap.range_eq_top.2 hsurj₀, finrank_top, Module.finrank_fin_fun, ← hker₀, hdim] at hrn
    omega
  -- a component of `H` independent of `h₁` at `q₀`
  set i₀ : Fin p := ⟨0, by omega⟩
  set i₁ : Fin p := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  obtain ⟨v₀, hv₀⟩ := hsurj₀ (Pi.single i₀ 1)
  obtain ⟨v₁, hv₁⟩ := hsurj₀ (Pi.single i₁ 1)
  set ℓ : Fin p → (E →L[ℝ] ℝ) := fun i => (ContinuousLinearMap.proj i).comp (fderiv ℝ H q₀)
  have hℓ : ∀ i v, ℓ i v = fderiv ℝ H q₀ v i := fun i v => rfl
  have hdh₁ : fderiv ℝ h₁ q₀ ≠ 0 := by
    intro h0
    have h := hc.normalized q₀ hq₀
    rw [lieDerivative_apply, h0] at h
    simp at h
  have hex : ∃ i, LinearIndependent ℝ ![fderiv ℝ h₁ q₀, ℓ i] := by
    by_contra hno
    have h0 := not_exists.1 hno i₀
    have h1 := not_exists.1 hno i₁
    rw [linearIndependent_fin2] at h0 h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, not_and, not_forall, not_not] at h0 h1
    obtain ⟨a₀, ha₀⟩ := h0 (fun h => by
      have := congrArg (fun T : E →L[ℝ] ℝ => T v₀) h
      simp [hℓ, hv₀] at this)
    obtain ⟨a₁, ha₁⟩ := h1 (fun h => by
      have := congrArg (fun T : E →L[ℝ] ℝ => T v₁) h
      simp [hℓ, hv₁] at this)
    have e := congrArg (fun T : E →L[ℝ] ℝ => T v₀) (ha₀.trans ha₁.symm)
    simp only [smul_apply, hℓ, hv₀, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hi.symm, mul_zero, mul_one] at e
    rw [e, zero_smul] at ha₀
    exact hdh₁ ha₀.symm
  obtain ⟨i, hli⟩ := hex
  set h₂ : E → ℝ := fun q => H q i with hh₂
  have hh₂c : ∀ q ∈ V₀, ContDiffAt ℝ ∞ h₂ q := fun q hq =>
    (contDiff_apply ℝ ℝ i).contDiffAt.comp q (hHc q hq)
  have hfd : ∀ q ∈ V₀, fderiv ℝ h₂ q = (ContinuousLinearMap.proj i).comp (fderiv ℝ H q) := by
    intro q hq
    have hd := ((hHc q hq).differentiableAt (by simp)).hasFDerivAt
    exact ((hasFDerivAt_apply i (H q)).comp q hd).fderiv
  -- independence near `q₀`
  have hcont : ContinuousAt (fun q => ![fderiv ℝ h₁ q, fderiv ℝ h₂ q]) q₀ := by
    refine continuousAt_pi.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simpa using (hh₁.continuous_fderiv (by simp)).continuousAt
    · simpa using ((hh₂c q₀ hq₀V₀).fderiv_right (m := 0) (by simp)).continuousAt
  have hli₀ : ![fderiv ℝ h₁ q₀, fderiv ℝ h₂ q₀] ∈ {f : Fin 2 → (E →L[ℝ] ℝ) | LinearIndependent ℝ f} := by
    rw [hfd q₀ hq₀V₀]
    exact hli
  have hev := hcont.preimage_mem_nhds
    ((isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := E →L[ℝ] ℝ) (ι := Fin 2)).mem_nhds hli₀)
  obtain ⟨V, hVsub, hVo, hq₀V⟩ := _root_.mem_nhds_iff.1
    (inter_mem hev (inter_mem (hV₀.mem_nhds hq₀V₀) (hU.mem_nhds hq₀)))
  refine ⟨V, hVo, hq₀V, fun q hq => (hVsub hq).2.2, h₂, fun q hq => hh₂c q (hVsub hq).2.1,
    fun q hq f hf => ?_, fun q hq => (hVsub hq).1⟩
  have hqV₀ := (hVsub hq).2.1
  obtain ⟨-, hker⟩ := hH q hqV₀
  have hfq : f q ∈ spanAt (Set.range F) q := mem_spanAt hf q
  rw [hker] at hfq
  rw [lieDerivative_apply, hfd q hqV₀]
  have h0 : fderiv ℝ H q (f q) = 0 := LinearMap.mem_ker.1 hfq
  simp [h0]

/-- **MLS p. 370, the existence of `h₂` "guaranteed by Frobenius' theorem", smooth:** on a
finite-dimensional space with `dim E = n`, for smooth `g₁, g₂, h₁` satisfying the printed
conditions on an open set `U` (`ChainedConversionConditions`), every `q₀ ∈ U` has an open
neighbourhood `V ⊂ U` and a smooth `h₂ : E → ℝ` with `dh₂ · Δ₂ = 0` on `V` and `dh₁(q), dh₂(q)`
linearly independent for `q ∈ V`. -/
theorem exists_chainedConversion_smooth [FiniteDimensional ℝ E] {g₁ g₂ : E → E} {n : ℕ}
    {h₁ : E → ℝ} {U : Set E} (hdim : Module.finrank ℝ E = n) (hg₁ : ContDiff ℝ ∞ g₁)
    (hg₂ : ContDiff ℝ ∞ g₂) (hh₁ : ContDiff ℝ ∞ h₁) (hU : IsOpen U)
    (hc : ChainedConversionConditions g₁ g₂ n h₁ U) {q₀ : E} (hq₀ : q₀ ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, ContDiff ℝ ∞ h₂ ∧
      (∀ q ∈ V, ∀ f ∈ conversionDelta2 g₁ g₂ n, lieDerivative f h₂ q = 0) ∧
      ∀ q ∈ V, LinearIndependent ℝ ![fderiv ℝ h₁ q, fderiv ℝ h₂ q] := by
  obtain ⟨V, hV, hq₀V, hVU, h₂, hh₂c, hΔ, hli⟩ :=
    exists_chainedConversion_contDiffAt hdim hg₁ hg₂ hh₁ hU hc hq₀
  -- a smooth bump equal to `1` near `q₀` and supported in `V`
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV q₀ hq₀V
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  let χ : ContDiffBump q₀ := ⟨r, 2 * r, hr0, by linarith⟩
  set h₂' : E → ℝ := fun q => χ q * h₂ q with hh₂'
  have hc' : ContDiff ℝ ∞ h₂' := by
    refine contDiff_iff_contDiffAt.2 fun q => ?_
    by_cases hq : q ∈ V
    · exact χ.contDiffAt.mul (hh₂c q hq)
    · have h2 : 2 * r < dist q q₀ := by
        by_contra h
        exact hq (hεV (by rw [mem_ball]; linarith [not_lt.1 h]))
      have hfar : (fun _ => (0 : ℝ)) =ᶠ[𝓝 q] h₂' := by
        filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
          h2] with y hy
        have hy' : χ.rOut ≤ dist y q₀ := le_of_lt (by simpa using hy)
        simp only [hh₂']
        rw [χ.zero_of_le_dist hy', zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hfar.symm
  have hball : ball q₀ r ⊆ V := fun y hy => hεV (ball_subset_ball (by linarith) hy)
  have heq : ∀ q ∈ ball q₀ r, h₂' =ᶠ[𝓝 q] h₂ := fun q hq => by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hq] with y hy
    simp only [hh₂', hy, Pi.one_apply, one_mul]
  refine ⟨ball q₀ r, isOpen_ball, mem_ball_self hr0, fun y hy => hVU (hball hy), h₂', hc',
    fun q hq f hf => ?_, fun q hq => ?_⟩
  · rw [lieDerivative_apply, (heq q hq).fderiv_eq, ← lieDerivative_apply]
    exact hΔ q (hball hq) f hf
  · rw [(heq q hq).fderiv_eq]
    exact hli q (hball hq)

/-- **MLS p. 370, the named statement `ChainedConversionStatement` with the dimension of the state
space equal to `n`:** on a finite-dimensional space `E`, for all smooth `g₁, g₂, h₁` and every
open `U` on which the printed conditions hold with `n = dim E`, every point of `U` has an open
neighbourhood `V ⊂ U` and a smooth `h₂` with `dh₂ · Δ₂ = 0` on `V`, independent of `dh₁`. -/
theorem chainedConversionStatement_of_finrank [FiniteDimensional ℝ E] :
    ∀ (g₁ g₂ : E → E) (n : ℕ) (h₁ : E → ℝ) (U : Set E), Module.finrank ℝ E = n →
      ContDiff ℝ ∞ g₁ → ContDiff ℝ ∞ g₂ → ContDiff ℝ ∞ h₁ → IsOpen U →
        ChainedConversionConditions g₁ g₂ n h₁ U → ∀ q₀ ∈ U,
          ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, ContDiff ℝ ∞ h₂ ∧
            (∀ q ∈ V, ∀ f ∈ conversionDelta2 g₁ g₂ n, lieDerivative f h₂ q = 0) ∧
            ∀ q ∈ V, LinearIndependent ℝ ![fderiv ℝ h₁ q, fderiv ℝ h₂ q] :=
  fun _ _ _ _ _ hdim hg₁ hg₂ hh₁ hU hc _ hq₀ =>
    exists_chainedConversion_smooth hdim hg₁ hg₂ hh₁ hU hc hq₀

/-- **MLS p. 370: conversion to one-chain form (8.7) under the printed conditions on a space of
dimension `n`:** for `n ≥ 2`, `dim E = n`, smooth `g₁, g₂, h₁` satisfying the printed conditions on
an open `U`, and every `q₀ ∈ U`, there are an open `V ∋ q₀` and a smooth `h₂` such that along
every curve with `q̇ = g₁(q)u₁ + g₂(q)u₂` the coordinates `z = φ(q)` satisfy (8.7) with
`v = β(q)u` at every time the curve is in `V`. -/
theorem hasDerivAt_chainedCoordinates_of_finrank [FiniteDimensional ℝ E] {g₁ g₂ : E → E} {n : ℕ}
    (hn : 2 ≤ n) (hdim : Module.finrank ℝ E = n) {h₁ : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂) (hh₁ : ContDiff ℝ ∞ h₁)
    (hc : ChainedConversionConditions g₁ g₂ n h₁ U) {q₀ : E} (hq₀ : q₀ ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, ContDiff ℝ ∞ h₂ ∧
      ∀ (q : ℝ → E) (u : ℝ → Fin 2 → ℝ) (t : ℝ), q t ∈ V →
        HasDerivAt q (driftFree ![g₁, g₂] (q t) (u t)) t →
        HasDerivAt (fun s => chainedCoordinates g₁ h₁ h₂ n (q s))
          (driftFree (chainFields n) (chainedCoordinates g₁ h₁ h₂ n (q t))
            (chainedInput g₁ g₂ h₂ n (q t) (u t))) t := by
  obtain ⟨V, hV, hq₀V, hVU, h₂, hh₂, hΔ, -⟩ :=
    exists_chainedConversion_smooth hdim hg₁ hg₂ hh₁ hU hc hq₀
  exact ⟨V, hV, hq₀V, hVU, h₂, hh₂, fun q u t hqt hq =>
    hasDerivAt_chainedCoordinates hn hV hg₁ hg₂ hh₁ hh₂ (fun q' hq' => hc.normalized q' (hVU hq'))
      (fun q' hq' => hc.lieDerivative_g₂ hn q' (hVU hq'))
      (fun k hk q' hq' => hΔ q' hq' _ ⟨⟨k, by omega⟩, rfl⟩) hqt hq⟩

end Nonholonomic
end RoboLean
