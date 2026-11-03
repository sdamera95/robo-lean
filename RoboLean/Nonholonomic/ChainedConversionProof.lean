import RoboLean.Nonholonomic.ChainedConversion
import RoboLean.Nonholonomic.FrobeniusFrame
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The second function of the chained-form conversion, with a `C¹` defining map (MLS p. 370)

**What MLS prints.** For `q̇ = g₁(q)u₁ + g₂(q)u₂` on `ℝⁿ` under the conditions of p. 370 (the
distributions `Δ₀, Δ₁, Δ₂` of constant rank and involutive, `h₁` with `dh₁ · Δ₁ = 0` and
`dh₁ · g₁ = 1`), "the existence of a function `h₂` independent of `h₁` such that `dh₂ · Δ₂ = 0` is
guaranteed by Frobenius' theorem" (p. 370). The library records this as the named statement
`ChainedConversionStatement`, with a smooth `h₂`.

**Proved here.** On a finite-dimensional space of dimension `n` (MLS: `q ∈ ℝⁿ`), under the printed
conditions on an open set `U`, every point of `U` has an open neighbourhood `V` and a function
`h₂` of class `C¹` on `V` with `dh₂ · Δ₂ = 0` on `V` and `dh₁, dh₂` linearly independent on `V`
(`exists_chainedConversion_classOne`). Route: Frobenius' theorem with a `C¹` defining map
(`isIntegrableAtOfClass_one_of_spanAt`) gives a map `H` with `Δ₂ = ker DH` and `DH` onto `ℝᵖ` near
the point; counting dimensions, `p = n − rank Δ₂ ≥ 2`; as `dh₁ ≠ 0`, one of the first two
components of `H` has a differential independent of `dh₁` at the point, hence nearby.

**What differs from the printed form.** `h₂` is of class `C¹` on `V`, not `C^∞` on the whole
space, because the library's Frobenius theorem has `C¹` defining maps; the "yields" step of the
conversion (`hasDerivAt_chainedCoordinates`) needs `L^{n−1}_{g₁}h₂`, so this `h₂` does not give
the chained form. The dimension hypothesis `finrank E = n` is printed only as `q ∈ ℝⁿ`; the
named statement `ChainedConversionStatement` does not carry it, and without it the existence can
fail: on `ℝ³` with `n = 4`, `g₁ = ∂/∂x`, `g₂ = ∂/∂y + x ∂/∂z` and `h₁ = x` satisfy the printed
conditions with `Δ₁ = Δ₂ = span{∂/∂y, ∂/∂z}`, whose annihilator is spanned by `dh₁` alone.

**Conventions.** Those of `Nonholonomic/ChainedConversion` and `Nonholonomic/Integrability2`.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS p. 370: the fields `ad^k_{g₁}g₂` spanning `Δ₁` and `Δ₂` are smooth** for smooth
`g₁, g₂`. -/
theorem contDiff_adIter_of_contDiff {g₁ g₂ : E → E} (hg₁ : ContDiff ℝ ∞ g₁)
    (hg₂ : ContDiff ℝ ∞ g₂) (k : ℕ) : ContDiff ℝ ∞ (adIter g₁ k g₂) := by
  induction k with
  | zero => simpa [adIter] using hg₂
  | succ k ih =>
    rw [adIter_succ]
    exact hg₁.lieBracket_vectorField ih (by simp)

/-- **MLS p. 370, the existence of `h₂` "guaranteed by Frobenius' theorem", with `C¹` in place of
`C^∞`:** on a finite-dimensional space with `dim E = n`, for smooth `g₁, g₂, h₁` satisfying the
printed conditions on an open set `U` (`ChainedConversionConditions`), every `q₀ ∈ U` has an open
neighbourhood `V ⊂ U` and a function `h₂`, `C¹` at every point of `V`, with `dh₂ · Δ₂ = 0` on `V`
and `dh₁(q), dh₂(q)` linearly independent for `q ∈ V`. -/
theorem exists_chainedConversion_classOne [FiniteDimensional ℝ E] {g₁ g₂ : E → E} {n : ℕ}
    {h₁ : E → ℝ} {U : Set E} (hdim : Module.finrank ℝ E = n) (hg₁ : ContDiff ℝ ∞ g₁)
    (hg₂ : ContDiff ℝ ∞ g₂) (hh₁ : ContDiff ℝ ∞ h₁) (hU : IsOpen U)
    (hc : ChainedConversionConditions g₁ g₂ n h₁ U) {q₀ : E} (hq₀ : q₀ ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, (∀ q ∈ V, ContDiffAt ℝ 1 h₂ q) ∧
      (∀ q ∈ V, ∀ f ∈ conversionDelta2 g₁ g₂ n, lieDerivative f h₂ q = 0) ∧
      ∀ q ∈ V, LinearIndependent ℝ ![fderiv ℝ h₁ q, fderiv ℝ h₂ q] := by
  set F : Fin (n - 2) → E → E := fun k => adIter g₁ k g₂ with hF
  have hFc : ∀ k, ContDiff ℝ 1 (F k) := fun k =>
    (contDiff_adIter_of_contDiff hg₁ hg₂ k).of_le (by exact_mod_cast le_top)
  obtain ⟨V₀, hV₀, hq₀V₀, p, H, hHc, hH⟩ :=
    isIntegrableAtOfClass_one_of_spanAt hU hFc hc.regular2 hc.involutive2 hq₀
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
  have hh₂c : ∀ q ∈ V₀, ContDiffAt ℝ 1 h₂ q := fun q hq =>
    (contDiff_apply ℝ ℝ i).contDiffAt.comp q (hHc q hq)
  have hfd : ∀ q ∈ V₀, fderiv ℝ h₂ q = (ContinuousLinearMap.proj i).comp (fderiv ℝ H q) := by
    intro q hq
    have hd := ((hHc q hq).differentiableAt one_ne_zero).hasFDerivAt
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
  obtain ⟨V, hVsub, hVo, hq₀V⟩ := mem_nhds_iff.1
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

end Nonholonomic
end RoboLean
