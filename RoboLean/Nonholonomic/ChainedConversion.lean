import RoboLean.Nonholonomic.ChainedForm
import RoboLean.Nonholonomic.Distribution

/-!
# Conversion of a two-input system to one-chain form: MLS Chapter 8, §3.2

MLS Chapter 8, §3.2, printed pp. 369–371: for `q̇ = g₁(q)u₁ + g₂(q)u₂` with `g₁, g₂` linearly
independent, "the system can be converted into one-chain form if the following distributions are
all of constant rank and involutive": `Δ₀ = span{g₁, g₂, ad_{g₁}g₂, …, ad^{n−2}_{g₁}g₂}`,
`Δ₁ = span{g₂, ad_{g₁}g₂, …, ad^{n−2}_{g₁}g₂}`, `Δ₂ = span{g₂, ad_{g₁}g₂, …, ad^{n−3}_{g₁}g₂}`,
"and there exists a function `h₁(q)` such that `dh₁ · Δ₁ = 0` and `dh₁ · g₁ = 1`"; then a function
`h₂` independent of `h₁` with `dh₂ · Δ₂ = 0` exists by Frobenius' theorem, and
`z = (h₁, L^{n−2}_{g₁}h₂, …, L_{g₁}h₂, h₂)`, `v₁ = u₁`,
`v₂ = (L^{n−1}_{g₁}h₂)u₁ + (L_{g₂}L^{n−2}_{g₁}h₂)u₂` "yields" the one-chain form (8.7).

**What is formalized.**

* The distributions `Δ₀, Δ₁, Δ₂` as sets of fields (`conversionDelta0`, `conversionDelta1`,
  `conversionDelta2`, spanned pointwise by the library's `spanAt`) and the printed sufficient
  conditions on an open set (`ChainedConversionConditions`).
* The "yields" step, proved: if `h₁, h₂` are smooth with `L_{g₁}h₁ = 1`, `L_{g₂}h₁ = 0` and
  `L_{ad^k_{g₁}g₂}h₂ = 0` for `k ≤ n − 3` on an open set, then along every curve in it with
  `q̇ = g₁u₁ + g₂u₂` the coordinates `z = φ(q)` satisfy the one-chain form (8.7) with inputs
  `v = β(q)u` (`hasDerivAt_chainedCoordinates`). The step `L_{g₂}L^j_{g₁}h₂ = 0`, `j ≤ n − 3`, comes
  from `L_{[f, g]} = L_f L_g − L_g L_f` (`lieDerivative_adIter_iterate_eq_zero`). The printed
  conditions give the hypotheses on `h₁` (`ChainedConversionConditions.lieDerivative_g₂`).
* The existence of `h₂` ("guaranteed by Frobenius' theorem") is the named statement
  `ChainedConversionStatement`, not proved; `hasDerivAt_chainedCoordinates_of_statement` combines
  it with the printed conditions. The book also does not show, and nothing here shows, that `φ` is
  a diffeomorphism or that `β(q)` is invertible.

**Corrected printing.** The book prints the last generator of `Δ₀` as `ad^{n−2}_{g₁}g₁`, which is
zero (`[g₁, g₁] = 0`); `Δ₀ = Δ₁ + span{g₁}` with `ad^{n−2}_{g₁}g₂` is meant, as the pattern of
`Δ₁` and the rank `n` needed for the chained form show.

**Conventions.** Fields are maps `E → E` on a real normed space (MLS: `ℝⁿ`), smooth (`C^∞`);
`L_f h` is the library's `lieDerivative` and `ad^k_f g` its `adIter` (MLS pp. 322, 364); the
chained form is the library's `chainFields n` with `z₁` entry `0`; the coordinate `z_k`,
`2 ≤ k ≤ n`, is `L^{n−k}_{g₁}h₂` (entry `k − 1`).
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS p. 370: the distribution `Δ₀ = span{g₁, g₂, ad_{g₁}g₂, …, ad^{n−2}_{g₁}g₂}`** as its set
of generators (corrected printing: the book's last generator `ad^{n−2}_{g₁}g₁` is zero). -/
def conversionDelta0 (g₁ g₂ : E → E) (n : ℕ) : Set (E → E) :=
  insert g₁ (Set.range fun k : Fin (n - 1) => adIter g₁ k g₂)

/-- **MLS p. 370: the distribution `Δ₁ = span{g₂, ad_{g₁}g₂, …, ad^{n−2}_{g₁}g₂}`** as its set of
generators. -/
def conversionDelta1 (g₁ g₂ : E → E) (n : ℕ) : Set (E → E) :=
  Set.range fun k : Fin (n - 1) => adIter g₁ k g₂

/-- **MLS p. 370: the distribution `Δ₂ = span{g₂, ad_{g₁}g₂, …, ad^{n−3}_{g₁}g₂}`** as its set of
generators. -/
def conversionDelta2 (g₁ g₂ : E → E) (n : ℕ) : Set (E → E) :=
  Set.range fun k : Fin (n - 2) => adIter g₁ k g₂

/-- **MLS p. 370: the sufficient conditions for conversion to one-chain form** on a set `U`:
`g₁, g₂` linearly independent; `Δ₀, Δ₁, Δ₂` of constant rank (`IsRegularOn`) and involutive; a
function `h₁` with `dh₁ · Δ₁ = 0` and `dh₁ · g₁ = 1`. -/
structure ChainedConversionConditions (g₁ g₂ : E → E) (n : ℕ) (h₁ : E → ℝ) (U : Set E) : Prop where
  /-- MLS p. 370: `g₁(q)` and `g₂(q)` are linearly independent. -/
  linearIndependent : ∀ q ∈ U, LinearIndependent ℝ ![g₁ q, g₂ q]
  /-- MLS p. 370: `Δ₀` has constant rank. -/
  regular0 : IsRegularOn (spanAt (conversionDelta0 g₁ g₂ n)) U
  /-- MLS p. 370: `Δ₀` is involutive. -/
  involutive0 : IsInvolutiveOn (spanAt (conversionDelta0 g₁ g₂ n)) U
  /-- MLS p. 370: `Δ₁` has constant rank. -/
  regular1 : IsRegularOn (spanAt (conversionDelta1 g₁ g₂ n)) U
  /-- MLS p. 370: `Δ₁` is involutive. -/
  involutive1 : IsInvolutiveOn (spanAt (conversionDelta1 g₁ g₂ n)) U
  /-- MLS p. 370: `Δ₂` has constant rank. -/
  regular2 : IsRegularOn (spanAt (conversionDelta2 g₁ g₂ n)) U
  /-- MLS p. 370: `Δ₂` is involutive. -/
  involutive2 : IsInvolutiveOn (spanAt (conversionDelta2 g₁ g₂ n)) U
  /-- MLS p. 370: `dh₁ · Δ₁ = 0`. -/
  annihilates : ∀ q ∈ U, ∀ f ∈ conversionDelta1 g₁ g₂ n, lieDerivative f h₁ q = 0
  /-- MLS p. 370: `dh₁ · g₁ = 1`. -/
  normalized : ∀ q ∈ U, lieDerivative g₁ h₁ q = 1

/-- **MLS p. 370: the coordinates `z = φ(q)`,** `z₁ = h₁`, `z_k = L^{n−k}_{g₁}h₂` for
`2 ≤ k ≤ n` (entry `k − 1`), so `z₂ = L^{n−2}_{g₁}h₂`, …, `z_{n−1} = L_{g₁}h₂`, `z_n = h₂`. -/
def chainedCoordinates (g₁ : E → E) (h₁ h₂ : E → ℝ) (n : ℕ) (q : E) : Fin n → ℝ :=
  fun i => if i.val = 0 then h₁ q else (lieDerivative g₁)^[n - 1 - i.val] h₂ q

/-- **MLS p. 370: the input transformation `v = β(q)u`,** `v₁ = u₁`,
`v₂ = (L^{n−1}_{g₁}h₂)u₁ + (L_{g₂}L^{n−2}_{g₁}h₂)u₂`. -/
def chainedInput (g₁ g₂ : E → E) (h₂ : E → ℝ) (n : ℕ) (q : E) (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![u 0, (lieDerivative g₁)^[n - 1] h₂ q * u 0 +
    lieDerivative g₂ ((lieDerivative g₁)^[n - 2] h₂) q * u 1]

/-- Lie derivatives of smooth functions along smooth fields are smooth. -/
private theorem contDiff_lieDerivative {f : E → E} {α : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (lieDerivative f α) :=
  (contDiff_infty_iff_fderiv.1 hα).2.clm_apply hf

/-- Brackets of smooth fields are smooth. -/
private theorem contDiff_lieBracket {f g : E → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (lieBracket ℝ f g) := by
  have h : lieBracket ℝ f g = fun x => fderiv ℝ g x (f x) - fderiv ℝ f x (g x) := rfl
  rw [h]
  exact ((contDiff_infty_iff_fderiv.1 hg).2.clm_apply hf).sub
    ((contDiff_infty_iff_fderiv.1 hf).2.clm_apply hg)

/-- Iterated brackets of smooth fields are smooth. -/
private theorem contDiff_adIter {g₁ g₂ : E → E} (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    (k : ℕ) : ContDiff ℝ ∞ (adIter g₁ k g₂) := by
  induction k with
  | zero => simpa [adIter] using hg₂
  | succ k ih =>
    rw [adIter_succ]
    exact contDiff_lieBracket hg₁ ih

/-- Iterated Lie derivatives of a smooth function along a smooth field are smooth. -/
private theorem contDiff_iterate_lieDerivative {g₁ : E → E} {h : E → ℝ} (hg₁ : ContDiff ℝ ∞ g₁)
    (hh : ContDiff ℝ ∞ h) (j : ℕ) : ContDiff ℝ ∞ ((lieDerivative g₁)^[j] h) := by
  induction j with
  | zero => simpa using hh
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_lieDerivative hg₁ ih

/-- **MLS p. 370, the step behind "yields": `L_{g₂}L^j_{g₁}h₂ = 0` for `j ≤ N`** on an open set
`U` where `L_{ad^k_{g₁}g₂}h₂ = 0` for `k ≤ N` (`dh₂ · Δ₂ = 0` with `N = n − 3`), for smooth `g₁, g₂,
h₂`; from `L_{[f, g]} = L_f L_g − L_g L_f` (MLS p. 325). -/
theorem lieDerivative_adIter_iterate_eq_zero {g₁ g₂ : E → E} {h₂ : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂) (hh₂ : ContDiff ℝ ∞ h₂)
    {N : ℕ} (h : ∀ k ≤ N, ∀ q ∈ U, lieDerivative (adIter g₁ k g₂) h₂ q = 0) :
    ∀ j ≤ N, ∀ q ∈ U, lieDerivative g₂ ((lieDerivative g₁)^[j] h₂) q = 0 := by
  have hstep : ∀ j k, j + k ≤ N → ∀ q ∈ U,
      lieDerivative (adIter g₁ k g₂) ((lieDerivative g₁)^[j] h₂) q = 0 := by
    intro j
    induction j with
    | zero =>
      intro k hk q hq
      simpa using h k (by omega) q hq
    | succ j ih =>
      intro k hk q hq
      have hα : ContDiff ℝ ∞ ((lieDerivative g₁)^[j] h₂) := contDiff_iterate_lieDerivative hg₁ hh₂ j
      have key := lieDerivative_lieBracket (hα.of_le (by simp)).contDiffAt
        ((hg₁.differentiable (by simp)) q)
        (((contDiff_adIter hg₁ hg₂ k).differentiable (by simp)) q)
      rw [← adIter_succ] at key
      have h1 := ih (k + 1) (by omega) q hq
      have h2 : lieDerivative g₁ (lieDerivative (adIter g₁ k g₂) ((lieDerivative g₁)^[j] h₂)) q =
          0 := by
        have he : lieDerivative (adIter g₁ k g₂) ((lieDerivative g₁)^[j] h₂) =ᶠ[𝓝 q]
            fun _ => (0 : ℝ) := by
          filter_upwards [hU.mem_nhds hq] with x hx using ih k (by omega) x hx
        rw [lieDerivative_apply, he.fderiv_eq]
        simp
      rw [Function.iterate_succ_apply']
      linarith
  intro j hj q hq
  simpa [adIter] using hstep j 0 (by omega) q hq

/-- **MLS p. 370: the conversion yields the one-chain form (8.7).** For `n ≥ 2`, smooth `g₁, g₂,
h₁, h₂` with `L_{g₁}h₁ = 1`, `L_{g₂}h₁ = 0` and `L_{ad^k_{g₁}g₂}h₂ = 0` for `k ≤ n − 3` on an open
set `U`: if `q̇(t) = g₁(q)u₁ + g₂(q)u₂` at a time `t` with `q(t) ∈ U`, then `z = φ(q)` has
derivative `ż = g₁^{chain}(z)v₁ + g₂^{chain}(z)v₂` there, with `v = β(q)u` (`chainedInput`). -/
theorem hasDerivAt_chainedCoordinates {g₁ g₂ : E → E} {h₁ h₂ : E → ℝ} {n : ℕ} (hn : 2 ≤ n)
    {U : Set E} (hU : IsOpen U) (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    (hh₁ : ContDiff ℝ ∞ h₁) (hh₂ : ContDiff ℝ ∞ h₂)
    (h₁g₁ : ∀ q ∈ U, lieDerivative g₁ h₁ q = 1) (h₁g₂ : ∀ q ∈ U, lieDerivative g₂ h₁ q = 0)
    (h₂Δ : ∀ k, k + 3 ≤ n → ∀ q ∈ U, lieDerivative (adIter g₁ k g₂) h₂ q = 0)
    {q : ℝ → E} {u : ℝ → Fin 2 → ℝ} {t : ℝ} (hqt : q t ∈ U)
    (hq : HasDerivAt q (driftFree ![g₁, g₂] (q t) (u t)) t) :
    HasDerivAt (fun s => chainedCoordinates g₁ h₁ h₂ n (q s))
      (driftFree (chainFields n) (chainedCoordinates g₁ h₁ h₂ n (q t))
        (chainedInput g₁ g₂ h₂ n (q t) (u t))) t := by
  have hd : ∀ F : E → ℝ, ContDiff ℝ ∞ F → HasDerivAt (fun s => F (q s))
      (u t 0 * lieDerivative g₁ F (q t) + u t 1 * lieDerivative g₂ F (q t)) t := by
    intro F hF
    have h := ((hF.differentiable (by simp)) (q t)).hasFDerivAt.comp_hasDerivAt t hq
    rw [show driftFree ![g₁, g₂] (q t) (u t) = u t 0 • g₁ (q t) + u t 1 • g₂ (q t) by
      simp [driftFree, Fin.sum_univ_two], map_add, map_smul, map_smul] at h
    simpa [lieDerivative_apply, Function.comp_def, smul_eq_mul] using h
  rw [hasDerivAt_pi]
  intro i
  by_cases hi0 : i.val = 0
  · simp only [chainedCoordinates, hi0, ite_true]
    rw [chain_driftFree_of_val_eq_zero _ _ hi0]
    have := hd h₁ hh₁
    rw [h₁g₁ _ hqt, h₁g₂ _ hqt] at this
    simpa [chainedInput] using this
  by_cases hi1 : i.val = 1
  · simp only [chainedCoordinates, hi1]
    rw [chain_driftFree_of_val_eq_one _ _ hi1]
    have := hd _ (contDiff_iterate_lieDerivative hg₁ hh₂ (n - 2))
    have he : lieDerivative g₁ ((lieDerivative g₁)^[n - 2] h₂) =
        (lieDerivative g₁)^[n - 1] h₂ := by
      rw [← Function.iterate_succ_apply' (f := lieDerivative g₁)]
      congr 1
      omega
    rw [he] at this
    rw [show n - 1 - 1 = n - 2 by omega]
    convert this using 1
    · funext s
      simp
    · unfold chainedInput
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
  · have hj : i.val - 1 < n := by omega
    have hz := lieDerivative_adIter_iterate_eq_zero hU hg₁ hg₂ hh₂ (N := n - 3)
      fun k hk q' hq' => h₂Δ k (by omega) q' hq'
    rw [chain_driftFree_of_val_eq_succ _ _ (j := ⟨i.val - 1, hj⟩) (by simp; omega)
      (by simp; omega)]
    simp only [chainedCoordinates, hi0, ite_false]
    have := hd _ (contDiff_iterate_lieDerivative hg₁ hh₂ (n - 1 - i.val))
    rw [hz (n - 1 - i.val) (by omega) _ hqt, mul_zero, add_zero] at this
    have hne : i.val - 1 ≠ 0 := by omega
    have he : lieDerivative g₁ ((lieDerivative g₁)^[n - 1 - i.val] h₂) =
        (lieDerivative g₁)^[n - 1 - (i.val - 1)] h₂ := by
      rw [← Function.iterate_succ_apply' (f := lieDerivative g₁)]
      congr 1
      omega
    rw [he] at this
    simpa [chainedInput, hne] using this

/-- **MLS p. 370: the printed conditions give `dh₁ · g₂ = 0`** (`g₂ ∈ Δ₁` for `n ≥ 2`), the
hypothesis on `h₁` of `hasDerivAt_chainedCoordinates` besides `dh₁ · g₁ = 1`. -/
theorem ChainedConversionConditions.lieDerivative_g₂ {g₁ g₂ : E → E} {n : ℕ} {h₁ : E → ℝ}
    {U : Set E} (hc : ChainedConversionConditions g₁ g₂ n h₁ U) (hn : 2 ≤ n) :
    ∀ q ∈ U, lieDerivative g₂ h₁ q = 0 := by
  intro q hq
  have h := hc.annihilates q hq (adIter g₁ 0 g₂) ⟨⟨0, by omega⟩, rfl⟩
  simpa [adIter] using h

/-- **MLS p. 370, "the existence of independent `h₁` and `h₂` … is guaranteed by Frobenius'
theorem", as a named statement:** for smooth `g₁, g₂` and `h₁` satisfying the printed
conditions on an open set `U`, near every point of `U` there is a smooth `h₂` with `dh₂ · Δ₂ = 0`
whose differential is independent of `dh₁`. As stated here, with `n` unrelated to the dimension of
`E`, this is false (`Examples/ChainedConversionCounterexample`, `n = 4` on `ℝ³`); MLS's `n` is the
dimension of the state space, and with `dim E = n` the existence holds with a `C¹` function `h₂`
(`Nonholonomic/ChainedConversionProof`), the smooth form resting on the smooth Frobenius theorem. -/
def ChainedConversionStatement (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (g₁ g₂ : E → E) (n : ℕ) (h₁ : E → ℝ) (U : Set E), ContDiff ℝ ∞ g₁ → ContDiff ℝ ∞ g₂ →
    ContDiff ℝ ∞ h₁ → IsOpen U → ChainedConversionConditions g₁ g₂ n h₁ U → ∀ q₀ ∈ U,
      ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, ContDiff ℝ ∞ h₂ ∧
        (∀ q ∈ V, ∀ f ∈ conversionDelta2 g₁ g₂ n, lieDerivative f h₂ q = 0) ∧
        ∀ q ∈ V, LinearIndependent ℝ ![fderiv ℝ h₁ q, fderiv ℝ h₂ q]

/-- **MLS p. 370: conversion to one-chain form under the printed conditions,** with the existence
of `h₂` taken from the named statement `ChainedConversionStatement`: for `n ≥ 2` and every point
`q₀` of `U` there are an open `V ∋ q₀` and a smooth `h₂` such that along every curve with
`q̇ = g₁(q)u₁ + g₂(q)u₂` the coordinates `z = φ(q)` satisfy (8.7) with `v = β(q)u` at every time
the curve is in `V`. -/
theorem hasDerivAt_chainedCoordinates_of_statement (hS : ChainedConversionStatement E)
    {g₁ g₂ : E → E} {n : ℕ} (hn : 2 ≤ n) {h₁ : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂) (hh₁ : ContDiff ℝ ∞ h₁)
    (hc : ChainedConversionConditions g₁ g₂ n h₁ U) {q₀ : E} (hq₀ : q₀ ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧ ∃ h₂ : E → ℝ, ContDiff ℝ ∞ h₂ ∧
      ∀ (q : ℝ → E) (u : ℝ → Fin 2 → ℝ) (t : ℝ), q t ∈ V →
        HasDerivAt q (driftFree ![g₁, g₂] (q t) (u t)) t →
        HasDerivAt (fun s => chainedCoordinates g₁ h₁ h₂ n (q s))
          (driftFree (chainFields n) (chainedCoordinates g₁ h₁ h₂ n (q t))
            (chainedInput g₁ g₂ h₂ n (q t) (u t))) t := by
  obtain ⟨V, hV, hq₀V, hVU, h₂, hh₂, hΔ, -⟩ := hS g₁ g₂ n h₁ U hg₁ hg₂ hh₁ hU hc q₀ hq₀
  exact ⟨V, hV, hq₀V, hVU, h₂, hh₂, fun q u t hqt hq =>
    hasDerivAt_chainedCoordinates hn hV hg₁ hg₂ hh₁ hh₂ (fun q' hq' => hc.normalized q' (hVU hq'))
      (fun q' hq' => hc.lieDerivative_g₂ hn q' (hVU hq'))
      (fun k hk q' hq' => hΔ q' hq' _ ⟨⟨k, by omega⟩, rfl⟩) hqt hq⟩

end Nonholonomic
end RoboLean
