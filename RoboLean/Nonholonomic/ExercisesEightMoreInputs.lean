import RoboLean.Nonholonomic.OptimalInputs
import RoboLean.Nonholonomic.PhilipHall
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Chapter 8, Exercise 7: every derivative of the optimal input (MLS p. 393)

MLS Chapter 8, Exercise 7, printed p. 393: "Proposition 8.4 gave a formula for the first
derivative of the optimal inputs. Use the method of the proof of that proposition to obtain a
formula for `ü`. Express the answer in terms of Lie brackets of the input vector fields. In fact,
if you are adventurous, try to find the formula for `u⁽ⁿ⁾`."

**What is formalized.** As in the library's treatment of Proposition 8.4 (p. 373), the necessary
conditions (8.12)–(8.13) are hypotheses along a curve `(q, p)`: `q̇ = Σ gᵢ(q) uᵢ`,
`ṗ = −∂H/∂q` and `uᵢ = −pᵀgᵢ(q)`. Write `φ_w(t) = p(t)ᵀ g_w(q(t))` for the pairing of the
multiplier with the field `g_w` of a formal Lie product `w` of the generators (the library's
`LieProduct.eval`). The method of the proof of Proposition 8.4 gives
`φ̇_w = −Σⱼ φ_{gⱼ} φ_{[gⱼ, w]}`; extending this rule as a derivation `D` of the polynomial algebra in
the variables `X_w`, `D X_w = −Σⱼ X_{gⱼ} X_{[gⱼ, w]}`, every polynomial in the pairings is
differentiated by applying `D`, and so

`uᵢ⁽ⁿ⁾(t) = −(Dⁿ X_{gᵢ})(φ(t))`,

a polynomial of degree `n + 1` in the pairings of brackets of length at most `n + 1`. For `n = 1`
it is `u̇ᵢ = Σⱼ φ_{gⱼ} φ_{[gⱼ, gᵢ]} = Σⱼ pᵀ[gᵢ, gⱼ] uⱼ`, the formula `u̇ = Ω(q, p)u` of (8.16).

**Conventions.** The state lies in a real normed space `E`, the multiplier in its dual; the
bracket is Mathlib's `lieBracket` (the book's `[f, g] = (∂g/∂q)f − (∂f/∂q)g`, p. 323); the input
fields are smooth (`C^∞`), so that every bracket is differentiable; the hypotheses hold at every
time, so that the iterated derivatives are those of functions on `ℝ`.
-/

noncomputable section

open Set Filter Topology VectorField MvPolynomial
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS Chapter 8, Exercise 7 (p. 393): the pairings** `φ_w(t) = p(t)ᵀ g_w(q(t))` of the
multiplier with the fields of the formal Lie products `w` of the input fields. -/
def costatePairing (g : Fin m → E → E) (q : ℝ → E) (p : ℝ → E →L[ℝ] ℝ) (t : ℝ) :
    LieProduct m → ℝ :=
  fun w => p t (LieProduct.eval g w (q t))

/-- **MLS Chapter 8, Exercise 7 (p. 393): the derivation `D`** of the polynomials in the pairing
variables `X_w` with `D X_w = −Σⱼ X_{gⱼ} X_{[gⱼ, w]}`, the rule `φ̇_w = −Σⱼ φ_{gⱼ} φ_{[gⱼ, w]}` of the
method of the proof of Proposition 8.4 (p. 373). -/
def optimalInputDerivation (m : ℕ) :
    Derivation ℝ (MvPolynomial (LieProduct m) ℝ) (MvPolynomial (LieProduct m) ℝ) :=
  mkDerivation ℝ fun w => -∑ j : Fin m, X (LieProduct.gen j) * X (LieProduct.br (LieProduct.gen j) w)

/-- **MLS p. 344 with Definition 7.1, p. 326: the field of every Lie product of smooth fields is
smooth** (the convention of Exercise 7, p. 393). -/
theorem LieProduct.contDiff_eval {g : Fin m → E → E} (hg : ∀ i, ContDiff ℝ ∞ (g i)) :
    ∀ w : LieProduct m, ContDiff ℝ ∞ (LieProduct.eval g w)
  | .gen i => hg i
  | .br a b => (LieProduct.contDiff_eval hg a).lieBracket_vectorField
      (LieProduct.contDiff_eval hg b) (by simp)

/-- **The method of the proof of MLS Proposition 8.4, p. 373, for Exercise 7, p. 393.** Along a
curve with `q̇ = Σ gᵢ(q)uᵢ`, `ṗ = −∂H/∂q` (8.12) and `uᵢ = −pᵀgᵢ(q)` (8.13) at `t`, for every field
`h` differentiable at `q(t)`: `d/dt pᵀh(q) = −Σⱼ (pᵀgⱼ(q)) (pᵀ[gⱼ, h](q))`. -/
theorem hasDerivAt_costate_apply {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ} {t : ℝ}
    (hq : HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : HasDerivAt p (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t)
    {h : E → E} (hh : DifferentiableAt ℝ h (q t)) :
    HasDerivAt (fun s => p s (h (q s)))
      (-∑ j, p t (g j (q t)) * p t (lieBracket ℝ (g j) h (q t))) t := by
  have hhq : HasDerivAt (fun s => h (q s))
      (fderiv ℝ h (q t) (driftFree g (q t) (optimalInput g q p t))) t :=
    hh.hasFDerivAt.comp_hasDerivAt t hq
  have hd := hp.clm_apply hhq
  convert hd using 1
  simp only [lieBracket, map_sub, driftFree, map_sum, map_smul, smul_eq_mul, optimalInput,
    _root_.neg_apply, FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp only [mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
  ring

/-- **MLS Chapter 8, Exercise 7 (p. 393): the derivative of a polynomial in the pairings.** Under
(8.12)–(8.13) at `t`, with smooth input fields, every polynomial `P` in the pairing variables
satisfies `d/dt P(φ(t)) = (D P)(φ(t))`. -/
theorem hasDerivAt_eval_costatePairing {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ}
    {t : ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hq : HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : HasDerivAt p (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t)
    (P : MvPolynomial (LieProduct m) ℝ) :
    HasDerivAt (fun s => eval (costatePairing g q p s) P)
      (eval (costatePairing g q p t) (optimalInputDerivation m P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, MvPolynomial.derivation_C, map_zero]
    exact hasDerivAt_const t a
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P w hP =>
    have hw : HasDerivAt (fun s => costatePairing g q p s w)
        (-∑ j, p t (g j (q t)) * p t (lieBracket ℝ (g j) (LieProduct.eval g w) (q t))) t :=
      hasDerivAt_costate_apply hq hp
        ((LieProduct.contDiff_eval hg w).differentiable (by simp) (q t))
    have h := hP.mul hw
    convert h using 1
    · funext s
      simp [costatePairing]
    · simp only [Derivation.leibniz, optimalInputDerivation, mkDerivation_X, smul_eq_mul, map_add,
        map_mul, eval_X, map_neg, map_sum]
      simp only [costatePairing, LieProduct.eval]
      ring

/-- **MLS Chapter 8, Exercise 7 (p. 393): the formula for `u⁽ⁿ⁾`.** If the necessary conditions
(8.12)–(8.13) hold at every time and the input fields are smooth, then for every `n` the `n`-th
derivative of the optimal input is `uᵢ⁽ⁿ⁾(t) = −(Dⁿ X_{gᵢ})(φ(t))`, a polynomial in the pairings
`pᵀ g_w(q)` of the Lie products `w` of length at most `n + 1`. -/
theorem iteratedDeriv_optimalInput {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hq : ∀ t, HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : ∀ t, HasDerivAt p
      (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t)
    (n : ℕ) (i : Fin m) :
    iteratedDeriv n (fun t => optimalInput g q p t i) =
      fun t => -eval (costatePairing g q p t)
        ((optimalInputDerivation m)^[n] (X (LieProduct.gen i))) := by
  induction n with
  | zero =>
    funext t
    simp [optimalInput, costatePairing, LieProduct.eval]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    exact ((hasDerivAt_eval_costatePairing hg (hq t) (hp t) _).neg).deriv

end Nonholonomic
end RoboLean
