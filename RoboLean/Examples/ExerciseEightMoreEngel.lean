import RoboLean.Examples.NilpotentFiveState
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Chapter 8, Exercise 10: Engel's method for the five-state system (MLS pp. 374 and 393)

MLS Chapter 8, Exercise 10, printed p. 393: "Extend the method used to find the optimal inputs for
Engel's system to find optimal inputs for the system of Exercise 2." The method is Example 8.4,
p. 374: the optimal inputs satisfy `u̇ = Ω(q, p)u` (8.16), are written `u₁ = r sin α`,
`u₂ = r cos α`, the multipliers of the coordinates the fields do not depend on are constant, the
angle satisfies a pendulum equation, "multiply both sides by `2α̇`, integrate", and the last step
(8.19) integrates the resulting first-order equation by elliptic integrals.

**What is formalized.** For the system of Exercise 2, `q̇ = (u₁, u₂, q₁u₂ − q₂u₁, q₁²u₂, q₂²u₁)`,
along a curve satisfying the necessary conditions (8.12)–(8.13) on `[0, T]` (hypotheses, as in the
library's Proposition 8.4) with the optimal input in the polar form `u = r(sin α, cos α)`:
* the multipliers `λ₃, λ₄, λ₅` of `q₃, q₄, q₅` are constant;
* `α̇ = 2(λ₃ + q₁λ₄ − q₂λ₅)`;
* the angle equation `α̈ = 2r(λ₄ sin α − λ₅ cos α)` (for `λ₅ = 0` Engel's `α̈ = 2p₄ r sin α`);
* the first integral `α̇² + 4r(λ₄ cos α + λ₅ sin α) = b` constant (Engel's
  `α̇² = b − 2δ cos α`, `δ = 2p₄r`).
The final step, the solution of the first-order equation by elliptic functions (8.19), is not
formalized (Mathlib has no elliptic functions); nor is the existence of the polar form.

**Conventions.** Coordinates `q 0 = q₁`, …, `q 4 = q₅`; the multiplier `p(t)` is a linear form and
`λₖ = p(eₖ)`; the optimal input is the library's `optimalInput` `uᵢ = −pᵀgᵢ(q)` (8.13); the bracket
is the library's (book's sign).
-/

noncomputable section

open Set VectorField Matrix Real
open scoped ContDiff
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Chapter 8, Exercise 2, p. 391: the input fields are smooth** (polynomial in `q₁, q₂`). -/
theorem fiveFields_contDiff (j : Fin 2) : ContDiff ℝ ∞ (fiveFields j) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases j <;> fin_cases i <;> simp [fiveFields, baseField, fiveG1, fiveG2] <;> fun_prop

/-- **MLS Example 8.4, p. 374, for Exercise 10, p. 393: the multipliers of `q₃, q₄, q₅` are
constant** along a curve with `ṗ = −∂H/∂q` (8.12) on `[0, T]`, since the fields do not depend on
these coordinates. -/
theorem five_multiplier_const {q : ℝ → Fin 5 → ℝ} {p : ℝ → (Fin 5 → ℝ) →L[ℝ] ℝ} {T : ℝ}
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput fiveFields q p t i • (p t).comp (fderiv ℝ (fiveFields i) (q t))) t)
    (k : Fin 5) (hk : 2 ≤ k.val) :
    ∀ t ∈ Icc 0 T, p t (Pi.single k 1) = p 0 (Pi.single k 1) := by
  have hbase : ∀ i, IsBase (fiveFields i) := by
    intro i
    fin_cases i
    · show IsBase (baseField fiveG1)
      exact isBase_baseField _
    · show IsBase (baseField fiveG2)
      exact isBase_baseField _
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => p s (Pi.single k 1)) 0 t := by
    intro t ht
    have h := (hp t ht).clm_apply (hasDerivAt_const t (Pi.single k (1 : ℝ)))
    convert h using 1
    have hz : ∀ i, fderiv ℝ (fiveFields i) (q t) (Pi.single k 1) = 0 := fun i =>
      fderiv_apply_eq_zero_of_isBase (hbase i) (q t)
        (Pi.single_eq_of_ne (fun h => by rw [← h] at hk; simp at hk) _)
        (Pi.single_eq_of_ne (fun h => by rw [← h] at hk; simp at hk) _)
    simp [hz]
  intro t ht
  have hcont : ContinuousOn (fun s => p s (Pi.single k 1)) (Icc 0 T) := fun s hs =>
    (hd s hs).continuousAt.continuousWithinAt
  have := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
  exact this

/-- **MLS Example 8.4, p. 374, extended to the system of Exercise 2 (Exercise 10, p. 393): the
angle equations.** Along a curve satisfying (8.12)–(8.13) on `[0, T]` with the optimal input in the
polar form `u = r(sin α, cos α)`, `r ≠ 0`, and with the constants `λₖ = p(0)(eₖ)`: at every
`t ∈ [0, T]`, `α̇ = Ω := 2(λ₃ + q₁λ₄ − q₂λ₅)`, `Ω̇ = 2r(λ₄ sin α − λ₅ cos α)` (so
`α̈ = 2r(λ₄ sin α − λ₅ cos α)`), and `Ω² + 4r(λ₄ cos α + λ₅ sin α)` is constant. -/
theorem five_angle_equations {q : ℝ → Fin 5 → ℝ} {p : ℝ → (Fin 5 → ℝ) →L[ℝ] ℝ} {T : ℝ}
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (driftFree fiveFields (q t) (optimalInput fiveFields q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput fiveFields q p t i • (p t).comp (fderiv ℝ (fiveFields i) (q t))) t)
    {r : ℝ} (hr : r ≠ 0) {α α' : ℝ → ℝ} (hα : ∀ t, HasDerivAt α (α' t) t)
    (hpolar : ∀ t, optimalInput fiveFields q p t = ![r * sin (α t), r * cos (α t)]) :
    ∀ t ∈ Icc 0 T,
      α' t = 2 * (p 0 (Pi.single 2 1) + q t 0 * p 0 (Pi.single 3 1) - q t 1 * p 0 (Pi.single 4 1)) ∧
      HasDerivAt (fun s => 2 * (p 0 (Pi.single 2 1) + q s 0 * p 0 (Pi.single 3 1) -
          q s 1 * p 0 (Pi.single 4 1)))
        (2 * r * (p 0 (Pi.single 3 1) * sin (α t) - p 0 (Pi.single 4 1) * cos (α t))) t ∧
      (2 * (p 0 (Pi.single 2 1) + q t 0 * p 0 (Pi.single 3 1) - q t 1 * p 0 (Pi.single 4 1))) ^ 2 +
          4 * r * (p 0 (Pi.single 3 1) * cos (α t) + p 0 (Pi.single 4 1) * sin (α t)) =
        (2 * (p 0 (Pi.single 2 1) + q 0 0 * p 0 (Pi.single 3 1) - q 0 1 * p 0 (Pi.single 4 1))) ^ 2 +
          4 * r * (p 0 (Pi.single 3 1) * cos (α 0) + p 0 (Pi.single 4 1) * sin (α 0)) := by
  have hc3 := five_multiplier_const hp 2 (by decide)
  have hc4 := five_multiplier_const hp 3 (by decide)
  have hc5 := five_multiplier_const hp 4 (by decide)
  set l₃ := p 0 (Pi.single 2 1) with hl₃
  set l₄ := p 0 (Pi.single 3 1) with hl₄
  set l₅ := p 0 (Pi.single 4 1) with hl₅
  have hg : ∀ i, ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (fiveFields i) (q t) := fun i t _ =>
    (fiveFields_contDiff i).differentiable (by simp) _
  have hu := hasDerivAt_optimalInput hg hq hp
  -- the input components and the state components
  have hq01 : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => q s 0) (r * sin (α t)) t ∧
      HasDerivAt (fun s => q s 1) (r * cos (α t)) t := by
    intro t ht
    have h := hq t ht
    rw [five_driftFree, hpolar t] at h
    exact ⟨by simpa using hasDerivAt_pi.1 h 0, by simpa using hasDerivAt_pi.1 h 1⟩
  have hOmega : ∀ t ∈ Icc 0 T, α' t = 2 * (l₃ + q t 0 * l₄ - q t 1 * l₅) := by
    intro t ht
    have h := hu t ht
    rw [five_optimalOmega, hpolar t] at h
    have h0 := hasDerivAt_pi.1 h 0
    have h1 := hasDerivAt_pi.1 h 1
    have e0 : HasDerivAt (fun s => optimalInput fiveFields q p s 0) (r * (cos (α t) * α' t)) t := by
      have := ((hα t).sin).const_mul r
      convert this using 1
      funext s
      simp [hpolar s]
    have e1 : HasDerivAt (fun s => optimalInput fiveFields q p s 1) (r * (-sin (α t) * α' t)) t := by
      have := ((hα t).cos).const_mul r
      convert this using 1
      funext s
      simp [hpolar s]
    have u0 := e0.unique h0
    have u1 := e1.unique h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at u0 u1
    rw [hc3 t ht, hc4 t ht, hc5 t ht] at u0 u1
    have key : r * α' t = r * (2 * (l₃ + q t 0 * l₄ - q t 1 * l₅)) := by
      have hs := sin_sq_add_cos_sq (α t)
      linear_combination (cos (α t)) * u0 - (sin (α t)) * u1 - r * α' t * hs +
        r * (2 * (l₃ + q t 0 * l₄ - q t 1 * l₅)) * hs
    exact mul_left_cancel₀ hr key
  have hdOmega : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => 2 * (l₃ + q s 0 * l₄ - q s 1 * l₅))
      (2 * r * (l₄ * sin (α t) - l₅ * cos (α t))) t := by
    intro t ht
    obtain ⟨h0, h1⟩ := hq01 t ht
    have := (((h0.mul_const l₄).const_add l₃).sub (h1.mul_const l₅)).const_mul 2
    convert this using 1
    ring
  refine fun t ht => ⟨hOmega t ht, hdOmega t ht, ?_⟩
  have hE : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => (2 * (l₃ + q s 0 * l₄ - q s 1 * l₅)) ^ 2 +
      4 * r * (l₄ * cos (α s) + l₅ * sin (α s))) 0 s := by
    intro s hs
    have h := ((hdOmega s hs).pow 2).add
      ((((hα s).cos.const_mul l₄).add ((hα s).sin.const_mul l₅)).const_mul (4 * r))
    convert h using 1
    rw [hOmega s hs]
    push_cast
    ring
  have hcont : ContinuousOn (fun s => (2 * (l₃ + q s 0 * l₄ - q s 1 * l₅)) ^ 2 +
      4 * r * (l₄ * cos (α s) + l₅ * sin (α s))) (Icc 0 T) := fun s hs =>
    (hE s hs).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun s hs => (hE s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht

end Examples
end RoboLean
