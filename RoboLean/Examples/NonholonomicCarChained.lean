import RoboLean.Nonholonomic.ChainedForm
import RoboLean.Examples.NonholonomicGrowth

/-!
# The kinematic car in chained form: MLS Example 8.3

MLS Chapter 8, Example 8.3, printed p. 371: "we rewrite the kinematic equations as `ẋ = u₁`,
`ẏ = tan θ u₁`, `θ̇ = (1/l) tan φ u₁`, `φ̇ = u₂`", and with `h₁ = x`, `h₂ = y` the change of
coordinates `z₁ = x`, `z₂ = (1/l) sec² θ tan φ`, `z₃ = tan θ`, `z₄ = y` and the input change
`u₁ = v₁`, `u₂ = −(2/l) sin² φ tan θ v₁ + l cos² θ cos² φ v₂` "give a one-chain system" (8.7).

**Source observation.** The printed conversion is correct for the printed rewritten system. That
system is not the car (7.14) of Example 7.5 (p. 337) after an input change: from (7.14),
`ẋ = cos θ u₁`, so `ẋ = w₁` with `w₁ = cos θ u₁` gives `θ̇ = (1/l) sec θ tan φ w₁`, with a factor
`sec θ` the rewritten system lacks. For (7.14) itself the same `z₁ = x`, `z₃ = tan θ`, `z₄ = y`
work with `z₂ = (1/l) sec³ θ tan φ`, `v₁ = cos θ u₁` and
`u₂ = −(3/l) sin² φ sec θ tan θ v₁ + l cos³ θ cos² φ v₂` (corrected printing, derived here).

**What is formalized.** Coordinates `q = (x, y, θ, φ)` as in `NonholonomicCar` (`q 0 = x`,
`q 1 = y`, `q 2 = θ`, `q 3 = φ`); domain `cos θ ≠ 0`, `cos φ ≠ 0`, `l ≠ 0` (not printed). Along any
curve differentiable at `t` and solving the car's equation at `t` with the transformed input, the
transformed state solves the one-chain system (8.7) with `n = 4` at `t`; the input transformations
are invertible on the domain. Convention checks of the printed formulas; nothing here concerns a
vehicle.
-/

noncomputable section

open Real Set
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Example 8.3, p. 371, the rewritten system as printed:
`g₁ = (1, tan θ, (1/l) tan φ, 0)`.** -/
def carRewrittenG1 (l : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![1, tan (q 2), tan (q 3) / l, 0]

/-- **MLS Example 8.3, p. 371: the input fields `(g₁, g₂)` of the rewritten system** (`g₂` of
(7.14)). -/
def carRewrittenFields (l : ℝ) : Fin 2 → (Fin 4 → ℝ) → Fin 4 → ℝ := ![carRewrittenG1 l, carG2]

/-- **MLS Example 8.3, p. 371: `z = (x, (1/l) sec² θ tan φ, tan θ, y)`.** -/
def carChainedState (l : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![q 0, tan (q 3) / (l * cos (q 2) ^ 2), tan (q 2), q 1]

/-- **MLS Example 8.3, p. 371: `u₁ = v₁`, `u₂ = −(2/l) sin² φ tan θ v₁ + l cos² θ cos² φ v₂`.** -/
def carChainedInput (l : ℝ) (q : Fin 4 → ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![v 0, -(2 / l) * sin (q 3) ^ 2 * tan (q 2) * v 0 + l * cos (q 2) ^ 2 * cos (q 3) ^ 2 * v 1]

/-- **MLS Example 8.3, p. 371: the rewritten car becomes the one-chain system (8.7).** If a curve
`q` solves the rewritten system at `t` with the input `u = β(q) v`, where `cos θ ≠ 0`, `cos φ ≠ 0`,
then `z = (x, (1/l) sec² θ tan φ, tan θ, y)` solves `ż₁ = v₁`, `ż₂ = v₂`, `ż₃ = z₂ v₁`, `ż₄ = z₃ v₁`
at `t`. -/
theorem carRewritten_hasDerivAt_chained {l : ℝ} (hl : l ≠ 0) {q : ℝ → Fin 4 → ℝ}
    {v : ℝ → Fin 2 → ℝ} {t : ℝ} (hθ : cos (q t 2) ≠ 0) (hφ : cos (q t 3) ≠ 0)
    (hq : HasDerivAt q (driftFree (carRewrittenFields l) (q t) (carChainedInput l (q t) (v t))) t) :
    HasDerivAt (fun s => carChainedState l (q s))
      (driftFree (chainFields 4) (carChainedState l (q t)) (v t)) t := by
  have hc : ∀ i, HasDerivAt (fun s => q s i)
      (driftFree (carRewrittenFields l) (q t) (carChainedInput l (q t) (v t)) i) t := fun i =>
    hasDerivAt_pi.1 hq i
  have hx := hc 0
  have hy := hc 1
  have hθ' := hc 2
  have hφ' := hc 3
  simp only [driftFree, Fin.sum_univ_two, carRewrittenFields, carRewrittenG1, carG2,
    carChainedInput, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.head_cons, Matrix.tail_cons, mul_zero, mul_one, add_zero, zero_add] at hx hy hθ' hφ'
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · rw [chain_driftFree_of_val_eq_zero _ _ rfl]
    simpa [carChainedState] using hx
  · rw [chain_driftFree_of_val_eq_one _ _ rfl]
    have hden : l * cos (q t 2) ^ 2 ≠ 0 := mul_ne_zero hl (pow_ne_zero 2 hθ)
    show HasDerivAt (fun s => tan (q s 3) / (l * cos (q s 2) ^ 2)) _ t
    have h0 := (Real.hasDerivAt_tan hφ).comp t hφ'
    have h : HasDerivAt (fun s => tan (q s 3) / (l * cos (q s 2) ^ 2)) _ t :=
      h0.div ((hθ'.cos.pow 2).const_mul l) hden
    convert h using 1
    simp only [Function.comp_apply]
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    field_simp
    ring
  · rw [chain_driftFree_of_val_eq_succ (j := 1) _ _ rfl (by norm_num)]
    show HasDerivAt (fun s => tan (q s 2)) _ t
    have h0 := (Real.hasDerivAt_tan hθ).comp t hθ'
    have h : HasDerivAt (fun s => tan (q s 2)) _ t := h0
    convert h using 1
    simp only [carChainedState, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [tan_eq_sin_div_cos]
    field_simp
  · rw [chain_driftFree_of_val_eq_succ (j := 2) _ _ rfl (by norm_num)]
    show HasDerivAt (fun s => q s 1) _ t
    convert hy using 1
    simp [carChainedState]

/-- **MLS Example 8.3, p. 371:** the printed input change is invertible where `cos θ ≠ 0`,
`cos φ ≠ 0`: every input `u` of the rewritten car is `β(q) v` for one `v`. -/
theorem carChainedInput_bijective {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hθ : cos (q 2) ≠ 0)
    (hφ : cos (q 3) ≠ 0) : Function.Bijective (carChainedInput l q) := by
  have hb : l * cos (q 2) ^ 2 * cos (q 3) ^ 2 ≠ 0 := by positivity
  refine ⟨fun v w h => ?_, fun u => ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [carChainedInput] at h0 h1
    rw [h0] at h1
    have h1' : l * cos (q 2) ^ 2 * cos (q 3) ^ 2 * (v 1 - w 1) = 0 := by linarith
    have h2 := (mul_eq_zero.1 h1').resolve_left hb
    ext i
    fin_cases i
    · exact h0
    · simp
      linarith
  · refine ⟨![u 0, (u 1 + (2 / l) * sin (q 3) ^ 2 * tan (q 2) * u 0) /
      (l * cos (q 2) ^ 2 * cos (q 3) ^ 2)], ?_⟩
    ext i
    fin_cases i
    · simp [carChainedInput]
    · simp [carChainedInput]
      field_simp
      ring

/-- **MLS Example 8.3, p. 371, corrected printing for (7.14): `z₂ = (1/l) sec³ θ tan φ`,**
`z = (x, (1/l) sec³ θ tan φ, tan θ, y)`. -/
def carChainedState' (l : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![q 0, tan (q 3) / (l * cos (q 2) ^ 3), tan (q 2), q 1]

/-- **MLS Example 8.3, p. 371, corrected printing for (7.14):** `u₁ = sec θ v₁` (that is,
`v₁ = cos θ u₁`) and `u₂ = −(3/l) sin² φ sec θ tan θ v₁ + l cos³ θ cos² φ v₂`. -/
def carChainedInput' (l : ℝ) (q : Fin 4 → ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![v 0 / cos (q 2),
    -(3 / l) * sin (q 3) ^ 2 * tan (q 2) / cos (q 2) * v 0 +
      l * cos (q 2) ^ 3 * cos (q 3) ^ 2 * v 1]

/-- **MLS Example 8.3, p. 371, corrected printing: the car (7.14) becomes the one-chain system
(8.7).** If a curve `q` solves (7.14) at `t` with the input `u = β(q) v` of `carChainedInput'`,
where `cos θ ≠ 0`, `cos φ ≠ 0`, then `z = (x, (1/l) sec³ θ tan φ, tan θ, y)` solves (8.7) with
`n = 4` at `t`. -/
theorem car_hasDerivAt_chained {l : ℝ} (hl : l ≠ 0) {q : ℝ → Fin 4 → ℝ} {v : ℝ → Fin 2 → ℝ} {t : ℝ}
    (hθ : cos (q t 2) ≠ 0) (hφ : cos (q t 3) ≠ 0)
    (hq : HasDerivAt q (driftFree (carFields l) (q t) (carChainedInput' l (q t) (v t))) t) :
    HasDerivAt (fun s => carChainedState' l (q s))
      (driftFree (chainFields 4) (carChainedState' l (q t)) (v t)) t := by
  have hc : ∀ i, HasDerivAt (fun s => q s i)
      (driftFree (carFields l) (q t) (carChainedInput' l (q t) (v t)) i) t := fun i =>
    hasDerivAt_pi.1 hq i
  have hx := hc 0
  have hy := hc 1
  have hθ' := hc 2
  have hφ' := hc 3
  simp only [driftFree, Fin.sum_univ_two, carFields, carG1, carG2,
    carChainedInput', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.head_cons, Matrix.tail_cons, mul_zero, mul_one, add_zero, zero_add] at hx hy hθ' hφ'
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · rw [chain_driftFree_of_val_eq_zero _ _ rfl]
    show HasDerivAt (fun s => q s 0) _ t
    convert hx using 1
    field_simp
  · rw [chain_driftFree_of_val_eq_one _ _ rfl]
    have hden : l * cos (q t 2) ^ 3 ≠ 0 := mul_ne_zero hl (pow_ne_zero 3 hθ)
    show HasDerivAt (fun s => tan (q s 3) / (l * cos (q s 2) ^ 3)) _ t
    have h0 := (Real.hasDerivAt_tan hφ).comp t hφ'
    have h : HasDerivAt (fun s => tan (q s 3) / (l * cos (q s 2) ^ 3)) _ t :=
      h0.div ((hθ'.cos.pow 3).const_mul l) hden
    convert h using 1
    simp only [Function.comp_apply]
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    field_simp
    ring
  · rw [chain_driftFree_of_val_eq_succ (j := 1) _ _ rfl (by norm_num)]
    show HasDerivAt (fun s => tan (q s 2)) _ t
    have h0 := (Real.hasDerivAt_tan hθ).comp t hθ'
    have h : HasDerivAt (fun s => tan (q s 2)) _ t := h0
    convert h using 1
    simp only [carChainedState', Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [tan_eq_sin_div_cos]
    field_simp
  · rw [chain_driftFree_of_val_eq_succ (j := 2) _ _ rfl (by norm_num)]
    show HasDerivAt (fun s => q s 1) _ t
    convert hy using 1
    simp only [carChainedState', Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [tan_eq_sin_div_cos]
    field_simp

/-- **MLS Example 8.3, p. 371, corrected printing:** the input change for (7.14) is invertible where
`cos θ ≠ 0`, `cos φ ≠ 0`. -/
theorem carChainedInput'_bijective {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hθ : cos (q 2) ≠ 0)
    (hφ : cos (q 3) ≠ 0) : Function.Bijective (carChainedInput' l q) := by
  have hb : l * cos (q 2) ^ 3 * cos (q 3) ^ 2 ≠ 0 := by positivity
  refine ⟨fun v w h => ?_, fun u => ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [carChainedInput'] at h0 h1
    have h0' : v 0 = w 0 := by
      exact (div_left_inj' hθ).1 h0
    rw [h0'] at h1
    have h1' : l * cos (q 2) ^ 3 * cos (q 3) ^ 2 * (v 1 - w 1) = 0 := by linarith
    have h2 := (mul_eq_zero.1 h1').resolve_left hb
    ext i
    fin_cases i
    · exact h0'
    · simp
      linarith
  · refine ⟨![u 0 * cos (q 2), (u 1 + (3 / l) * sin (q 3) ^ 2 * tan (q 2) * u 0) /
      (l * cos (q 2) ^ 3 * cos (q 3) ^ 2)], ?_⟩
    ext i
    fin_cases i
    · simp [carChainedInput']
      field_simp
    · simp [carChainedInput']
      field_simp
      ring

end Examples
end RoboLean
