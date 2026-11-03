import RoboLean.Examples.NonholonomicBrockett
import RoboLean.Nonholonomic.OptimalInputs
import RoboLean.Nonholonomic.Nilpotent

/-!
# The optimal inputs of Brockett's system by the method of Proposition 8.4: MLS Chapter 8,
# Exercise 9

MLS Chapter 8, Exercise 9, printed p. 393: "Apply the methods of Proposition 8.16 to solve the
optimal control inputs for the model control system we studied in Section 2, namely
`q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₁u₂ − q₂u₁`." No Proposition 8.16 exists; the method meant is that of
Proposition 8.4 (p. 373), `u̇ = Ω(q, p)u` with `Ω_{ij} = pᵀ[gᵢ, gⱼ]`.

**What is formalized.** Along a curve `(q, p)` on `[0, T]` satisfying the necessary conditions
(8.12)–(8.13) for (8.2) (hypotheses, as in the library's Proposition 8.4):
* `Ω(q, p) = [[0, 2p₃], [−2p₃, 0]]` with `p₃ = p(e₃)`, and `p₃` is constant, since the fields do
  not depend on `q₃`;
* hence `u(t) = e^{Λt}u(0)` with `Λ = [[0, −λ], [λ, 0]]`, `λ = −2p₃(0)`, the stationary input of
  p. 359 (`brockettInput`);
* from `q(0) = 0` the state is the library's `brockettState λ u(0)`, so `q₁(1) = q₂(1) = 0` with
  `u(0) ≠ 0` forces `λ = 2nπ` and `q₃(1) = ‖u(0)‖²/(2nπ)`, the analysis of p. 360 (whose cost
  comparison is the library's `brockett_cost_ge`).
-/

noncomputable section

open Set VectorField Matrix Real
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

private theorem brockettFields_isBase (i : Fin 2) : IsBase (brockettFields i) := by
  intro q v h0 h1
  fin_cases i <;> ext j <;> fin_cases j <;> simp [brockettFields, brockettG1, brockettG2, h0, h1]

private theorem brockettFields_differentiable (i : Fin 2) (q : Fin 3 → ℝ) :
    DifferentiableAt ℝ (brockettFields i) q := by
  refine differentiableAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [brockettFields, brockettG1, brockettG2] <;> fun_prop

/-- **MLS Chapter 8, Exercise 9, p. 393, with (8.16), p. 373: `Ω(q, p)` for Brockett's system,**
`Ω₁₂ = p[g₁, g₂] = 2p₃` with `p₃ = p(e₃)`. -/
theorem brockett_optimalOmega (q : Fin 3 → ℝ) (p : (Fin 3 → ℝ) →L[ℝ] ℝ) :
    optimalOmega brockettFields q p =
      !![0, 2 * p (Pi.single 2 1); -(2 * p (Pi.single 2 1)), 0] := by
  have hv : (![0, 0, 2] : Fin 3 → ℝ) = (2 : ℝ) • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp
  have h01 : p (lieBracket ℝ (brockettFields 0) (brockettFields 1) q) = 2 * p (Pi.single 2 1) := by
    rw [show brockettFields 0 = brockettG1 from rfl, show brockettFields 1 = brockettG2 from rfl,
      brockett_lieBracket, hv, map_smul, smul_eq_mul]
  have h10 : p (lieBracket ℝ (brockettFields 1) (brockettFields 0) q) =
      -(2 * p (Pi.single 2 1)) := by
    rw [lieBracket_swap, map_neg, h01]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [optimalOmega, lieBracket_self, h01, h10]

/-- **MLS Chapter 8, Exercise 9, p. 393: `p₃` is constant** along a curve satisfying (8.12), since
`∂H/∂q₃ = 0` (the fields do not depend on `q₃`). -/
theorem brockett_multiplier_const {q : ℝ → Fin 3 → ℝ} {p : ℝ → (Fin 3 → ℝ) →L[ℝ] ℝ} {T : ℝ}
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput brockettFields q p t i • (p t).comp (fderiv ℝ (brockettFields i) (q t))) t) :
    ∀ t ∈ Icc 0 T, p t (Pi.single 2 1) = p 0 (Pi.single 2 1) := by
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => p s (Pi.single 2 1)) 0 t := by
    intro t ht
    have h := (hp t ht).clm_apply (hasDerivAt_const t (Pi.single 2 1 : Fin 3 → ℝ))
    convert h using 1
    have hz : ∀ i, fderiv ℝ (brockettFields i) (q t) (Pi.single 2 1) = 0 := fun i =>
      fderiv_apply_eq_zero_of_isBase (brockettFields_isBase i) (q t) (by simp) (by simp)
    simp [hz]
  intro t ht
  refine constant_of_has_deriv_right_zero (f := fun s => p s (Pi.single 2 1)) ?_ ?_ t ht
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt

/-- **MLS Chapter 8, Exercise 9, p. 393: the optimal input is the stationary input of p. 359,**
`u(t) = e^{Λt}u(0)`, `Λ = [[0, −λ], [λ, 0]]`, `λ = −2p₃(0)`, on `[0, T]`, along a curve satisfying
(8.12)–(8.13) for (8.2). -/
theorem brockett_optimalInput_eq {q : ℝ → Fin 3 → ℝ} {p : ℝ → (Fin 3 → ℝ) →L[ℝ] ℝ} {T : ℝ}
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q
      (driftFree brockettFields (q t) (optimalInput brockettFields q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput brockettFields q p t i • (p t).comp (fderiv ℝ (brockettFields i) (q t))) t) :
    ∀ t ∈ Icc 0 T, optimalInput brockettFields q p t =
      brockettInput (-2 * p 0 (Pi.single 2 1)) (optimalInput brockettFields q p 0) t := by
  set u := optimalInput brockettFields q p
  set lam := -2 * p 0 (Pi.single 2 1)
  have hu := hasDerivAt_optimalInput (fun i t _ => brockettFields_differentiable i (q t)) hq hp
  have hc := brockett_multiplier_const hp
  have hu' : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => u s 0) (-lam * u t 1) t ∧
      HasDerivAt (fun s => u s 1) (lam * u t 0) t := by
    intro t ht
    have h := hu t ht
    rw [brockett_optimalOmega, hc t ht] at h
    refine ⟨?_, ?_⟩
    · convert (hasDerivAt_pi.1 h) 0 using 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, lam, u]
    · convert (hasDerivAt_pi.1 h) 1 using 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, lam, u]
  have hl : ∀ t, HasDerivAt (fun s => lam * s) lam t := fun t => by
    simpa using (hasDerivAt_id t).const_mul lam
  -- the rotated input `w = e^{−Λt}u` is constant
  have hw : ∀ i : Fin 2, ∀ t ∈ Icc 0 T,
      ![u t 0 * cos (lam * t) + u t 1 * sin (lam * t),
        -(u t 0 * sin (lam * t)) + u t 1 * cos (lam * t)] i = u 0 i := by
    intro i
    have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => ![u s 0 * cos (lam * s) + u s 1 * sin (lam * s),
        -(u s 0 * sin (lam * s)) + u s 1 * cos (lam * s)] i) 0 t := by
      intro t ht
      obtain ⟨h0, h1⟩ := hu' t ht
      fin_cases i
      · convert (h0.mul (hl t).cos).add (h1.mul (hl t).sin) using 1
        · funext s
          simp
        · ring
      · convert (h0.mul (hl t).sin).neg.add (h1.mul (hl t).cos) using 1
        · funext s
          simp
        · ring
    intro t ht
    have h := constant_of_has_deriv_right_zero (f := fun s => ![u s 0 * cos (lam * s) +
        u s 1 * sin (lam * s), -(u s 0 * sin (lam * s)) + u s 1 * cos (lam * s)] i)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
    rw [h]
    fin_cases i <;> simp
  intro t ht
  have w0 := hw 0 t ht
  have w1 := hw 1 t ht
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at w0 w1
  funext i
  fin_cases i
  · show u t 0 = u 0 0 * cos (lam * t) - u 0 1 * sin (lam * t)
    rw [← w0, ← w1]
    linear_combination (-u t 0) * sin_sq_add_cos_sq (lam * t)
  · show u t 1 = u 0 0 * sin (lam * t) + u 0 1 * cos (lam * t)
    rw [← w0, ← w1]
    linear_combination (-u t 1) * sin_sq_add_cos_sq (lam * t)

/-- **MLS Chapter 8, Exercise 9, p. 393, with p. 360: the state from the origin.** Along a curve
satisfying (8.12)–(8.13) for (8.2) with `q(0) = 0` and `λ = −2p₃(0) ≠ 0`, the state is
`brockettState λ u(0)` on `[0, T]`; for `T = 1` with `q₁(1) = q₂(1) = 0` and `u(0) ≠ 0`, `λ = 2nπ`
for an integer `n` and `q₃(1) = ‖u(0)‖²/(2nπ)`. -/
theorem brockett_optimal_state {q : ℝ → Fin 3 → ℝ} {p : ℝ → (Fin 3 → ℝ) →L[ℝ] ℝ} {T : ℝ}
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q
      (driftFree brockettFields (q t) (optimalInput brockettFields q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput brockettFields q p t i • (p t).comp (fderiv ℝ (brockettFields i) (q t))) t)
    (hq0 : q 0 = 0) (hlam : -2 * p 0 (Pi.single 2 1) ≠ 0) :
    (∀ t ∈ Icc 0 T, q t = brockettState (-2 * p 0 (Pi.single 2 1))
      (optimalInput brockettFields q p 0) t) ∧
    (T = 1 → q 1 0 = 0 → q 1 1 = 0 → optimalInput brockettFields q p 0 ≠ 0 →
      ∃ n : ℤ, -2 * p 0 (Pi.single 2 1) = 2 * n * π ∧
        q 1 2 = (optimalInput brockettFields q p 0 0 ^ 2 +
          optimalInput brockettFields q p 0 1 ^ 2) / (2 * n * π)) := by
  set lam := -2 * p 0 (Pi.single 2 1)
  set u₀ := optimalInput brockettFields q p 0
  have hu := brockett_optimalInput_eq hq hp
  have hS : ∀ t, HasDerivAt (brockettState lam u₀)
      (driftFree brockettFields (brockettState lam u₀ t) (brockettInput lam u₀ t)) t :=
    brockettState_hasDerivAt hlam u₀
  have hqc : ∀ i, ∀ t ∈ Icc 0 T, HasDerivAt (fun s => q s i)
      (driftFree brockettFields (q t) (brockettInput lam u₀ t) i) t := by
    intro i t ht
    have h := (hasDerivAt_pi.1 (hq t ht)) i
    rwa [hu t ht] at h
  have hSc : ∀ i, ∀ t, HasDerivAt (fun s => brockettState lam u₀ s i)
      (driftFree brockettFields (brockettState lam u₀ t) (brockettInput lam u₀ t) i) t :=
    fun i t => (hasDerivAt_pi.1 (hS t)) i
  have heq : ∀ i : Fin 3, (∀ t ∈ Icc 0 T, driftFree brockettFields (q t) (brockettInput lam u₀ t) i =
      driftFree brockettFields (brockettState lam u₀ t) (brockettInput lam u₀ t) i) →
      ∀ t ∈ Icc 0 T, q t i = brockettState lam u₀ t i := by
    intro i hi
    refine eq_of_has_deriv_right_eq (f' := fun t =>
        driftFree brockettFields (brockettState lam u₀ t) (brockettInput lam u₀ t) i)
      (fun t ht => ?_) (fun t _ => (hSc i t).hasDerivWithinAt)
      (fun t ht => (hqc i t ht).continuousAt.continuousWithinAt)
      (fun t _ => (hSc i t).continuousAt.continuousWithinAt) ?_
    · rw [← hi t (Ico_subset_Icc_self ht)]
      exact (hqc i t (Ico_subset_Icc_self ht)).hasDerivWithinAt
    · rw [hq0, brockettState_zero]
  have h0 := heq 0 (fun t _ => by simp [brockett_driftFree])
  have h1 := heq 1 (fun t _ => by simp [brockett_driftFree])
  have h2 := heq 2 (fun t ht => by simp [brockett_driftFree, h0 t ht, h1 t ht])
  have hall : ∀ t ∈ Icc 0 T, q t = brockettState lam u₀ t := by
    intro t ht
    ext i
    fin_cases i
    · exact h0 t ht
    · exact h1 t ht
    · exact h2 t ht
  refine ⟨hall, fun hT hA hB hu0 => ?_⟩
  subst hT
  have h1' := hall 1 ⟨zero_le_one, le_rfl⟩
  rw [h1'] at hA hB
  obtain ⟨n, hn⟩ := (brockettState_one_eq_zero_iff hlam hu0).1 ⟨hA, hB⟩
  refine ⟨n, hn, ?_⟩
  rw [h1', hn, brockettState_one n]
  rfl

end Examples
end RoboLean
