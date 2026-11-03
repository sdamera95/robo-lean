import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of sinusoids over one period (MLS Chapter 8, §2.3)

MLS Chapter 8, printed pp. 365–366 (Algorithm 3 and the proof of Proposition 8.3): the steering
computations for the one-chain system rest on integrals over one period `[0, 1]` of products of
`1 − cos 2πt` with `cos 2πkt`: "the only way to have `qᵢ(1) ≠ qᵢ(0)` is to have `qᵢ` have a
component at frequency zero" (p. 366). The two facts used are
`∫₀¹ (1 − cos 2πt)^i cos 2πkt dt = 0` for `i < k` and `= (−1/2)^k` for `i = k`.

**Conventions.** Integrals are Mathlib's interval integrals `∫ t in (0:ℝ)..1`; frequencies are
natural numbers.
-/

noncomputable section

open Real intervalIntegral

namespace RoboLean
namespace Nonholonomic

/-- **MLS p. 366: a sinusoid of nonzero integer frequency integrates to zero over a period,**
`∫₀¹ cos 2πkt dt = 0` for `k ≥ 1`. -/
theorem integral_cos_two_pi_mul {k : ℕ} (hk : 1 ≤ k) :
    ∫ t in (0 : ℝ)..1, cos (2 * π * k * t) = 0 := by
  have hc : (2 * π * k : ℝ) ≠ 0 :=
    mul_ne_zero (by positivity) (by exact_mod_cast (show k ≠ 0 by omega))
  rw [intervalIntegral.integral_comp_mul_left (f := fun x => cos x) hc, integral_cos, mul_one,
    show 2 * π * (k : ℝ) = ((2 * k : ℕ) : ℝ) * π by push_cast; ring, sin_nat_mul_pi]
  simp

/-- **MLS p. 366:** `∫₀¹ sin 2πkt dt = 0` for every natural `k`. -/
theorem integral_sin_two_pi_mul (k : ℕ) :
    ∫ t in (0 : ℝ)..1, sin (2 * π * k * t) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hc : (2 * π * k : ℝ) ≠ 0 :=
    mul_ne_zero (by positivity) (by exact_mod_cast hk.ne')
  rw [intervalIntegral.integral_comp_mul_left (f := fun x => sin x) hc, integral_sin, mul_one,
    show 2 * π * (k : ℝ) = (k : ℝ) * (2 * π) by ring, cos_nat_mul_two_pi]
  simp

/-- The integral `∫₀¹ (1 − cos 2πt)^i cos 2πmt dt` (supporting definition for MLS p. 366). -/
private def periodIntegral (i m : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) ^ i * cos (2 * π * m * t)

/-- Lowering the power by the product formula `cos a cos b = (cos(a + b) + cos(a − b))/2`
(supporting lemma for MLS p. 366). -/
private theorem periodIntegral_succ_succ (i m : ℕ) :
    periodIntegral (i + 1) (m + 1) = periodIntegral i (m + 1) - (1 / 2) * periodIntegral i (m + 2) -
      (1 / 2) * periodIntegral i m := by
  have key : ∀ t : ℝ, (1 - cos (2 * π * t)) ^ (i + 1) * cos (2 * π * ((m + 1 : ℕ) : ℝ) * t) =
      (1 - cos (2 * π * t)) ^ i * cos (2 * π * ((m + 1 : ℕ) : ℝ) * t) -
        (1 / 2) * ((1 - cos (2 * π * t)) ^ i * cos (2 * π * ((m + 2 : ℕ) : ℝ) * t)) -
        (1 / 2) * ((1 - cos (2 * π * t)) ^ i * cos (2 * π * (m : ℝ) * t)) := by
    intro t
    have h1 : cos (2 * π * ((m + 2 : ℕ) : ℝ) * t) =
        cos (2 * π * ((m + 1 : ℕ) : ℝ) * t + 2 * π * t) := by
      congr 1
      push_cast
      ring
    have h2 : cos (2 * π * (m : ℝ) * t) = cos (2 * π * ((m + 1 : ℕ) : ℝ) * t - 2 * π * t) := by
      congr 1
      push_cast
      ring
    rw [h1, h2, cos_add, cos_sub, pow_succ]
    ring
  have hint : ∀ j : ℕ, IntervalIntegrable
      (fun t : ℝ => (1 - cos (2 * π * t)) ^ i * cos (2 * π * (j : ℝ) * t))
      MeasureTheory.volume 0 1 :=
    fun j => (by fun_prop : Continuous fun t : ℝ =>
      (1 - cos (2 * π * t)) ^ i * cos (2 * π * (j : ℝ) * t)).intervalIntegrable 0 1
  simp only [periodIntegral]
  simp_rw [key]
  rw [intervalIntegral.integral_sub ((hint _).sub ((hint _).const_mul _)) ((hint _).const_mul _),
    intervalIntegral.integral_sub (hint _) ((hint _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **MLS p. 366 (proof of Proposition 8.3): lower powers carry no zero-frequency term,**
`∫₀¹ (1 − cos 2πt)^i cos 2πkt dt = 0` for `i < k`. -/
theorem integral_one_sub_cos_pow_mul_cos_of_lt {i k : ℕ} (h : i < k) :
    ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) ^ i * cos (2 * π * k * t) = 0 := by
  change periodIntegral i k = 0
  induction i generalizing k with
  | zero =>
    simp only [periodIntegral, pow_zero, one_mul]
    exact integral_cos_two_pi_mul (by omega)
  | succ i ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [periodIntegral_succ_succ, ih (by omega), ih (by omega), ih (by omega)]
    ring

/-- **MLS p. 366 (proof of Proposition 8.3): the zero-frequency term,**
`∫₀¹ (1 − cos 2πt)^k cos 2πkt dt = (−1/2)^k`. -/
theorem integral_one_sub_cos_pow_mul_cos_self (k : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) ^ k * cos (2 * π * k * t) = (-1 / 2 : ℝ) ^ k := by
  change periodIntegral k k = _
  induction k with
  | zero => simp [periodIntegral]
  | succ k ih =>
    rw [periodIntegral_succ_succ, ih,
      show periodIntegral k (k + 1) = 0 from integral_one_sub_cos_pow_mul_cos_of_lt (by omega),
      show periodIntegral k (k + 2) = 0 from integral_one_sub_cos_pow_mul_cos_of_lt (by omega)]
    ring

end Nonholonomic
end RoboLean
