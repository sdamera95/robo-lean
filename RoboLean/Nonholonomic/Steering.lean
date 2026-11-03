import RoboLean.Nonholonomic.ChainedForm
import RoboLean.Nonholonomic.SteeringIntegrals
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Steering the one-chain system with sinusoids: MLS Algorithm 3 and Proposition 8.3

MLS Chapter 8, printed pp. 365–366: Algorithm 3 steers the one-chain system (8.7) coordinate by
coordinate; for `k ≥ 1` the inputs `u₁ = a sin 2πt`, `u₂ = b cos 2πkt` on `[0, 1]` give
`q_{k+2}(1) − q_{k+2}(0) = (a/4π)^k b/k!` and return `q₁, …, q_{k+1}` to their initial values
("produces motion only in `q_{k+2}` and not in `qⱼ`, `j < k + 2`, after one period", proof of
Proposition 8.3, p. 366), from any initial state ("the initial conditions generate extra terms …
and this integrates to zero", p. 366).

**Route.** For any trajectory on `[0, 1]` with `q₁(1) = q₁(0)` and continuous inputs, integration
by parts along `dqᵢ₊₁ = qᵢ dq₁` gives
`qⱼ(1) − qⱼ(0) = ∫₀¹ (q₁(0) − q₁(t))^{j−2}/(j−2)! u₂(t) dt` for `j ≥ 2`
(`IsTrajectory.chain_sub_eq_integral`); for the sinusoids `q₁(t) − q₁(0) = (a/2π)(1 − cos 2πt)`, and
the integrals of `SteeringIntegrals` evaluate the right-hand side. The book's proof tracks the
lowest-frequency term of each coordinate instead.

**Conventions.** Coordinates as in `ChainedForm`: `qᵢ` is the entry with index `i − 1`. Trajectories
are those of `IsTrajectory` on `[0, 1]` (continuous on `[0, 1]`, the equation away from finitely
many times); the input is any continuous function of time, here a sinusoid, not a piecewise constant
input.
-/

noncomputable section

open Set Filter Topology Real intervalIntegral

namespace RoboLean
namespace Nonholonomic

/-- **MLS Algorithm 3, p. 365: the inputs `u₁ = a sin 2πt`, `u₂ = b cos 2πkt`.** -/
def chainSinusoid (a b : ℝ) (k : ℕ) (t : ℝ) : Fin 2 → ℝ :=
  ![a * sin (2 * π * t), b * cos (2 * π * k * t)]

/-- **MLS p. 366:** the inputs of Algorithm 3 are continuous in time. -/
theorem continuous_chainSinusoid (a b : ℝ) (k : ℕ) : Continuous (chainSinusoid a b k) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [chainSinusoid] <;> fun_prop

/-- **MLS eq. (8.7), p. 364: `q₁(t) − q₁(0) = ∫₀ᵗ u₁`** along a trajectory on `[0, 1]` with
continuous inputs, for `t ∈ [0, 1]`. -/
theorem IsTrajectory.chain_sub_eq_integral_zero {n : ℕ} {u : ℝ → Fin 2 → ℝ} (hu : Continuous u)
    {x : ℝ → Fin n → ℝ} (hx : IsTrajectory (chainFields n) u 1 x) {i₀ : Fin n} (hi₀ : i₀.val = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : x t i₀ - x 0 i₀ = ∫ s in (0 : ℝ)..t, u s 0 := by
  obtain ⟨hc, S, hS⟩ := hx
  have hu0 : Continuous fun s => u s 0 := (continuous_apply 0).comp hu
  refine (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => x s i₀)
    (fun s => u s 0) ht.1 S.countable_toSet
    (((continuous_apply i₀).comp_continuousOn hc).mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => ?_) (hu0.intervalIntegrable 0 t)).symm
  have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.1, lt_of_lt_of_le hs.1.2 ht.2⟩
  have h := hasDerivAt_pi.1 (hS s hs1 hs.2) i₀
  rwa [chain_driftFree_of_val_eq_zero _ _ hi₀] at h

/-- **MLS pp. 365–366 (proof of Proposition 8.3), the integration-by-parts formula:** along a
trajectory of the one-chain system on `[0, 1]` with continuous inputs and `q₁(1) = q₁(0)`,
`qⱼ(1) − qⱼ(0) = ∫₀¹ (q₁(0) − q₁(t))^{j−2}/(j−2)! u₂(t) dt` for `j ≥ 2` (entry index
`j − 1 ≥ 1`). -/
theorem IsTrajectory.chain_sub_eq_integral {n : ℕ} {u : ℝ → Fin 2 → ℝ} (hu : Continuous u)
    {x : ℝ → Fin n → ℝ} (hx : IsTrajectory (chainFields n) u 1 x) {i₀ : Fin n} (hi₀ : i₀.val = 0)
    (hret : x 1 i₀ = x 0 i₀) (j : Fin n) (hj : 1 ≤ j.val) :
    x 1 j - x 0 j =
      ∫ t in (0 : ℝ)..1, (x 0 i₀ - x t i₀) ^ (j.val - 1) / ((j.val - 1).factorial : ℝ) * u t 1 := by
  obtain ⟨hc, S, hS⟩ := hx
  set y : ℕ → ℝ → ℝ := fun m t => if h : m < n then x t ⟨m, h⟩ else 0 with hy
  set w : ℝ → ℝ := fun t => x 0 i₀ - x t i₀ with hw
  set D : ℕ → ℝ → ℝ := fun m t => if m = 1 then u t 1 else u t 0 * y (m - 1) t with hDdef
  have hcomp : ∀ i : Fin n, ContinuousOn (fun t => x t i) (Icc 0 1) := fun i =>
    (continuous_apply i).comp_continuousOn hc
  have hyc : ∀ m, ContinuousOn (y m) (Icc 0 1) := by
    intro m
    by_cases h : m < n
    · simpa [hy, h] using hcomp ⟨m, h⟩
    · simpa [hy, h] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1))
  have hu0 : Continuous fun t => u t 0 := (continuous_apply 0).comp hu
  have hu1 : Continuous fun t => u t 1 := (continuous_apply 1).comp hu
  have hDc : ∀ m, ContinuousOn (D m) (Icc 0 1) := by
    intro m
    by_cases h : m = 1
    · simpa [hDdef, h] using hu1.continuousOn
    · have hD : D m = fun t => u t 0 * y (m - 1) t := by
        funext t
        simp [hDdef, h]
      rw [hD]
      exact hu0.continuousOn.mul (hyc (m - 1))
  have hwc : ContinuousOn w (Icc 0 1) := continuousOn_const.sub (hcomp i₀)
  have hcd : ∀ i : Fin n, ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ S →
      HasDerivAt (fun t => x t i) (driftFree (chainFields n) (x s) (u s) i) s :=
    fun i s hs hsS => hasDerivAt_pi.1 (hS s hs hsS) i
  have hwd : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ S → HasDerivAt w (-u s 0) s := by
    intro s hs hsS
    have h := (hcd i₀ s hs hsS).const_sub (x 0 i₀)
    rwa [chain_driftFree_of_val_eq_zero _ _ hi₀] at h
  have hyd : ∀ m, 1 ≤ m → m < n → ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ S → HasDerivAt (y m) (D m s) s := by
    intro m hm hmn s hs hsS
    have hfun : y m = fun t => x t ⟨m, hmn⟩ := by
      funext t
      simp [hy, hmn]
    rw [hfun]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      have h := hcd ⟨1, hmn⟩ s hs hsS
      rw [chain_driftFree_of_val_eq_one _ _ rfl] at h
      simpa [hDdef] using h
    · have h := hcd ⟨m, hmn⟩ s hs hsS
      rw [chain_driftFree_of_val_eq_succ (j := ⟨m - 1, by omega⟩) _ _ (by simp; omega)
        (by simp; omega)] at h
      convert h using 1
      simp [hDdef, hy, show m ≠ 1 by omega, show m - 1 < n by omega]
  have hw0 : w 0 = 0 := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hret]
  have step : ∀ m, 1 ≤ m → m + 1 < n → ∀ r : ℕ,
      ∫ t in (0 : ℝ)..1, w t ^ r / (r.factorial : ℝ) * D (m + 1) t =
        ∫ t in (0 : ℝ)..1, w t ^ (r + 1) / ((r + 1).factorial : ℝ) * D m t := by
    intro m hm hmn r
    have hP : ∀ s ∈ Ioo (0 : ℝ) 1 \ (S : Set ℝ),
        HasDerivAt (fun t => w t ^ (r + 1) / ((r + 1).factorial : ℝ) * y m t)
          (-(w s ^ r / (r.factorial : ℝ) * D (m + 1) s) +
            w s ^ (r + 1) / ((r + 1).factorial : ℝ) * D m s) s := by
      rintro s ⟨hs, hsS⟩
      have h1 := (((hwd s hs hsS).pow (r + 1)).div_const ((r + 1).factorial : ℝ)).mul
        (hyd m hm (by omega) s hs hsS)
      have hD1 : D (m + 1) s = u s 0 * y m s := by simp [hDdef, show m ≠ 0 by omega]
      simp only [Pi.pow_apply] at h1
      convert h1 using 1
      rw [hD1, Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    have hint1 : IntervalIntegrable (fun t => w t ^ r / (r.factorial : ℝ) * D (m + 1) t)
        MeasureTheory.volume 0 1 :=
      (((hwc.pow r).div_const _).mul (hDc _)).intervalIntegrable_of_Icc zero_le_one
    have hint2 : IntervalIntegrable
        (fun t => w t ^ (r + 1) / ((r + 1).factorial : ℝ) * D m t) MeasureTheory.volume 0 1 :=
      (((hwc.pow (r + 1)).div_const _).mul (hDc _)).intervalIntegrable_of_Icc zero_le_one
    have hneg : IntervalIntegrable (fun t => -(w t ^ r / (r.factorial : ℝ) * D (m + 1) t))
        MeasureTheory.volume 0 1 := hint1.neg
    have hftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (fun t => w t ^ (r + 1) / ((r + 1).factorial : ℝ) * y m t)
      (fun t => -(w t ^ r / (r.factorial : ℝ) * D (m + 1) t) +
        w t ^ (r + 1) / ((r + 1).factorial : ℝ) * D m t) zero_le_one
      S.countable_toSet (((hwc.pow (r + 1)).div_const _).mul (hyc m)) hP (hneg.add hint2)
    rw [intervalIntegral.integral_add hneg hint2, intervalIntegral.integral_neg] at hftc
    simp only [hw0, hw1, zero_pow (Nat.succ_ne_zero r), zero_div, zero_mul, sub_zero] at hftc
    linarith
  have iter : ∀ m, 1 ≤ m → m < n → ∀ r : ℕ,
      ∫ t in (0 : ℝ)..1, w t ^ r / (r.factorial : ℝ) * D m t =
        ∫ t in (0 : ℝ)..1, w t ^ (r + m - 1) / ((r + m - 1).factorial : ℝ) * u t 1 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _ r
      simp [hDdef]
    | succ m hm ih =>
      intro hmn r
      rw [step m hm hmn r, ih (by omega) (r + 1), show r + 1 + m - 1 = r + (m + 1) - 1 by omega]
  have hyj : ∀ t, y j.val t = x t j := fun t => by simp [hy, j.isLt]
  have hftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (y j.val) (D j.val)
    zero_le_one S.countable_toSet (hyc _) (fun s hs => hyd j.val hj j.isLt s hs.1 hs.2)
    ((hDc _).intervalIntegrable_of_Icc zero_le_one)
  rw [← hyj 1, ← hyj 0, ← hftc]
  have h := iter j.val hj j.isLt 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, zero_add] at h
  exact h

/-- **MLS Algorithm 3, p. 365, and Proposition 8.3, p. 366: steering `q_{k+2}`.** For `k ≥ 1`, every
trajectory of the one-chain system on `[0, 1]` with inputs `u₁ = a sin 2πt`, `u₂ = b cos 2πkt`,
from any initial state, returns `q₁, …, q_{k+1}` (indices `≤ k`) to their initial values and moves
`q_{k+2}` (index `k + 1`) by `(a/4π)^k b/k!`. -/
theorem IsTrajectory.chain_steering {n k : ℕ} (hk : 1 ≤ k) (a b : ℝ) {x : ℝ → Fin n → ℝ}
    (hx : IsTrajectory (chainFields n) (chainSinusoid a b k) 1 x) :
    (∀ j : Fin n, j.val ≤ k → x 1 j = x 0 j) ∧
      ∀ j : Fin n, j.val = k + 1 → x 1 j - x 0 j = (a / (4 * π)) ^ k * b / (k.factorial : ℝ) := by
  have hu := continuous_chainSinusoid a b k
  have hq1 : ∀ i₀ : Fin n, i₀.val = 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      x t i₀ - x 0 i₀ = a / (2 * π) * (1 - cos (2 * π * t)) := by
    intro i₀ hi₀ t ht
    rw [hx.chain_sub_eq_integral_zero hu hi₀ ht]
    have hc : (2 * π : ℝ) ≠ 0 := by positivity
    simp only [chainSinusoid, Matrix.cons_val_zero]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (f := fun x => sin x) hc, integral_sin, smul_eq_mul,
      mul_zero, cos_zero]
    field_simp
  have hret : ∀ i₀ : Fin n, i₀.val = 0 → x 1 i₀ = x 0 i₀ := by
    intro i₀ hi₀
    have h := hq1 i₀ hi₀ 1 ⟨zero_le_one, le_rfl⟩
    rw [mul_one, cos_two_pi, sub_self, mul_zero] at h
    linarith
  have hmove : ∀ j : Fin n, 1 ≤ j.val → x 1 j - x 0 j =
      (-(a / (2 * π))) ^ (j.val - 1) / ((j.val - 1).factorial : ℝ) * b *
        ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) ^ (j.val - 1) * cos (2 * π * k * t) := by
    intro j hj
    have hi₀ : (⟨0, by omega⟩ : Fin n).val = 0 := rfl
    rw [hx.chain_sub_eq_integral hu hi₀ (hret _ hi₀) j hj, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have h := hq1 _ hi₀ t ht
    simp only [chainSinusoid, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show x 0 ⟨0, by omega⟩ - x t ⟨0, by omega⟩ = -(a / (2 * π)) * (1 - cos (2 * π * t)) by
      linarith, mul_pow]
    ring
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rcases Nat.eq_zero_or_pos j.val with h0 | h0
    · exact hret j h0
    · have h := hmove j h0
      rw [integral_one_sub_cos_pow_mul_cos_of_lt (by omega), mul_zero] at h
      linarith
  · rw [hmove j (by omega), hj, Nat.add_sub_cancel, integral_one_sub_cos_pow_mul_cos_self]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_assoc, mul_comm b, ← mul_assoc, ← mul_pow]
    congr 2
    field_simp
    ring

/-- **MLS Algorithm 3, p. 365, `k = 1`:** with `u₁ = a sin 2πt`, `u₂ = b cos 2πt`, `q₁` and `q₂`
return and `q₃(1) − q₃(0) = ab/(4π)`. -/
theorem IsTrajectory.chain_steering_one {n : ℕ} (a b : ℝ) {x : ℝ → Fin n → ℝ}
    (hx : IsTrajectory (chainFields n) (chainSinusoid a b 1) 1 x) :
    (∀ j : Fin n, j.val ≤ 1 → x 1 j = x 0 j) ∧
      ∀ j : Fin n, j.val = 2 → x 1 j - x 0 j = a * b / (4 * π) := by
  obtain ⟨h1, h2⟩ := hx.chain_steering le_rfl a b
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

/-- **MLS Algorithm 3, p. 365, `k = 2`:** with `u₁ = a sin 2πt`, `u₂ = b cos 4πt`, `q₁, q₂, q₃`
return and `q₄(1) − q₄(0) = a²b/(32π²)`. -/
theorem IsTrajectory.chain_steering_two {n : ℕ} (a b : ℝ) {x : ℝ → Fin n → ℝ}
    (hx : IsTrajectory (chainFields n) (chainSinusoid a b 2) 1 x) :
    (∀ j : Fin n, j.val ≤ 2 → x 1 j = x 0 j) ∧
      ∀ j : Fin n, j.val = 3 → x 1 j - x 0 j = a ^ 2 * b / (32 * π ^ 2) := by
  obtain ⟨h1, h2⟩ := hx.chain_steering (by norm_num) a b
  refine ⟨h1, fun j hj => ?_⟩
  rw [h2 j hj]
  simp only [Nat.factorial_two, Nat.cast_ofNat]
  field_simp
  ring

/-- **MLS Proposition 8.3, p. 366, existence of the steering trajectory:** for every initial state
and every `k`, `a`, `b`, the one-chain system has a trajectory on `[0, 1]` under the inputs of
Algorithm 3. -/
theorem chain_exists_trajectory_sinusoid (n k : ℕ) (a b : ℝ) (q₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, x 0 = q₀ ∧ IsTrajectory (chainFields n) (chainSinusoid a b k) 1 x := by
  obtain ⟨x, hx0, hx⟩ := chain_exists_solution n (continuous_chainSinusoid a b k) q₀
  exact ⟨x, hx0, IsTrajectory.of_hasDerivAt 1 hx⟩

end Nonholonomic
end RoboLean
