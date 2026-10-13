import RoboLean.Control.LinearizationTimeVarying

/-!
# A time-varying linearization: `ż = −(1 + sin t) z` (MLS Theorem 4.6, p. 184)

**The system.** On `ℝⁿ` (sup norm), the linear time-varying system `ż = A(t)z` with
`A(t) = −(1 + sin t) I` (`periodicRate`). Its decay rate `1 + sin t` vanishes at
`t = 3π/2 + 2kπ`, so no constant matrix describes it, yet
`Φ(t, s) = e^{−(t − s) + cos t − cos s} I` (`periodicRateTransition`) satisfies
`‖Φ(t, s)‖ ≤ e² e^{−(t − s)}` for `s ≤ t`. The nonlinear system
`ẋᵢ = −(1 + sin t) sin xᵢ` (`periodicSineField`) has `ż = A(t)z` as its uniform linearization
(4.39), since `|sin y − y| ≤ |y|³` for `|y| ≤ 1`.

**What is proved here.**

* `Φ` is the state-transition matrix of `ż = A(t)z` (`isStateTransition_periodicRate`) and decays
  exponentially (`norm_periodicRateTransition_le`), so the origin of `ż = A(t)z` is uniformly
  asymptotically stable (`uniformlyAsymptoticallyStable_periodicRate`), the hypothesis of
  Theorem 4.6;
* `A` is continuous and bounded by `2` (`continuous_periodicRate`, `norm_periodicRate_le`);
* the sine system has the uniform linearization `A` (`isUniformLinearization_periodicSineField`),
  so by Theorem 4.6 with a time-varying linearization its origin is exponentially stable
  (`exponentiallyStable_periodicSineField`).

These are statements about the model equations; the example is chosen so that every hypothesis
can be checked by hand, not to model a physical system.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean.Examples

open Stability

variable {n : ℕ}

/-- **The time-varying coefficient `A(t) = −(1 + sin t) I` on `ℝⁿ`** (an instance of the
linearization (4.40) of MLS Theorem 4.6, p. 184; time first). -/
def periodicRate (t : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (-(1 + Real.sin t)) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))

/-- **The state-transition matrix of `ż = −(1 + sin t) z`**:
`Φ(t, s) = e^{−(t − s) + cos t − cos s} I` (MLS eq. (4.40), p. 184). -/
def periodicRateTransition (t s : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  Real.exp (-(t - s) + Real.cos t - Real.cos s) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))

/-- **The nonlinear system `ẋᵢ = −(1 + sin t) sin xᵢ`** on `ℝⁿ` (an instance of (4.37), MLS
p. 184; time first). -/
def periodicSineField (t : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (-(1 + Real.sin t)) • fun i => Real.sin (x i)

/-- **`Φ(t, s) = e^{−(t − s) + cos t − cos s} I` is the state-transition matrix of
`ż = −(1 + sin t) z`** (MLS eq. (4.40), p. 184). -/
theorem isStateTransition_periodicRate :
    IsStateTransition (periodicRate (n := n)) periodicRateTransition := by
  refine ⟨fun s _ => by simp [periodicRateTransition], fun t s r _ _ _ => ?_,
    fun t s _ _ => ?_⟩
  · simp only [periodicRateTransition]
    rw [smul_mul_smul_comm, one_mul, ← Real.exp_add]
    congr 2
    ring
  · have hg : HasDerivAt (fun τ => -(τ - s) + Real.cos τ - Real.cos s) (-1 + -Real.sin t) t := by
      have := (((hasDerivAt_id t).sub_const s).neg.add (Real.hasDerivAt_cos t)).sub_const
        (Real.cos s)
      simpa using this
    have h1 : HasDerivWithinAt (fun τ => periodicRateTransition (n := n) τ s)
        ((Real.exp (-(t - s) + Real.cos t - Real.cos s) * (-1 + -Real.sin t)) •
          (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) (Ici 0) t :=
      (hg.exp.smul_const (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))).hasDerivWithinAt
    refine h1.congr_deriv ?_
    rw [periodicRate, periodicRateTransition, smul_mul_smul_comm, one_mul]
    congr 1
    ring

/-- **The state-transition matrix of `ż = −(1 + sin t) z` decays exponentially:**
`‖Φ(t, s)‖ ≤ e² e^{−(t − s)}` (operator norm of the sup norm; MLS eq. (4.40),
p. 184). -/
theorem norm_periodicRateTransition_le (t s : ℝ) :
    ‖periodicRateTransition (n := n) t s‖ ≤ Real.exp 2 * Real.exp (-(1 * (t - s))) := by
  rw [periodicRateTransition, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add]
  have h1 : Real.exp (-(t - s) + Real.cos t - Real.cos s) ≤ Real.exp (2 + -(1 * (t - s))) :=
    Real.exp_le_exp.2 (by linarith [Real.cos_le_one t, Real.neg_one_le_cos s])
  calc Real.exp (-(t - s) + Real.cos t - Real.cos s) * ‖(1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖
      ≤ Real.exp (2 + -(1 * (t - s))) * 1 :=
        mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 + -(1 * (t - s))) := mul_one _

/-- **The origin of `ż = −(1 + sin t) z` is uniformly asymptotically stable** (the hypothesis of
MLS Theorem 4.6, p. 184, on (4.40)), from the exponential bound on its state-transition
matrix. -/
theorem uniformlyAsymptoticallyStable_periodicRate :
    UniformlyAsymptoticallyStable (fun t z => periodicRate (n := n) t z) 0 :=
  (isStateTransition_periodicRate.uniformlyAsymptoticallyStable_iff_exists_norm_le).2
    ⟨Real.exp 2, 1, one_pos, fun t s _ _ => norm_periodicRateTransition_le t s⟩

/-- **`A(t) = −(1 + sin t) I` is continuous** (the added hypothesis of MLS Theorem 4.6, p. 184,
as formalized). -/
theorem continuous_periodicRate : Continuous (periodicRate (n := n)) :=
  (continuous_const.add Real.continuous_sin).neg.smul continuous_const

/-- **`A(t) = −(1 + sin t) I` is bounded: `‖A(t)‖ ≤ 2`** (the boundedness hypothesis of MLS
Theorem 4.6, p. 184; operator norm of the sup norm). -/
theorem norm_periodicRate_le (t : ℝ) : ‖periodicRate (n := n) t‖ ≤ 2 := by
  rw [periodicRate, norm_smul, Real.norm_eq_abs, abs_neg]
  have h1 : |1 + Real.sin t| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [Real.sin_le_one t, Real.neg_one_le_sin t]
  calc |1 + Real.sin t| * ‖(1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ 2 * 1 :=
        mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
    _ = 2 := mul_one 2

/- `|sin y − y| ≤ |y|³` for `|y| ≤ 1`, from Mathlib's `Real.sin_bound`. -/
private theorem abs_sin_sub_self_le {y : ℝ} (hy : |y| ≤ 1) : |Real.sin y - y| ≤ |y| ^ 3 := by
  have h1 := Real.sin_bound hy
  have h0 : 0 ≤ |y| := abs_nonneg y
  have h5 : |y| ^ 5 ≤ |y| ^ 3 := pow_le_pow_of_le_one h0 hy (by norm_num)
  have h3 : |y ^ 3 / 6| = |y| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  calc |Real.sin y - y| = |(Real.sin y - (y - y ^ 3 / 6)) + -(y ^ 3 / 6)| := by ring_nf
    _ ≤ |Real.sin y - (y - y ^ 3 / 6)| + |-(y ^ 3 / 6)| := abs_add_le _ _
    _ ≤ |y| ^ 5 / 100 + |y| ^ 3 / 6 := by rw [abs_neg, h3]; linarith
    _ ≤ |y| ^ 3 := by nlinarith [pow_nonneg h0 3]

/-- **`ż = −(1 + sin t) z` is the uniform linearization (4.39) of `ẋᵢ = −(1 + sin t) sin xᵢ`**
(MLS p. 184): `‖f(t, x) − A(t)x‖ ≤ 2‖x‖³` for `‖x‖ ≤ 1`, uniformly in `t`. -/
theorem isUniformLinearization_periodicSineField :
    IsUniformLinearization (periodicSineField (n := n)) periodicRate := by
  intro γ hγ
  refine ⟨min 1 (γ / 2), by positivity, fun t _ x hx => ?_⟩
  have hx1 : ‖x‖ ≤ 1 := hx.trans (min_le_left _ _)
  have hxγ : ‖x‖ ≤ γ / 2 := hx.trans (min_le_right _ _)
  have heq : periodicSineField t x - periodicRate t x =
      (-(1 + Real.sin t)) • fun i => Real.sin (x i) - x i := by
    ext i
    simp [periodicSineField, periodicRate, mul_sub]
  have hsin : ‖fun i => Real.sin (x i) - x i‖ ≤ ‖x‖ ^ 3 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have hxi : |x i| ≤ ‖x‖ := by simpa using norm_le_pi_norm x i
    rw [Real.norm_eq_abs]
    exact (abs_sin_sub_self_le (hxi.trans hx1)).trans (pow_le_pow_left₀ (abs_nonneg _) hxi 3)
  have hc : ‖(-(1 + Real.sin t))‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_neg, abs_le]
    constructor <;> linarith [Real.sin_le_one t, Real.neg_one_le_sin t]
  rw [heq, norm_smul]
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  calc ‖(-(1 + Real.sin t))‖ * ‖fun i => Real.sin (x i) - x i‖ ≤ 2 * ‖x‖ ^ 3 :=
        mul_le_mul hc hsin (norm_nonneg _) (by norm_num)
    _ ≤ γ * ‖x‖ := by nlinarith [mul_nonneg h0 h0, mul_le_mul_of_nonneg_left hx1 h0]

/-- **MLS Theorem 4.6 (p. 184) applied with a time-varying linearization:** the origin of
`ẋᵢ = −(1 + sin t) sin xᵢ` on `ℝⁿ` is exponentially stable (Definition 4.3), hence uniformly
asymptotically stable, from `exponentiallyStable_of_isUniformLinearization_timeVarying`. -/
theorem exponentiallyStable_periodicSineField :
    ExponentiallyStable (periodicSineField (n := n)) 0 :=
  exponentiallyStable_of_isUniformLinearization_timeVarying continuous_periodicRate.continuousOn
    ⟨2, fun t _ => norm_periodicRate_le t⟩ uniformlyAsymptoticallyStable_periodicRate
    isUniformLinearization_periodicSineField

end RoboLean.Examples
