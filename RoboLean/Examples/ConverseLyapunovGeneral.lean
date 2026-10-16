import RoboLean.Control.ConverseLyapunovGeneral
import RoboLean.Control.StateTransitionPiecewise
import RoboLean.Examples.LinearizationTimeVarying

/-!
# Instances: the four-bound converse and state-transition matrices (MLS pp. 179, 183–184)

* The linear time-varying system `ż = −(1 + sin t) z` on `ℝⁿ` (the linearization used for MLS
  Theorem 4.6, p. 184) has a differentiable flow `φ(t, s, x) = Φ(t, s) x`
  (`isDifferentiableFlow_periodicRate`) and a Lyapunov function with all four bounds of MLS Theorem
  4.5, p. 183 (`exists_lyapunov_periodicRate`): the hypotheses of the general converse are met by a
  system with a genuinely time-varying `A(t)`.
* The scalar `A(t) = 0` for `t < 1`, `A(t) = −1` for `t ≥ 1` is bounded and continuous except at one
  point, so it is piecewise continuous in MLS's sense (p. 179), and it has no state-transition
  matrix in the library's sense (`not_exists_isStateTransition_jumpRate`): the solutions of
  `ż = A(t)z` have no derivative at `t = 1`.

These are instances, not separate results. State sup norms.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean.Examples

open Stability

variable {n : ℕ}

/-- **`ż = −(1 + sin t) z` has a differentiable flow (MLS Theorem 4.5, p. 183; eq. (4.40), p.
184):** `φ(t, s, x) = Φ(t, s) x` with `Φ(t, s) = e^{−(t − s) + cos t − cos s} I`, `Df(t, y) = A(t)`
and `∂φ/∂x = Φ(t, s)`. -/
theorem isDifferentiableFlow_periodicRate :
    IsDifferentiableFlow (fun t z => periodicRate (n := n) t z) (fun t _ => periodicRate t)
      (fun t s x => periodicRateTransition t s x) (fun t s _ => periodicRateTransition t s) :=
  isStateTransition_periodicRate.isDifferentiableFlow

/-- **A Lyapunov function with all four bounds of MLS Theorem 4.5 (p. 183) for
`ż = −(1 + sin t) z`** on `ℝⁿ` (sup norm): there are `V`, `V̇`, `∂V/∂x` and constants
`a₁, a₂, a₃, a₄, ε > 0` with `V` continuous on `[0, ∞) × ℝⁿ` and, for `t ≥ 0` and `‖x‖ ≤ ε`,
`a₁‖x‖² ≤ V ≤ a₂‖x‖²`, `V̇ ≤ −a₃‖x‖²` along the solutions, and `‖∂V/∂x‖ ≤ a₄‖x‖`. From the
exponential bound `‖Φ(t, s)‖ ≤ e² e^{−(t − s)}` and `‖A(t)‖ ≤ 2`. -/
theorem exists_lyapunov_periodicRate :
    ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
      ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
        ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
        HasDerivAlongSolutions (fun t z => periodicRate t z) V Vdot univ ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
        ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ :=
  (isStateTransition_periodicRate.exponentiallyStable_iff_exists_lyapunov
    (fun t _ => norm_periodicRate_le t)).1
    ((isStateTransition_periodicRate.uniformlyAsymptoticallyStable_iff_globallyExponentiallyStable.1
      uniformlyAsymptoticallyStable_periodicRate).exponentiallyStable)

/-- **A piecewise continuous rate with one jump (MLS p. 179, "piecewise continuous in `t`"):**
`A(t) = 0` for `t < 1` and `A(t) = −1` for `t ≥ 1`, on `ℝ¹`. -/
def jumpRate (t : ℝ) : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  if t < 1 then 0 else -1

/-- **The jump rate is bounded, `‖A(t)‖ ≤ 1`** (MLS Theorem 4.6, p. 184, "`A(·)` bounded"). -/
theorem norm_jumpRate_le (t : ℝ) : ‖jumpRate t‖ ≤ 1 := by
  unfold jumpRate
  split_ifs
  · simp
  · rw [norm_neg]
    exact ContinuousLinearMap.norm_id_le

/-- **The jump rate is continuous at every `t ≠ 1`** (piecewise continuity, MLS p. 179). -/
theorem continuousAt_jumpRate {t : ℝ} (ht : t ≠ 1) : ContinuousAt jumpRate t := by
  rcases lt_or_gt_of_ne ht with h | h
  · refine (continuousAt_const (y := (0 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)))).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    simp [jumpRate, mem_Iio.1 hs]
  · refine (continuousAt_const (y := (-1 : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ)))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    simp [jumpRate, not_lt.2 (le_of_lt (mem_Ioi.1 hs))]

/-- **The jump rate has no state-transition matrix (MLS eq. (4.40), p. 184, with the piecewise
continuity of p. 179):** there is no `Φ` with `IsStateTransition jumpRate Φ`, since the left limit
`0` of `A` at `t = 1` differs from `A(1) = −1` (`IsStateTransition.eq_of_tendsto_nhdsWithin_Iio`). A
convention check on one input. -/
theorem not_exists_isStateTransition_jumpRate :
    ¬ ∃ Φ : ℝ → ℝ → (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ), IsStateTransition jumpRate Φ := by
  rintro ⟨Φ, hΦ⟩
  have hL : Tendsto jumpRate (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [jumpRate, mem_Iio.1 hs]
  have h1 := hΦ.eq_of_tendsto_nhdsWithin_Iio one_pos hL
  have h2 := congrArg (fun L : (Fin 1 → ℝ) →L[ℝ] (Fin 1 → ℝ) => L (fun _ => 1) 0) h1
  simp [jumpRate] at h2

end RoboLean.Examples
