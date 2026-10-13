import RoboLean.Control.LinearTimeVarying

/-!
# Stability by linearization with a time-varying linearization (MLS Theorem 4.6, p. 184)

**What MLS prints (read this session, pp. 184–185).** For `ẋ = f(x, t)` with `f(0, t) = 0` for
`t ≥ 0` (4.37), `A(t) = ∂f(x, t)/∂x |_{x=0}` (4.38) and the uniform linearization condition
`lim_{‖x‖→0} sup_{t≥0} ‖f(x, t) − A(t)x‖/‖x‖ = 0` (4.39): "Theorem 4.6. Stability by
linearization. Consider the system (4.37) and assume [(4.39)]. Further, let `A(·)` defined in
equation (4.38) be bounded. If 0 is a uniformly asymptotically stable equilibrium point of (4.40)
then it is a locally uniformly asymptotically stable equilibrium point of (4.37)." MLS gives no
proof.

**Formalized here**, on `ℝⁿ` with the sup norm, for a time-varying `A(t)`:

* with a state-transition matrix `Φ` of `ż = A(t)z` (`IsStateTransition A Φ`), `‖A(t)‖ ≤ M` and
  an exponential bound `‖Φ(t, s)‖ ≤ C e^{−α(t − s)}`, (4.39) gives exponential stability of the
  origin of `ẋ = f(x, t)`
  (`IsStateTransition.exponentiallyStable_of_isUniformLinearization_of_norm_le`);
  with uniform asymptotic stability of `ż = A(t)z` in place of the bound, the same
  (`IsStateTransition.exponentiallyStable_of_isUniformLinearization`);
* Theorem 4.6 with the hypotheses as printed plus continuity of `A` on `[0, ∞)`: exponential
  stability (`exponentiallyStable_of_isUniformLinearization_timeVarying`), hence the printed local
  uniform asymptotic stability
  (`uniformlyAsymptoticallyStable_of_isUniformLinearization_timeVarying`).

**Route.** Uniform asymptotic stability of `ż = A(t)z` gives `‖Φ(t, s)‖ ≤ C e^{−α(t − s)}`
(`IsStateTransition.exists_norm_le_of_uniformlyAsymptoticallyStable`). The Lyapunov function is the
Gramian `V(t, x) = ∫_t^{t+T} ‖Φ(s, t)x‖₂² ds` with `T = 1 + log(2nC'² + 1)/(2α)` (E026's horizon):
`T e^{−2MT} ‖x‖² ≤ V ≤ T n C'² ‖x‖²` (the lower bound uses `A` bounded), and along a solution
`V̇ = 2 ∫ Φ(s,t)(f − Ax) ⬝ Φ(s,t)x ds + ‖Φ(t + T, t)x‖₂² − ‖x‖₂² ≤ −‖x‖²/4` on the ball where
`‖f(t, x) − A(t)x‖ ≤ ‖x‖/(8TnC'² + 1)`. The local form of Theorem 4.5
(`exponentiallyStable_of_quadratic_lyapunov_local`, E019) concludes. No continuity of `f` and no
existence of solutions of `ẋ = f(x, t)` is assumed.

**Hypotheses MLS does not state.** `A` continuous on `[0, ∞)`, so that the state-transition
matrix exists (`exists_isStateTransition`); MLS's standing conditions (p. 179) allow piecewise
continuity in `t`, which the library's notion of solution (a derivative at every `t > t₀`) does
not accommodate. The versions with `IsStateTransition A Φ` as a hypothesis do not need it.

**Conventions.** As in `RoboLean.Stability` and E026: time first, (4.39) as
`IsUniformLinearization f A` (which gives `f(t, 0) = 0` for `t ≥ 0`), `A : ℝ → (ℝⁿ →L[ℝ] ℝⁿ)`,
"bounded" as `‖A(t)‖ ≤ M` for `t ≥ 0` (operator norm of the sup norm), exponential stability
(Definition 4.3, constants independent of `t₀`), which implies uniform asymptotic stability.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean
namespace Stability

variable {n : ℕ} {f : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} {A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}

namespace IsStateTransition

variable {Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}

/-- **MLS Theorem 4.6 (p. 184) with a time-varying linearization, from an exponential bound on the
state-transition matrix.** Let `ẋ = f(x, t)` on `ℝⁿ` (sup norm) have the uniform linearization
`ż = A(t)z` (4.39), with `A` bounded (`‖A(t)‖ ≤ M` for `t ≥ 0`), and let `Φ` be a
state-transition matrix of `ż = A(t)z` with `‖Φ(t, s)‖ ≤ C e^{−α(t − s)}` for `0 ≤ s ≤ t`,
`α > 0`. Then the origin of `ẋ = f(x, t)` is exponentially stable (Definition 4.3). No continuity
of `f` or `A` is assumed. Proof: the Gramian Lyapunov function `gramianForm Φ T t x x` and the
local form of Theorem 4.5. -/
theorem exponentiallyStable_of_isUniformLinearization_of_norm_le (hΦ : IsStateTransition A Φ)
    {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) {C α : ℝ} (hα : 0 < α)
    (hdec : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ C * Real.exp (-(α * (t - s))))
    (hf : IsUniformLinearization f A) : ExponentiallyStable f 0 := by
  set M' := max M 0 with hM'def
  have hM' : ∀ t, 0 ≤ t → ‖A t‖ ≤ M' := fun t ht => (hM t ht).trans (le_max_left _ _)
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set C' := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hdec' : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ C' * Real.exp (-(α * (t - s))) :=
    fun t s hs hst => (hdec t s hs hst).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hK : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ C' := by
    intro t s hs hst
    have he : Real.exp (-(α * (t - s))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hα.le (sub_nonneg.2 hst)])
    exact (hdec' t s hs hst).trans (mul_le_of_le_one_right hC'0 he)
  -- a horizon `T` with `n (C' e^{−αT})² ≤ 1/2`
  set D : ℝ := 2 * n * C' ^ 2 + 1 with hDdef
  have hD : 0 < D := by positivity
  set T : ℝ := 1 + Real.log D / (2 * α) with hTdef
  have hT : 0 < T := by
    have : 0 ≤ Real.log D := Real.log_nonneg (by simp only [hDdef]; nlinarith [sq_nonneg C'])
    positivity
  have hsmall : (n : ℝ) * (C' * Real.exp (-(α * T))) ^ 2 ≤ 1 / 2 := by
    have h1 : Real.exp (-(α * T)) ^ 2 = Real.exp (-(2 * α)) / D := by
      have harg : -(α * T) + -(α * T) = -(2 * α) + -Real.log D := by
        rw [hTdef]
        field_simp
        ring
      rw [sq, ← Real.exp_add, harg, Real.exp_add, Real.exp_neg (Real.log D), Real.exp_log hD,
        div_eq_mul_inv]
    have h2 : Real.exp (-(2 * α)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hCe : C' ^ 2 * Real.exp (-(2 * α)) ≤ C' ^ 2 := by
      nlinarith [sq_nonneg C', Real.exp_pos (-(2 * α))]
    rw [mul_pow, h1]
    calc (n : ℝ) * (C' ^ 2 * (Real.exp (-(2 * α)) / D))
        = n * (C' ^ 2 * Real.exp (-(2 * α))) / D := by ring
      _ ≤ n * C' ^ 2 / D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCe (Nat.cast_nonneg n)) hD.le
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hD, hDdef]
        linarith
  -- the perturbation radius
  set κ := T * (n * C' ^ 2) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set γ := 1 / (8 * κ + 1) with hγ
  have hγ0 : 0 < γ := by positivity
  have hκγ : 2 * κ * γ ≤ 1 / 4 := by
    rw [hγ, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨r, hr, hlin⟩ := hf γ hγ0
  have ha₁ : 0 < T * Real.exp (-(2 * (M' * T))) := by positivity
  refine exponentiallyStable_of_quadratic_lyapunov_local (V := fun t y => gramianForm Φ T t y y)
    (Vdot := fun t y => 2 * gramianForm Φ T t (f t y - A t y) y +
      (Φ (t + T) t y ⬝ᵥ Φ (t + T) t y - y ⬝ᵥ y))
    (a₃ := 1 / 4) ha₁ (by positivity : (0 : ℝ) < κ + 1) (by norm_num) hr
    (hΦ.continuousOn_gramianForm hT.le) (fun t ht y _ => hΦ.le_gramianForm hM'0 hM' hT.le ht y)
    (fun t ht y _ => ?_) ?_ ?_
  · have h1 := (le_abs_self _).trans (abs_gramianForm_le hT.le hK ht y y)
    nlinarith [sq_nonneg ‖y‖]
  · intro t₀ ht₀ x hx t ht _
    exact hΦ.hasDerivAt_gramianForm hT.le (ht₀.trans_lt ht) (hx.2 t ht)
  · intro t ht y hy
    have h1 := abs_gramianForm_le hT.le hK ht (f t y - A t y) y
    have h2 : ‖f t y - A t y‖ ≤ γ * ‖y‖ := hlin t ht y hy
    have h3 : Φ (t + T) t y ⬝ᵥ Φ (t + T) t y ≤ 1 / 2 * ‖y‖ ^ 2 := by
      have hΦy : ‖Φ (t + T) t y‖ ≤ C' * Real.exp (-(α * T)) * ‖y‖ := by
        have := hdec' (t + T) t ht (by linarith)
        rw [show t + T - t = T by ring] at this
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right this (norm_nonneg _))
      calc Φ (t + T) t y ⬝ᵥ Φ (t + T) t y ≤ n * ‖Φ (t + T) t y‖ ^ 2 :=
            Control.dotProduct_self_le_mul_sq_norm _
        _ ≤ n * (C' * Real.exp (-(α * T)) * ‖y‖) ^ 2 := by gcongr
        _ = n * (C' * Real.exp (-(α * T))) ^ 2 * ‖y‖ ^ 2 := by ring
        _ ≤ 1 / 2 * ‖y‖ ^ 2 := by gcongr
    have h4 := Control.sq_norm_le_dotProduct_self y
    have h5 : 2 * gramianForm Φ T t (f t y - A t y) y ≤ 1 / 4 * ‖y‖ ^ 2 := by
      have h6 : κ * ‖f t y - A t y‖ * ‖y‖ ≤ κ * (γ * ‖y‖) * ‖y‖ := by gcongr
      have h7 := (le_abs_self _).trans (h1.trans h6)
      nlinarith [mul_le_mul_of_nonneg_right hκγ (sq_nonneg ‖y‖)]
    show 2 * gramianForm Φ T t (f t y - A t y) y + (Φ (t + T) t y ⬝ᵥ Φ (t + T) t y - y ⬝ᵥ y) ≤
      -(1 / 4 * ‖y‖ ^ 2)
    linarith

/-- **MLS Theorem 4.6 (p. 184) with a time-varying linearization, given a state-transition
matrix, exponential form.** If `ż = A(t)z` (4.40) is a uniform linearization (4.39) of
`ẋ = f(x, t)` on `ℝⁿ`, `A` is bounded (`‖A(t)‖ ≤ M` for `t ≥ 0`), `Φ` is a state-transition matrix
of `ż = A(t)z` and its origin is uniformly asymptotically stable, then the origin of
`ẋ = f(x, t)` is exponentially stable. No continuity of `A` is assumed beyond what `Φ` carries. -/
theorem exponentiallyStable_of_isUniformLinearization (hΦ : IsStateTransition A Φ) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) (hL : UniformlyAsymptoticallyStable (fun t z => A t z) 0)
    (hf : IsUniformLinearization f A) : ExponentiallyStable f 0 := by
  obtain ⟨C, α, hα, hd⟩ := hΦ.exists_norm_le_of_uniformlyAsymptoticallyStable hL
  exact hΦ.exponentiallyStable_of_isUniformLinearization_of_norm_le hM hα hd hf

end IsStateTransition

/-- **MLS Theorem 4.6 (p. 184) with a time-varying linearization, exponential form.** Let
`ẋ = f(x, t)` on `ℝⁿ` (sup norm) satisfy (4.39) with `A : ℝ → (ℝⁿ →L[ℝ] ℝⁿ)`, let `A` be bounded
(`‖A(t)‖ ≤ M` for `t ≥ 0`, as printed) and continuous on `[0, ∞)` (a hypothesis MLS does not state),
and let the origin of `ż = A(t)z` (4.40) be uniformly asymptotically stable. Then the origin of
`ẋ = f(x, t)` is exponentially stable (Definition 4.3), which is stronger than the printed
conclusion (`uniformlyAsymptoticallyStable_of_isUniformLinearization_timeVarying`). No continuity
of `f` and no existence of its solutions is assumed. -/
theorem exponentiallyStable_of_isUniformLinearization_timeVarying
    (hAc : ContinuousOn A (Ici 0)) (hAb : ∃ M, ∀ t, 0 ≤ t → ‖A t‖ ≤ M)
    (hL : UniformlyAsymptoticallyStable (fun t z => A t z) 0)
    (hf : IsUniformLinearization f A) : ExponentiallyStable f 0 := by
  obtain ⟨M, hM⟩ := hAb
  obtain ⟨Φ, hΦ⟩ := exists_isStateTransition hAc hM
  exact hΦ.exponentiallyStable_of_isUniformLinearization hM hL hf

/-- **MLS Theorem 4.6 (p. 184), as printed, with a time-varying linearization:** if (4.39) holds,
`A(·)` is bounded, and `0` is a uniformly asymptotically stable equilibrium point of `ż = A(t)z`
(4.40), then `0` is a locally uniformly asymptotically stable equilibrium point of `ẋ = f(x, t)`
(4.37); on `ℝⁿ` with the sup norm, with the added hypothesis that `A` is continuous on `[0, ∞)`.
The library's uniform asymptotic stability is local (a ball of initial states, MLS p. 180). -/
theorem uniformlyAsymptoticallyStable_of_isUniformLinearization_timeVarying
    (hAc : ContinuousOn A (Ici 0)) (hAb : ∃ M, ∀ t, 0 ≤ t → ‖A t‖ ≤ M)
    (hL : UniformlyAsymptoticallyStable (fun t z => A t z) 0)
    (hf : IsUniformLinearization f A) : UniformlyAsymptoticallyStable f 0 :=
  (exponentiallyStable_of_isUniformLinearization_timeVarying hAc hAb hL hf
    ).uniformlyAsymptoticallyStable

end Stability
end RoboLean
