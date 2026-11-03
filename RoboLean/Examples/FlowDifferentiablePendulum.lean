import RoboLean.Control.FlowDifferentiable
import RoboLean.Examples.NonlinearSpring

/-!
# The damped pendulum has a flow differentiable in the initial state (MLS pp. 179, 183 and 189)

**What MLS prints.** Example 4.7 (p. 189) treats the spring–mass system (4.45) with damper,
`ẋ₁ = x₂`, `ẋ₂ = −f(x₂) − g(x₁)`; the damped pendulum is the instance `f = id`, `g = sin`
(`Examples.NonlinearSpring`). MLS's standing assumption (p. 179) asks the standard conditions for
existence and uniqueness of solutions, and the fourth bound of Theorem 4.5 (p. 183) needs the
derivative of the solutions in the initial state.

**Proved here.** The field `x ↦ (x₂, −x₂ − sin x₁)` has the derivative
`h ↦ (h₂, −h₂ − cos x₁ · h₁)` (`hasFDerivAt_dampedPendulum`), continuous in `x` and bounded by `2`
in operator norm for the sup norm, so every hypothesis of `exists_isDifferentiableFlow_autonomous`
is met on this nonlinear field: it has a flow differentiable in the initial state with the
variational equation (`exists_isDifferentiableFlow_dampedPendulum`).

**Carrier.** As in `Examples.NonlinearSpring`: state `(x₁, x₂) ∈ ℝ × ℝ` with the sup norm, the
system time-invariant and written `fun _ => springField id Real.sin` (time first, ignored). This is
an instance of a general theorem; it is not a claim about a physical pendulum.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean.Examples

/-- **The derivative of the damped pendulum field (MLS Example 4.7, p. 189, with `f = id`,
`g = sin`):** at `x = (x₁, x₂)` it is the linear map `h ↦ (h₂, −h₂ − cos x₁ · h₁)` on `ℝ × ℝ`. -/
def dampedPendulumDeriv (x : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (-(ContinuousLinearMap.snd ℝ ℝ ℝ) - Real.cos x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- **The damped pendulum field is differentiable (MLS Example 4.7, p. 189):** the field
`springField id sin`, `x ↦ (x₂, −x₂ − sin x₁)`, has the Fréchet derivative
`dampedPendulumDeriv x` at every `x`. State `(x₁, x₂)`, sup norm. -/
theorem hasFDerivAt_dampedPendulum (x : ℝ × ℝ) :
    HasFDerivAt (springField id Real.sin) (dampedPendulumDeriv x) x := by
  have hsin : HasFDerivAt (fun y : ℝ × ℝ => Real.sin y.1)
      (Real.cos x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (Real.hasDerivAt_sin x.1).comp_hasFDerivAt x hasFDerivAt_fst
  have hsnd := hasFDerivAt_snd (p := x) (𝕜 := ℝ) (E := ℝ) (F := ℝ)
  exact hsnd.prodMk (hsnd.neg.sub hsin)

/-- **The derivative of the damped pendulum field is continuous in the state (MLS Example 4.7,
p. 189).** -/
theorem continuous_dampedPendulumDeriv : Continuous dampedPendulumDeriv := by
  have h : Continuous fun x : ℝ × ℝ =>
      -(ContinuousLinearMap.snd ℝ ℝ ℝ) - Real.cos x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ :=
    continuous_const.sub ((Real.continuous_cos.comp continuous_fst).smul continuous_const)
  exact (ContinuousLinearMap.prodL ℝ).continuous.comp (continuous_const.prodMk h)

/-- **The derivative of the damped pendulum field is bounded (MLS Example 4.7, p. 189):**
`‖dampedPendulumDeriv x‖ ≤ 2` in operator norm for the sup norm on `ℝ × ℝ`; so the field is
globally Lipschitz, as MLS's standing assumption of p. 179 asks. -/
theorem norm_dampedPendulumDeriv_le (x : ℝ × ℝ) : ‖dampedPendulumDeriv x‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => ?_
  simp only [dampedPendulumDeriv, ContinuousLinearMap.prod_apply, sub_apply, neg_apply,
    smul_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', Prod.norm_mk,
    smul_eq_mul]
  have h1 := norm_fst_le h
  have h2 := norm_snd_le h
  have hc := Real.abs_cos_le_one x.1
  rw [Real.norm_eq_abs] at *
  refine max_le (by linarith [abs_nonneg h.1]) ?_
  calc |-h.2 - Real.cos x.1 * h.1| ≤ |h.2| + |Real.cos x.1| * |h.1| := by
        rw [← abs_neg h.2, ← abs_mul]; exact abs_sub _ _
    _ ≤ 2 * ‖h‖ := by nlinarith [abs_nonneg h.1, abs_nonneg (Real.cos x.1)]

/-- **The damped pendulum has a flow differentiable in the initial state (MLS Example 4.7, p. 189,
with the standing assumption of p. 179 and the fourth bound of Theorem 4.5, p. 183):** there are
`φ` and `D` with `IsDifferentiableFlow (fun _ => springField id sin) (fun _ => dampedPendulumDeriv)
φ D`; every hypothesis of `exists_isDifferentiableFlow_autonomous` is met with `K = 2`. -/
theorem exists_isDifferentiableFlow_dampedPendulum :
    ∃ φ : ℝ → ℝ → ℝ × ℝ → ℝ × ℝ, ∃ D : ℝ → ℝ → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      Stability.IsDifferentiableFlow (fun _ => springField id Real.sin)
        (fun _ => dampedPendulumDeriv) φ D := by
  exact Stability.exists_isDifferentiableFlow_autonomous (K := 2) hasFDerivAt_dampedPendulum
    continuous_dampedPendulumDeriv fun y => by simpa using norm_dampedPendulumDeriv_le y

end RoboLean.Examples
