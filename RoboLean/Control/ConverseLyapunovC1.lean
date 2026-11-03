import RoboLean.Control.ConverseLyapunovGeneral
import RoboLean.Control.FlowDifferentiable

/-!
# The converse of the exponential stability theorem for fields with a bounded continuous derivative
(MLS Theorem 4.5, p. 183)

**What MLS states.** Theorem 4.5 (p. 183): "`x* = 0` is an exponentially stable equilibrium point of
`ẋ = f(x, t)` if and only if there exists an `ε > 0` and a function `V(x, t)` which satisfies
`α₁‖x‖² ≤ V(x, t) ≤ α₂‖x‖²`, `V̇|_{ẋ = f(x, t)} ≤ −α₃‖x‖²`, `‖∂V/∂x (x, t)‖ ≤ α₄‖x‖` for some
positive constants `α₁, α₂, α₃, α₄`, and `‖x‖ ≤ ε`." The standing assumption (p. 179) is that
`f(x, t)` satisfies the standard conditions for existence and uniqueness of solutions, for
instance Lipschitz continuity in `x` uniformly in `t`.

**Formalized here.** On `ℝⁿ` with the sup norm, for a time-varying field `f(t, x)` (time first)
continuous in `t ≥ 0`, with the Fréchet derivative `Df(t, y)` in `y`, `Df` continuous on
`[0, ∞) × ℝⁿ` and bounded in operator norm by `K`: the "only if" direction with all four bounds
(`exists_lyapunov_of_exponentiallyStable_of_fderiv`) and the equivalence
(`exponentiallyStable_iff_exists_lyapunov_of_fderiv`), with no flow hypothesis. The flow
differentiable in the initial state is constructed by `exists_isDifferentiableFlow`, `f(t, ·)` is
`K`-Lipschitz by the mean value inequality, and the theorems of `Control/ConverseLyapunovGeneral`
apply. The Lyapunov function and the constants are those of
`exists_lyapunov_of_exponentiallyStable_of_isDifferentiableFlow`.

**Hypotheses against MLS.** MLS asks Lipschitz continuity in `x` uniformly in `t` and piecewise
continuity in `t`; here `f` is continuous in `t` and has a continuous derivative in `x` bounded on
`[0, ∞) × ℝⁿ` (a global bound). A field that is only locally Lipschitz, or whose derivative is
bounded only near the origin, is not covered.

**Conventions.** As in `Control/ConverseLyapunovGeneral`: time first, `V t x` for MLS's `V(x, t)`,
`V̇` the derivative along solutions, `∂V/∂x` the Fréchet derivative of `x ↦ V(t, x)` with its
operator norm for the sup norm on `ℝⁿ`, the bounds on `‖x‖ ≤ ε`.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean
namespace Stability

variable {n : ℕ}

/-- A field with derivative bounded by `K` is `K`-Lipschitz (the mean value inequality; MLS's
standing assumption, p. 179, Lipschitz continuity in `x` uniformly in `t`). -/
private theorem lipschitzWith_of_fderiv_le {f : ℝ → (Fin n → ℝ) → Fin n → ℝ}
    {Df : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {K : NNReal}
    (hDf : ∀ t, 0 ≤ t → ∀ y, HasFDerivAt (f t) (Df t y) y)
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) : ∀ t, 0 ≤ t → LipschitzWith K (f t) := fun t ht =>
  lipschitzWith_of_nnnorm_fderiv_le (fun y => (hDf t ht y).differentiableAt) fun y => by
    rw [(hDf t ht y).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
    exact hK t ht y

/-- **The converse of MLS Theorem 4.5 (p. 183) with all four bounds, for fields with a bounded
continuous derivative.** On `ℝⁿ` (sup norm), let `f(t, x)` be continuous in `t ≥ 0` for every `x`,
and let `f(t, ·)` have the Fréchet derivative `Df(t, y)` at every `y` for `t ≥ 0`, with `Df`
continuous on `[0, ∞) × ℝⁿ` and `‖Df(t, y)‖ ≤ K` there. If the origin is exponentially stable
(Definition 4.3, pp. 180–181), there are `V`, its derivative `V̇` along every solution, a Fréchet
derivative `∂V/∂x` and constants `a₁, a₂, a₃, a₄, ε > 0` with `V` continuous on `[0, ∞) × ℝⁿ` and,
for `t ≥ 0` and `‖x‖ ≤ ε`: `a₁‖x‖² ≤ V(t, x) ≤ a₂‖x‖²`, `V̇(t, x) ≤ −a₃‖x‖²`, `x ↦ V(t, x)` has the
derivative `∂V/∂x (t, x)` at `x`, and `‖∂V/∂x (t, x)‖ ≤ a₄‖x‖` (operator norm). Time first. -/
theorem exists_lyapunov_of_exponentiallyStable_of_fderiv
    {f : ℝ → (Fin n → ℝ) → Fin n → ℝ} {Df : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {K : NNReal} (hf : ∀ x, ContinuousOn (fun t => f t x) (Ici 0))
    (hDf : ∀ t, 0 ≤ t → ∀ y, HasFDerivAt (f t) (Df t y) y)
    (hDfc : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) (hexp : ExponentiallyStable f 0) :
    ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
      ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
        ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
        HasDerivAlongSolutions f V Vdot univ ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
        ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ := by
  obtain ⟨φ, D, hφ⟩ := exists_isDifferentiableFlow hf hDf hDfc hK
  exact exists_lyapunov_of_exponentiallyStable_of_isDifferentiableFlow hφ
    (lipschitzWith_of_fderiv_le hDf hK) hexp

/-- **MLS Theorem 4.5 (p. 183) with all four bounds, for fields with a bounded continuous
derivative.** Under the hypotheses of `exists_lyapunov_of_exponentiallyStable_of_fderiv` (on `ℝⁿ`
with the sup norm; `f` continuous in `t ≥ 0`, `Df` continuous and bounded by `K` on
`[0, ∞) × ℝⁿ`), the origin of `ẋ = f(x, t)` is exponentially stable (Definition 4.3) if and only if
there are `V`, `V̇`, `∂V/∂x` and constants `a₁, a₂, a₃, a₄, ε > 0` with `V` continuous on
`[0, ∞) × ℝⁿ`, `a₁‖x‖² ≤ V(t, x) ≤ a₂‖x‖²`, `V̇(t, x) ≤ −a₃‖x‖²` along the solutions, `∂V/∂x (t, x)`
the derivative of `x ↦ V(t, x)` and `‖∂V/∂x (t, x)‖ ≤ a₄‖x‖`, for `t ≥ 0` and `‖x‖ ≤ ε`. No flow
hypothesis. Time first. -/
theorem exponentiallyStable_iff_exists_lyapunov_of_fderiv
    {f : ℝ → (Fin n → ℝ) → Fin n → ℝ} {Df : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {K : NNReal} (hf : ∀ x, ContinuousOn (fun t => f t x) (Ici 0))
    (hDf : ∀ t, 0 ≤ t → ∀ y, HasFDerivAt (f t) (Df t y) y)
    (hDfc : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) :
    ExponentiallyStable f 0 ↔
      ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
        ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
          ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
          HasDerivAlongSolutions f V Vdot univ ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
          ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ := by
  obtain ⟨φ, D, hφ⟩ := exists_isDifferentiableFlow hf hDf hDfc hK
  exact exponentiallyStable_iff_exists_lyapunov_of_isDifferentiableFlow hφ
    (lipschitzWith_of_fderiv_le hDf hK)

end Stability
end RoboLean
