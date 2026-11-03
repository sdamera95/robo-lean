import RoboLean.Nonholonomic.FlowsGroup
import RoboLean.Examples.CommutingFlowsSine

/-!
# The flow of `X(x) = (sin x₁, 0)` is a diffeomorphism with the group property (MLS pp. 322–323)

For the field `sinFirst` of `Examples.CommutingFlowsSine` on `ℝ × ℝ` (sup norm), the flows of
`X` and `−X` exist and are differentiable in the initial state
(`exists_isDifferentiableFlow_autonomous`), so every hypothesis of `flow_add` and
`flow_isDiffeomorph` is met on this nonlinear field. The systems are time-invariant, written
`fun _ => X` (time first, ignored). This is an instance of a general theorem; it is not a claim
about a mechanism.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean.Examples

/-- **The flow of `sinFirst` is a diffeomorphism with the group property (MLS pp. 322–323), every
hypothesis met:** for `X(x) = (sin x₁, 0)` on `ℝ × ℝ` there are flows `φ` of `X` and `φ'` of `−X`
differentiable in the initial state with `φ^X_t ∘ φ^X_s = φ^X_{t+s}` for `t, s ≥ 0` and, for
every `t ≥ 0`, `φ^X_t` and `φ^{−X}_t` inverse to each other. -/
theorem exists_flow_sinFirst_isDiffeomorph :
    ∃ φ φ' : ℝ → ℝ → ℝ × ℝ → ℝ × ℝ, ∃ DX' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      ∃ D D' : ℝ → ℝ → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
        Stability.IsDifferentiableFlow (fun _ => sinFirst)
          (fun _ => sinFirstDeriv) φ D ∧
        Stability.IsDifferentiableFlow (fun _ => -sinFirst) (fun _ => DX') φ' D' ∧
        (∀ t s, 0 ≤ t → 0 ≤ s → ∀ x, φ t 0 (φ s 0 x) = φ (t + s) 0 x) ∧
        ∀ t, 0 ≤ t → Function.LeftInverse (φ' t 0) (φ t 0) ∧
          Function.RightInverse (φ' t 0) (φ t 0) := by
  have hK : ∀ y, ‖sinFirstDeriv y‖ ≤ ((1 : NNReal) : ℝ) := fun y => by
    simpa using norm_sinFirstDeriv_le y
  obtain ⟨φ, D, hX⟩ :=
    Stability.exists_isDifferentiableFlow_autonomous hasFDerivAt_sinFirst
      continuous_sinFirstDeriv hK
  obtain ⟨φ', D', hX'⟩ :=
    Stability.exists_isDifferentiableFlow_autonomous (F := -sinFirst)
      (DF := fun x => -sinFirstDeriv x) (fun y => (hasFDerivAt_sinFirst y).neg)
      continuous_sinFirstDeriv.neg fun y => by rw [norm_neg]; exact hK y
  exact ⟨φ, φ', fun x => -sinFirstDeriv x, D, D', hX, hX',
    fun t s ht hs x => Nonholonomic.flow_add hX ht hs x, fun t ht =>
      ⟨(Nonholonomic.flow_isDiffeomorph hX hX' ht).1,
        (Nonholonomic.flow_isDiffeomorph hX hX' ht).2.1⟩⟩

end RoboLean.Examples
