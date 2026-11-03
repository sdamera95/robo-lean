import RoboLean.Nonholonomic.FlowsTwoSided
import RoboLean.Examples.CommutingFlowsSine

/-!
# The flow of `X(x) = (sin x₁, 0)` for all real times (MLS pp. 322–323)

For the field `sinFirst` of `Examples.CommutingFlowsSine` on `ℝ × ℝ` (sup norm), the flows of
`X` and `−X` exist and are differentiable in the initial state
(`exists_isDifferentiableFlow_autonomous`), so every hypothesis of `twoSidedFlow_zero`,
`twoSidedFlow_add` and `isIntegralCurve_twoSidedFlow` is met on this nonlinear field: the
two-sided flow is the identity at time `0`, has the group property for all real `t` and `s`, and
is an integral curve of `X` through every point. The systems are time-invariant, written
`fun _ => X` (time first, ignored). This is an instance of a general theorem; it is not a claim
about a mechanism.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean.Examples

/-- **The flow of `sinFirst` for all real times (MLS pp. 322–323), every hypothesis met:** for
`X(x) = (sin x₁, 0)` on `ℝ × ℝ` there are flows `φ` of `X` and `φ'` of `−X` differentiable in the
initial state whose two-sided flow is the identity at `0`, has the group property for all real `t`,
`s` and is an integral curve of `X` through every point. -/
theorem exists_twoSidedFlow_sinFirst :
    ∃ φ φ' : ℝ → ℝ → ℝ × ℝ → ℝ × ℝ, ∃ DX' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      ∃ D D' : ℝ → ℝ → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
        Stability.IsDifferentiableFlow (fun _ => sinFirst) (fun _ => sinFirstDeriv) φ D ∧
        Stability.IsDifferentiableFlow (fun _ => -sinFirst) (fun _ => DX') φ' D' ∧
        (∀ x, Nonholonomic.twoSidedFlow φ φ' 0 x = x) ∧
        (∀ t s x, Nonholonomic.twoSidedFlow φ φ' t (Nonholonomic.twoSidedFlow φ φ' s x) =
          Nonholonomic.twoSidedFlow φ φ' (t + s) x) ∧
        ∀ x, IsIntegralCurve (fun t => Nonholonomic.twoSidedFlow φ φ' t x) (fun _ => sinFirst) := by
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
    fun x => Nonholonomic.twoSidedFlow_zero hX x,
    fun t s x => Nonholonomic.twoSidedFlow_add hX hX' t s x,
    fun x => Nonholonomic.isIntegralCurve_twoSidedFlow hX hX' x⟩

end RoboLean.Examples
