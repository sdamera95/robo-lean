import RoboLean.Control.PDControl
import RoboLean.Control.ComputedTorque
import RoboLean.Examples.PlanarTwoLinkDynamics

/-!
# The planar two-link arm under PD and computed torque control (MLS §5.2–5.3)

The arm of MLS Figure 4.4 (p. 164, `planarTwoLinkArm`, E012) as a `ManipulatorModel 2`, with link
masses `m₁, m₂`, an arbitrary gravitational constant `g` and upward vector `up` (MLS treats the arm
as horizontal, `up = +z`, p. 165; any `up`, for example a vertical plane with `up = +y`, is allowed
here) and an arbitrary field `Nₑ` of further joint forces. For positive masses and principal
moments it satisfies every model hypothesis of the controller theorems: symmetric link inertias
and `M(θ)` positive definite at every configuration. With the gains `K_p = K_v = I`:

* PD control with compensation of `N` makes `(θ_d, 0)` a Lyapunov-stable equilibrium
  (`planarTwoLinkArm_stableAt_pdCompensatedTorque`, MLS Proposition 4.9 as formalized);
* computed torque gives exponential tracking of every twice-differentiable desired trajectory
  (`planarTwoLinkArm_computedTorque_tracking`, MLS Proposition 4.8).

These are instances showing that the hypotheses of the general theorems can be met; they are not
separate results, and nothing here concerns a physical arm.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean.Examples

/-- **The planar two-link arm of MLS Figure 4.4 (p. 164) as a manipulator model (4.47)**, with link
masses `![m₁, m₂]`, gravitational constant `g`, upward vector `up` and further joint forces `Nₑ`. -/
def planarTwoLinkModel (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) : ManipulatorModel 2 where
  chain := planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  mass := ![m₁, m₂]
  gravity := g
  up := up
  jointForce := Ne

variable (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)

/-- The inertia matrix of the model is the arm's `M(θ)` (MLS eq. (4.10), E012). -/
theorem planarTwoLinkModel_M (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M =
      (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix := by
  funext q
  unfold ManipulatorModel.M planarTwoLinkModel
  rfl

/-- The link inertias of the planar arm `[[mᵢ I, 0], [0, diag(Iᵢ)]]` are symmetric (MLS p. 162). -/
theorem planarTwoLinkArm_linkInertia_isSymm (k : Fin 2) :
    ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkInertia k).IsSymm := by
  fin_cases k
  · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)
  · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)

/-- **MLS Proposition 4.9 as formalized, for the planar two-link arm.** With positive masses and
principal moments, any gravity data and joint forces, and `K_p = K_v = I`, PD control with
compensation of `N` makes the set point `(θ_d, 0)` stable in the sense of Lyapunov at every
`t₀ ≥ 0`. -/
theorem planarTwoLinkArm_stableAt_pdCompensatedTorque (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (θd : Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.StableAt
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdCompensatedTorque 1 1 θd))
      (θd, 0) t₀ := by
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  exact ManipulatorModel.stableAt_pdCompensatedTorque _ hsymm hM Matrix.PosDef.one
    Matrix.PosSemidef.one θd ht₀

/-- **MLS Proposition 4.8 for the planar two-link arm.** With positive masses and principal
moments, any gravity data and joint forces, and `K_p = K_v = I`, there are `m, α > 0` such that
every solution of the arm under the computed torque law, for every twice-differentiable desired
trajectory, tracks it with error at most `m e^{−α(t − t₀)}` times the initial error. -/
theorem planarTwoLinkArm_computedTorque_tracking (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ m > 0, ∃ α > 0, ∀ {θd θd' θd'' : ℝ → Fin 2 → ℝ}, (∀ t, HasDerivAt θd (θd' t) t) →
      (∀ t, HasDerivAt θd' (θd'' t) t) → ∀ t₀, 0 ≤ t₀ →
      ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).computedTorque 1 1 θd θd' θd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  exact ManipulatorModel.computedTorque_tracking _ hM Matrix.PosDef.one Matrix.PosDef.one

end RoboLean.Examples
