import RoboLean.Control.PDControl
import RoboLean.Examples.ThreeLinkGravity

/-!
# The bare PD law (4.51) on the three-link arm in gravity (MLS Proposition 4.9 caution)

MLS Proposition 4.9 (p. 193) claims that for `θ̇_d ≡ 0` and `K_v, K_p > 0` the PD law (4.51)
`τ = −K_v ė − K_p e` applied to (4.47) "renders the equilibrium point `θ = θ_d` globally
asymptotically stable". For the three-link arm of MLS Example 4.3 (pp. 172–175, `threeLinkArm`)
in uniform gravity along `−z`, with no further joint forces, the gravity term at `θ = 0` is
`(0, −g (m₂ r₁ + m₃ l₁ + m₃ r₂), −g m₃ r₂)` (from `threeLinkArm_gravityTerm`, the formalized
(4.25) with `g` restored). So for `θ_d = 0`, `g ≠ 0` and `m₂ r₁ + m₃ l₁ + m₃ r₂ ≠ 0` (for example
positive masses and lengths) the constant motion `θ ≡ θ_d` does not satisfy (4.47) under (4.51),
whatever the gains: `θ = θ_d` is not a rest point of that closed loop, so the printed conclusion
fails for this system. This is a counterexample to the literal reading of the printed statement;
it does not concern the printed proof's system (4.52), which omits `N`.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean.Examples

/-- **The three-link arm of MLS Example 4.3 (p. 172) as a manipulator model (4.47)**, in uniform
gravity `g` along `−z` (`up = +z`, as in Example 4.3), with no further joint forces. -/
def threeLinkModel (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ) (g : ℝ) :
    ManipulatorModel 3 where
  chain := threeLinkArm m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃
  mass := ![m₁, m₂, m₃]
  gravity := g
  up := Rotation.zAxis
  jointForce := fun _ _ => 0

/-- **The caution on MLS Proposition 4.9 (p. 193), on Example 4.3's arm.** If `g ≠ 0` and
`m₂ r₁ + m₃ l₁ + m₃ r₂ ≠ 0`, then for all gains `K_p, K_v` the constant motion `θ ≡ 0` does not
satisfy the equations of motion (4.47) under the bare PD law (4.51) with set point `θ_d = 0`, at
any time `t`. -/
theorem threeLinkArm_not_equilibrium_pd (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ)
    {g : ℝ} (hg : g ≠ 0) (hm : m₂ * r₁ + m₃ * l₁ + m₃ * r₂ ≠ 0)
    (Kp Kv : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    ¬ (threeLinkModel m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃ g).EquationsOfMotionAt (fun _ => 0)
      (ManipulatorModel.pdTorque Kp Kv 0 t 0 0) t := by
  have hsymm : ∀ k, ((threeLinkModel m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃ g).chain.linkInertia
      k).IsSymm := by
    intro k
    fin_cases k
    · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)
    · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)
    · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)
  rw [ManipulatorModel.equationsOfMotionAt_const_pdTorque_iff _ hsymm]
  intro hN
  have h1 := congrFun hN 1
  simp only [ManipulatorModel.N, threeLinkModel, threeLinkArm_gravityTerm, Pi.add_apply,
    Pi.zero_apply, add_zero] at h1
  simp at h1
  apply hm
  have : -(g * (m₂ * r₁ + m₃ * l₁ + m₃ * r₂)) = 0 := by linarith
  have := neg_eq_zero.mp this
  exact (mul_eq_zero.mp this).resolve_left hg

end RoboLean.Examples
