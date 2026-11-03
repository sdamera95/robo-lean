import RoboLean.Examples.SlotConstraintWorkspace
import RoboLean.Control.WorkspacePDControl
import RoboLean.Control.ConstrainedManipulator

/-!
# The slot dynamics through workspace coordinates as explicit formulas (MLS Exercise 12(c))

MLS Chapter 4, Exercise 12(c), printed p. 210: "Write the dynamics of the constrained system in terms
of `w` and its derivatives, the dynamic parameters of the unconstrained system, and the matrices
`J(θ)` and `K(s)`."

Model. The unconstrained system is any two-joint manipulator model `(M, C, N)` (`ManipulatorModel 2`,
for instance the planar two-link arm), the workspace coordinates are `w = p(θ)` with `p` the
end-effector map `planarArmXY` of the planar arm and `J(θ)` its Jacobian, and the workspace system
is (4.55), p. 197, written as a robot in `w` through an inverse `g` of `p`
(`ManipulatorModel.workspaceRobot`; the arm's `p` is invertible only locally, and `g` is any map with
the needed inverse property where it is used). The slot is `w = f(s) = (l + s cos α, s sin α)` with
`K = ∂f/∂s = (cos α, sin α)` and `K̇ = 0`. Results: the projected inertia, Coriolis matrix and force
(4.61) of the workspace system on the slot are `Kᵀ J⁻ᵀ M J⁻¹ K`, `Kᵀ J⁻ᵀ (C − M J⁻¹ J̇) J⁻¹ K` and
`Kᵀ J⁻ᵀ N`, all at `θ = g(f(s))` and `θ̇ = J⁻¹ K ṡ`; and the constrained equations of motion in
workspace coordinates give `Kᵀ J⁻ᵀ M J⁻¹ K s̈ + Kᵀ J⁻ᵀ (C − M J⁻¹ J̇) J⁻¹ K ṡ + Kᵀ J⁻ᵀ N = Kᵀ F`.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

open MapJacobian Control

/-- The Jacobian `K = (cos α, sin α)` of the slot parameterization (MLS Exercise 12(b), p. 209), as
a `2 × 1` matrix. -/
def slotK (α : ℝ) : Matrix (Fin 2) (Fin 1) ℝ := !![Real.cos α; Real.sin α]

/-- **MLS Exercise 12(c), p. 210: the inertia of the slot dynamics in workspace coordinates.** The
projected inertia (4.61) of the workspace system (4.55) on the slot is `Kᵀ J⁻ᵀ M(θ) J⁻¹ K` at
`θ = g(f(s))`, `J = J(θ)` the Jacobian of `planarArmXY`. -/
theorem slot_workspace_projectedM (P : ManipulatorModel 2) (l₁ l₂ l α : ℝ)
    (g : (Fin 2 → ℝ) → Fin 2 → ℝ) (s : Fin 1 → ℝ) :
    (P.workspaceRobot (planarArmXY l₁ l₂) g).projectedM (slotPath l α) s =
      (slotK α)ᵀ * (((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹)ᵀ *
        P.M (g (slotPath l α s)) * (jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹) * slotK α := by
  simp only [RobotSystem.projectedM, ManipulatorModel.workspaceRobot, ManipulatorModel.workspaceM,
    jac_slotPath, slotK]

/-- **MLS Exercise 12(c), p. 210: the Coriolis matrix of the slot dynamics in workspace
coordinates.** The projected Coriolis matrix (4.61) of the workspace system on the slot is
`Kᵀ J⁻ᵀ (C(θ, θ̇) − M(θ) J⁻¹ J̇) J⁻¹ K` at `θ = g(f(s))`, `θ̇ = J⁻¹ K ṡ`, with `J̇ = J̇(θ, θ̇)`
(`K̇ = 0`). -/
theorem slot_workspace_projectedC (P : ManipulatorModel 2) (l₁ l₂ l α : ℝ)
    (g : (Fin 2 → ℝ) → Fin 2 → ℝ) (s s' : Fin 1 → ℝ) :
    (P.workspaceRobot (planarArmXY l₁ l₂) g).projectedC (slotPath l α) s s' =
      (slotK α)ᵀ * P.workspaceC (planarArmXY l₁ l₂) (g (slotPath l α s))
        ((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹ *ᵥ (slotK α *ᵥ s')) * slotK α := by
  simp only [RobotSystem.projectedC, ManipulatorModel.workspaceRobot, jac_slotPath, jacDot_slotPath,
    slotK, Matrix.mul_zero, add_zero, Matrix.mul_assoc]

/-- **MLS Exercise 12(c), p. 210: the force term of the slot dynamics in workspace coordinates.**
The projected force (4.61) of the workspace system on the slot is `Kᵀ J⁻ᵀ N(θ, θ̇)` at
`θ = g(f(s))`, `θ̇ = J⁻¹ K ṡ`. -/
theorem slot_workspace_projectedN (P : ManipulatorModel 2) (l₁ l₂ l α : ℝ)
    (g : (Fin 2 → ℝ) → Fin 2 → ℝ) (s s' : Fin 1 → ℝ) :
    (P.workspaceRobot (planarArmXY l₁ l₂) g).projectedN (slotPath l α) s s' =
      (slotK α)ᵀ *ᵥ (((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹)ᵀ *ᵥ
        P.N (g (slotPath l α s))
          ((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹ *ᵥ (slotK α *ᵥ s'))) := by
  simp only [RobotSystem.projectedN, ManipulatorModel.workspaceRobot, ManipulatorModel.workspaceN,
    jac_slotPath, slotK]

/-- **MLS Exercise 12(c), p. 210: the dynamics of the constrained system through workspace
coordinates.** If the workspace system satisfies its equations of motion on the slot at
`w = f(s)`, `ẇ = K ṡ`, `ẅ = K s̈` with a constraint multiplier and workspace force `F`, then
`Kᵀ J⁻ᵀ M J⁻¹ K s̈ + Kᵀ J⁻ᵀ (C − M J⁻¹ J̇) J⁻¹ K ṡ + Kᵀ J⁻ᵀ N = Kᵀ F` with the parameters at
`θ = g(f(s))`, `θ̇ = J⁻¹ K ṡ`. -/
theorem slot_workspace_dynamics (P : ManipulatorModel 2) (l₁ l₂ l α : ℝ)
    (g : (Fin 2 → ℝ) → Fin 2 → ℝ) {s s' s'' : Fin 1 → ℝ} {F : Fin 2 → ℝ} {μ : Fin 1 → ℝ}
    (hE : (P.workspaceRobot (planarArmXY l₁ l₂) g).ConstrainedEquationsAt (slotConstraint l α)
      (slotPath l α s) (slotK α *ᵥ s') (slotK α *ᵥ s'') F μ) :
    ((slotK α)ᵀ * (((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹)ᵀ *
        P.M (g (slotPath l α s)) * (jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹) * slotK α) *ᵥ
        s'' +
      ((slotK α)ᵀ * P.workspaceC (planarArmXY l₁ l₂) (g (slotPath l α s))
        ((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹ *ᵥ (slotK α *ᵥ s')) * slotK α) *ᵥ s' +
      (slotK α)ᵀ *ᵥ (((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹)ᵀ *ᵥ
        P.N (g (slotPath l α s))
          ((jac (planarArmXY l₁ l₂) (g (slotPath l α s)))⁻¹ *ᵥ (slotK α *ᵥ s'))) =
      (slotK α)ᵀ *ᵥ F := by
  have h := (P.workspaceRobot (planarArmXY l₁ l₂) g).projected_eq_of_constrainedEquationsAt
    (isSurfaceParametrization_slot l α) (φ := s) (φ' := s') (φ'' := s'') (by
      rw [jac_slotPath, jacDot_slotPath, Matrix.zero_mulVec, add_zero]
      exact hE)
  rw [slot_workspace_projectedM, slot_workspace_projectedC, slot_workspace_projectedN,
    jac_slotPath] at h
  exact h

end RoboLean.Examples
