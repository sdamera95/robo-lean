import RoboLean.Geometry.TwistAdjoint
import RoboLean.Geometry.TwistExp

/-!
# Equivariance of the actual twist exponential

MLS printed p. 42, equation (2.35), states that the actual matrix exponential
commutes with rigid conjugation. Combining this with the adjoint coordinate
change on printed p. 59, equation (2.64), gives the fixed-frame covariance
of an entire constant-twist motion (ledger X08 and X44).

The twist, real parameter, and rigid transform are unrestricted. This algebraic
result does not require a normalized axis and does not assert a velocity law
for a time-dependent change of frame.
-/

noncomputable section

open scoped Matrix.Norms.Operator

namespace RoboLean

namespace RigidTransform

/-- A homogeneous rigid matrix is a unit, with the represented group inverse. -/
theorem isUnit_toHomogeneous (g : RigidTransform) : IsUnit g.toHomogeneous :=
  isUnit_iff_exists.mpr
    ⟨(g⁻¹).toHomogeneous, g.toHomogeneous_mul_inv, g.toHomogeneous_inv_mul⟩

/-- MLS equation (2.35), generalized to any real homogeneous-sized matrix. -/
theorem matrix_exp_conj (g : RigidTransform) (A : HomogeneousMatrix) :
    NormedSpace.exp (g.toHomogeneous * A * g.toHomogeneous⁻¹) =
      g.toHomogeneous * NormedSpace.exp A * g.toHomogeneous⁻¹ :=
  Matrix.exp_conj g.toHomogeneous A g.isUnit_toHomogeneous

end RigidTransform

namespace Twist

/-- Adjoint coordinate change intertwines the actual matrix exponentials. -/
theorem matrix_exp_adjoint (g : RigidTransform) (ξ : Twist) (t : ℝ) :
    NormedSpace.exp (t • (adjoint g ξ).hat) =
      g.toHomogeneous * NormedSpace.exp (t • ξ.hat) * g.toHomogeneous⁻¹ := by
  calc
    NormedSpace.exp (t • (adjoint g ξ).hat) =
        NormedSpace.exp (g.toHomogeneous * (t • ξ.hat) * g.toHomogeneous⁻¹) := by
      rw [hat_adjoint]
      simp only [mul_smul_comm, smul_mul_assoc]
    _ = _ := g.matrix_exp_conj (t • ξ.hat)

/-- Re-expressing a constant twist conjugates its whole rigid displacement.
The transform `g` is fixed across the real motion parameter `t`. -/
theorem exp_adjoint (g : RigidTransform) (ξ : Twist) (t : ℝ) :
    exp (adjoint g ξ) t = g * exp ξ t * g⁻¹ := by
  apply RigidTransform.toHomogeneous_injective
  simp only [toHomogeneous_exp, RigidTransform.toHomogeneous_mul,
    RigidTransform.toHomogeneous_inv]
  exact matrix_exp_adjoint g ξ t

/-- The same covariance expressed on point coordinates. -/
theorem exp_adjoint_applyPoint (g : RigidTransform) (ξ : Twist) (t : ℝ) (q : Vec3) :
    (exp (adjoint g ξ) t).applyPoint (g.applyPoint q) =
      g.applyPoint ((exp ξ t).applyPoint q) := by
  rw [exp_adjoint]
  simp

/-- A constant-twist motion fixes its own twist under the adjoint, `Ad_{exp(ξ̂t)} ξ = ξ`, for every
real twist and parameter: `ξ̂` commutes with `exp(tξ̂)`, so the conjugation of MLS eq. (2.35),
p. 42, leaves `ξ̂` unchanged. This is the step behind MLS eq. (4.27), p. 176, where
`A_{lj}` may start at joint `j + 1` because the factor `exp(ξ̂ⱼθⱼ)` does not move `ξⱼ`. -/
theorem adjoint_exp_self (ξ : Twist) (t : ℝ) : adjoint (exp ξ t) ξ = ξ := by
  apply hat_injective
  rw [hat_adjoint, ← RigidTransform.toHomogeneous_inv]
  have hc : Commute (exp ξ t).toHomogeneous ξ.hat := by
    rw [toHomogeneous_exp]
    exact (((Commute.refl ξ.hat).smul_right t).exp_right).symm
  rw [hc.eq, mul_assoc, RigidTransform.toHomogeneous_mul_inv, mul_one]

end Twist

end RoboLean
