import RoboLean.Geometry.TwistAdjoint
import RoboLean.Geometry.TwistBracket

/-!
# Adjoint preservation of the twist bracket

This is an algebraic consequence of the matrix commutator in MLS Appendix A,
printed pp. 410–411, Examples A.6–A.8, and the conjugation formula in Example
A.18 on printed p. 415. The coordinate adjoint and bracket are independently
defined; their existing hat bridges connect this proof to those coordinates.
-/

noncomputable section

namespace RoboLean
namespace Twist

/-- Conjugation by an actual homogeneous rigid transform preserves matrix
commutators. Only associativity and the independently proved inverse law are used. -/
theorem homogeneous_conjugate_commutator (g : RigidTransform) (A B : HomogeneousMatrix) :
    g.toHomogeneous * (A * B - B * A) * g.toHomogeneous⁻¹ =
      (g.toHomogeneous * A * g.toHomogeneous⁻¹) *
        (g.toHomogeneous * B * g.toHomogeneous⁻¹) -
      (g.toHomogeneous * B * g.toHomogeneous⁻¹) *
        (g.toHomogeneous * A * g.toHomogeneous⁻¹) := by
  have hi : g.toHomogeneous⁻¹ * g.toHomogeneous = 1 := by
    rw [← RigidTransform.toHomogeneous_inv]
    exact RigidTransform.toHomogeneous_inv_mul g
  have hm (M N : HomogeneousMatrix) :
      (g.toHomogeneous * M * g.toHomogeneous⁻¹) *
        (g.toHomogeneous * N * g.toHomogeneous⁻¹) =
      g.toHomogeneous * (M * N) * g.toHomogeneous⁻¹ := by
    calc
      _ = g.toHomogeneous *
          (M * ((g.toHomogeneous⁻¹ * g.toHomogeneous) * (N * g.toHomogeneous⁻¹))) := by
        simp only [mul_assoc]
      _ = _ := by rw [hi, one_mul]; simp only [mul_assoc]
  rw [hm, hm, mul_sub, sub_mul]

/-- The independently defined linear-first coordinate adjoint preserves the
independently defined twist bracket for all real twists and rigid transforms. -/
theorem adjoint_bracket (g : RigidTransform) (ξ η : Twist) :
    adjoint g (bracket ξ η) = bracket (adjoint g ξ) (adjoint g η) := by
  apply hat_injective
  simp only [hat_adjoint, hat_bracket]
  exact homogeneous_conjugate_commutator g ξ.hat η.hat

/-- The real linear adjoint equivalence preserves the bracket as well. -/
theorem adjointEquiv_bracket (g : RigidTransform) (ξ η : Twist) :
    adjointEquiv g (bracket ξ η) = bracket (adjointEquiv g ξ) (adjointEquiv g η) :=
  adjoint_bracket g ξ η

/-- Two twists commute precisely when their images under the same adjoint commute. -/
theorem adjoint_bracket_eq_zero_iff (g : RigidTransform) (ξ η : Twist) :
    bracket (adjoint g ξ) (adjoint g η) = 0 ↔ bracket ξ η = 0 := by
  rw [← adjoint_bracket]
  constructor
  · intro h
    have hi := congrArg (adjoint g⁻¹) h
    simpa only [adjoint_inv_adjoint, adjoint_zero] using hi
  · intro h
    rw [h, adjoint_zero]

end Twist
end RoboLean
