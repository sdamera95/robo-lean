import RoboLean.Geometry.HybridVelocity
import RoboLean.Geometry.Wrench

/-!
# Wrenches in hybrid coordinates (MLS Exercise 18(e), p. 79)

A wrench `Fᵇ = (fᵇ, τᵇ)` applied at the origin of the body frame and written in body coordinates
is, in hybrid coordinates, the same force and moment at the same point written in the orientation of
the spatial frame: `F^h = diag(R, R) Fᵇ`, the transfer (2.65) by the pure rotation `(0, R)`. It pairs
with the hybrid velocity to the same power as `Fᵇ` with `Vᵇ`. Under a fixed change of spatial frame
`a`, `F^h` is rotated by `R_a`; under a fixed change of body frame `b` (the body wrench re-expressed
at the new body origin), `F^h` is transferred by the pure translation `(−R p_b, I)`.

Conventions: `Wrench.transform g` is the transfer (2.65)–(2.66) from B's origin to A's origin for
`g = g_AB`; the pairing is `Wrench.pair` (p. 61); the hybrid velocity is
`RigidTransform.hybridVelocity`.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace RigidTransform

/-- The hybrid coordinates of a body wrench, `F^h = (R fᵇ, R τᵇ)` for the pose `g = (p, R)` (MLS
Exercise 18(e), p. 79): the transfer (2.65), p. 62, by the pure rotation `(0, R)`. -/
def hybridWrench (g : RigidTransform) (F : Wrench) : Wrench :=
  Wrench.transform ⟨g.rotation, 0⟩ F

/-- **MLS Exercise 18(e), p. 79, interpretation:** a body wrench in hybrid coordinates pairs with the
hybrid velocity to the power it delivers in body coordinates, `F^h · V^h = Fᵇ · Vᵇ` (pairing of
p. 61). -/
theorem pair_hybridWrench_hybridVelocity {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) (F : Wrench) :
    Wrench.pair (hybridWrench (g t) F) (hybridVelocity g D t h) =
      Wrench.pair F (bodyVelocity g D t h) := by
  rw [hybridWrench, hybridVelocity_eq_adjoint_bodyVelocity, Wrench.pair_transform_adjoint]

/-- **MLS Exercise 18(e), p. 79, change of spatial frame:** for a fixed change `a` of spatial frame
(pose `a g`), the hybrid coordinates of an unchanged body wrench are rotated by `R_a` alone. -/
theorem hybridWrench_mul_left (a g : RigidTransform) (F : Wrench) :
    hybridWrench (a * g) F = Wrench.transform ⟨a.rotation, 0⟩ (hybridWrench g F) := by
  rw [hybridWrench, hybridWrench, ← Wrench.transform_mul]
  congr 1
  ext1 <;> simp

/-- **MLS Exercise 18(e), p. 79, change of body frame:** for a fixed change `b` of body frame (pose
`g b`, the body wrench re-expressed at the new body origin as `transform b⁻¹ Fᵇ`), the hybrid
coordinates are transferred by the pure translation `(−R p_b, I)` alone. -/
theorem hybridWrench_mul_right (g b : RigidTransform) (F : Wrench) :
    hybridWrench (g * b) (Wrench.transform b⁻¹ F) =
      Wrench.transform ⟨1, -g.rotation.act b.translation⟩ (hybridWrench g F) := by
  rw [hybridWrench, hybridWrench, ← Wrench.transform_mul, ← Wrench.transform_mul]
  congr 1
  ext1
  · simp [mul_assoc]
  · simp [← Rotation.act_mul, mul_assoc]

end RigidTransform
end RoboLean
