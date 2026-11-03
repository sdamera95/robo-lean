import RoboLean.Geometry.IsometryRigidBody

/-!
# The reflection of MLS p. 21 preserves distances but is not a rigid body transformation

MLS p. 21: "the mapping `(x, y, z) ↦ (x, y, −z)` preserves distances but reflects points in the
body about the `xy` plane", which is why Definition 2.1 also requires the cross product to be
preserved. This file checks both halves on that map: it satisfies the length clause of
Definition 2.1 and fails the cross-product clause, so it is not a rigid body transformation and is
not the point action of any `(p, R) ∈ SE(3)`.
-/

noncomputable section

namespace RoboLean.Examples

/-- The reflection `(x, y, z) ↦ (x, y, −z)` about the `xy` plane, MLS p. 21. -/
def reflectXY (v : Vec3) : Vec3 :=
  WithLp.toLp 2 ![v 0, v 1, -v 2]

/-- MLS p. 21: the reflection about the `xy` plane preserves distances, the length clause of
Definition 2.1. Euclidean norm. -/
theorem reflectXY_norm_sub (p q : Vec3) : ‖reflectXY p - reflectXY q‖ = ‖p - q‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, reflectXY]
  ring

/-- MLS p. 21: the reflection about the `xy` plane does not preserve cross products, so it is not
a rigid body transformation in the sense of Definition 2.1 (it is not the point action of any
element of `SE(3)`, `isRigidBodyTransformation_iff`). -/
theorem not_isRigidBodyTransformation_reflectXY : ¬ IsRigidBodyTransformation reflectXY := by
  intro hg
  have h := congrArg (fun v : Vec3 => v 2)
    (hg.cross 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1))
  simp [reflectXY, Vec3.cross, crossProduct] at h
  norm_num at h

end RoboLean.Examples
