import RoboLean.Geometry.RigidTransform
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Cross products in Euclidean three-space

The coordinate cross product is transported through the explicit `WithLp`
conversion. Proper rotations and the free-vector action of rigid transformations
preserve this right-handed product.
-/

open Matrix

namespace RoboLean

namespace Vec3

/-- The right-handed cross product on Euclidean three-space. -/
noncomputable def cross (u v : Vec3) : Vec3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

theorem cross_coordinates (u v : Vec3) :
    WithLp.ofLp (cross u v) = crossProduct (WithLp.ofLp u) (WithLp.ofLp v) := rfl

end Vec3

namespace Rotation

/-- Proper rotations preserve the cross product (MLS Lemma 2.1, equation 2.6). -/
theorem act_cross (R : Rotation) (u v : Vec3) :
    R.act (Vec3.cross u v) = Vec3.cross (R.act u) (R.act v) := by
  apply ext_inner_right ℝ
  intro z
  let w := R⁻¹.act z
  have hz : z = R.act w := (R.act_inv_act z).symm
  rw [hz, R.inner_act]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change WithLp.ofLp w ⬝ᵥ crossProduct (WithLp.ofLp u) (WithLp.ofLp v) =
    (R.val *ᵥ WithLp.ofLp w) ⬝ᵥ
      crossProduct (R.val *ᵥ WithLp.ofLp u) (R.val *ᵥ WithLp.ofLp v)
  rw [triple_product_eq_det, triple_product_eq_det]
  have hm : Matrix.of ![R.val *ᵥ WithLp.ofLp w, R.val *ᵥ WithLp.ofLp u,
      R.val *ᵥ WithLp.ofLp v] =
      Matrix.of ![WithLp.ofLp w, WithLp.ofLp u, WithLp.ofLp v] * R.valᵀ := by
    simp [Matrix.cons_mul, Matrix.vecMul_transpose]
  change Matrix.det (Matrix.of ![WithLp.ofLp w, WithLp.ofLp u, WithLp.ofLp v]) =
    Matrix.det (Matrix.of ![R.val *ᵥ WithLp.ofLp w, R.val *ᵥ WithLp.ofLp u,
      R.val *ᵥ WithLp.ofLp v])
  rw [hm, Matrix.det_mul, Matrix.det_transpose, R.det_eq_one, mul_one]

end Rotation

namespace RigidTransform

/-- Rigid transformations preserve cross products of free vectors (MLS Proposition 2.7). -/
theorem applyVector_cross (g : RigidTransform) (u v : Vec3) :
    g.applyVector (Vec3.cross u v) = Vec3.cross (g.applyVector u) (g.applyVector v) :=
  g.rotation.act_cross u v

end RigidTransform
end RoboLean
