import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Rigid transformations in three-dimensional Euclidean space

Rotations reuse Mathlib's special orthogonal group. Vectors carry the Euclidean
norm through `EuclideanSpace`, and matrices act on column coordinates.

The product `g * h` applies `h` first. Points transform as `R x + p`, while free
vectors transform as `R v`. Frame labels and physical units are not encoded here.
-/

open Matrix

namespace RoboLean

/-- Three-dimensional real coordinate space with its Euclidean metric. -/
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

/-- Proper rotations: orthogonal real matrices with determinant one. -/
abbrev Rotation : Type := Matrix.specialOrthogonalGroup (Fin 3) ℝ

namespace Rotation

/-- The linear action of a rotation on Euclidean coordinates. -/
noncomputable def act (R : Rotation) : Vec3 →ₗ[ℝ] Vec3 :=
  Matrix.toEuclideanLin R.val

theorem act_apply (R : Rotation) (x : Vec3) (i : Fin 3) :
    R.act x i = (R.val *ᵥ WithLp.ofLp x) i := rfl

theorem transpose_mul (R : Rotation) : R.valᵀ * R.val = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.property.1

theorem mul_transpose (R : Rotation) : R.val * R.valᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp R.property.1

/-- For real orthogonal matrices, group inversion is transpose. -/
@[simp] theorem inv_val (R : Rotation) : (R⁻¹).val = R.valᵀ := rfl

@[simp] theorem det_eq_one (R : Rotation) : Matrix.det R.val = 1 := R.property.2

@[simp] theorem act_one (x : Vec3) : (1 : Rotation).act x = x := by
  apply WithLp.ofLp_injective
  change (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x = WithLp.ofLp x
  exact Matrix.one_mulVec _

@[simp] theorem act_mul (R S : Rotation) (x : Vec3) :
    (R * S).act x = R.act (S.act x) := by
  apply WithLp.ofLp_injective
  change (R.val * S.val) *ᵥ WithLp.ofLp x = R.val *ᵥ (S.val *ᵥ WithLp.ofLp x)
  exact (Matrix.mulVec_mulVec _ _ _).symm

theorem inner_act (R : Rotation) (x y : Vec3) :
    inner ℝ (R.act x) (R.act y) = inner ℝ x y := by
  simp only [act, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (R.val *ᵥ WithLp.ofLp y) ⬝ᵥ (R.val *ᵥ WithLp.ofLp x) =
    WithLp.ofLp y ⬝ᵥ WithLp.ofLp x
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    transpose_mul, Matrix.one_mulVec, dotProduct_comm]

/-- The matrix action packaged with its Euclidean norm-preservation proof. -/
noncomputable def toLinearIsometry (R : Rotation) : Vec3 →ₗᵢ[ℝ] Vec3 :=
  R.act.isometryOfInner R.inner_act

@[simp] theorem norm_act (R : Rotation) (x : Vec3) : ‖R.act x‖ = ‖x‖ :=
  R.toLinearIsometry.norm_map x

@[simp] theorem dist_act (R : Rotation) (x y : Vec3) :
    dist (R.act x) (R.act y) = dist x y :=
  R.toLinearIsometry.dist_map x y

@[simp] theorem inv_act_act (R : Rotation) (x : Vec3) :
    R⁻¹.act (R.act x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

@[simp] theorem act_inv_act (R : Rotation) (x : Vec3) :
    R.act (R⁻¹.act x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

end Rotation

/-- A proper rigid transformation, with named rotation and translation fields. -/
@[ext]
structure RigidTransform where
  rotation : Rotation
  translation : Vec3

namespace RigidTransform

noncomputable instance : One RigidTransform := ⟨⟨1, 0⟩⟩

noncomputable instance : Mul RigidTransform :=
  ⟨fun g h ↦ ⟨g.rotation * h.rotation, g.rotation.act h.translation + g.translation⟩⟩

noncomputable instance : Inv RigidTransform :=
  ⟨fun g ↦ ⟨g.rotation⁻¹, -(g.rotation⁻¹).act g.translation⟩⟩

@[simp] theorem one_rotation : (1 : RigidTransform).rotation = 1 := rfl
@[simp] theorem one_translation : (1 : RigidTransform).translation = 0 := rfl
@[simp] theorem mul_rotation (g h : RigidTransform) :
    (g * h).rotation = g.rotation * h.rotation := rfl
@[simp] theorem mul_translation (g h : RigidTransform) :
    (g * h).translation = g.rotation.act h.translation + g.translation := rfl
@[simp] theorem inv_rotation (g : RigidTransform) :
    g⁻¹.rotation = g.rotation⁻¹ := rfl
@[simp] theorem inv_translation (g : RigidTransform) :
    g⁻¹.translation = -(g.rotation⁻¹).act g.translation := rfl

/-- The inverse translation in the textbook's explicit matrix coordinates. -/
theorem inv_translation_coordinates (g : RigidTransform) :
    WithLp.ofLp g⁻¹.translation = -(g.rotation.valᵀ *ᵥ WithLp.ofLp g.translation) := rfl

noncomputable instance : Group RigidTransform where
  mul_assoc g h k := by
    ext <;> simp [mul_assoc, map_add, add_assoc]
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp

/-- Action on a point; translation affects point coordinates. -/
noncomputable def applyPoint (g : RigidTransform) (x : Vec3) : Vec3 :=
  g.rotation.act x + g.translation

/-- Action on a free vector; translation does not affect it. -/
noncomputable def applyVector (g : RigidTransform) (v : Vec3) : Vec3 :=
  g.rotation.act v

@[simp] theorem one_applyPoint (x : Vec3) : (1 : RigidTransform).applyPoint x = x := by
  simp [applyPoint]

@[simp] theorem mul_applyPoint (g h : RigidTransform) (x : Vec3) :
    (g * h).applyPoint x = g.applyPoint (h.applyPoint x) := by
  simp [applyPoint, map_add, add_assoc]

@[simp] theorem one_applyVector (v : Vec3) : (1 : RigidTransform).applyVector v = v := by
  simp [applyVector]

@[simp] theorem mul_applyVector (g h : RigidTransform) (v : Vec3) :
    (g * h).applyVector v = g.applyVector (h.applyVector v) := by
  simp [applyVector]

@[simp] theorem inv_applyPoint_applyPoint (g : RigidTransform) (x : Vec3) :
    g⁻¹.applyPoint (g.applyPoint x) = x := by
  rw [← mul_applyPoint, inv_mul_cancel, one_applyPoint]

@[simp] theorem applyPoint_inv_applyPoint (g : RigidTransform) (x : Vec3) :
    g.applyPoint (g⁻¹.applyPoint x) = x := by
  rw [← mul_applyPoint, mul_inv_cancel, one_applyPoint]

theorem applyPoint_sub_applyPoint (g : RigidTransform) (x y : Vec3) :
    g.applyPoint x - g.applyPoint y = g.applyVector (x - y) := by
  simp [applyPoint, applyVector, map_sub]

theorem applyPoint_add (g : RigidTransform) (x v : Vec3) :
    g.applyPoint (x + v) = g.applyPoint x + g.applyVector v := by
  simp [applyPoint, applyVector, map_add, add_right_comm]

@[simp] theorem inner_applyVector (g : RigidTransform) (v w : Vec3) :
    inner ℝ (g.applyVector v) (g.applyVector w) = inner ℝ v w :=
  g.rotation.inner_act v w

@[simp] theorem norm_applyVector (g : RigidTransform) (v : Vec3) :
    ‖g.applyVector v‖ = ‖v‖ := g.rotation.norm_act v

@[simp] theorem dist_applyPoint (g : RigidTransform) (x y : Vec3) :
    dist (g.applyPoint x) (g.applyPoint y) = dist x y := by
  simpa only [applyPoint, dist_add_right] using g.rotation.dist_act x y

/-- Algebraic orientation convention: the linear part has determinant one. -/
@[simp] theorem rotation_det (g : RigidTransform) : g.rotation.val.det = 1 :=
  g.rotation.det_eq_one

end RigidTransform
end RoboLean
