import RoboLean.Geometry.RigidTransform
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Homogeneous coordinates for rigid transforms

The row and column index `Fin 3 ⊕ Fin 1` keeps the spatial and homogeneous
coordinates separate. The matrix is `[R p; 0 1]`, as in MLS §2.3.1, printed
pp. 36–37, equations (2.23)–(2.24). Points have last coordinate `1`; vectors
have last coordinate `0`.
-/

noncomputable section

namespace RoboLean

open Matrix

abbrev HomogeneousIndex := Fin 3 ⊕ Fin 1

abbrev HomogeneousMatrix := Matrix HomogeneousIndex HomogeneousIndex ℝ

/-- Homogeneous coordinates of a point. -/
def homogeneousPoint (x : Vec3) : HomogeneousIndex → ℝ :=
  Sum.elim (WithLp.ofLp x) (fun _ => 1)

/-- Homogeneous coordinates of a displacement vector. -/
def homogeneousVector (v : Vec3) : HomogeneousIndex → ℝ :=
  Sum.elim (WithLp.ofLp v) (fun _ => 0)

namespace RigidTransform

/-- The homogeneous matrix `[R p; 0 1]` of a rigid transform. -/
def toHomogeneous (g : RigidTransform) : HomogeneousMatrix :=
  fromBlocks g.rotation.val (Matrix.of fun i _ => g.translation i) 0 1

@[simp]
theorem toHomogeneous_rotation (g : RigidTransform) :
    g.toHomogeneous.toBlocks₁₁ = g.rotation.val := rfl

@[simp]
theorem toHomogeneous_translation (g : RigidTransform) (i : Fin 3) :
    g.toHomogeneous (Sum.inl i) (Sum.inr 0) = g.translation i := rfl

@[simp]
theorem toHomogeneous_lowerLeft (g : RigidTransform) :
    g.toHomogeneous.toBlocks₂₁ = 0 := rfl

@[simp]
theorem toHomogeneous_lowerRight (g : RigidTransform) :
    g.toHomogeneous.toBlocks₂₂ = 1 := rfl

theorem toHomogeneous_injective : Function.Injective toHomogeneous := by
  intro g h e
  have hr : g.rotation = h.rotation := by
    apply Subtype.ext
    exact congrArg Matrix.toBlocks₁₁ e
  have ht : g.translation = h.translation := by
    ext i
    exact congrArg (fun M => M (Sum.inl i) (Sum.inr 0)) e
  cases g
  cases h
  cases hr
  cases ht
  rfl

@[simp]
theorem toHomogeneous_one : toHomogeneous 1 = 1 := by
  change Matrix.fromBlocks 1 0 0 1 = (1 : HomogeneousMatrix)
  exact Matrix.fromBlocks_one

@[simp]
theorem toHomogeneous_mul (g h : RigidTransform) :
    (g * h).toHomogeneous = g.toHomogeneous * h.toHomogeneous := by
  simp only [toHomogeneous, mul_rotation, mul_translation,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]
  congr 1

/-- The pair representation embeds multiplicatively into homogeneous matrices. -/
def toHomogeneousHom : RigidTransform →* HomogeneousMatrix where
  toFun := toHomogeneous
  map_one' := toHomogeneous_one
  map_mul' := toHomogeneous_mul

@[simp]
theorem toHomogeneous_inv_mul (g : RigidTransform) :
    (g⁻¹).toHomogeneous * g.toHomogeneous = 1 := by
  rw [← toHomogeneous_mul, inv_mul_cancel, toHomogeneous_one]

@[simp]
theorem toHomogeneous_mul_inv (g : RigidTransform) :
    g.toHomogeneous * (g⁻¹).toHomogeneous = 1 := by
  rw [← toHomogeneous_mul, mul_inv_cancel, toHomogeneous_one]

@[simp]
theorem toHomogeneous_inv (g : RigidTransform) :
    (g⁻¹).toHomogeneous = g.toHomogeneous⁻¹ := by
  exact (Matrix.inv_eq_left_inv (toHomogeneous_inv_mul g)).symm

theorem toHomogeneous_mulVec_point (g : RigidTransform) (x : Vec3) :
    g.toHomogeneous *ᵥ homogeneousPoint x = homogeneousPoint (g.applyPoint x) := by
  rw [toHomogeneous, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    simp [homogeneousPoint, applyPoint, Rotation.act_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
  | inr i =>
    simp [homogeneousPoint, Matrix.zero_mulVec, Matrix.one_mulVec]

theorem toHomogeneous_mulVec_vector (g : RigidTransform) (v : Vec3) :
    g.toHomogeneous *ᵥ homogeneousVector v = homogeneousVector (g.applyVector v) := by
  rw [toHomogeneous, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    simp [homogeneousVector, applyVector, Rotation.act_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
  | inr i =>
    simp [homogeneousVector, Matrix.zero_mulVec, Matrix.one_mulVec]

end RigidTransform

/-- Exactly the homogeneous matrices with a proper rotation in the upper left
block and lower blocks `[0 1]`; translation is unrestricted. -/
def HomogeneousTransform :=
  { M : HomogeneousMatrix //
    M.toBlocks₁₁ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
    M.toBlocks₂₁ = 0 ∧ M.toBlocks₂₂ = 1 }

namespace HomogeneousTransform

/-- Recover the rotation and translation from a homogeneous rigid matrix. -/
def toRigidTransform (M : HomogeneousTransform) : RigidTransform where
  rotation := ⟨M.val.toBlocks₁₁, M.property.1⟩
  translation := WithLp.toLp 2 (fun i => M.val (Sum.inl i) (Sum.inr 0))

@[simp]
theorem toRigidTransform_toHomogeneous (M : HomogeneousTransform) :
    M.toRigidTransform.toHomogeneous = M.val := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨rfl, ?_, M.property.2.1.symm, M.property.2.2.symm⟩
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

end HomogeneousTransform

namespace RigidTransform

/-- The homogeneous representation with its defining block conditions. -/
def asHomogeneous (g : RigidTransform) : HomogeneousTransform :=
  ⟨g.toHomogeneous, g.rotation.property, rfl, rfl⟩

@[simp]
theorem asHomogeneous_toRigidTransform (g : RigidTransform) :
    g.asHomogeneous.toRigidTransform = g := by
  apply toHomogeneous_injective
  exact HomogeneousTransform.toRigidTransform_toHomogeneous g.asHomogeneous

/-- Pair and homogeneous representations are equivalent, with no condition on
the translation and exactly the proper-rotation and lower-row conditions above. -/
def homogeneousEquiv : RigidTransform ≃ HomogeneousTransform where
  toFun := asHomogeneous
  invFun := HomogeneousTransform.toRigidTransform
  left_inv := asHomogeneous_toRigidTransform
  right_inv M := by
    apply Subtype.ext
    exact M.toRigidTransform_toHomogeneous

end RigidTransform

end RoboLean
