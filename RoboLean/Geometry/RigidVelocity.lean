import RoboLean.Geometry.RotationVelocity
import RoboLean.Geometry.TwistTrajectory
import RoboLean.Geometry.TwistAdjoint
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Abel

/-!
# Spatial and body velocities of differentiable pose curves

MLS printed pp54–56, equations (2.53)–(2.61). Every velocity definition
requires an actual derivative of the homogeneous pose matrix. Component
and zero-bottom-row derivatives are extracted from that premise.

The spatial linear part is `ṗ - ωˢ × p`, while the body linear part is
`R⁻¹ ṗ`. Body point coordinates are held constant; body-expressed physical
velocity is a rotated spatial velocity, not their coordinate derivative.
No frame typing, physical calibration, or ODE uniqueness is claimed.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace RigidTransform

variable {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}

/-- The translation-column component of a homogeneous derivative. -/
def translationDerivative (D : HomogeneousMatrix) : Vec3 :=
  WithLp.toLp 2 (fun i ↦ D (Sum.inl i) (Sum.inr 0))

/-- A pose derivative supplies the derivative of its rotation block. -/
theorem hasDerivAt_rotation
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    HasDerivAt (fun s ↦ (g s).rotation.val) D.toBlocks₁₁ t := by
  let L : HomogeneousMatrix →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    { toFun M := M.toBlocks₁₁
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

/-- A pose derivative supplies the derivative of its Euclidean translation. -/
theorem hasDerivAt_translation
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    HasDerivAt (fun s ↦ (g s).translation) (translationDerivative D) t := by
  let L : HomogeneousMatrix →ₗ[ℝ] Vec3 :=
    { toFun := translationDerivative
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

/-- The lower-left derivative block is zero because the pose block is constant. -/
theorem derivative_lowerLeft
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) : D.toBlocks₂₁ = 0 := by
  let L : HomogeneousMatrix →ₗ[ℝ] Matrix (Fin 1) (Fin 3) ℝ :=
    { toFun M := M.toBlocks₂₁
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hd := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt (fun _ : ℝ ↦ (0 : Matrix (Fin 1) (Fin 3) ℝ)) D.toBlocks₂₁ t at hd
  exact hd.unique (hasDerivAt_const t 0)

/-- The lower-right derivative block is zero, although the pose block is one. -/
theorem derivative_lowerRight
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) : D.toBlocks₂₂ = 0 := by
  let L : HomogeneousMatrix →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℝ :=
    { toFun M := M.toBlocks₂₂
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hd := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt (fun _ : ℝ ↦ (1 : Matrix (Fin 1) (Fin 1) ℝ)) D.toBlocks₂₂ t at hd
  exact hd.unique (hasDerivAt_const t 1)

/-- The actual derivative consists of its rotation derivative and translation column. -/
theorem derivative_eq_fromBlocks
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    D = fromBlocks D.toBlocks₁₁ (Matrix.of fun i _ ↦ translationDerivative D i) 0 0 := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨rfl, ?_, derivative_lowerLeft h, derivative_lowerRight h⟩
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

/-- MLS (2.53)/(2.59): spatial twist with derivative evidence retained. -/
def spatialVelocity (g : ℝ → RigidTransform) (D : HomogeneousMatrix) (t : ℝ)
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) : Twist :=
  let ω := Rotation.spatialAngularVelocity (fun s ↦ (g s).rotation) D.toBlocks₁₁ t
    (hasDerivAt_rotation h)
  ⟨translationDerivative D - Vec3.cross ω (g t).translation, ω⟩

/-- MLS (2.55)/(2.60): body twist with derivative evidence retained. -/
def bodyVelocity (g : ℝ → RigidTransform) (D : HomogeneousMatrix) (t : ℝ)
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) : Twist :=
  ⟨(g t).rotation⁻¹.act (translationDerivative D),
    Rotation.bodyAngularVelocity (fun s ↦ (g s).rotation) D.toBlocks₁₁ t
      (hasDerivAt_rotation h)⟩

@[simp] theorem spatialVelocity_linear
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    (spatialVelocity g D t h).linear = translationDerivative D -
      Vec3.cross (spatialVelocity g D t h).angular (g t).translation := rfl

@[simp] theorem bodyVelocity_linear
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    (bodyVelocity g D t h).linear = (g t).rotation⁻¹.act (translationDerivative D) := rfl

/-- The two angular components obey the rotation-velocity conversion. -/
theorem bodyVelocity_angular
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    (bodyVelocity g D t h).angular =
      (g t).rotation⁻¹.act (spatialVelocity g D t h).angular :=
  Rotation.bodyAngularVelocity_eq (hasDerivAt_rotation h)

/-- The spatial velocity matrix is exactly `Ḣ H⁻¹`, including its zero bottom row. -/
theorem hat_spatialVelocity
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    (spatialVelocity g D t h).hat = D * (g t).toHomogeneous⁻¹ := by
  have hcross := Rotation.spatial_velocity_eq_cross (hasDerivAt_rotation h)
    ((g t).rotation⁻¹.act (g t).translation)
  rw [Rotation.act_inv_act] at hcross
  rw [← toHomogeneous_inv]
  conv_rhs => rw [derivative_eq_fromBlocks h]
  simp only [Twist.hat, spatialVelocity,
    Rotation.hat_spatialAngularVelocity, toHomogeneous, inv_rotation, inv_translation,
    Rotation.inv_val, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero]
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨rfl, ?_, rfl, rfl⟩
  ext i j
  change (translationDerivative D -
      Vec3.cross (Rotation.spatialAngularVelocity (fun s ↦ (g s).rotation)
        D.toBlocks₁₁ t (hasDerivAt_rotation h)) (g t).translation) i =
    (Matrix.toEuclideanLin D.toBlocks₁₁ (-((g t).rotation⁻¹.act (g t).translation)) +
      translationDerivative D) i
  rw [map_neg, hcross]
  simp only [sub_eq_add_neg, add_comm]

/-- The body velocity matrix is exactly `H⁻¹ Ḣ`, including its zero bottom row. -/
theorem hat_bodyVelocity
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    (bodyVelocity g D t h).hat = (g t).toHomogeneous⁻¹ * D := by
  rw [← toHomogeneous_inv]
  conv_rhs => rw [derivative_eq_fromBlocks h]
  simp only [Twist.hat, bodyVelocity,
    Rotation.hat_bodyAngularVelocity, toHomogeneous, inv_rotation, inv_translation,
    Rotation.inv_val, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero]
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨rfl, ?_, rfl, rfl⟩
  ext i j
  rfl

/-- Membership in the independent twist-matrix carrier follows from the actual derivative. -/
theorem spatial_matrix_mem_se3
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    D * (g t).toHomogeneous⁻¹ ∈ se3Submodule := by
  rw [← hat_spatialVelocity h]
  exact Twist.hat_mem_se3Submodule _

/-- Body velocity matrices also belong to the independent twist-matrix carrier. -/
theorem body_matrix_mem_se3
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    (g t).toHomogeneous⁻¹ * D ∈ se3Submodule := by
  rw [← hat_bodyVelocity h]
  exact Twist.hat_mem_se3Submodule _

/-- MLS (2.54): a point fixed in the body has the stated spatial physical velocity. -/
theorem hasDerivAt_applyPoint_spatial
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) (q : Vec3) :
    HasDerivAt (fun s ↦ (g s).applyPoint q)
      (Vec3.cross (spatialVelocity g D t h).angular ((g t).applyPoint q) +
        (spatialVelocity g D t h).linear) t := by
  have hd := (Rotation.hasDerivAt_act (hasDerivAt_rotation h) q).add
    (hasDerivAt_translation h)
  change HasDerivAt (fun s ↦ (g s).applyPoint q)
    (Matrix.toEuclideanLin D.toBlocks₁₁ q + translationDerivative D) t at hd
  convert hd using 1
  rw [Rotation.spatial_velocity_eq_cross (hasDerivAt_rotation h) q]
  simp only [spatialVelocity, applyPoint, Vec3.cross_add]
  abel

/-- MLS (2.56): rotate physical spatial velocity into body coordinates. -/
theorem body_point_velocity
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) (q : Vec3) :
    (g t).rotation⁻¹.act (Matrix.toEuclideanLin D.toBlocks₁₁ q + translationDerivative D) =
      Vec3.cross (bodyVelocity g D t h).angular q + (bodyVelocity g D t h).linear := by
  rw [map_add, Rotation.body_velocity_eq_cross (hasDerivAt_rotation h) q]
  rfl

/-- MLS (2.57)/(2.61): spatial and body twists are related by the rigid adjoint. -/
theorem spatialVelocity_eq_adjoint_body
    (h : HasDerivAt (fun s ↦ (g s).toHomogeneous) D t) :
    spatialVelocity g D t h = Twist.adjoint (g t) (bodyVelocity g D t h) := by
  apply Twist.ext
  · rw [Twist.adjoint_linear, bodyVelocity_linear, bodyVelocity_angular,
      Rotation.act_inv_act, Rotation.act_inv_act, spatialVelocity_linear,
      Vec3.cross_anticomm (g t).translation]
    rfl
  · rw [Twist.adjoint_angular, bodyVelocity_angular, Rotation.act_inv_act]

/-- MLS p58: differentiate a constant-twist motion with an arbitrary differentiable parameter. -/
theorem hasDerivAt_toHomogeneous_exp_mul (ξ : Twist) (g₀ : RigidTransform)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s ↦ (Twist.exp ξ (θ s) * g₀).toHomogeneous)
      ((θ' • ξ.hat) * (Twist.exp ξ (θ t) * g₀).toHomogeneous) t := by
  have he : HasDerivAt (fun s ↦ (Twist.exp ξ (θ s)).toHomogeneous)
      (θ' • (ξ.hat * (Twist.exp ξ (θ t)).toHomogeneous)) t :=
    (Twist.hasDerivAt_exp_toHomogeneous ξ (θ t)).scomp t hθ
  have hg : HasDerivAt
      (fun s ↦ (Twist.exp ξ (θ s)).toHomogeneous * g₀.toHomogeneous)
      ((θ' • (ξ.hat * (Twist.exp ξ (θ t)).toHomogeneous)) * g₀.toHomogeneous) t :=
    he.mul_const g₀.toHomogeneous
  convert hg using 1 <;>
    simp only [toHomogeneous_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- MLS p58: the spatial velocity is the instantaneous parameter rate times the fixed twist. -/
theorem spatialVelocity_exp_mul (ξ : Twist) (g₀ : RigidTransform)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t) :
    spatialVelocity (fun s ↦ Twist.exp ξ (θ s) * g₀)
      ((θ' • ξ.hat) * (Twist.exp ξ (θ t) * g₀).toHomogeneous) t
      (hasDerivAt_toHomogeneous_exp_mul ξ g₀ hθ) = θ' • ξ := by
  apply Twist.hat_injective
  rw [hat_spatialVelocity, Twist.hat_smul, ← toHomogeneous_inv,
    Matrix.mul_assoc, toHomogeneous_mul_inv, Matrix.mul_one]

private theorem hat_mul_exp_comm (ξ : Twist) (a : ℝ) :
    ξ.hat * (Twist.exp ξ a).toHomogeneous =
      (Twist.exp ξ a).toHomogeneous * ξ.hat := by
  rw [Twist.toHomogeneous_exp]
  have hl : HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • ξ.hat))
      (ξ.hat * NormedSpace.exp (a • ξ.hat)) a :=
    hasDerivAt_exp_smul_const' ξ.hat a
  have hr : HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • ξ.hat))
      (NormedSpace.exp (a • ξ.hat) * ξ.hat) a :=
    hasDerivAt_exp_smul_const ξ.hat a
  exact hl.unique hr

/-- MLS p58: body velocity uses the fixed initial pose, with the same instantaneous rate. -/
theorem bodyVelocity_exp_mul (ξ : Twist) (g₀ : RigidTransform)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t) :
    bodyVelocity (fun s ↦ Twist.exp ξ (θ s) * g₀)
      ((θ' • ξ.hat) * (Twist.exp ξ (θ t) * g₀).toHomogeneous) t
      (hasDerivAt_toHomogeneous_exp_mul ξ g₀ hθ) = θ' • Twist.adjoint g₀⁻¹ ξ := by
  have he : ((Twist.exp ξ (θ t))⁻¹).toHomogeneous * ξ.hat *
      (Twist.exp ξ (θ t)).toHomogeneous = ξ.hat := by
    rw [Matrix.mul_assoc, hat_mul_exp_comm, ← Matrix.mul_assoc,
      toHomogeneous_inv_mul, Matrix.one_mul]
  apply Twist.hat_injective
  rw [hat_bodyVelocity, Twist.hat_smul]
  calc
    _ = θ' • ((g₀⁻¹).toHomogeneous *
        (((Twist.exp ξ (θ t))⁻¹).toHomogeneous * ξ.hat *
          (Twist.exp ξ (θ t)).toHomogeneous) * g₀.toHomogeneous) := by
      rw [← toHomogeneous_inv, _root_.mul_inv_rev]
      simp only [toHomogeneous_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = θ' • ((g₀⁻¹).toHomogeneous * ξ.hat * g₀.toHomogeneous) := by rw [he]
    _ = _ := by rw [Twist.hat_adjoint, ← toHomogeneous_inv, inv_inv]

end RigidTransform
end RoboLean
