import RoboLean.Geometry.RigidVelocityComposition
import RoboLean.Geometry.TwistExpClosedForm
import RoboLean.Examples.RigidTransform

/-!
# Symbolic offset-axis velocities

MLS Example 2.5, printed pp56–57, takes the pose of B in A to have rotation
`Rz(θ)` and translation `(-l₂ sin θ, l₁ + l₂ cos θ, l₀)`. The pose below is
constructed from constant translations and the actual twist exponential; its
coordinate matrix is then proved equal to that independently stated formula.

For arbitrary constant real offsets and any angle derivative `HasDerivAt θ θ' t`,
its spatial twist is `(l₁ θ',0,0; 0,0,θ')` and body twist is
`(-l₂ θ',0,0; 0,0,θ')`. Derivative evidence comes from the exponential and
product rules. No positivity or nonzero-link assumption is needed for these
coordinate identities. Frame labels, units, and physical calibration are not
enforced by the types.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix
open scoped Matrix.Norms.Operator

/-- The source pose, as a fixed offset, actual z-axis exponential, and body offset. -/
def planarPose (l₀ l₁ l₂ a : ℝ) : RigidTransform :=
  (⟨1, vec 0 l₁ l₀⟩ : RigidTransform) *
    (Twist.exp (0, Rotation.zAxis) a * ⟨1, vec 0 l₂ 0⟩)

private theorem planarPureRotation (a : ℝ) :
    Twist.exp (0, Rotation.zAxis) a = (⟨Rotation.zRotation a, 0⟩ : RigidTransform) := by
  have hz : ‖Twist.angular (0, Rotation.zAxis)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Twist.angular, Rotation.zAxis, Fin.sum_univ_succ]
  apply RigidTransform.ext
  · exact Twist.exp_rotation _ _
  · rw [Twist.exp_translation_of_angular_norm_eq_one _ hz]
    simp [Twist.linear]

/-- The source orientation is the positive right-handed z rotation. -/
theorem planarPose_rotation (l₀ l₁ l₂ a : ℝ) :
    (planarPose l₀ l₁ l₂ a).rotation = Rotation.zRotation a := by
  simp [planarPose, RigidTransform.mul_rotation, Twist.exp_rotation, Rotation.zRotation]

/-- The body-origin coordinates agree with the displayed source pose. -/
theorem planarPose_translation (l₀ l₁ l₂ a : ℝ) :
    (planarPose l₀ l₁ l₂ a).translation =
      vec (-l₂ * Real.sin a) (l₁ + l₂ * Real.cos a) l₀ := by
  rw [planarPose, planarPureRotation]
  simp only [RigidTransform.mul_translation, Rotation.act_one]
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, vec] <;> ring

/-- Full homogeneous source matrix from MLS printed p56, with arbitrary constant offsets. -/
theorem planarPose_toHomogeneous (l₀ l₁ l₂ a : ℝ) :
    (planarPose l₀ l₁ l₂ a).toHomogeneous = Matrix.fromBlocks
      !![Real.cos a, -Real.sin a, 0; Real.sin a, Real.cos a, 0; 0, 0, 1]
      (Matrix.of fun i (_ : Fin 1) =>
        ![-l₂ * Real.sin a, l₁ + l₂ * Real.cos a, l₀] i) 0 1 := by
  simp only [RigidTransform.toHomogeneous, planarPose_rotation,
    Rotation.zRotation_val, planarPose_translation]
  rfl

/-- The product-rule derivative at angle `a` and instantaneous angular rate `a'`. -/
def planarPoseDerivative (l₀ l₁ l₂ a a' : ℝ) : HomogeneousMatrix :=
  (⟨1, vec 0 l₁ l₀⟩ : RigidTransform).toHomogeneous *
    ((a' • Twist.hat (0, Rotation.zAxis)) *
      (Twist.exp (0, Rotation.zAxis) a * ⟨1, vec 0 l₂ 0⟩).toHomogeneous)

/-- The derivative is proved for every differentiable angle, including zero instantaneous rate. -/
theorem hasDerivAt_planarPose (l₀ l₁ l₂ : ℝ) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => (planarPose l₀ l₁ l₂ (θ s)).toHomogeneous)
      (planarPoseDerivative l₀ l₁ l₂ (θ t) θ') t :=
  RigidTransform.hasDerivAt_toHomogeneous_const_mul (⟨1, vec 0 l₁ l₀⟩ : RigidTransform)
    (RigidTransform.hasDerivAt_toHomogeneous_exp_mul (0, Rotation.zAxis)
      (⟨1, vec 0 l₂ 0⟩ : RigidTransform) hθ)

/-- MLS p57: spatial linear velocity depends on the fixed spatial offset `l₁`. -/
theorem planarPose_spatialVelocity (l₀ l₁ l₂ : ℝ) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    RigidTransform.spatialVelocity (fun s => planarPose l₀ l₁ l₂ (θ s))
      (planarPoseDerivative l₀ l₁ l₂ (θ t) θ') t (hasDerivAt_planarPose l₀ l₁ l₂ hθ) =
      (vec (l₁ * θ') 0 0, vec 0 0 θ') := by
  calc
    _ = Twist.adjoint (⟨1, vec 0 l₁ l₀⟩ : RigidTransform)
        (θ' • (0, Rotation.zAxis)) := by
      exact (RigidTransform.spatialVelocity_const_mul
        (⟨1, vec 0 l₁ l₀⟩ : RigidTransform)
        (RigidTransform.hasDerivAt_toHomogeneous_exp_mul (0, Rotation.zAxis)
          (⟨1, vec 0 l₂ 0⟩ : RigidTransform) hθ)).trans
        (congrArg (Twist.adjoint (⟨1, vec 0 l₁ l₀⟩ : RigidTransform))
          (RigidTransform.spatialVelocity_exp_mul (0, Rotation.zAxis)
            (⟨1, vec 0 l₂ 0⟩ : RigidTransform) hθ))
    _ = _ := by
      apply Prod.ext <;> ext i <;> fin_cases i <;>
        simp [Twist.adjoint, Twist.linear, Twist.angular, Rotation.act_one,
          Vec3.cross, cross_apply, Rotation.zAxis, vec]

/-- MLS p57: body linear velocity depends on the body offset `l₂`, with the opposite sign. -/
theorem planarPose_bodyVelocity (l₀ l₁ l₂ : ℝ) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    RigidTransform.bodyVelocity (fun s => planarPose l₀ l₁ l₂ (θ s))
      (planarPoseDerivative l₀ l₁ l₂ (θ t) θ') t (hasDerivAt_planarPose l₀ l₁ l₂ hθ) =
      (vec (-l₂ * θ') 0 0, vec 0 0 θ') := by
  calc
    _ = θ' • Twist.adjoint (⟨1, vec 0 l₂ 0⟩ : RigidTransform)⁻¹ (0, Rotation.zAxis) := by
      exact (RigidTransform.bodyVelocity_const_mul
        (⟨1, vec 0 l₁ l₀⟩ : RigidTransform)
        (RigidTransform.hasDerivAt_toHomogeneous_exp_mul (0, Rotation.zAxis)
          (⟨1, vec 0 l₂ 0⟩ : RigidTransform) hθ)).trans
        (RigidTransform.bodyVelocity_exp_mul (0, Rotation.zAxis)
          (⟨1, vec 0 l₂ 0⟩ : RigidTransform) hθ)
    _ = _ := by
      apply Prod.ext <;> ext i <;> fin_cases i <;>
        simp [Twist.adjoint, Twist.linear, Twist.angular, RigidTransform.inv_rotation,
          RigidTransform.inv_translation, Rotation.act_one, Vec3.cross, cross_apply,
          Rotation.zAxis, vec]; ring

/-- MLS Example 2.6: the first frame has height `l₀`; the second joint is offset by `l₁`. -/
def twoLinkPose (l₀ l₁ a b : ℝ) : RigidTransform :=
  planarPose l₀ 0 0 a * planarPose 0 l₁ 0 b

/-- The chosen source frame chain has `p_AB=(0,0,l₀)` and `p_BC=(0,l₁,0)`.
This fixes the origins used by the spatial-velocity columns on printed p60. -/
theorem twoLinkPose_factors (l₀ l₁ a b : ℝ) :
    twoLinkPose l₀ l₁ a b =
      (⟨Rotation.zRotation a, vec 0 0 l₀⟩ : RigidTransform) *
      ⟨Rotation.zRotation b, vec 0 l₁ 0⟩ := by
  have ha : planarPose l₀ 0 0 a =
      (⟨Rotation.zRotation a, vec 0 0 l₀⟩ : RigidTransform) := by
    apply RigidTransform.ext
    · exact planarPose_rotation _ _ _ _
    · simp [planarPose_translation]
  have hb : planarPose 0 l₁ 0 b =
      (⟨Rotation.zRotation b, vec 0 l₁ 0⟩ : RigidTransform) := by
    apply RigidTransform.ext
    · exact planarPose_rotation _ _ _ _
    · simp [planarPose_translation]
  rw [twoLinkPose, ha, hb]

/-- Product-rule derivative of the actual two-joint pose. -/
def twoLinkPoseDerivative (l₀ l₁ a b a' b' : ℝ) : HomogeneousMatrix :=
  planarPoseDerivative l₀ 0 0 a a' * (planarPose 0 l₁ 0 b).toHomogeneous +
    (planarPose l₀ 0 0 a).toHomogeneous * planarPoseDerivative 0 l₁ 0 b b'

/-- Both joint derivatives are derived from their angle derivatives before composing poses. -/
theorem hasDerivAt_twoLinkPose (l₀ l₁ : ℝ) {θ₁ θ₂ : ℝ → ℝ} {θ₁' θ₂' t : ℝ}
    (h₁ : HasDerivAt θ₁ θ₁' t) (h₂ : HasDerivAt θ₂ θ₂' t) :
    HasDerivAt (fun s => (twoLinkPose l₀ l₁ (θ₁ s) (θ₂ s)).toHomogeneous)
      (twoLinkPoseDerivative l₀ l₁ (θ₁ t) (θ₂ t) θ₁' θ₂') t :=
  RigidTransform.hasDerivAt_toHomogeneous_mul
    (hasDerivAt_planarPose l₀ 0 0 h₁) (hasDerivAt_planarPose 0 l₁ 0 h₂)

/-- The two printed spatial columns in MLS p60 follow from the actual frame-chain derivative.
Agreement with independently specified Chapter 3 forward kinematics is a separate obligation. -/
theorem twoLinkPose_spatialVelocity (l₀ l₁ : ℝ) {θ₁ θ₂ : ℝ → ℝ} {θ₁' θ₂' t : ℝ}
    (h₁ : HasDerivAt θ₁ θ₁' t) (h₂ : HasDerivAt θ₂ θ₂' t) :
    RigidTransform.spatialVelocity (fun s => twoLinkPose l₀ l₁ (θ₁ s) (θ₂ s))
      (twoLinkPoseDerivative l₀ l₁ (θ₁ t) (θ₂ t) θ₁' θ₂') t
      (hasDerivAt_twoLinkPose l₀ l₁ h₁ h₂) =
      θ₁' • ((vec 0 0 0, vec 0 0 1) : Twist) +
      θ₂' • ((vec (l₁ * Real.cos (θ₁ t)) (l₁ * Real.sin (θ₁ t)) 0, vec 0 0 1) : Twist) := by
  calc
    _ = RigidTransform.spatialVelocity (fun s => planarPose l₀ 0 0 (θ₁ s))
          (planarPoseDerivative l₀ 0 0 (θ₁ t) θ₁') t (hasDerivAt_planarPose l₀ 0 0 h₁) +
        Twist.adjoint (planarPose l₀ 0 0 (θ₁ t))
          (RigidTransform.spatialVelocity (fun s => planarPose 0 l₁ 0 (θ₂ s))
            (planarPoseDerivative 0 l₁ 0 (θ₂ t) θ₂') t
            (hasDerivAt_planarPose 0 l₁ 0 h₂)) :=
      RigidTransform.spatialVelocity_mul
        (hasDerivAt_planarPose l₀ 0 0 h₁) (hasDerivAt_planarPose 0 l₁ 0 h₂)
    _ = (vec 0 0 0, vec 0 0 θ₁') +
        Twist.adjoint (planarPose l₀ 0 0 (θ₁ t)) (vec (l₁ * θ₂') 0 0, vec 0 0 θ₂') := by
      rw [planarPose_spatialVelocity l₀ 0 0 h₁, planarPose_spatialVelocity 0 l₁ 0 h₂]
      simp
    _ = _ := by
      apply Prod.ext <;> ext i <;> fin_cases i <;>
        simp [Twist.adjoint, Twist.linear, Twist.angular, planarPose_rotation,
          planarPose_translation, Rotation.act_apply, Rotation.zRotation_val,
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Vec3.cross, cross_apply, vec] <;> ring

end RoboLean.Examples
