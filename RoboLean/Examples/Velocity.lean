import RoboLean.Geometry.RigidVelocity
import RoboLean.Geometry.TwistTrajectory
import RoboLean.Geometry.TwistExpClosedForm
import RoboLean.Examples.RigidTransform

/-!
# An offset-axis velocity witness

This is the numerical instance `l₀=0`, `l₁=3`, `l₂=5`, `θ(t)=2t` of
MLS Example 2.5, printed pp56–57. The pose maps body coordinates B to the
fixed frame A. At zero its origin is `(0,8,0)` and moves with velocity
`(-10,0,0)`. The spatial linear twist is instead `(6,0,0)`:
`vˢ = ṗ - ωˢ × p = (-10,0,0) - (-16,0,0)`.

The derivative below is proved from the actual matrix exponential and product
rule. This concrete instance does not establish the whole symbolic example,
physical calibration, or unit/frame typing.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix
open scoped Matrix.Norms.Operator

/-- An offset fixed-axis motion, with constant translations on either side. -/
def offsetVelocityPose (t : ℝ) : RigidTransform :=
  (⟨1, vec 0 3 0⟩ : RigidTransform) *
    Twist.exp ⟨0, vec 0 0 1⟩ (2 * t) * ⟨1, vec 0 5 0⟩

private theorem offsetAngularNorm : ‖Twist.angular ⟨0, vec 0 0 1⟩‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Twist.angular, vec, Fin.sum_univ_succ]

/-- The middle exponential is the actual positive z rotation, with no translation. -/
theorem offsetVelocityPose_pureRotation (t : ℝ) :
    offsetVelocityPose t = (⟨1, vec 0 3 0⟩ : RigidTransform) *
      ⟨Rotation.exp (vec 0 0 1) (2 * t), 0⟩ * ⟨1, vec 0 5 0⟩ := by
  have he : Twist.exp ⟨0, vec 0 0 1⟩ (2 * t) =
      (⟨Rotation.exp (vec 0 0 1) (2 * t), 0⟩ : RigidTransform) := by
    apply RigidTransform.ext
    · exact Twist.exp_rotation _ _
    · rw [Twist.exp_translation_of_angular_norm_eq_one _ offsetAngularNorm]
      simp
  simp only [offsetVelocityPose, he]

/-- The initial pose has no rotation and its two offsets add to eight along +y. -/
theorem offsetVelocityPose_zero :
    offsetVelocityPose 0 = ⟨1, vec 0 8 0⟩ := by
  simp only [offsetVelocityPose, mul_zero, Twist.exp_zero, mul_one]
  apply RigidTransform.ext
  · simp
  · change (1 : Rotation).act (vec 0 5 0) + vec 0 3 0 = _
    rw [Rotation.act_one]
    ext i
    fin_cases i <;> norm_num [vec]

/-- The expected matrix derivative has angular rate two and origin velocity minus ten. -/
def offsetVelocityDerivative : HomogeneousMatrix :=
  Matrix.fromBlocks !![0, -2, 0; 2, 0, 0; 0, 0, 0]
    (Matrix.of fun i (_ : Fin 1) => ![-10, 0, 0] i) 0 0

/-- Actual differentiation, with the derivative matrix computed independently in coordinates. -/
theorem hasDerivAt_offsetVelocityPose_zero :
    HasDerivAt (fun t => (offsetVelocityPose t).toHomogeneous)
      offsetVelocityDerivative 0 := by
  have hθ : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
  have he : HasDerivAt
      (fun t : ℝ => (Twist.exp ⟨0, vec 0 0 1⟩ (2 * t)).toHomogeneous)
      ((2 : ℝ) • Twist.hat ⟨0, vec 0 0 1⟩) 0 := by
    have he' : HasDerivAt
        (fun t : ℝ => (Twist.exp ⟨0, vec 0 0 1⟩ (2 * t)).toHomogeneous)
        ((2 : ℝ) • (Twist.hat ⟨0, vec 0 0 1⟩ *
          (Twist.exp ⟨0, vec 0 0 1⟩ (2 * 0)).toHomogeneous)) 0 :=
      (Twist.hasDerivAt_exp_toHomogeneous ⟨0, vec 0 0 1⟩ (2 * 0)).scomp 0 hθ
    simpa only [mul_zero, Twist.exp_zero, RigidTransform.toHomogeneous_one, mul_one] using he'
  have h : HasDerivAt
      (fun t : ℝ => (⟨1, vec 0 3 0⟩ : RigidTransform).toHomogeneous *
        (Twist.exp ⟨0, vec 0 0 1⟩ (2 * t)).toHomogeneous *
        (⟨1, vec 0 5 0⟩ : RigidTransform).toHomogeneous)
      ((⟨1, vec 0 3 0⟩ : RigidTransform).toHomogeneous *
        ((2 : ℝ) • Twist.hat ⟨0, vec 0 0 1⟩) *
        (⟨1, vec 0 5 0⟩ : RigidTransform).toHomogeneous) 0 :=
    (he.const_mul (⟨1, vec 0 3 0⟩ : RigidTransform).toHomogeneous).mul_const
      (⟨1, vec 0 5 0⟩ : RigidTransform).toHomogeneous
  have hD : (⟨1, vec 0 3 0⟩ : RigidTransform).toHomogeneous *
      ((2 : ℝ) • Twist.hat ⟨0, vec 0 0 1⟩) *
      (⟨1, vec 0 5 0⟩ : RigidTransform).toHomogeneous = offsetVelocityDerivative := by
    simp only [RigidTransform.toHomogeneous, Twist.hat, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_multiply]
    apply Matrix.ext_iff_blocks.mpr
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [offsetVelocityDerivative, Twist.linear, Twist.angular, Vec3.hat,
        Matrix.mul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ, vec]
  simpa only [offsetVelocityPose, RigidTransform.toHomogeneous_mul, hD] using h

/-- The body origin's actual velocity at zero is minus ten along x. -/
theorem hasDerivAt_offsetVelocityPose_translation_zero :
    HasDerivAt (fun t => (offsetVelocityPose t).translation) (vec (-10) 0 0) 0 := by
  simpa [RigidTransform.translationDerivative, offsetVelocityDerivative, vec] using
    RigidTransform.hasDerivAt_translation hasDerivAt_offsetVelocityPose_zero

/-- The spatial linear part subtracts `ω×p`, giving six rather than minus ten. -/
theorem offsetVelocityPose_spatial_zero :
    RigidTransform.spatialVelocity offsetVelocityPose offsetVelocityDerivative 0
      hasDerivAt_offsetVelocityPose_zero = ⟨vec 6 0 0, vec 0 0 2⟩ := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_spatialVelocity, offsetVelocityPose_zero,
    ← RigidTransform.toHomogeneous_inv]
  simp only [offsetVelocityDerivative, RigidTransform.toHomogeneous,
    RigidTransform.inv_rotation, RigidTransform.inv_translation, inv_one,
    Rotation.act_one, Twist.hat, Matrix.fromBlocks_multiply]
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Twist.linear, Twist.angular, Vec3.hat, Matrix.mul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ, vec]

/-- At this pose the body linear part is the rotated origin velocity, minus ten. -/
theorem offsetVelocityPose_body_zero :
    RigidTransform.bodyVelocity offsetVelocityPose offsetVelocityDerivative 0
      hasDerivAt_offsetVelocityPose_zero = ⟨vec (-10) 0 0, vec 0 0 2⟩ := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_bodyVelocity, offsetVelocityPose_zero,
    ← RigidTransform.toHomogeneous_inv]
  simp only [offsetVelocityDerivative, RigidTransform.toHomogeneous,
    RigidTransform.inv_rotation, RigidTransform.inv_translation, inv_one,
    Rotation.act_one, Twist.hat, Matrix.fromBlocks_multiply]
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Twist.linear, Twist.angular, Vec3.hat, Matrix.mul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_succ, vec]

end RoboLean.Examples
