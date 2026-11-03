import RoboLean.Examples.TwistTwoDofManipulator
import RoboLean.Geometry.RigidVelocity
import RoboLean.Kinematics.SerialChain

/-!
# Exercise 2.16(b)–(d): velocities of the two-degree-of-freedom manipulator of Figure 2.17

MLS Chapter 2, Exercise 16, printed pp. 77–78, parts (b)–(d): "(b) Compute the spatial velocity of
`C₃` relative to `C₀` as functions of the joint angles and the joint rates. (c) Compute the body
velocity of `C₃` relative to `C₀` as functions of the joint angles and the joint rates. (d) Optional:
Find the spatial velocity of the origin of `C₃` and use this to check your answer for parts (b) and
(c)."

The pose is the one of part (a) (`twoDofPose_eq`, with the figure reading stated there), written as
the product of exponentials `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} g(0)` (eq. (3.3), p. 87) with the revolute twists
`ξ₁` about the vertical axis through the origin and `ξ₂` about the vertical axis through
`(l₁, 0, 0)`. Along joint trajectories `θ₁(t)`, `θ₂(t)` with rates `θ̇₁`, `θ̇₂`, the homogeneous
matrix has the derivative given by the product rule, and with the library's spatial and body
velocities (eqs. (2.53), (2.55), pp. 54–56):

* (b) `Vˢ = (l₁ sin θ₁ θ̇₂, −l₁ cos θ₁ θ̇₂, 0, 0, 0, θ̇₁ + θ̇₂)`, which is `θ̇₁ ξ₁ + θ̇₂ Ad_{e^{ξ̂₁θ₁}} ξ₂`;
* (c) `Vᵇ = (l₁ sin θ₂ θ̇₁, l₁ cos θ₂ θ̇₁ + l₂ (θ̇₁ + θ̇₂), 0, 0, 0, θ̇₁ + θ̇₂)`;
* (d) the origin of `C₃` moves with velocity
  `ṗ = (−l₁ sin θ₁ θ̇₁ − l₂ sin (θ₁ + θ₂)(θ̇₁ + θ̇₂), l₁ cos θ₁ θ̇₁ + l₂ cos (θ₁ + θ₂)(θ̇₁ + θ̇₂), 0)`,
  and `vˢ = ṗ − ωˢ × p`, `vᵇ = Rᵀ ṗ` (the library's definitions of the two velocities, p. 54–56),
  which these values satisfy.

Twists are `(v, ω)`, linear part first.
-/

noncomputable section

open Real Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean.Examples

/-- The `z`-axis is a unit vector (MLS p. 31). -/
private theorem norm_zAxis_two : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Rotation.zAxis, Fin.sum_univ_three]

/-- The rotation exponential about `e_z` is `R_z` (MLS p. 31). -/
private theorem exp_zAxis_two (θ : ℝ) : Rotation.exp Rotation.zAxis θ = Rotation.zRotation θ := rfl

/-- The twist of the first joint of MLS Figure 2.17, printed p. 77: rotation about the vertical
axis through the origin of `C₀` (eq. (2.36), p. 42, revolute form of p. 87). -/
def twoDofTwist₁ : Twist := Twist.revolute Rotation.zAxis 0

/-- The twist of the second joint of MLS Figure 2.17, printed p. 77: rotation about the vertical
axis through `(l₁, 0, 0)`. -/
def twoDofTwist₂ (l₁ : ℝ) : Twist := Twist.revolute Rotation.zAxis (WithLp.toLp 2 ![l₁, 0, 0])

/-- The reference configuration `g(0)` of `C₃` in MLS Figure 2.17, printed p. 77: the translation
by `(l₁ + l₂, 0, l₀)`. -/
def twoDofHome (l₀ l₁ l₂ : ℝ) : RigidTransform := ⟨1, WithLp.toLp 2 ![l₁ + l₂, 0, l₀]⟩

/-- MLS Exercise 2.16 with eq. (3.3), printed pp. 77, 87: the pose of part (a) is the product of
exponentials `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} g(0)`. -/
theorem twoDofPose_eq_exp (l₀ l₁ l₂ θ₁ θ₂ : ℝ) :
    twoDofFrame01 l₀ θ₁ * twoDofFrame12 l₁ θ₂ * twoDofFrame23 l₂ =
      Twist.exp twoDofTwist₁ θ₁ * Twist.exp (twoDofTwist₂ l₁) θ₂ * twoDofHome l₀ l₁ l₂ := by
  rw [twoDofPose_eq, twoDofTwist₁, twoDofTwist₂, Twist.exp_revolute _ _ norm_zAxis_two,
    Twist.exp_revolute _ _ norm_zAxis_two]
  apply RigidTransform.ext
  · simp [twoDofHome, Rotation.zRotation, Rotation.exp_add]
  · apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [twoDofHome, Rotation.act_apply, exp_zAxis_two, Rotation.zRotation_val,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, cos_add, sin_add] <;> ring

/-- The derivative of the homogeneous matrix of the pose of MLS Figure 2.17 (printed p. 77) at
joint angles `θ₁, θ₂` and rates `ω₁, ω₂`, by the product rule applied to `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} g(0)`
(eq. (2.36), p. 42). -/
def twoDofPoseDerivative (l₀ l₁ l₂ θ₁ θ₂ ω₁ ω₂ : ℝ) : HomogeneousMatrix :=
  (ω₁ • (twoDofTwist₁.hat * (Twist.exp twoDofTwist₁ θ₁).toHomogeneous)) *
      (Twist.exp (twoDofTwist₂ l₁) θ₂).toHomogeneous * (twoDofHome l₀ l₁ l₂).toHomogeneous +
    (Twist.exp twoDofTwist₁ θ₁).toHomogeneous *
      (ω₂ • ((twoDofTwist₂ l₁).hat * (Twist.exp (twoDofTwist₂ l₁) θ₂).toHomogeneous)) *
      (twoDofHome l₀ l₁ l₂).toHomogeneous

/-- MLS Exercise 2.16, printed pp. 77–78: along differentiable joint trajectories the homogeneous
matrix of `g_{C₀C₃}` has the derivative `twoDofPoseDerivative`. -/
theorem hasDerivAt_twoDofPose (l₀ l₁ l₂ : ℝ) {θ₁ θ₂ : ℝ → ℝ} {ω₁ ω₂ t : ℝ}
    (h₁ : HasDerivAt θ₁ ω₁ t) (h₂ : HasDerivAt θ₂ ω₂ t) :
    HasDerivAt
      (fun s => (twoDofFrame01 l₀ (θ₁ s) * twoDofFrame12 l₁ (θ₂ s) * twoDofFrame23 l₂).toHomogeneous)
      (twoDofPoseDerivative l₀ l₁ l₂ (θ₁ t) (θ₂ t) ω₁ ω₂) t := by
  have hfun : (fun s => (twoDofFrame01 l₀ (θ₁ s) * twoDofFrame12 l₁ (θ₂ s) *
      twoDofFrame23 l₂).toHomogeneous) = fun s =>
      (Twist.exp twoDofTwist₁ (θ₁ s)).toHomogeneous *
        (Twist.exp (twoDofTwist₂ l₁) (θ₂ s)).toHomogeneous * (twoDofHome l₀ l₁ l₂).toHomogeneous := by
    funext s
    rw [twoDofPose_eq_exp, RigidTransform.toHomogeneous_mul, RigidTransform.toHomogeneous_mul]
  rw [hfun]
  have hA := (Twist.hasDerivAt_exp_toHomogeneous twoDofTwist₁ (θ₁ t)).scomp t h₁
  have hB := (Twist.hasDerivAt_exp_toHomogeneous (twoDofTwist₂ l₁) (θ₂ t)).scomp t h₂
  have hAB := (hA.mul hB).mul_const (twoDofHome l₀ l₁ l₂).toHomogeneous
  rw [twoDofPoseDerivative, ← add_mul]
  exact hAB

/-- **MLS Exercise 2.16(b)**, printed p. 78: the spatial velocity of `C₃` relative to `C₀` is
`(l₁ sin θ₁ θ̇₂, −l₁ cos θ₁ θ̇₂, 0, 0, 0, θ̇₁ + θ̇₂)` (eq. (2.53), p. 54). -/
theorem twoDof_spatialVelocity (l₀ l₁ l₂ : ℝ) {θ₁ θ₂ : ℝ → ℝ} {ω₁ ω₂ t : ℝ}
    (h₁ : HasDerivAt θ₁ ω₁ t) (h₂ : HasDerivAt θ₂ ω₂ t) :
    RigidTransform.spatialVelocity
        (fun s => twoDofFrame01 l₀ (θ₁ s) * twoDofFrame12 l₁ (θ₂ s) * twoDofFrame23 l₂)
        (twoDofPoseDerivative l₀ l₁ l₂ (θ₁ t) (θ₂ t) ω₁ ω₂) t
        (hasDerivAt_twoDofPose l₀ l₁ l₂ h₁ h₂) =
      ⟨WithLp.toLp 2 ![l₁ * sin (θ₁ t) * ω₂, -(l₁ * cos (θ₁ t) * ω₂), 0],
        WithLp.toLp 2 ![0, 0, ω₁ + ω₂]⟩ := by
  have hsv : RigidTransform.spatialVelocity
        (fun s => twoDofFrame01 l₀ (θ₁ s) * twoDofFrame12 l₁ (θ₂ s) * twoDofFrame23 l₂)
        (twoDofPoseDerivative l₀ l₁ l₂ (θ₁ t) (θ₂ t) ω₁ ω₂) t
        (hasDerivAt_twoDofPose l₀ l₁ l₂ h₁ h₂) =
      ω₁ • twoDofTwist₁ + ω₂ • Twist.adjoint (Twist.exp twoDofTwist₁ (θ₁ t)) (twoDofTwist₂ l₁) := by
    apply Twist.hat_injective
    rw [RigidTransform.hat_spatialVelocity]
    show twoDofPoseDerivative l₀ l₁ l₂ (θ₁ t) (θ₂ t) ω₁ ω₂ *
      (twoDofFrame01 l₀ (θ₁ t) * twoDofFrame12 l₁ (θ₂ t) * twoDofFrame23 l₂).toHomogeneous⁻¹ = _
    rw [twoDofPose_eq_exp, Twist.hat_add, Twist.hat_smul, Twist.hat_smul, Twist.hat_adjoint]
    have hD : twoDofPoseDerivative l₀ l₁ l₂ (θ₁ t) (θ₂ t) ω₁ ω₂ =
        (ω₁ • twoDofTwist₁.hat + ω₂ • ((Twist.exp twoDofTwist₁ (θ₁ t)).toHomogeneous *
          (twoDofTwist₂ l₁).hat * (Twist.exp twoDofTwist₁ (θ₁ t)).toHomogeneous⁻¹)) *
        (Twist.exp twoDofTwist₁ (θ₁ t) * Twist.exp (twoDofTwist₂ l₁) (θ₂ t) *
          twoDofHome l₀ l₁ l₂).toHomogeneous := by
      rw [twoDofPoseDerivative, RigidTransform.toHomogeneous_mul,
        RigidTransform.toHomogeneous_mul, ← RigidTransform.toHomogeneous_inv]
      have hAi := RigidTransform.toHomogeneous_inv_mul (Twist.exp twoDofTwist₁ (θ₁ t))
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((Twist.exp twoDofTwist₁ (θ₁ t))⁻¹).toHomogeneous, hAi,
        Matrix.one_mul]
    rw [hD, Matrix.mul_assoc, ← RigidTransform.toHomogeneous_inv (Twist.exp twoDofTwist₁ (θ₁ t) *
      Twist.exp (twoDofTwist₂ l₁) (θ₂ t) * twoDofHome l₀ l₁ l₂),
      RigidTransform.toHomogeneous_mul_inv, Matrix.mul_one]
  rw [hsv]
  simp only [twoDofTwist₁, twoDofTwist₂, Twist.exp_revolute _ _ norm_zAxis_two, exp_zAxis_two]
  apply Twist.ext <;> apply WithLp.ofLp_injective <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Rotation.act_apply, Rotation.zRotation_val, Vec3.cross_coordinates,
      crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Rotation.zAxis] <;> ring

/-- **MLS Exercise 2.16(d)**, printed p. 78: the origin of `C₃` moves with velocity
`(−l₁ sin θ₁ θ̇₁ − l₂ sin (θ₁ + θ₂)(θ̇₁ + θ̇₂), l₁ cos θ₁ θ̇₁ + l₂ cos (θ₁ + θ₂)(θ̇₁ + θ̇₂), 0)`,
the translation column of the derivative of the homogeneous matrix (at angles `θ₁, θ₂` and rates
`ω₁, ω₂`; along trajectories it is the derivative of the origin by `hasDerivAt_twoDofPose`). -/
theorem twoDof_originVelocity (l₀ l₁ l₂ θ₁ θ₂ ω₁ ω₂ : ℝ) :
    RigidTransform.translationDerivative (twoDofPoseDerivative l₀ l₁ l₂ θ₁ θ₂ ω₁ ω₂) =
      WithLp.toLp 2 ![-(l₁ * sin θ₁ * ω₁) - l₂ * sin (θ₁ + θ₂) * (ω₁ + ω₂),
        l₁ * cos θ₁ * ω₁ + l₂ * cos (θ₁ + θ₂) * (ω₁ + ω₂), 0] := by
  have h₁ : HasDerivAt (fun s => θ₁ + ω₁ * s) ω₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ω₁).const_add θ₁
  have h₂ : HasDerivAt (fun s => θ₂ + ω₂ * s) ω₂ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ω₂).const_add θ₂
  have hsv := twoDof_spatialVelocity l₀ l₁ l₂ h₁ h₂
  have hlin := RigidTransform.spatialVelocity_linear (hasDerivAt_twoDofPose l₀ l₁ l₂ h₁ h₂)
  simp only [mul_zero, add_zero] at hsv hlin
  rw [hsv] at hlin
  have hp := twoDofPose_eq l₀ l₁ l₂ θ₁ θ₂
  rw [hp] at hlin
  dsimp only at hlin
  rw [eq_sub_iff_add_eq] at hlin
  rw [← hlin]
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [Vec3.cross_coordinates, crossProduct] <;> ring

/-- **MLS Exercise 2.16(c)**, printed p. 78: the body velocity of `C₃` relative to `C₀` is
`(l₁ sin θ₂ θ̇₁, l₁ cos θ₂ θ̇₁ + l₂ (θ̇₁ + θ̇₂), 0, 0, 0, θ̇₁ + θ̇₂)` (eq. (2.55), p. 56). -/
theorem twoDof_bodyVelocity (l₀ l₁ l₂ : ℝ) {θ₁ θ₂ : ℝ → ℝ} {ω₁ ω₂ t : ℝ}
    (h₁ : HasDerivAt θ₁ ω₁ t) (h₂ : HasDerivAt θ₂ ω₂ t) :
    RigidTransform.bodyVelocity
        (fun s => twoDofFrame01 l₀ (θ₁ s) * twoDofFrame12 l₁ (θ₂ s) * twoDofFrame23 l₂)
        (twoDofPoseDerivative l₀ l₁ l₂ (θ₁ t) (θ₂ t) ω₁ ω₂) t
        (hasDerivAt_twoDofPose l₀ l₁ l₂ h₁ h₂) =
      ⟨WithLp.toLp 2 ![l₁ * sin (θ₂ t) * ω₁, l₁ * cos (θ₂ t) * ω₁ + l₂ * (ω₁ + ω₂), 0],
        WithLp.toLp 2 ![0, 0, ω₁ + ω₂]⟩ := by
  have hlin := RigidTransform.bodyVelocity_linear (hasDerivAt_twoDofPose l₀ l₁ l₂ h₁ h₂)
  have hang := RigidTransform.bodyVelocity_angular (hasDerivAt_twoDofPose l₀ l₁ l₂ h₁ h₂)
  rw [twoDof_spatialVelocity l₀ l₁ l₂ h₁ h₂] at hang
  rw [twoDof_originVelocity] at hlin
  have hp := twoDofPose_eq l₀ l₁ l₂ (θ₁ t) (θ₂ t)
  simp only [hp] at hlin hang
  have hs1 := sin_sq_add_cos_sq (θ₁ t)
  have hs2 := sin_sq_add_cos_sq (θ₂ t)
  apply Twist.ext
  · rw [hlin]
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, cos_add, sin_add]
    · linear_combination l₁ * ω₁ * sin (θ₂ t) * hs1
    · linear_combination (l₁ * ω₁ * cos (θ₂ t) + l₂ * (ω₁ + ω₂)) * hs1 +
        l₂ * (ω₁ + ω₂) * (sin (θ₁ t) ^ 2 + cos (θ₁ t) ^ 2) * hs2
  · rw [hang]
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

end RoboLean.Examples
