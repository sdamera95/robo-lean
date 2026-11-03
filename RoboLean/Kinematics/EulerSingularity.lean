import RoboLean.Kinematics.Singularity
import RoboLean.Geometry.ElementaryRotations

/-!
# Singularities of Euler-angle parameterizations (MLS Exercise 14)

MLS Exercise 14, printed p. 150: "If we think of `(α, β, γ)` as joint angles of a robot
manipulator, then we can find the singularities of an Euler angle parameterization by calculating
the Jacobian of the 'forward kinematics', where we are concerned only with the rotation portion of
the forward kinematics map. Use this point of view to find singularities for (a) ZYZ, (b) ZYX,
(c) XYZ Euler angles."

`eulerChain a b c` is the chain of three revolute joints with unit axes `a, b, c` through the
origin and `g_st(0) = I`; its forward kinematics is the pure rotation
`e^{âα} e^{b̂β} e^{ĉγ}` (MLS eq. (3.3), p. 87). Its spatial Jacobian columns (MLS eq. (3.54),
p. 116) are `(0, ωᵢ')` with `ω₁' = a`, `ω₂' = e^{âα} b`, `ω₃' = e^{âα} e^{b̂β} c`, so a
configuration is singular (MLS p. 123) exactly when the `3 × 3` matrix with these columns has zero
determinant. For the three orders of the exercise the determinant is `-sin β` (ZYZ), `-cos β` (ZYX)
and `cos β` (XYZ): ZYZ angles are singular exactly at `sin β = 0`, ZYX and XYZ angles exactly at
`cos β = 0`.

Conventions: twists `(v, ω)`, Lean joint `k` is the book's joint `k + 1` (`θ 0 = α`, `θ 1 = β`,
`θ 2 = γ`), real angles, the elementary rotations of MLS p. 31.
-/

noncomputable section

open Real Matrix

namespace RoboLean

namespace SerialChain

private theorem revolute_zero (v : Vec3) : Twist.revolute v 0 = ⟨0, v⟩ := by
  apply Twist.ext <;> simp [Twist.revolute]

private theorem exp_rot {a : Vec3} (ha : ‖a‖ = 1) (t : ℝ) :
    Twist.exp ⟨0, a⟩ t = ⟨Rotation.exp a t, 0⟩ := by
  rw [← revolute_zero, Twist.exp_revolute a 0 ha]
  simp

private theorem adjoint_rot (R : Rotation) (v : Vec3) :
    Twist.adjoint ⟨R, 0⟩ ⟨0, v⟩ = ⟨0, R.act v⟩ := by
  rw [← revolute_zero, Twist.adjoint_revolute]
  simp [RigidTransform.applyVector, RigidTransform.applyPoint, revolute_zero]

private theorem norm_zAxis_e : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem exp_zAxis_e (t : ℝ) : Rotation.exp Rotation.zAxis t = Rotation.zRotation t := rfl

/-- The chain of three revolute joints with axes `a, b, c` through the origin and reference tool
pose `I`, MLS Exercise 14, p. 150: an Euler-angle parameterization read as a manipulator. -/
def eulerChain (a b c : Vec3) : SerialChain 3 where
  twist := ![Twist.revolute a 0, Twist.revolute b 0, Twist.revolute c 0]
  toolRef := 1

/-- The angular parts `ω₁' = a`, `ω₂' = e^{âα} b`, `ω₃' = e^{âα} e^{b̂β} c` of the spatial Jacobian
columns of `eulerChain a b c` (MLS eq. (3.54), p. 116), as the columns of a `3 × 3` matrix. -/
def eulerJacobian (a b c : Vec3) (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    ![a, (Rotation.exp a (θ 0)).act b, (Rotation.exp a (θ 0) * Rotation.exp b (θ 1)).act c] j i

/-- **MLS Exercise 14, p. 150, with eq. (3.54), p. 116.** For unit axes `a, b, c`, the spatial
Jacobian columns of `eulerChain a b c` are the pure rotations `(0, ωᵢ')` about the current axes
`ω₁' = a`, `ω₂' = e^{âα} b`, `ω₃' = e^{âα} e^{b̂β} c`. -/
theorem eulerChain_spatialJacobian {a b c : Vec3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (θ : Fin 3 → ℝ) :
    (eulerChain a b c).spatialJacobian θ = ![⟨0, a⟩, ⟨0, (Rotation.exp a (θ 0)).act b⟩,
      ⟨0, (Rotation.exp a (θ 0) * Rotation.exp b (θ 1)).act c⟩] := by
  funext i
  fin_cases i <;>
    simp [spatialJacobian, jointMotions, eulerChain, List.ofFn_succ, revolute_zero, exp_rot ha,
      exp_rot hb, adjoint_rot]

/-- **MLS Exercise 14, p. 150, and p. 123.** For unit axes, a configuration of the Euler-angle
chain is singular exactly when the determinant of the matrix of current rotation axes
`[ω₁' ω₂' ω₃']` vanishes. -/
theorem isSingular_eulerChain_iff {a b c : Vec3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (θ : Fin 3 → ℝ) : (eulerChain a b c).IsSingular θ ↔ (eulerJacobian a b c θ).det = 0 := by
  rw [isSingular_iff_not_linearIndependent _ θ (by norm_num), eulerChain_spatialJacobian ha hb]
  set ω : Fin 3 → Vec3 := ![a, (Rotation.exp a (θ 0)).act b,
    (Rotation.exp a (θ 0) * Rotation.exp b (θ 1)).act c]
  have hcomp : (![⟨0, a⟩, ⟨0, (Rotation.exp a (θ 0)).act b⟩,
      ⟨0, (Rotation.exp a (θ 0) * Rotation.exp b (θ 1)).act c⟩] : Fin 3 → Twist) =
      Twist.revoluteLinear 0 ∘ ω := by
    funext i
    fin_cases i <;> simp [ω, Twist.revoluteLinear_apply, revolute_zero]
  have hker : LinearMap.ker (Twist.revoluteLinear 0) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have := congrArg Twist.angular hv
    simpa [Twist.revoluteLinear_apply, Twist.revolute] using this
  rw [hcomp, LinearMap.linearIndependent_iff _ hker]
  have hcol : (eulerJacobian a b c θ).col = fun j => WithLp.ofLp (ω j) := by
    funext j i
    simp [eulerJacobian, Matrix.col, ω]
  rw [← (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap.linearIndependent_iff
      (LinearEquiv.ker _)]
  change ¬LinearIndependent ℝ (fun j => WithLp.ofLp (ω j)) ↔ _
  rw [← hcol, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not]

/-- **MLS Exercise 14(a), p. 150: ZYZ Euler angles.** The determinant of the axis matrix is
`-sin β`, so the ZYZ parameterization is singular exactly when `sin β = 0`. -/
theorem isSingular_eulerChain_zyz (θ : Fin 3 → ℝ) :
    (eulerJacobian Rotation.zAxis Rotation.yAxis Rotation.zAxis θ).det = -sin (θ 1) ∧
      ((eulerChain Rotation.zAxis Rotation.yAxis Rotation.zAxis).IsSingular θ ↔
        sin (θ 1) = 0) := by
  have hdet : (eulerJacobian Rotation.zAxis Rotation.yAxis Rotation.zAxis θ).det =
      -sin (θ 1) := by
    simp only [eulerJacobian, exp_zAxis_e, Rotation.exp_yAxis]
    simp [Matrix.det_fin_three, Rotation.act_apply, Rotation.zRotation_val, Rotation.yMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Rotation.zAxis,
      Rotation.yAxis]
    linear_combination (-sin (θ 1)) * sin_sq_add_cos_sq (θ 0)
  rw [isSingular_eulerChain_iff norm_zAxis_e Rotation.norm_yAxis, hdet, neg_eq_zero]
  exact ⟨rfl, Iff.rfl⟩

/-- **MLS Exercise 14(b), p. 150: ZYX Euler angles.** The determinant of the axis matrix is
`-cos β`, so the ZYX parameterization is singular exactly when `cos β = 0`, i.e. at
`β = ±π/2` modulo `2π`. -/
theorem isSingular_eulerChain_zyx (θ : Fin 3 → ℝ) :
    (eulerJacobian Rotation.zAxis Rotation.yAxis Rotation.xAxis θ).det = -cos (θ 1) ∧
      ((eulerChain Rotation.zAxis Rotation.yAxis Rotation.xAxis).IsSingular θ ↔
        cos (θ 1) = 0) := by
  have hdet : (eulerJacobian Rotation.zAxis Rotation.yAxis Rotation.xAxis θ).det =
      -cos (θ 1) := by
    simp only [eulerJacobian, exp_zAxis_e, Rotation.exp_yAxis]
    simp [Matrix.det_fin_three, Rotation.act_apply, Rotation.zRotation_val, Rotation.yMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Rotation.zAxis,
      Rotation.yAxis, Rotation.xAxis]
    linear_combination (-cos (θ 1)) * sin_sq_add_cos_sq (θ 0)
  rw [isSingular_eulerChain_iff norm_zAxis_e Rotation.norm_yAxis, hdet, neg_eq_zero]
  exact ⟨rfl, Iff.rfl⟩

/-- **MLS Exercise 14(c), p. 150: XYZ Euler angles.** The determinant of the axis matrix is
`cos β`, so the XYZ parameterization is singular exactly when `cos β = 0`. -/
theorem isSingular_eulerChain_xyz (θ : Fin 3 → ℝ) :
    (eulerJacobian Rotation.xAxis Rotation.yAxis Rotation.zAxis θ).det = cos (θ 1) ∧
      ((eulerChain Rotation.xAxis Rotation.yAxis Rotation.zAxis).IsSingular θ ↔
        cos (θ 1) = 0) := by
  have hdet : (eulerJacobian Rotation.xAxis Rotation.yAxis Rotation.zAxis θ).det =
      cos (θ 1) := by
    simp only [eulerJacobian, Rotation.exp_yAxis, Rotation.exp_xAxis]
    simp [Matrix.det_fin_three, Rotation.act_apply, Rotation.yMatrix,
      Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Rotation.zAxis,
      Rotation.yAxis, Rotation.xAxis]
    linear_combination (cos (θ 1)) * sin_sq_add_cos_sq (θ 0)
  rw [isSingular_eulerChain_iff Rotation.norm_xAxis Rotation.norm_yAxis, hdet]
  exact ⟨rfl, Iff.rfl⟩

end SerialChain

end RoboLean
