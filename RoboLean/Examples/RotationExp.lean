import RoboLean.Geometry.RotationExp
import RoboLean.Geometry.Rodrigues
import RoboLean.Examples.RigidTransform

/-!
# Exact exponential convention checks

MLS printed p31 writes the positive `Rz` rotation with entries `-sin t` above
and `sin t` below the diagonal. These witnesses relate the actual matrix
exponential to the independently specified `quarterTurn`, including a nonunit
axis whose parameter must be scaled to obtain the same rotation.
-/

namespace RoboLean.Examples

private theorem norm_zAxis : ‖vec 0 0 1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [vec, Fin.sum_univ_succ]

/-- Positive angle in radians about `+z` gives the existing right-handed quarter turn. -/
theorem exp_z_pi_div_two : Rotation.exp (vec 0 0 1) (Real.pi / 2) = quarterTurn := by
  apply Subtype.ext
  rw [Rotation.exp_val, Vec3.exp_hat_of_norm_eq_one _ norm_zAxis]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterTurn, Vec3.hat, vec, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The positive `+z` exponential sends the positive x-axis to the positive y-axis. -/
theorem exp_z_pi_div_two_act_x :
    (Rotation.exp (vec 0 0 1) (Real.pi / 2)).act (vec 1 0 0) = vec 0 1 0 := by
  rw [exp_z_pi_div_two, quarterTurn_act]
  simp

/-- Points on the rotation axis stay fixed in this exact quarter-turn witness. -/
theorem exp_z_pi_div_two_act_z :
    (Rotation.exp (vec 0 0 1) (Real.pi / 2)).act (vec 0 0 1) = vec 0 0 1 := by
  rw [exp_z_pi_div_two, quarterTurn_act]
  simp

/-- Doubling the axis doubles angular rate, so parameter `π/4` gives a quarter turn. -/
theorem exp_two_z_pi_div_four : Rotation.exp (vec 0 0 2) (Real.pi / 4) = quarterTurn := by
  have haxis : vec 0 0 2 = (2 : ℝ) • vec 0 0 1 := by
    ext i
    fin_cases i <;> norm_num [vec]
  rw [haxis, Rotation.exp_smul, show Real.pi / 4 * 2 = Real.pi / 2 by ring,
    exp_z_pi_div_two]

end RoboLean.Examples
