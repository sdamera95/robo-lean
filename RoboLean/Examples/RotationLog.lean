import RoboLean.Geometry.RotationLog
import RoboLean.Geometry.ElementaryRotations
import RoboLean.Examples.RotationExp

/-!
# Independent rotation recovery and endpoint witnesses

MLS printed pp30–31 motivates principal-angle recovery and elementary axis
rotations. The generic skew-part formula needs nonzero sine; at identity and
at a half-turn its totalized real-coordinate expression below is zero, not a
unit axis. The half-turn fixture is an independently specified diagonal matrix,
and both `+x` and `-x` exponentiate to it at `π`. Arbitrary-vector quarter-turn
actions check the handedness of all three elementary families.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix

/-- The independently specified x-axis half-turn, with diagonal `(1,-1,-1)`. -/
def halfTurnX : Rotation :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    · norm_num [Matrix.det_fin_three]⟩

/-- The actual positive x exponential reaches the independently written half-turn. -/
theorem exp_x_pi_halfTurnX : Rotation.exp Rotation.xAxis Real.pi = halfTurnX := by
  apply Subtype.ext
  rw [Rotation.exp_xAxis_val]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Rotation.xMatrix, halfTurnX]

/-- Reversing the axis gives the same half-turn at the same positive angle. -/
theorem exp_neg_x_pi_halfTurnX : Rotation.exp (-Rotation.xAxis) Real.pi = halfTurnX := by
  rw [show -Rotation.xAxis = (-1 : ℝ) • Rotation.xAxis by simp, Rotation.exp_smul]
  apply Subtype.ext
  rw [Rotation.exp_xAxis_val]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Rotation.xMatrix, halfTurnX]

/-- Two distinct unit signed axes realize this exact half-turn. -/
theorem halfTurnX_axis_nonunique :
    ‖Rotation.xAxis‖ = 1 ∧ ‖-Rotation.xAxis‖ = 1 ∧
      Rotation.xAxis ≠ -Rotation.xAxis ∧
      Rotation.exp Rotation.xAxis Real.pi = halfTurnX ∧
      Rotation.exp (-Rotation.xAxis) Real.pi = halfTurnX := by
  refine ⟨Rotation.norm_xAxis, by simp, ?_, exp_x_pi_halfTurnX, exp_neg_x_pi_halfTurnX⟩
  intro h
  have h₀ := congrArg (fun v : Vec3 => v 0) h
  norm_num [Rotation.xAxis] at h₀

/-- Identity has principal angle zero by direct evaluation of its trace. -/
theorem identity_principalAngle : Rotation.principalAngle (1 : Rotation) = 0 := by
  norm_num [Rotation.principalAngle, Matrix.trace, Matrix.diag,
    Matrix.one_apply, Fin.sum_univ_succ]

/-- The generic expression at identity is zero and therefore cannot be its unit-axis selector. -/
theorem identity_genericAxis_zero : Rotation.genericAxis (1 : Rotation) = 0 := by
  rw [Rotation.genericAxis, identity_principalAngle]
  simp

/-- The diagonal fixture has trace minus one and principal angle `π`. -/
theorem halfTurnX_principalAngle : Rotation.principalAngle halfTurnX = Real.pi := by
  norm_num [Rotation.principalAngle, halfTurnX, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

/-- A half-turn also lies outside the nonzero-sine recovery domain. -/
theorem halfTurnX_genericAxis_zero : Rotation.genericAxis halfTurnX = 0 := by
  rw [Rotation.genericAxis, halfTurnX_principalAngle]
  simp

/-- The independent positive z quarter-turn has principal angle `π/2`. -/
theorem quarterTurn_principalAngle : Rotation.principalAngle quarterTurn = Real.pi / 2 := by
  norm_num [Rotation.principalAngle, quarterTurn, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

/-- The literal skew entries recover the positive z unit axis for the quarter-turn. -/
theorem quarterTurn_genericAxis : Rotation.genericAxis quarterTurn = vec 0 0 1 := by
  rw [Rotation.genericAxis, quarterTurn_principalAngle]
  ext i
  fin_cases i <;> norm_num [quarterTurn, Vec3.vee, vec]

/-- The recovered quarter-turn parameters reconstruct the original independent matrix. -/
theorem quarterTurn_genericAxis_reconstruct :
    Rotation.exp (Rotation.genericAxis quarterTurn) (Rotation.principalAngle quarterTurn) = quarterTurn := by
  rw [quarterTurn_genericAxis, quarterTurn_principalAngle, exp_z_pi_div_two]

/-- Positive x quarter-turn acts as `(x,y,z) ↦ (x,-z,y)`. -/
theorem exp_x_quarter_coordinates (x y z : ℝ) :
    (Rotation.exp Rotation.xAxis (Real.pi / 2)).act (vec x y z) = vec x (-z) y := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;>
    simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

/-- Positive y quarter-turn acts as `(x,y,z) ↦ (z,y,-x)`. -/
theorem exp_y_quarter_coordinates (x y z : ℝ) :
    (Rotation.exp Rotation.yAxis (Real.pi / 2)).act (vec x y z) = vec z y (-x) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_yAxis_val]
  fin_cases i <;>
    simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

/-- Positive z quarter-turn acts as `(x,y,z) ↦ (-y,x,z)`. -/
theorem exp_z_quarter_coordinates (x y z : ℝ) :
    (Rotation.exp Rotation.zAxis (Real.pi / 2)).act (vec x y z) = vec (-y) x z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

end RoboLean.Examples
