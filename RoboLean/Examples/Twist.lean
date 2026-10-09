import RoboLean.Geometry.Twist
import RoboLean.Geometry.TwistAdjoint
import RoboLean.Geometry.TwistExp
import RoboLean.Geometry.TwistExpClosedForm
import RoboLean.Examples.RotationExp

/-!
# Exact twist convention witnesses

MLS printed pp39–42, equations (2.25)–(2.32), order twist coordinates as
`(v, ω)` and put the angular hat and linear column in `[hat(ω) v; 0 0]`.
Printed p55, equations (2.57)–(2.58), gives the adjoint linear part
`R v + p × R ω`. These witnesses have independently specified coordinates;
they are not reconstructions of the expected value through the same API.

All actions below are active maps in one fixed right-handed coordinate frame.
The `g` and `h` fixtures are the existing quarter-turn/translation examples.
The examples do not assert physical calibration, typed units, or frame labels.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix
open scoped Matrix.Norms.Operator

/-- Distinct nonzero components make angular/linear swaps observable. -/
def mixedTwist : Twist := (vec 1 2 3, vec 4 5 6)

/-- The linear column is `(1,2,3)`, while the skew block uses `(4,5,6)`. -/
theorem mixedTwist_hat :
    mixedTwist.hat = Matrix.fromBlocks
      !![0, -6, 5; 6, 0, -4; -5, 4, 0]
      (Matrix.of fun i (_ : Fin 1) => ![1, 2, 3] i) 0 0 := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨?_, ?_, rfl, rfl⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mixedTwist, Twist.hat, Twist.angular, Vec3.hat, vec]
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- `(4,5,6) × (1,1,1) + (1,2,3) = (0,4,2)`; the last coordinate is zero. -/
theorem mixedTwist_hat_point :
    mixedTwist.hat *ᵥ homogeneousPoint (vec 1 1 1) =
      homogeneousVector (vec 0 4 2) := by
  rw [Twist.hat_mulVec_point]
  congr 1
  ext i
  fin_cases i <;>
    norm_num [mixedTwist, Twist.linear, Twist.angular, Vec3.cross, cross_apply, vec]

/-- Rotation about the positive z-axis through `(1,2,0)` has `v = (2,-1,0)`. -/
def offsetAxisTwist : Twist := (vec 2 (-1) 0, vec 0 0 1)

/-- The point on the offset axis has zero instantaneous velocity. -/
theorem offsetAxisTwist_axis_point :
    offsetAxisTwist.hat *ᵥ homogeneousPoint (vec 1 2 0) =
      homogeneousVector (vec 0 0 0) := by
  rw [Twist.hat_mulVec_point]
  congr 1
  ext i
  fin_cases i <;>
    norm_num [offsetAxisTwist, Twist.linear, Twist.angular, Vec3.cross, cross_apply, vec]

/-- One unit along +x from that axis has velocity +y, detecting the origin sign. -/
theorem offsetAxisTwist_off_axis_point :
    offsetAxisTwist.hat *ᵥ homogeneousPoint (vec 2 2 0) =
      homogeneousVector (vec 0 1 0) := by
  rw [Twist.hat_mulVec_point]
  congr 1
  ext i
  fin_cases i <;>
    norm_num [offsetAxisTwist, Twist.linear, Twist.angular, Vec3.cross, cross_apply, vec]

/-- Here `Rv=(-2,1,3)`, `Rω=(-5,4,6)`, and `p×Rω=(0,-21,14)`. -/
theorem adjoint_g_mixedTwist :
    Twist.adjoint g mixedTwist = (vec (-2) (-20) 17, vec (-5) 4 6) := by
  apply Prod.ext
  · change quarterTurn.act (vec 1 2 3) +
      Vec3.cross (vec 1 2 3) (quarterTurn.act (vec 4 5 6)) = _
    rw [quarterTurn_act, quarterTurn_act]
    ext i
    fin_cases i <;> norm_num [Vec3.cross, cross_apply, vec]
  · exact quarterTurn_act 4 5 6

/-- Applying `h` before `g` gives translation `(1,4,3)` and this adjoint. -/
theorem adjoint_g_mul_h_mixedTwist :
    Twist.adjoint (g * h) mixedTwist = (vec 10 (-20) 27, vec (-5) 4 6) := by
  apply Prod.ext
  · change (g * h).rotation.act (vec 1 2 3) +
      Vec3.cross (g * h).translation ((g * h).rotation.act (vec 4 5 6)) = _
    rw [g_mul_h_translation]
    change (quarterTurn * 1).act (vec 1 2 3) +
      Vec3.cross (vec 1 4 3) ((quarterTurn * 1).act (vec 4 5 6)) = _
    rw [mul_one, quarterTurn_act, quarterTurn_act]
    ext i
    fin_cases i <;> norm_num [Vec3.cross, cross_apply, vec]
  · change (quarterTurn * 1).act (vec 4 5 6) = _
    rw [mul_one, quarterTurn_act]

/-- Reversing the active transforms gives translation `(3,2,3)` and a different result. -/
theorem adjoint_h_mul_g_mixedTwist :
    Twist.adjoint (h * g) mixedTwist = (vec (-2) (-32) 25, vec (-5) 4 6) := by
  apply Prod.ext
  · change (h * g).rotation.act (vec 1 2 3) +
      Vec3.cross (h * g).translation ((h * g).rotation.act (vec 4 5 6)) = _
    rw [h_mul_g_translation]
    change (1 * quarterTurn).act (vec 1 2 3) +
      Vec3.cross (vec 3 2 3) ((1 * quarterTurn).act (vec 4 5 6)) = _
    rw [one_mul, quarterTurn_act, quarterTurn_act]
    ext i
    fin_cases i <;> norm_num [Vec3.cross, cross_apply, vec]
  · change (1 * quarterTurn).act (vec 4 5 6) = _
    rw [one_mul, quarterTurn_act]

/-- The actual exponential of an unnormalized pure translation has displacement `t v`. -/
theorem pure_translation_exp_two :
    Twist.exp (vec 2 (-1) 3, 0) 2 = ⟨1, vec 4 (-2) 6⟩ := by
  have hv : (2 : ℝ) • vec 2 (-1) 3 = vec 4 (-2) 6 := by
    ext i
    fin_cases i <;> norm_num [vec]
  apply RigidTransform.toHomogeneous_injective
  rw [Twist.toHomogeneous_exp, Twist.exp_hat_pure_translation, hv]

/-- The zero twist stays at the homogeneous identity at every real parameter. -/
theorem zero_twist_exp_homogeneous (t : ℝ) :
    (Twist.exp (0 : Twist) t).toHomogeneous = 1 := by
  rw [Twist.exp_zero_twist, RigidTransform.toHomogeneous_one]

/-- Nonzero linear motion together with unit angular motion about +z. -/
def helicalTwist : Twist := (vec 1 2 3, vec 0 0 1)

private theorem helicalTwist_angular_norm : ‖helicalTwist.angular‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [helicalTwist, Twist.angular, vec, Fin.sum_univ_succ]

/-- For a quarter turn, `(I-R)(ω×v)=(-1,3,0)` and the axial term is `(0,0,3π/2)`. -/
theorem helicalTwist_exp_pi_div_two :
    Twist.exp helicalTwist (Real.pi / 2) =
      ⟨quarterTurn, vec (-1) 3 (3 * Real.pi / 2)⟩ := by
  have hR : NormedSpace.exp ((Real.pi / 2) • Vec3.hat helicalTwist.angular) =
      quarterTurn.val := by
    change (Rotation.exp (vec 0 0 1) (Real.pi / 2)).val = quarterTurn.val
    rw [exp_z_pi_div_two]
  apply RigidTransform.toHomogeneous_injective
  rw [Twist.toHomogeneous_exp,
    Twist.exp_hat_of_angular_norm_eq_one _ helicalTwist_angular_norm, hR]
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨rfl, ?_, rfl, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [RigidTransform.toHomogeneous, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      helicalTwist, Twist.linear, Twist.angular, Vec3.hat, Vec3.outer, quarterTurn, vec] <;>
    ring

/-- Doubling both components at `π/4` gives the same pose as the full twist at `π/2`. -/
theorem scaled_helicalTwist_exp_pi_div_four :
    Twist.exp (vec 2 4 6, vec 0 0 2) (Real.pi / 4) =
      ⟨quarterTurn, vec (-1) 3 (3 * Real.pi / 2)⟩ := by
  have hscale : (vec 2 4 6, vec 0 0 2) = (2 : ℝ) • helicalTwist := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> norm_num [helicalTwist, vec]
  rw [hscale, Twist.exp_smul,
    show Real.pi / 4 * 2 = Real.pi / 2 by ring, helicalTwist_exp_pi_div_two]

end RoboLean.Examples
