import RoboLean.Geometry.TwistExp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Ring

/-!
# Constant-twist trajectories in a fixed reference frame

MLS Chapter 2, printed pp39–42 and 49, equations (2.25)–(2.26),
(2.37), and (2.45). Points at the initial and current time are expressed
in the same fixed frame. An initial pose maps constant body coordinates
into that frame before the exponential acts by left multiplication.

The results use the actual matrix exponential for every constant twist,
including zero and nonunit angular parts. They prove the differential
equation and initial value, without a uniqueness or physical-rate claim.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Twist

/-- The offset-axis velocity field, without a unit-axis premise. -/
theorem offset_axis_velocity (ω q p : Vec3) :
    Vec3.cross ω (p - q) = Vec3.cross ω p + (-Vec3.cross ω q) := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [Vec3.cross, cross_apply] <;> ring

/-- MLS (2.25)–(2.26): the offset-axis field as a homogeneous twist action. -/
theorem hat_offset_axis_mulVec_point (ω q p : Vec3) :
    hat (⟨-Vec3.cross ω q, ω⟩ : Twist) *ᵥ homogeneousPoint p =
      homogeneousVector (Vec3.cross ω (p - q)) := by
  rw [hat_mulVec_point, offset_axis_velocity]

/-- Exponential matrix action agrees with the packaged affine point action. -/
theorem exp_mulVec_point (ξ : Twist) (t : ℝ) (q : Vec3) :
    NormedSpace.exp (t • ξ.hat) *ᵥ homogeneousPoint q =
      homogeneousPoint ((exp ξ t).applyPoint q) := by
  rw [← toHomogeneous_exp, RigidTransform.toHomogeneous_mulVec_point]

/-- The actual homogeneous matrix exponential solves the constant-twist ODE. -/
theorem hasDerivAt_exp_toHomogeneous (ξ : Twist) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (exp ξ s).toHomogeneous)
      (ξ.hat * (exp ξ t).toHomogeneous) t := by
  simp only [toHomogeneous_exp]
  exact hasDerivAt_exp_smul_const' ξ.hat t

/-- Homogeneous point trajectories have vector derivatives, with last coordinate zero. -/
theorem hasDerivAt_homogeneousPoint_exp_applyPoint (ξ : Twist) (q : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ homogeneousPoint ((exp ξ s).applyPoint q))
      (homogeneousVector
        (Vec3.cross ξ.angular ((exp ξ t).applyPoint q) + ξ.linear)) t := by
  let L : HomogeneousMatrix →ₗ[ℝ] (HomogeneousIndex → ℝ) :=
    (LinearMap.applyₗ (R := ℝ) (M₂ := HomogeneousIndex → ℝ)
      (homogeneousPoint q)).comp Matrix.toLin'.toLinearMap
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_toHomogeneous ξ t)
  change HasDerivAt
    (fun s : ℝ ↦ (exp ξ s).toHomogeneous *ᵥ homogeneousPoint q)
    ((ξ.hat * (exp ξ t).toHomogeneous) *ᵥ homogeneousPoint q) t at h
  simpa only [← Matrix.mulVec_mulVec, RigidTransform.toHomogeneous_mulVec_point,
    hat_mulVec_point] using h

/-- MLS p40: every initial point follows the constant field `ω × q + v`. -/
theorem hasDerivAt_exp_applyPoint (ξ : Twist) (q : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (exp ξ s).applyPoint q)
      (Vec3.cross ξ.angular ((exp ξ t).applyPoint q) + ξ.linear) t := by
  let L : (HomogeneousIndex → ℝ) →ₗ[ℝ] Vec3 :=
    { toFun x := WithLp.toLp 2 (fun i ↦ x (Sum.inl i))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_homogeneousPoint_exp_applyPoint ξ q t)
  exact h

/-- The prescribed initial point is recovered at parameter zero. -/
@[simp] theorem exp_zero_applyPoint (ξ : Twist) (q : Vec3) :
    (exp ξ 0).applyPoint q = q := by
  rw [exp_zero, RigidTransform.one_applyPoint]

/-- MLS (2.37)/(2.45): active motion acts on the initial pose from the left. -/
theorem toHomogeneous_exp_mul (ξ : Twist) (t : ℝ) (g₀ : RigidTransform) :
    (exp ξ t * g₀).toHomogeneous =
      NormedSpace.exp (t • ξ.hat) * g₀.toHomogeneous := by
  rw [RigidTransform.toHomogeneous_mul, toHomogeneous_exp]

/-- A constant body point first uses the initial pose, then the active displacement. -/
theorem exp_mul_applyPoint (ξ : Twist) (t : ℝ) (g₀ : RigidTransform) (q : Vec3) :
    (exp ξ t * g₀).applyPoint q = (exp ξ t).applyPoint (g₀.applyPoint q) :=
  RigidTransform.mul_applyPoint _ _ _

/-- The point carried by an initial pose satisfies the same fixed-frame velocity field. -/
theorem hasDerivAt_exp_mul_applyPoint (ξ : Twist) (g₀ : RigidTransform)
    (q : Vec3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (exp ξ s * g₀).applyPoint q)
      (Vec3.cross ξ.angular ((exp ξ t * g₀).applyPoint q) + ξ.linear) t := by
  simpa only [exp_mul_applyPoint] using hasDerivAt_exp_applyPoint ξ (g₀.applyPoint q) t

/-- The initial pose supplies the fixed-frame initial point. -/
@[simp] theorem exp_zero_mul_applyPoint (ξ : Twist) (g₀ : RigidTransform) (q : Vec3) :
    (exp ξ 0 * g₀).applyPoint q = g₀.applyPoint q := by
  rw [exp_zero, one_mul]

end Twist
end RoboLean
