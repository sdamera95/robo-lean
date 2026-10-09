import RoboLean.Geometry.TwistScrew
import RoboLean.Geometry.TwistExpClosedForm
import RoboLean.Geometry.TwistExpAdjoint
import RoboLean.Geometry.RotationSurjectivity
import RoboLean.Geometry.RotationVelocity

/-!
# Geometric screw motion and its actual twist exponential

MLS printed pp. 46–49, Definition 2.2, equations (2.40)–(2.41), and
Proposition 2.10. Finite-pitch and pure-translation motions have separate
constructors. Parameters are signed, not norm-based magnitudes; stationary
motion is explicit. The geometric rigid transform is defined independently
of the twist exponential, and their agreement is a theorem.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Twist

private theorem exp_parallel_axis (ω : Vec3) (hω : ‖ω‖ = 1) (pitch t : ℝ) :
    exp ⟨pitch • ω, ω⟩ t = ⟨Rotation.exp ω t, (pitch * t) • ω⟩ := by
  have houter : Vec3.outer ω ω *ᵥ WithLp.ofLp ω = WithLp.ofLp ω := by
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ ↦ A *ᵥ WithLp.ofLp ω)
      (Vec3.hat_sq_of_norm_eq_one ω hω)
    rw [pow_two, ← Matrix.mulVec_mulVec, Vec3.hat_mulVec_self, Matrix.mulVec_zero,
      Matrix.sub_mulVec, Matrix.one_mulVec] at h
    exact sub_eq_zero.mp h.symm
  apply RigidTransform.ext
  · exact exp_rotation ⟨pitch • ω, ω⟩ t
  · rw [exp_translation_of_angular_norm_eq_one ⟨pitch • ω, ω⟩ hω t]
    apply WithLp.ofLp_injective
    change (((1 - NormedSpace.exp (t • Vec3.hat ω)) * Vec3.hat ω +
      t • Vec3.outer ω ω) *ᵥ (pitch • WithLp.ofLp ω)) =
      (pitch * t) • WithLp.ofLp ω
    simp only [Matrix.mulVec_smul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      Vec3.hat_mulVec_self, Matrix.mulVec_zero, Matrix.smul_mulVec, houter,
      zero_add, smul_smul]

/-- MLS (2.40): the finite screw generator gives the independently specified
rotation and translation, including zero and negative parameters. -/
theorem exp_fromScrew (ω q : Vec3) (pitch t : ℝ) (hω : ‖ω‖ = 1) :
    exp (fromScrew ω q pitch) t =
      ⟨Rotation.exp ω t,
        q - (Rotation.exp ω t).act q + (pitch * t) • ω⟩ := by
  have hξ : fromScrew ω q pitch = adjoint (⟨1, q⟩ : RigidTransform) ⟨pitch • ω, ω⟩ := by
    apply Twist.ext
    · change -Vec3.cross ω q + pitch • ω =
        (1 : Rotation).act (pitch • ω) + Vec3.cross q ((1 : Rotation).act ω)
      rw [Rotation.act_one, Rotation.act_one, Vec3.cross_anticomm q ω]
      exact add_comm _ _
    · exact (Rotation.act_one ω).symm
  rw [hξ, exp_adjoint, exp_parallel_axis ω hω pitch t]
  apply RigidTransform.ext
  · simp
  · simp [map_neg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The actual exponential moves each point by rotation about the axis and
translation parallel to that same directed axis. -/
theorem exp_fromScrew_applyPoint (ω q : Vec3) (pitch t : ℝ) (hω : ‖ω‖ = 1)
    (x : Vec3) :
    (exp (fromScrew ω q pitch) t).applyPoint x =
      (Rotation.exp ω t).act (x - q) + q + (pitch * t) • ω := by
  rw [exp_fromScrew ω q pitch t hω]
  simp only [RigidTransform.applyPoint, map_sub]
  module

/-- MLS p. 49: points on the finite screw axis move only along that axis. -/
theorem exp_fromScrew_applyPoint_on_axis (ω q : Vec3) (pitch t r : ℝ)
    (hω : ‖ω‖ = 1) :
    (exp (fromScrew ω q pitch) t).applyPoint (q + r • ω) =
      (q + r • ω) + (pitch * t) • ω := by
  rw [exp_fromScrew_applyPoint ω q pitch t hω]
  simp only [add_sub_cancel_left, map_smul, Rotation.exp_act_unit_axis ω hω t]
  module

/-- The pure-translation branch, including a zero direction or zero parameter. -/
theorem exp_pure_translation_applyPoint (v : Vec3) (t : ℝ) (x : Vec3) :
    (exp ⟨v, 0⟩ t).applyPoint x = x + t • v := by
  rw [exp_pure_translation]
  simp [RigidTransform.applyPoint]

end Twist

/-- Geometric screw data with unit directions, signed parameters, and explicit
finite-pitch, pure-translation, and stationary cases. Infinity is not a real pitch. -/
inductive ScrewMotion where
  | finite (axis point : Vec3) (pitch parameter : ℝ) (unit_axis : ‖axis‖ = 1)
  | translation (direction : Vec3) (parameter : ℝ) (unit_direction : ‖direction‖ = 1)
  | stationary

namespace ScrewMotion

/-- The literal geometric rigid displacement from MLS (2.40) and (2.41). -/
def toRigidTransform : ScrewMotion → RigidTransform
  | .finite ω q pitch t _ =>
      ⟨Rotation.exp ω t, q - (Rotation.exp ω t).act q + (pitch * t) • ω⟩
  | .translation v t _ => ⟨1, t • v⟩
  | .stationary => 1

/-- The associated generator; its exponential is not used to define the motion. -/
def generator : ScrewMotion → Twist
  | .finite ω q pitch _ _ => Twist.fromScrew ω q pitch
  | .translation v _ _ => ⟨v, 0⟩
  | .stationary => 0

/-- The signed motion parameter, independent of the norm-based screw magnitude. -/
def parameter : ScrewMotion → ℝ
  | .finite _ _ _ t _ => t
  | .translation _ t _ => t
  | .stationary => 0

/-- Every nonstationary datum has a unit generator in the source's two-branch sense. -/
theorem generator_isUnit (S : ScrewMotion) (hS : S ≠ .stationary) :
    Twist.IsUnitTwist S.generator := by
  cases S with
  | finite ω q pitch t hω => exact Or.inl hω
  | translation v t hv => exact Or.inr ⟨rfl, hv⟩
  | stationary => exact (hS rfl).elim

/-- Proposition 2.10: actual twist exponentiation agrees with independently
specified finite-pitch and pure-translation geometric motions. -/
theorem exp_generator (S : ScrewMotion) :
    Twist.exp S.generator S.parameter = S.toRigidTransform := by
  cases S with
  | finite ω q pitch t hω => exact Twist.exp_fromScrew ω q pitch t hω
  | translation v t hv => exact Twist.exp_pure_translation v t
  | stationary => exact Twist.exp_zero 0

/-- Replacing an axis representative by another point on the same directed line
leaves the independent geometric displacement unchanged. -/
theorem finite_axis_shift (ω q : Vec3) (pitch t r : ℝ) (hω : ‖ω‖ = 1) :
    (finite ω (q + r • ω) pitch t hω).toRigidTransform =
      (finite ω q pitch t hω).toRigidTransform := by
  rw [← exp_generator, ← exp_generator]
  exact Twist.exp_fromScrew_axis_shift ω q pitch r t

/-- Zero parameter is stationary for every finite screw datum. -/
@[simp] theorem finite_zero (ω q : Vec3) (pitch : ℝ) (hω : ‖ω‖ = 1) :
    (finite ω q pitch 0 hω).toRigidTransform = 1 := by
  rw [← exp_generator]
  exact Twist.exp_zero _

/-- Zero translation parameter is stationary for every unit translation direction. -/
@[simp] theorem translation_zero (v : Vec3) (hv : ‖v‖ = 1) :
    (translation v 0 hv).toRigidTransform = 1 := by
  rw [← exp_generator]
  exact Twist.exp_zero _

@[simp] theorem stationary_toRigidTransform : stationary.toRigidTransform = 1 := rfl

end ScrewMotion
end RoboLean

namespace RoboLean.Twist

private theorem norm_zAxis_motion : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

/-- The explicit translation coefficient for any twist with positive unit z-axis. -/
theorem exp_zAxis_translation (v : Vec3) (t : ℝ) :
    (exp ⟨v, Rotation.zAxis⟩ t).translation = WithLp.toLp 2
      ![Real.sin t * v 0 + (Real.cos t - 1) * v 1,
        (1 - Real.cos t) * v 0 + Real.sin t * v 1, t * v 2] := by
  have hR : NormedSpace.exp (t • Vec3.hat Rotation.zAxis) =
      (Rotation.zRotation t).val := rfl
  rw [exp_translation_of_angular_norm_eq_one ⟨v, Rotation.zAxis⟩ norm_zAxis_motion t,
    hR, Rotation.zRotation_val]
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Vec3.hat, Vec3.outer, Rotation.zAxis, Matrix.vecMulVec, Matrix.one_apply,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

/-- MLS Examples 2.2–2.3: constant relative motion about the line through
`(0,l₁,0)`, multiplied by the initial pose. All real angles, including zero, occur. -/
theorem exp_offset_z_mul_initial (l₁ l₂ t : ℝ) :
    exp ⟨WithLp.toLp 2 ![l₁, 0, 0], Rotation.zAxis⟩ t *
      (⟨1, WithLp.toLp 2 ![0, l₁ + l₂, 0]⟩ : RigidTransform) =
      ⟨Rotation.zRotation t,
        WithLp.toLp 2 ![-l₂ * Real.sin t, l₁ + l₂ * Real.cos t, 0]⟩ := by
  apply RigidTransform.ext
  · simp [exp_rotation, Rotation.zRotation]
  · rw [RigidTransform.mul_translation, exp_rotation, exp_zAxis_translation]
    apply WithLp.ofLp_injective
    change (Rotation.exp Rotation.zAxis t).val *ᵥ ![0, l₁ + l₂, 0] +
        ![Real.sin t * l₁ + (Real.cos t - 1) * 0,
          (1 - Real.cos t) * l₁ + Real.sin t * 0, t * 0] =
        ![-l₂ * Real.sin t, l₁ + l₂ * Real.cos t, 0]
    rw [show (Rotation.exp Rotation.zAxis t).val =
      !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]
      from Rotation.zRotation_val t]
    ext i
    fin_cases i <;> simp <;> ring

/-- MLS Example 2.2's absolute-pose exponential coordinates. The actual
restriction is `cos t ≠ 1`, excluding every full turn, not merely `t = 0`. -/
theorem exp_absolute_z_pose (l₁ l₂ t : ℝ) (ht : Real.cos t ≠ 1) :
    exp ⟨WithLp.toLp 2 ![(l₁ - l₂) / 2,
      (l₁ + l₂) * Real.sin t / (2 * (1 - Real.cos t)), 0], Rotation.zAxis⟩ t =
      ⟨Rotation.zRotation t,
        WithLp.toLp 2 ![-l₂ * Real.sin t, l₁ + l₂ * Real.cos t, 0]⟩ := by
  have hden : 1 - Real.cos t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have htrig : (l₁ + l₂) * (Real.sin t ^ 2 + Real.cos t ^ 2 - 1) = 0 := by
    rw [Real.sin_sq_add_cos_sq]
    ring
  apply RigidTransform.ext
  · exact exp_rotation _ t
  · rw [exp_zAxis_translation]
    apply WithLp.ofLp_injective
    ext i
    fin_cases i
    · dsimp
      field_simp [hden]
      ring
    · dsimp
      field_simp [hden]
      nlinarith [htrig]
    · simp

end RoboLean.Twist
