import RoboLean.Geometry.TwistScrewMotion
import RoboLean.Geometry.TwistScrewInvariants

/-!
# Frame changes of geometric screw motion

Derived from MLS equation (2.40), printed pp. 46–47, and equation (2.64),
p. 59. A fixed rigid transform moves the axis point and rotates its directed
axis, preserving pitch and the signed motion parameter. Reversing the directed
axis requires reversing that parameter to preserve the same displacement.
Pure translation and stationary motion remain separate cases.
-/

noncomputable section

namespace RoboLean.ScrewMotion

/-- Move the geometric motion by a fixed proper rigid transform. The parameter
is unchanged, including when it is negative. -/
def conjugate (g : RigidTransform) : ScrewMotion → ScrewMotion
  | .finite ω q pitch t hω =>
      .finite (g.applyVector ω) (g.applyPoint q) pitch t (by simpa using hω)
  | .translation v t hv => .translation (g.applyVector v) t (by simpa using hv)
  | .stationary => .stationary

@[simp] theorem parameter_conjugate (g : RigidTransform) (S : ScrewMotion) :
    (conjugate g S).parameter = S.parameter := by
  cases S <;> rfl

/-- The independently transformed geometric generator agrees with the coordinate adjoint. -/
theorem generator_conjugate (g : RigidTransform) (S : ScrewMotion) :
    (conjugate g S).generator = Twist.adjoint g S.generator := by
  cases S with
  | finite ω q pitch t hω => exact (Twist.adjoint_fromScrew g ω q pitch).symm
  | translation v t hv =>
      simp [conjugate, generator, Twist.adjoint, Twist.angular, Twist.linear,
        RigidTransform.applyVector]
  | stationary => simp [conjugate, generator]

/-- Geometric frame transformation equals conjugation of the actual displacement. -/
theorem toRigidTransform_conjugate (g : RigidTransform) (S : ScrewMotion) :
    (conjugate g S).toRigidTransform = g * S.toRigidTransform * g⁻¹ := by
  calc
    (conjugate g S).toRigidTransform =
        Twist.exp (conjugate g S).generator (conjugate g S).parameter :=
      (exp_generator _).symm
    _ = Twist.exp (Twist.adjoint g S.generator) S.parameter := by
      rw [generator_conjugate, parameter_conjugate]
    _ = g * Twist.exp S.generator S.parameter * g⁻¹ :=
      Twist.exp_adjoint g S.generator S.parameter
    _ = g * S.toRigidTransform * g⁻¹ := by rw [exp_generator]

/-- Point coordinates transformed by the same fixed frame change give the same motion. -/
theorem conjugate_applyPoint (g : RigidTransform) (S : ScrewMotion) (x : Vec3) :
    (conjugate g S).toRigidTransform.applyPoint (g.applyPoint x) =
      g.applyPoint (S.toRigidTransform.applyPoint x) := by
  rw [toRigidTransform_conjugate]
  simp

/-- A point on the original finite axis moves along the transformed axis after
conjugation. Axis membership uses the actual affine-line carrier. -/
theorem conjugate_finite_applyPoint_on_axis (g : RigidTransform) (ω q : Vec3)
    (pitch t : ℝ) (hω : ‖ω‖ = 1) (x : Vec3) (hx : x ∈ axisLine q ω) :
    (conjugate g (.finite ω q pitch t hω)).toRigidTransform.applyPoint
        (g.applyPoint x) = g.applyPoint x + (pitch * t) • g.applyVector ω := by
  obtain ⟨r, rfl⟩ := (mem_axisLine_iff q ω x).mp hx
  rw [conjugate_applyPoint]
  have hmove : (finite ω q pitch t hω).toRigidTransform.applyPoint (q + r • ω) =
      (q + r • ω) + (pitch * t) • ω := by
    rw [← exp_generator]
    exact Twist.exp_fromScrew_applyPoint_on_axis ω q pitch t r hω
  rw [hmove, RigidTransform.applyPoint_add]
  simp [RigidTransform.applyVector]

/-- Reverse the directed axis and signed parameter together. The finite pitch
stays the same; no claim is made that an axis reversal alone preserves motion. -/
def reverseAxis : ScrewMotion → ScrewMotion
  | .finite ω q pitch t hω => .finite (-ω) q pitch (-t) (by simpa using hω)
  | .translation v t hv => .translation (-v) (-t) (by simpa using hv)
  | .stationary => .stationary

@[simp] theorem parameter_reverseAxis (S : ScrewMotion) :
    S.reverseAxis.parameter = -S.parameter := by
  cases S <;> simp [reverseAxis, parameter]

/-- Axis reversal negates the entire linear/angular generator. -/
theorem generator_reverseAxis (S : ScrewMotion) :
    S.reverseAxis.generator = -S.generator := by
  cases S with
  | finite ω q pitch t hω =>
      simpa only [reverseAxis, generator, neg_one_smul] using
        (Twist.fromScrew_smul ω q pitch (-1)).symm
  | translation v t hv => simp [reverseAxis, generator]
  | stationary => simp [reverseAxis, generator]

/-- The combined sign reversal preserves the independently defined rigid displacement. -/
theorem toRigidTransform_reverseAxis (S : ScrewMotion) :
    S.reverseAxis.toRigidTransform = S.toRigidTransform := by
  rw [← exp_generator, generator_reverseAxis, parameter_reverseAxis]
  have h : Twist.exp (-S.generator) (-S.parameter) =
      Twist.exp S.generator S.parameter := by
    simpa using Twist.exp_smul (-1 : ℝ) S.generator (-S.parameter)
  rw [h, exp_generator]

end RoboLean.ScrewMotion
