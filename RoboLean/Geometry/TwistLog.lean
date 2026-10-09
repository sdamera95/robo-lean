import RoboLean.Geometry.RotationLog
import RoboLean.Geometry.TwistSurjectivity

/-!
# A selected principal twist and the inverse translation equation

MLS printed p. 43, equation (2.38), uses a unit axis and `0 < θ < 2π` to
solve the translation coefficient equation. Here the coefficient is inverted
as an actual matrix on that proven nonsingular interval, including `θ = π`.
This is the unit-axis coefficient, not the scaled-log-vector coefficient in
Appendix Example A.15, printed p. 414. We do not use that display's sine
denominator under its insufficient printed nonzero-vector condition.

The selected principal twist below uses the trace-based principal angle and
an existentially chosen unit axis. The zero-angle branch is pure translation,
including zero translation; otherwise the whole twist is scaled to parameter
one. This is a noncomputable selection, with no uniqueness, smoothness, or
numerical implementation guarantee, particularly at the half-turn axis choice.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Twist

/-- Solve the unit-axis translation coefficient equation using its matrix inverse.
Correctness and uniqueness below require the stated nonsingular interval. -/
def inverseTranslation (ω : Vec3) (θ : ℝ) (p : Vec3) : Vec3 :=
  WithLp.toLp 2 ((translationJacobian ω θ)⁻¹ *ᵥ WithLp.ofLp p)

@[simp] theorem inverseTranslation_zero (ω : Vec3) (θ : ℝ) :
    inverseTranslation ω θ 0 = 0 := by
  apply WithLp.ofLp_injective
  change (translationJacobian ω θ)⁻¹ *ᵥ (0 : Fin 3 → ℝ) = 0
  simp

/-- The inverse coefficient reconstructs every translation, including at `π`. -/
theorem translationJacobian_inverseTranslation (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₂π : θ < 2 * Real.pi) (p : Vec3) :
    translationJacobian ω θ *ᵥ WithLp.ofLp (inverseTranslation ω θ p) =
      WithLp.ofLp p :=
  translationJacobian_mulVec_inv_mulVec ω hω θ hθ₀ hθ₂π (WithLp.ofLp p)

/-- For a fixed axis and admissible parameter, the linear twist component solving
MLS equation (2.38) is unique; this is not uniqueness of all twist logarithms. -/
theorem inverseTranslation_eq_iff (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₂π : θ < 2 * Real.pi) (p v : Vec3) :
    translationJacobian ω θ *ᵥ WithLp.ofLp v = WithLp.ofLp p ↔
      v = inverseTranslation ω θ p := by
  constructor
  · intro h
    apply WithLp.ofLp_injective
    apply translationJacobian_mulVec_injective ω hω θ hθ₀ hθ₂π
    rw [h, translationJacobian_inverseTranslation ω hω θ hθ₀ hθ₂π p]
  · rintro rfl
    exact translationJacobian_inverseTranslation ω hω θ hθ₀ hθ₂π p

/-- The solved linear component reconstructs the actual rigid exponential. -/
theorem exp_inverseTranslation (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₂π : θ < 2 * Real.pi) (p : Vec3) :
    exp (inverseTranslation ω θ p, ω) θ =
      { rotation := Rotation.exp ω θ, translation := p } := by
  apply RigidTransform.ext
  · exact exp_rotation (inverseTranslation ω θ p, ω) θ
  · rw [exp_translation_of_angular_norm_eq_one (inverseTranslation ω θ p, ω) hω θ]
    apply WithLp.ofLp_injective
    exact translationJacobian_inverseTranslation ω hω θ hθ₀ hθ₂π p

end Twist

namespace RigidTransform

/-- A selected unit axis for the rotation at its actual principal angle.
No sign selection or continuity is specified at half-turns. -/
def selectedPrincipalAxis (g : RigidTransform) : Vec3 :=
  Classical.choose (Rotation.exists_unit_axis_principalAngle g.rotation)

theorem selectedPrincipalAxis_spec (g : RigidTransform) :
    ‖selectedPrincipalAxis g‖ = 1 ∧
      Rotation.exp (selectedPrincipalAxis g) (Rotation.principalAngle g.rotation) =
        g.rotation :=
  Classical.choose_spec (Rotation.exists_unit_axis_principalAngle g.rotation)

/-- A selected exponential coordinate at parameter one. Both twist components
are scaled in the nonzero-angle branch. Zero angle uses pure translation. -/
def principalTwist (g : RigidTransform) : Twist := by
  classical
  exact if Rotation.principalAngle g.rotation = 0 then
    (g.translation, 0)
  else
    Rotation.principalAngle g.rotation •
      (Twist.inverseTranslation (selectedPrincipalAxis g)
        (Rotation.principalAngle g.rotation) g.translation, selectedPrincipalAxis g)

/-- Pure translation has zero angular component, including zero translation. -/
theorem principalTwist_of_rotation_eq_one (g : RigidTransform) (hR : g.rotation = 1) :
    principalTwist g = (g.translation, 0) := by
  have hθ : Rotation.principalAngle g.rotation = 0 := by
    rw [hR]
    norm_num [Rotation.principalAngle, Matrix.trace_one]
  simp [principalTwist, hθ]

theorem principalTwist_of_principalAngle_ne_zero (g : RigidTransform)
    (hθ : Rotation.principalAngle g.rotation ≠ 0) :
    principalTwist g = Rotation.principalAngle g.rotation •
      (Twist.inverseTranslation (selectedPrincipalAxis g)
        (Rotation.principalAngle g.rotation) g.translation, selectedPrincipalAxis g) := by
  simp [principalTwist, hθ]

@[simp] theorem principalTwist_one : principalTwist 1 = 0 := by
  rw [principalTwist_of_rotation_eq_one (1 : RigidTransform) rfl]
  apply Prod.ext <;> ext i <;> simp

/-- The selected twist reconstructs every rigid transform at parameter one,
including identity, pure translation, and half-turn rotations. -/
theorem exp_principalTwist (g : RigidTransform) : Twist.exp (principalTwist g) 1 = g := by
  classical
  by_cases hθ : Rotation.principalAngle g.rotation = 0
  · have hR := (selectedPrincipalAxis_spec g).2
    rw [hθ, Rotation.exp_zero] at hR
    rw [principalTwist_of_rotation_eq_one g hR.symm,
      Twist.exp_pure_translation, one_smul]
    exact RigidTransform.ext hR rfl
  · have hθ₀ : 0 < Rotation.principalAngle g.rotation :=
      lt_of_le_of_ne (Rotation.principalAngle_mem_Icc g.rotation).1 (Ne.symm hθ)
    have hθ₂π : Rotation.principalAngle g.rotation < 2 * Real.pi := by
      have h := (Rotation.principalAngle_mem_Icc g.rotation).2
      linarith [Real.pi_pos]
    rw [principalTwist_of_principalAngle_ne_zero g hθ, Twist.exp_smul, one_mul,
      Twist.exp_inverseTranslation (selectedPrincipalAxis g) (selectedPrincipalAxis_spec g).1
        (Rotation.principalAngle g.rotation) hθ₀ hθ₂π g.translation]
    exact RigidTransform.ext (selectedPrincipalAxis_spec g).2 rfl

/-- The angular part of the selected exponential coordinate has magnitude equal
to the principal rotation angle; no six-coordinate physical norm is asserted. -/
theorem norm_principalTwist_angular (g : RigidTransform) :
    ‖(principalTwist g).angular‖ = Rotation.principalAngle g.rotation := by
  classical
  by_cases hθ : Rotation.principalAngle g.rotation = 0
  · simp [principalTwist, hθ, Twist.angular]
  · rw [principalTwist_of_principalAngle_ne_zero g hθ]
    change ‖Rotation.principalAngle g.rotation • selectedPrincipalAxis g‖ = _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Rotation.principalAngle_mem_Icc g.rotation).1,
      (selectedPrincipalAxis_spec g).1, mul_one]

end RigidTransform
end RoboLean
