import RoboLean.Geometry.RotationLog

/-!
# Periodicity and parameter ambiguity of rotation exponentials

MLS printed p. 30 after equation (2.17), and p. 31 after Theorem 2.6, describe
full-turn shifts and simultaneous reversal of axis and angle. These identities
use the actual exponential. Periodicity requires a unit axis; simultaneous
sign reversal does not. Principal angles in `[0, π]` are equal for equal
rotations, even when the representing unit axes differ.

These are derived support statements for R20–R21, not new numbered book
obligations. They do not assert endpoint axis uniqueness or a smooth logarithm.
-/

namespace RoboLean.Rotation

/-- A unit-axis exponential is unchanged by any integer number of full turns. -/
theorem exp_add_int_mul_two_pi (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) (k : ℤ) :
    exp ω (θ + k * (2 * Real.pi)) = exp ω θ := by
  apply Subtype.ext
  simp only [exp_val, Vec3.exp_hat_of_norm_eq_one ω hω,
    Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

theorem exp_add_two_pi (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) :
    exp ω (θ + 2 * Real.pi) = exp ω θ := by
  simpa using exp_add_int_mul_two_pi ω hω θ 1

@[simp] theorem exp_two_pi (ω : Vec3) (hω : ‖ω‖ = 1) :
    exp ω (2 * Real.pi) = 1 := by
  simpa using exp_add_two_pi ω hω 0

/-- Reversing an arbitrary axis is equivalent to reversing the parameter. -/
theorem exp_neg_axis (ω : Vec3) (θ : ℝ) : exp (-ω) θ = exp ω (-θ) := by
  simpa using exp_smul (-1 : ℝ) ω θ

/-- Simultaneous sign reversal works without a unit-axis premise. -/
theorem exp_neg_axis_neg (ω : Vec3) (θ : ℝ) : exp (-ω) (-θ) = exp ω θ := by
  rw [exp_neg_axis, neg_neg]

/-- The axis/angle ambiguity stated after MLS Theorem 2.6. -/
theorem exp_neg_axis_two_pi_sub (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) :
    exp (-ω) (2 * Real.pi - θ) = exp ω θ := by
  rw [exp_neg_axis]
  have h := exp_add_two_pi ω hω (-(2 * Real.pi - θ))
  have heq : -(2 * Real.pi - θ) + 2 * Real.pi = θ := by ring
  rw [heq] at h
  exact h.symm

/-- Equal rotations represented by unit axes have the same angle when both
parameters lie in the principal interval. Their axes need not agree at endpoints. -/
theorem angle_eq_of_exp_eq_of_mem_Icc (ω η : Vec3) (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1)
    (θ φ : ℝ) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hφ₀ : 0 ≤ φ) (hφπ : φ ≤ Real.pi) (h : exp ω θ = exp η φ) : θ = φ := by
  have hθ := arccos_trace_exp_of_mem_Icc ω hω θ hθ₀ hθπ
  have hφ := arccos_trace_exp_of_mem_Icc η hη φ hφ₀ hφπ
  rw [h] at hθ
  exact hθ.symm.trans hφ

/-- A fixed unit axis has an injective parameterization on `[0, π]`. -/
theorem exp_eq_iff_of_mem_Icc (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ φ : ℝ) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hφ₀ : 0 ≤ φ) (hφπ : φ ≤ Real.pi) :
    exp ω θ = exp ω φ ↔ θ = φ := by
  constructor
  · exact angle_eq_of_exp_eq_of_mem_Icc ω ω hω hω θ φ hθ₀ hθπ hφ₀ hφπ
  · intro h
    rw [h]

end RoboLean.Rotation
