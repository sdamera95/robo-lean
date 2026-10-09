import RoboLean.Geometry.TwistScrew
import RoboLean.Geometry.TwistExpClosedForm

/-!
# Magnitude-based normalization of an entire twist

MLS printed pp48–49, equation (2.44) and the two unit-twist branches.
Normalization divides both components by screw magnitude and handles zero
explicitly. The actual exponential parameter is rescaled by that same
magnitude. Existing angular normalization is retained as the rotating case;
this API also covers nonzero pure translation without inventing finite pitch.
-/

noncomputable section

namespace RoboLean.Twist

/-- Normalize both twist components by the source's branch-dependent magnitude. -/
def normalized (ξ : Twist) : Twist := (screwMagnitude ξ)⁻¹ • ξ

@[simp] theorem normalized_zero : normalized (0 : Twist) = 0 := by
  simp [normalized]

@[simp] theorem normalized_linear (ξ : Twist) :
    (normalized ξ).linear = (screwMagnitude ξ)⁻¹ • ξ.linear := rfl

@[simp] theorem normalized_angular (ξ : Twist) :
    (normalized ξ).angular = (screwMagnitude ξ)⁻¹ • ξ.angular := rfl

/-- On the rotating branch this is the existing full-pair angular normalization. -/
theorem normalized_of_angular_ne_zero (ξ : Twist) (hω : ξ.angular ≠ 0) :
    normalized ξ = ‖ξ.angular‖⁻¹ • ξ := by
  rw [normalized, screwMagnitude_of_angular_ne_zero ξ hω]

/-- The pure-translation branch normalizes its linear direction, including the zero convention. -/
theorem normalized_pure_translation (v : Vec3) :
    normalized (v, 0) = (‖v‖⁻¹ • v, 0) := by
  simp [normalized, screwMagnitude, linear, angular]

/-- Every nonzero twist normalizes to unit screw magnitude. -/
theorem normalized_unit (ξ : Twist) (hξ : ξ ≠ 0) : IsUnitTwist (normalized ξ) := by
  have hm : screwMagnitude ξ ≠ 0 := fun h ↦ hξ ((screwMagnitude_eq_zero_iff ξ).mp h)
  rw [isUnitTwist_iff_magnitude_eq_one, normalized, screwMagnitude_smul,
    abs_inv, abs_of_nonneg (screwMagnitude_nonneg ξ), inv_mul_cancel₀ hm]

/-- Normalization changes neither coordinate component beyond a common scalar factor. -/
theorem magnitude_smul_normalized (ξ : Twist) : screwMagnitude ξ • normalized ξ = ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  have hm : screwMagnitude ξ ≠ 0 := fun h ↦ hξ ((screwMagnitude_eq_zero_iff ξ).mp h)
  rw [normalized, smul_smul, mul_inv_cancel₀ hm, one_smul]

theorem normalized_of_unit (ξ : Twist) (hξ : IsUnitTwist ξ) : normalized ξ = ξ := by
  rw [normalized, (isUnitTwist_iff_magnitude_eq_one ξ).mp hξ, inv_one, one_smul]

@[simp] theorem normalized_idempotent (ξ : Twist) : normalized (normalized ξ) = normalized ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  exact normalized_of_unit _ (normalized_unit ξ hξ)

/-- Actual exponential motion is preserved after full-pair and parameter normalization. -/
theorem exp_eq_normalized (ξ : Twist) (t : ℝ) :
    exp ξ t = exp (normalized ξ) (screwMagnitude ξ * t) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  have hm : screwMagnitude ξ ≠ 0 := fun h ↦ hξ ((screwMagnitude_eq_zero_iff ξ).mp h)
  rw [normalized, exp_smul]
  congr 1
  field_simp [hm]

/-- Scaling normalization retains only the scalar's sign, including the zero convention. -/
theorem normalized_smul (ξ : Twist) (c : ℝ) :
    normalized (c • ξ) = (c / |c|) • normalized ξ := by
  simp only [normalized, screwMagnitude_smul, mul_inv, smul_smul, div_eq_mul_inv]
  congr 1
  ring

/-- A positive full-twist scale preserves its normalized directed coordinates. -/
theorem normalized_smul_of_pos (ξ : Twist) (c : ℝ) (hc : 0 < c) :
    normalized (c • ξ) = normalized ξ := by
  rw [normalized_smul, abs_of_pos hc, div_self (ne_of_gt hc), one_smul]

/-- A negative full-twist scale reverses the normalized directed coordinates. -/
theorem normalized_smul_of_neg (ξ : Twist) (c : ℝ) (hc : c < 0) :
    normalized (c • ξ) = -normalized ξ := by
  rw [normalized_smul, abs_of_neg hc, div_neg, div_self (ne_of_lt hc), neg_one_smul]

end RoboLean.Twist
