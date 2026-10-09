import RoboLean.Geometry.RotationExp
import RoboLean.Geometry.Rodrigues
import RoboLean.Geometry.RotationSurjectivity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Principal angles and axis recovery for proper rotations

MLS printed pp. 29–31, equations (2.16)–(2.18), motivate these R20–R21
identities. The forward formulas start from the actual matrix exponential with
an explicitly unit Euclidean axis. The arbitrary-rotation statements then use
the independently proved existence of an axis and angle in `[0, π]`.

Generic signed-axis recovery requires `sin θ ≠ 0`, which excludes the half-turn
denominator that the printed condition `θ ≠ 0` alone does not exclude. The
separate half-turn formula recovers the axis projector, not a unique signed axis.
No global smooth logarithm or endpoint uniqueness is asserted.
-/

namespace RoboLean
namespace Rotation

open Matrix

private theorem trace_hat_zero (ω : Vec3) : Matrix.trace (Vec3.hat ω) = 0 := by
  simp [Matrix.trace, Vec3.hat, Fin.sum_univ_succ]

private theorem trace_outer_self (ω : Vec3) :
    Matrix.trace (Vec3.outer ω ω) = ‖ω‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.trace, Matrix.diag, Vec3.outer, Matrix.vecMulVec, pow_two]

/-- MLS equation (2.17)'s trace identity for an actual unit-axis exponential. -/
theorem trace_exp_of_norm_eq_one (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) :
    Matrix.trace (exp ω θ).val = 1 + 2 * Real.cos θ := by
  simp [exp_val, Vec3.exp_hat_of_norm_eq_one ω hω,
    Vec3.hat_sq_of_norm_eq_one ω hω, trace_hat_zero, trace_outer_self, hω]
  ring

/-- The three antisymmetric entries in MLS equation (2.18), as a matrix identity. -/
theorem exp_sub_transpose_of_norm_eq_one (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) :
    (exp ω θ).val - (exp ω θ).valᵀ = (2 * Real.sin θ) • Vec3.hat ω := by
  have htranspose : (exp ω θ).valᵀ = (exp ω (-θ)).val := by
    rw [exp_neg, inv_val]
  rw [htranspose, exp_val, exp_val, Vec3.exp_hat_of_norm_eq_one ω hω θ,
    Vec3.exp_hat_of_norm_eq_one ω hω (-θ)]
  simp only [Real.sin_neg, Real.cos_neg]
  module

/-- Generic recovery of the signed axis, with the nonzero sine denominator
required by the formula. In particular this theorem does not apply at a half-turn. -/
theorem axis_recovery_of_sin_ne_zero (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    (2 * Real.sin θ)⁻¹ • Vec3.vee ((exp ω θ).val - (exp ω θ).valᵀ) = ω := by
  rw [exp_sub_transpose_of_norm_eq_one ω hω θ, ← Vec3.hat_smul,
    Vec3.vee_hat, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) hθ), one_smul]

/-- Arccosine recovers the actual parameter on its principal interval, endpoints
included. This does not recover a unique signed axis at either endpoint. -/
theorem arccos_trace_exp_of_mem_Icc (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Real.arccos ((Matrix.trace (exp ω θ).val - 1) / 2) = θ := by
  have ht : (Matrix.trace (exp ω θ).val - 1) / 2 = Real.cos θ := by
    rw [trace_exp_of_norm_eq_one ω hω θ]
    ring
  rw [ht, Real.arccos_cos hθ₀ hθπ]

/-- At a half-turn, `R + I` is twice the unit-axis projector. This formula
retains the sign ambiguity of the axis and avoids division by `sin π`. -/
theorem exp_pi_add_one_of_norm_eq_one (ω : Vec3) (hω : ‖ω‖ = 1) :
    (exp ω Real.pi).val + 1 = (2 : ℝ) • Vec3.outer ω ω := by
  rw [exp_val, Vec3.exp_hat_of_norm_eq_one ω hω Real.pi,
    Vec3.hat_sq_of_norm_eq_one ω hω]
  simp only [Real.sin_pi, Real.cos_pi, zero_smul, add_zero]
  module

/-- MLS equation (2.17): the principal angle as a scalar in `[0, π]`. -/
noncomputable def principalAngle (R : Rotation) : ℝ :=
  Real.arccos ((Matrix.trace R.val - 1) / 2)

theorem principalAngle_mem_Icc (R : Rotation) :
    principalAngle R ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- Every rotation is the exponential of some unit axis at its actual trace-based
principal angle. This remains an existence statement at the endpoints. -/
theorem exists_unit_axis_principalAngle (R : Rotation) :
    ∃ ω : Vec3, ‖ω‖ = 1 ∧ exp ω (principalAngle R) = R := by
  obtain ⟨ω, hω, θ, hθ₀, hθπ, hR⟩ := R.exists_unit_axis_angle_le_pi
  have hangle := arccos_trace_exp_of_mem_Icc ω hω θ hθ₀ hθπ
  rw [hR] at hangle
  refine ⟨ω, hω, ?_⟩
  change exp ω (Real.arccos ((Matrix.trace R.val - 1) / 2)) = R
  rw [hangle, hR]

/-- The trace bounds used by MLS equation (2.17), for every proper rotation. -/
theorem trace_mem_Icc (R : Rotation) : Matrix.trace R.val ∈ Set.Icc (-1 : ℝ) 3 := by
  obtain ⟨ω, hω, hR⟩ := R.exists_unit_axis_principalAngle
  have ht := trace_exp_of_norm_eq_one ω hω (principalAngle R)
  rw [hR] at ht
  have hc := Real.cos_mem_Icc (principalAngle R)
  constructor <;> linarith [hc.1, hc.2]

/-- MLS equation (2.18)'s coordinate expression. It is an axis under the
nonzero-sine hypothesis below; it does not select an axis at either endpoint. -/
noncomputable def genericAxis (R : Rotation) : Vec3 :=
  (2 * Real.sin (principalAngle R))⁻¹ • Vec3.vee (R.val - R.valᵀ)

/-- For a nondegenerate principal angle, the trace/skew formula returns a unit
axis whose actual exponential reconstructs the given rotation. -/
theorem genericAxis_spec (R : Rotation) (hθ : Real.sin (principalAngle R) ≠ 0) :
    ‖genericAxis R‖ = 1 ∧ exp (genericAxis R) (principalAngle R) = R := by
  obtain ⟨ω, hω, hR⟩ := R.exists_unit_axis_principalAngle
  have haxis : genericAxis R = ω := by
    have h := axis_recovery_of_sin_ne_zero ω hω (principalAngle R) hθ
    simpa only [hR, genericAxis] using h
  rw [haxis]
  exact ⟨hω, hR⟩

/-- A rotation with principal angle `π` has a unit-axis projector even though
the generic skew-part extraction is unavailable there. -/
theorem exists_unit_axis_projector_of_principalAngle_eq_pi (R : Rotation)
    (hθ : principalAngle R = Real.pi) :
    ∃ ω : Vec3, ‖ω‖ = 1 ∧ R.val + 1 = (2 : ℝ) • Vec3.outer ω ω := by
  obtain ⟨ω, hω, hR⟩ := R.exists_unit_axis_principalAngle
  rw [hθ] at hR
  refine ⟨ω, hω, ?_⟩
  rw [← hR]
  exact exp_pi_add_one_of_norm_eq_one ω hω

end Rotation
end RoboLean
