import RoboLean.Geometry.TwistAdjoint
import RoboLean.Geometry.TwistExp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Algebraic screw parameters of twists

MLS printed pp47–49, equations (2.42)–(2.44), with the finite branch
restricted to a nonzero angular component. The axis point below is the
perpendicular representative; it is not an arbitrary choice on the axis.

Whole-twist scaling preserves finite pitch and this point, including for
negative nonzero scalars. This does not preserve the directed axis sign.
The reconstruction identities are coordinate algebra, not a proof of the
finite screw-motion formula or Chasles' theorem.
-/

noncomputable section
open Matrix

namespace RoboLean
/-- Finite pitch, pure translation, and the explicit stationary zero-twist convention. -/
inductive ScrewPitch where
  | finite (value : ℝ)
  | infinite
  | stationary

namespace Twist

private theorem cross_self_vec (u : Vec3) : Vec3.cross u u = 0 := by
  apply WithLp.ofLp_injective
  exact _root_.cross_self (WithLp.ofLp u)

private theorem inner_cross_left (u v : Vec3) : inner ℝ u (Vec3.cross u v) = 0 := by
  rw [real_inner_comm]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change WithLp.ofLp u ⬝ᵥ crossProduct (WithLp.ofLp u) (WithLp.ofLp v) = 0
  exact dot_self_cross _ _

private theorem cross_cross_self (u v : Vec3) :
    Vec3.cross u (Vec3.cross u v) = inner ℝ u v • u - ‖u‖ ^ 2 • v := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Vec3.cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq] <;>
    ring

/-- MLS (2.42), restricted to twists with a genuine angular axis. -/
def finitePitch (ξ : Twist) (_hω : ξ.angular ≠ 0) : ℝ :=
  inner ℝ ξ.angular ξ.linear / ‖ξ.angular‖ ^ 2

/-- MLS (2.43): the perpendicular point on the axis of a rotating twist. -/
def axisPoint (ξ : Twist) (_hω : ξ.angular ≠ 0) : Vec3 :=
  (‖ξ.angular‖ ^ 2)⁻¹ • Vec3.cross ξ.angular ξ.linear

/-- The chosen finite-axis point is perpendicular to the angular direction. -/
theorem axisPoint_orthogonal (ξ : Twist) (hω : ξ.angular ≠ 0) :
    inner ℝ ξ.angular (axisPoint ξ hω) = 0 := by
  rw [axisPoint, real_inner_smul_right, inner_cross_left, mul_zero]

/-- Every rotating twist reconstructs from its finite pitch and perpendicular axis point. -/
theorem finite_reconstruction (ξ : Twist) (hω : ξ.angular ≠ 0) :
    ξ.linear = -Vec3.cross ξ.angular (axisPoint ξ hω) + finitePitch ξ hω • ξ.angular := by
  have hn : ‖ξ.angular‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hω)
  rw [axisPoint, Vec3.cross_smul, cross_cross_self]
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul,
    finitePitch, div_eq_mul_inv]
  module

/-- Algebraic twist generator for axis direction, axis point, and finite pitch.
Nonzero or unit direction is required separately for geometric interpretations. -/
def fromScrew (ω q : Vec3) (pitch : ℝ) : Twist :=
  (-Vec3.cross ω q + pitch • ω, ω)

/-- The finite parameters reconstruct the original twist, including unnormalized axes. -/
theorem fromScrew_reconstruction (ξ : Twist) (hω : ξ.angular ≠ 0) :
    fromScrew ξ.angular (axisPoint ξ hω) (finitePitch ξ hω) = ξ := by
  apply Prod.ext
  · exact (finite_reconstruction ξ hω).symm
  · rfl

/-- Moving the axis point along its direction leaves the algebraic generator unchanged. -/
theorem fromScrew_axis_shift (ω q : Vec3) (pitch r : ℝ) :
    fromScrew ω (q + r • ω) pitch = fromScrew ω q pitch := by
  simp [fromScrew, Vec3.cross_add, Vec3.cross_smul, cross_self_vec]

/-- Scaling a twist scales both components; the finite-pitch parameter is unchanged. -/
theorem fromScrew_smul (ω q : Vec3) (pitch c : ℝ) :
    c • fromScrew ω q pitch = fromScrew (c • ω) q pitch := by
  apply Prod.ext
  · simp [fromScrew, Vec3.smul_cross, smul_add, smul_neg, smul_smul, mul_comm]
  · rfl

/-- A nonzero scalar preserves the nonzero-angular domain of finite parameters. -/
theorem angular_smul_ne_zero (ξ : Twist) (hω : ξ.angular ≠ 0)
    (c : ℝ) (hc : c ≠ 0) : (c • ξ).angular ≠ 0 :=
  smul_ne_zero hc hω

/-- Whole-twist scaling by a nonzero scalar preserves finite pitch. -/
theorem finitePitch_smul (ξ : Twist) (hω : ξ.angular ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    finitePitch (c • ξ) (angular_smul_ne_zero ξ hω c hc) = finitePitch ξ hω := by
  change inner ℝ (c • ξ.angular) (c • ξ.linear) / ‖c • ξ.angular‖ ^ 2 =
    inner ℝ ξ.angular ξ.linear / ‖ξ.angular‖ ^ 2
  rw [real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp [hc, norm_ne_zero_iff.mpr hω]

/-- Whole-twist scaling preserves the perpendicular axis point, not its directed sign. -/
theorem axisPoint_smul (ξ : Twist) (hω : ξ.angular ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    axisPoint (c • ξ) (angular_smul_ne_zero ξ hω c hc) = axisPoint ξ hω := by
  change (‖c • ξ.angular‖ ^ 2)⁻¹ • Vec3.cross (c • ξ.angular) (c • ξ.linear) =
    (‖ξ.angular‖ ^ 2)⁻¹ • Vec3.cross ξ.angular ξ.linear
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Vec3.smul_cross, Vec3.cross_smul, smul_smul, smul_smul]
  congr 1
  field_simp [hc, norm_ne_zero_iff.mpr hω]

/-- Axis-point shifts also leave the actual exponential motion unchanged. -/
theorem exp_fromScrew_axis_shift (ω q : Vec3) (pitch r t : ℝ) :
    exp (fromScrew ω (q + r • ω) pitch) t = exp (fromScrew ω q pitch) t := by
  rw [fromScrew_axis_shift]

/-- MLS (2.42), with a separate stationary tag for the zero-twist degeneracy.
The source calls angular-zero twists infinite-pitch; zero has no directed
axis, so this API distinguishes it from nonzero pure translation. -/
def screwPitch (ξ : Twist) : ScrewPitch := by
  classical
  exact if hω : ξ.angular = 0 then
    if ξ.linear = 0 then .stationary else .infinite
  else .finite (finitePitch ξ hω)

@[simp] theorem screwPitch_of_angular_ne_zero (ξ : Twist) (hω : ξ.angular ≠ 0) :
    screwPitch ξ = .finite (finitePitch ξ hω) := by
  simp [screwPitch, hω]

/-- A nonzero pure translation has the infinite-pitch tag, not a finite real pitch. -/
@[simp] theorem screwPitch_pure_translation (v : Vec3) (hv : v ≠ 0) :
    screwPitch (v, 0) = .infinite := by
  simp [screwPitch, linear, angular, hv]

/-- Zero twist has no directed axis and receives its own stationary tag. -/
@[simp] theorem screwPitch_zero : screwPitch (0 : Twist) = .stationary := by
  simp [screwPitch, linear, angular]

theorem screwPitch_eq_stationary_iff (ξ : Twist) :
    screwPitch ξ = .stationary ↔ ξ = 0 := by
  classical
  rcases ξ with ⟨v, ω⟩
  by_cases hω : ω = 0 <;> by_cases hv : v = 0 <;>
    simp [screwPitch, linear, angular, hω, hv]

theorem screwPitch_eq_infinite_iff (ξ : Twist) :
    screwPitch ξ = .infinite ↔ ξ.angular = 0 ∧ ξ.linear ≠ 0 := by
  classical
  rcases ξ with ⟨v, ω⟩
  by_cases hω : ω = 0 <;> by_cases hv : v = 0 <;>
    simp [screwPitch, linear, angular, hω, hv]

/-- A nonzero whole-twist rescaling preserves the pitch classification and finite value. -/
theorem screwPitch_smul (ξ : Twist) (c : ℝ) (hc : c ≠ 0) :
    screwPitch (c • ξ) = screwPitch ξ := by
  classical
  by_cases hω : ξ.angular = 0
  · have hωc : (c • ξ).angular = 0 := by
      change c • ξ.angular = 0
      rw [hω, smul_zero]
    simp [screwPitch, hωc, hω, hc, linear]
  · rw [screwPitch_of_angular_ne_zero _ (angular_smul_ne_zero ξ hω c hc),
      screwPitch_of_angular_ne_zero ξ hω, finitePitch_smul ξ hω c hc]

/-- MLS (2.44): a nonnegative screw magnitude, not a six-coordinate Euclidean norm. -/
def screwMagnitude (ξ : Twist) : ℝ := by
  classical
  exact if ξ.angular = 0 then ‖ξ.linear‖ else ‖ξ.angular‖

@[simp] theorem screwMagnitude_of_angular_eq_zero (ξ : Twist) (hω : ξ.angular = 0) :
    screwMagnitude ξ = ‖ξ.linear‖ := by
  simp [screwMagnitude, hω]

@[simp] theorem screwMagnitude_of_angular_ne_zero (ξ : Twist) (hω : ξ.angular ≠ 0) :
    screwMagnitude ξ = ‖ξ.angular‖ := by
  simp [screwMagnitude, hω]

@[simp] theorem screwMagnitude_zero : screwMagnitude (0 : Twist) = 0 := by
  simp [screwMagnitude, linear, angular]

theorem screwMagnitude_nonneg (ξ : Twist) : 0 ≤ screwMagnitude ξ := by
  classical
  unfold screwMagnitude
  split <;> exact norm_nonneg _

theorem screwMagnitude_eq_zero_iff (ξ : Twist) : screwMagnitude ξ = 0 ↔ ξ = 0 := by
  classical
  rcases ξ with ⟨v, ω⟩
  by_cases hω : ω = 0 <;> simp [screwMagnitude, linear, angular, hω]

/-- Norm-based magnitude scales by the absolute scalar, including negative and zero scalars. -/
theorem screwMagnitude_smul (ξ : Twist) (c : ℝ) :
    screwMagnitude (c • ξ) = |c| * screwMagnitude ξ := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  by_cases hω : ξ.angular = 0
  · have hωc : (c • ξ).angular = 0 := by
      change c • ξ.angular = 0
      rw [hω, smul_zero]
    rw [screwMagnitude_of_angular_eq_zero _ hωc, screwMagnitude_of_angular_eq_zero _ hω]
    change ‖c • ξ.linear‖ = |c| * ‖ξ.linear‖
    rw [norm_smul, Real.norm_eq_abs]
  · rw [screwMagnitude_of_angular_ne_zero _ (angular_smul_ne_zero ξ hω c hc),
      screwMagnitude_of_angular_ne_zero _ hω]
    change ‖c • ξ.angular‖ = |c| * ‖ξ.angular‖
    rw [norm_smul, Real.norm_eq_abs]

/-- MLS p49: unit angular norm, or zero angular part and unit translation norm. -/
def IsUnitTwist (ξ : Twist) : Prop :=
  ‖ξ.angular‖ = 1 ∨ (ξ.angular = 0 ∧ ‖ξ.linear‖ = 1)

theorem isUnitTwist_iff_magnitude_eq_one (ξ : Twist) :
    IsUnitTwist ξ ↔ screwMagnitude ξ = 1 := by
  classical
  by_cases hω : ξ.angular = 0 <;> simp [IsUnitTwist, screwMagnitude, hω]

/-- For a unit twist the magnitude of `c • ξ` is `|c|`, not a signed rate. -/
theorem screwMagnitude_smul_of_unit (ξ : Twist) (hξ : IsUnitTwist ξ) (c : ℝ) :
    screwMagnitude (c • ξ) = |c| := by
  rw [screwMagnitude_smul, (isUnitTwist_iff_magnitude_eq_one ξ).mp hξ, mul_one]

end Twist
end RoboLean
