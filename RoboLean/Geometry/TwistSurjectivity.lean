import RoboLean.Geometry.RotationSurjectivity
import RoboLean.Geometry.TwistExpJacobian

/-!
# Every rigid transform is an actual twist exponential

MLS Proposition 2.9, printed pp. 42–43. A unit axis and an angle in `[0,π]`
come from the rotation theorem. The positive-angle branch solves equation
(2.38) using the checked translation coefficient; the zero-angle branch is
pure translation. This is an existence result, without a unique or smooth log.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean.RigidTransform

/-- MLS Proposition 2.9 for the actual exponential, including identity,
pure translations, and rotations through `π`. -/
theorem exists_twist_exp (g : RigidTransform) :
    ∃ ξ : Twist, ∃ t : ℝ, Twist.exp ξ t = g := by
  obtain ⟨ω, hω, t, ht0, htπ, hR⟩ := g.rotation.exists_unit_axis_angle_le_pi
  by_cases hz : t = 0
  · subst t
    have hg : g.rotation = 1 := by simpa using hR.symm
    refine ⟨(g.translation, 0), 1, ?_⟩
    rw [Twist.exp_pure_translation, one_smul]
    exact RigidTransform.ext hg.symm rfl
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
    have ht2π : t < 2 * Real.pi := by linarith [Real.pi_pos]
    let A := Twist.translationJacobian ω t
    let v : Vec3 := WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp g.translation)
    refine ⟨(v, ω), t, ?_⟩
    apply RigidTransform.ext
    · exact (Twist.exp_rotation (v, ω) t).trans hR
    · rw [Twist.exp_translation_of_angular_norm_eq_one (v, ω) hω t]
      apply WithLp.ofLp_injective
      exact Twist.translationJacobian_mulVec_inv_mulVec ω hω t htpos ht2π
        (WithLp.ofLp g.translation)

/-- Every rigid transform is attained at parameter one after scaling the entire
linear/angular twist pair. No unit-twist or logarithm-selection claim is made. -/
theorem exists_twist_exp_one (g : RigidTransform) :
    ∃ ξ : Twist, Twist.exp ξ 1 = g := by
  obtain ⟨ξ, t, h⟩ := exists_twist_exp g
  refine ⟨t • ξ, ?_⟩
  simpa only [Twist.exp_smul, one_mul] using h

end RoboLean.RigidTransform
