import RoboLean.Geometry.TwistScrewMotion
import RoboLean.Geometry.TwistSurjectivity

/-!
# Chasles existence for proper rigid displacements

MLS Theorem 2.11, printed p. 49. The geometric point-action predicate below
is independent of the twist exponential. Its existence theorem uses the
checked exponential surjectivity and screw-motion agreement, separating
stationary, pure-translation, and finite-pitch cases. No axis uniqueness,
smooth logarithm, or equivalence of whole trajectories is claimed.
-/

noncomputable section

namespace RoboLean.RigidTransform

/-- Every proper rigid transform has independent geometric screw-motion data. -/
theorem exists_screw_motion (g : RigidTransform) :
    ∃ S : ScrewMotion, S.toRigidTransform = g := by
  obtain ⟨⟨v, ω⟩, hExp⟩ := exists_twist_exp_one g
  by_cases hω : ω = 0
  · subst ω
    by_cases hv : v = 0
    · subst v
      refine ⟨.stationary, ?_⟩
      change (⟨1, 0⟩ : RigidTransform) = g
      simpa only [Twist.exp_pure_translation, smul_zero] using hExp
    · have hd : ‖‖v‖⁻¹ • v‖ = 1 := by
        simpa only [NormedSpace.normalize] using NormedSpace.norm_normalize hv
      refine ⟨.translation (‖v‖⁻¹ • v) ‖v‖ hd, ?_⟩
      change (⟨1, ‖v‖ • (‖v‖⁻¹ • v)⟩ : RigidTransform) = g
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
      simpa only [Twist.exp_pure_translation, one_smul] using hExp
  · let η : Twist := ‖ω‖⁻¹ • (⟨v, ω⟩ : Twist)
    have hη : ‖η.angular‖ = 1 := Twist.angular_norm_normalize ⟨v, ω⟩ hω
    have hη0 : η.angular ≠ 0 := by
      intro h
      simp [h] at hη
    refine ⟨.finite η.angular (Twist.axisPoint η hη0)
      (Twist.finitePitch η hη0) ‖ω‖ hη, ?_⟩
    rw [← ScrewMotion.exp_generator]
    change Twist.exp (Twist.fromScrew η.angular (Twist.axisPoint η hη0)
      (Twist.finitePitch η hη0)) ‖ω‖ = g
    rw [Twist.fromScrew_reconstruction η hη0]
    have hn := Twist.exp_normalize_angular ⟨v, ω⟩ hω 1
    simpa only [mul_one] using hn.symm.trans hExp

/-- Independent geometric meaning of a screw displacement: either pure
translation, or rotation about a unit directed axis followed by parallel
translation. The formula is a predicate on the action of `g`, not a definition
of its exponential representation. -/
def IsScrewDisplacement (g : RigidTransform) : Prop :=
  (∃ d : Vec3, ∀ x : Vec3, g.applyPoint x = x + d) ∨
    ∃ ω q : Vec3, ∃ pitch t : ℝ, ‖ω‖ = 1 ∧
      ∀ x : Vec3, g.applyPoint x =
        (Rotation.exp ω t).act (x - q) + q + (pitch * t) • ω

/-- Chasles' theorem for every proper rigid displacement, with pure translation
and identity included explicitly by the left branch. -/
theorem isScrewDisplacement (g : RigidTransform) : IsScrewDisplacement g := by
  obtain ⟨S, rfl⟩ := exists_screw_motion g
  cases S with
  | finite ω q pitch t hω =>
      refine Or.inr ⟨ω, q, pitch, t, hω, ?_⟩
      intro x
      simp only [ScrewMotion.toRigidTransform, RigidTransform.applyPoint, map_sub]
      module
  | translation v t hv =>
      refine Or.inl ⟨t • v, ?_⟩
      intro x
      simp [ScrewMotion.toRigidTransform, RigidTransform.applyPoint]
  | stationary =>
      refine Or.inl ⟨0, ?_⟩
      intro x
      simp [ScrewMotion.toRigidTransform]

end RoboLean.RigidTransform
