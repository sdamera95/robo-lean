import RoboLean.Geometry.WrenchScrew
import RoboLean.Geometry.TwistScrewInvariants

/-!
# Wrench screw coordinates under frame conversion

Derived from MLS printed pp. 62–66: the wrench transfer includes the moment
origin shift; finite pitch, norm-based screw magnitude, and the finite affine
axis describe the same screw in another frame. The proof explicitly intertwines
wrench transfer with twist adjoint after swapping `(f, τ)` to `(τ, f)`.

The pure-couple axis convention in equation (2.70) chooses a line through the
coordinate origin. It therefore rotates under a frame change; its full affine
image is that canonical line only when the translation lies in the rotated
moment direction. Zero retains its absent axis. No invariance of a mixed
six-coordinate Euclidean norm or physical contact model is asserted.
-/

noncomputable section

namespace RoboLean
namespace Wrench

/-- Explicit force/moment swap intertwines actual wrench transfer and twist adjoint
(MLS printed p. 62, equation (2.66), and the swap of printed pp. 64 and 67). -/
theorem toTwist_transform (g : RigidTransform) (F : Wrench) :
    toTwist (transform g F) = Twist.adjoint g (toTwist F) := by
  apply Twist.ext
  · change Vec3.cross g.translation (g.rotation.act F.force) + g.rotation.act F.torque =
      g.rotation.act F.torque + Vec3.cross g.translation (g.rotation.act F.force)
    exact add_comm _ _
  · rfl

/-- Wrench transfer has zero force exactly when the original force is zero
(MLS printed p. 62, equation (2.66)). -/
theorem transform_force_eq_zero_iff (g : RigidTransform) (F : Wrench) :
    (transform g F).force = 0 ↔ F.force = 0 := by
  constructor
  · intro h
    have hi := congrArg g.rotation⁻¹.act h
    simpa only [transform_force, Rotation.inv_act_act, map_zero] using hi
  · intro h
    simp only [transform_force, h, map_zero]

/-- Wrench transfer keeps a nonzero force nonzero (MLS printed p. 62, equation (2.66)). -/
theorem force_ne_zero_transform (g : RigidTransform) (F : Wrench) (hf : F.force ≠ 0) :
    (transform g F).force ≠ 0 :=
  fun h => hf ((transform_force_eq_zero_iff g F).mp h)

/-- Wrench transfer sends only the zero wrench to zero (MLS printed p. 62,
equation (2.65)). -/
theorem transform_eq_zero_iff (g : RigidTransform) (F : Wrench) :
    transform g F = 0 ↔ F = 0 := by
  constructor
  · intro h
    have hi := congrArg (transform g⁻¹) h
    simpa only [transform_inv_transform, transform_zero] using hi
  · rintro rfl
    exact transform_zero g

/-- Finite pitch is invariant under a change of wrench frame and moment origin
(MLS printed pp. 62 and 65, equations (2.66) and (2.69)). -/
theorem finitePitch_transform (g : RigidTransform) (F : Wrench) (hf : F.force ≠ 0) :
    finitePitch (transform g F) (force_ne_zero_transform g F hf) = finitePitch F hf := by
  simpa only [finitePitch, toTwist_transform] using
    Twist.finitePitch_adjoint g (toTwist F) hf

/-- Pitch classification is frame invariant, including finite force, nonzero pure
couple, and zero cases (MLS printed pp. 62 and 65). -/
theorem screwPitch_transform (g : RigidTransform) (F : Wrench) :
    screwPitch (transform g F) = screwPitch F := by
  unfold screwPitch
  rw [toTwist_transform, Twist.screwPitch_adjoint]

/-- The source's branch-dependent magnitude is frame invariant, including zero
(MLS printed pp. 62 and 66, equations (2.66) and (2.71)). -/
theorem screwMagnitude_transform (g : RigidTransform) (F : Wrench) :
    screwMagnitude (transform g F) = screwMagnitude F := by
  unfold screwMagnitude
  rw [toTwist_transform, Twist.screwMagnitude_adjoint]

/-- The normalized finite-force direction rotates with the coordinate frame
(MLS printed pp. 62 and 65). -/
theorem forceDirection_transform (g : RigidTransform) (F : Wrench) (hf : F.force ≠ 0) :
    forceDirection (transform g F) (force_ne_zero_transform g F hf) =
      g.applyVector (forceDirection F hf) := by
  simp [forceDirection, RigidTransform.applyVector, Rotation.norm_act, map_smul]

/-- The actual finite wrench axis equals the finite axis of the swapped twist
(MLS printed p. 65, equation (2.70)). -/
theorem finiteAxis_eq_twist (F : Wrench) (hf : F.force ≠ 0) :
    finiteAxis F hf = Twist.finiteAxis (toTwist F) hf := rfl

/-- A nonzero-force affine axis transforms by the full rigid point action
(MLS printed pp. 62 and 65). -/
theorem finiteAxis_transform (g : RigidTransform) (F : Wrench) (hf : F.force ≠ 0) :
    g.applyPoint '' (finiteAxis F hf : Set Vec3) =
      (finiteAxis (transform g F) (force_ne_zero_transform g F hf) : Set Vec3) := by
  simpa only [finiteAxis_eq_twist, toTwist_transform] using
    Twist.finiteAxis_adjoint g (toTwist F) hf

/-- Pure-couple torque rotates and is unaffected by a change of origin
(MLS printed p. 62, equation (2.66), with zero force). -/
theorem transform_torque_of_force_eq_zero (g : RigidTransform) (F : Wrench)
    (hf : F.force = 0) : (transform g F).torque = g.rotation.act F.torque := by
  simp only [transform_torque, hf, map_zero, Vec3.cross_zero, zero_add]

/-- A nonzero pure couple stays nonzero under wrench transfer (MLS printed p. 62,
equation (2.66)). -/
theorem torque_ne_zero_transform (g : RigidTransform) (F : Wrench)
    (hf : F.force = 0) (hτ : F.torque ≠ 0) : (transform g F).torque ≠ 0 := by
  rw [transform_torque_of_force_eq_zero g F hf]
  intro h
  have hi := congrArg g.rotation⁻¹.act h
  exact hτ (by simpa only [Rotation.inv_act_act, map_zero] using hi)

/-- The normalized nonzero pure-couple direction rotates (MLS printed pp. 62 and 65). -/
theorem coupleDirection_transform (g : RigidTransform) (F : Wrench)
    (hf : F.force = 0) (hτ : F.torque ≠ 0) :
    coupleDirection (transform g F) (torque_ne_zero_transform g F hf hτ) =
      g.applyVector (coupleDirection F hτ) := by
  simp only [coupleDirection, transform_torque_of_force_eq_zero g F hf,
    Rotation.norm_act, RigidTransform.applyVector, map_smul]

/-- The source's origin-based pure-couple axis transforms by rotation alone
(MLS printed p. 65, equation (2.70), second branch). -/
theorem coupleAxis_transform_vector (g : RigidTransform) (F : Wrench)
    (hf : F.force = 0) (hτ : F.torque ≠ 0) :
    g.applyVector '' (coupleAxis F hf hτ : Set Vec3) =
      (coupleAxis (transform g F) ((transform_force_eq_zero_iff g F).mpr hf)
        (torque_ne_zero_transform g F hf hτ) : Set Vec3) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (mem_coupleAxis F hf hτ y).mp hy
    apply (mem_coupleAxis _ _ _ _).mpr
    refine ⟨r, ?_⟩
    simp only [RigidTransform.applyVector, map_smul,
      transform_torque_of_force_eq_zero g F hf]
  · intro hx
    obtain ⟨r, hr⟩ := (mem_coupleAxis _ _ _ x).mp hx
    refine ⟨r • F.torque, (mem_coupleAxis F hf hτ _).mpr ⟨r, rfl⟩, ?_⟩
    simpa only [RigidTransform.applyVector, map_smul,
      transform_torque_of_force_eq_zero g F hf] using hr.symm

/-- The affine image equals the canonical pure-couple axis when the translated
origin lies on its rotated line; the translation premise is essential
(MLS printed p. 65, equation (2.70), second branch). -/
theorem coupleAxis_transform_point_of_translation_mem (g : RigidTransform) (F : Wrench)
    (hf : F.force = 0) (hτ : F.torque ≠ 0)
    (hp : g.translation ∈ Submodule.span ℝ {g.rotation.act F.torque}) :
    g.applyPoint '' (coupleAxis F hf hτ : Set Vec3) =
      (coupleAxis (transform g F) ((transform_force_eq_zero_iff g F).mpr hf)
        (torque_ne_zero_transform g F hf hτ) : Set Vec3) := by
  change g.applyPoint '' (axisLine 0 F.torque : Set Vec3) =
    (axisLine 0 (transform g F).torque : Set Vec3)
  rw [RigidTransform.image_axisLine, transform_torque_of_force_eq_zero g F hf]
  have hp' : g.translation ∈ axisLine 0 (g.rotation.act F.torque) := by
    simpa only [axisLine, AffineSubspace.mem_mk', vsub_eq_sub, sub_zero] using hp
  have heq := (axisLine_eq_iff_mem 0 g.translation (g.rotation.act F.torque)).mpr hp'
  simpa only [RigidTransform.applyPoint, map_zero, zero_add, RigidTransform.applyVector] using
    congrArg (fun A : AffineSubspace ℝ Vec3 => (A : Set Vec3)) heq

/-- Zero alone retains the absent-axis branch after any wrench frame conversion
(an explicit extension of MLS printed p. 65). -/
theorem screwAxis_transform_eq_none_iff (g : RigidTransform) (F : Wrench) :
    screwAxis (transform g F) = none ↔ F = 0 := by
  rw [screwAxis_eq_none_iff, transform_eq_zero_iff]

end Wrench
end RoboLean
