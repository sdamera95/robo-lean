import RoboLean.Geometry.ScrewAxis
import RoboLean.Geometry.NormalizedTwist

/-!
# Screw parameters under frame changes and signed scaling

These derived bridges combine MLS printed pp47–49, equations (2.42)–(2.44),
with the adjoint frame-change formula on pp55 and 59, equations (2.58)/(2.64).
Finite pitch and screw magnitude are preserved. Finite affine axes transform
by point action. The conventionally origin-based pure-translation axis only
rotates; its affine image is generally another member of the parallel family.
No Euclidean metric on all six twist coordinates is asserted.
-/

noncomputable section
open Matrix

namespace RoboLean.Twist

private theorem inner_cross_right (u v : Vec3) : inner ℝ v (Vec3.cross u v) = 0 := by
  rw [real_inner_comm]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change WithLp.ofLp v ⬝ᵥ crossProduct (WithLp.ofLp u) (WithLp.ofLp v) = 0
  exact dot_cross_self _ _

private theorem cross_self_vec (u : Vec3) : Vec3.cross u u = 0 := by
  apply WithLp.ofLp_injective
  exact _root_.cross_self _

private theorem cross_cross_self (u v : Vec3) :
    Vec3.cross u (Vec3.cross u v) = inner ℝ u v • u - ‖u‖ ^ 2 • v := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Vec3.cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq] <;>
    ring

/-- Adjoint transformation preserves whether an angular component vanishes. -/
@[simp] theorem adjoint_angular_eq_zero_iff (g : RigidTransform) (ξ : Twist) :
    (adjoint g ξ).angular = 0 ↔ ξ.angular = 0 := by
  rw [adjoint_angular]
  constructor
  · intro h
    have hi := congrArg g.rotation⁻¹.act h
    simpa only [Rotation.inv_act_act, map_zero] using hi
  · intro h
    simp [h]

theorem adjoint_angular_ne_zero (g : RigidTransform) (ξ : Twist) (hω : ξ.angular ≠ 0) :
    (adjoint g ξ).angular ≠ 0 :=
  fun h ↦ hω ((adjoint_angular_eq_zero_iff g ξ).mp h)

@[simp] theorem adjoint_eq_zero_iff (g : RigidTransform) (ξ : Twist) :
    adjoint g ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    have hi := congrArg (adjoint g⁻¹) h
    simpa only [adjoint_inv_adjoint, adjoint_zero] using hi
  · rintro rfl
    exact adjoint_zero g

/-- Finite pitch is invariant under rigid changes of reference coordinates. -/
theorem finitePitch_adjoint (g : RigidTransform) (ξ : Twist) (hω : ξ.angular ≠ 0) :
    finitePitch (adjoint g ξ) (adjoint_angular_ne_zero g ξ hω) = finitePitch ξ hω := by
  unfold finitePitch
  rw [adjoint_angular, adjoint_linear, inner_add_right, Rotation.inner_act,
    inner_cross_right, add_zero, Rotation.norm_act]

theorem screwMagnitude_adjoint (g : RigidTransform) (ξ : Twist) :
    screwMagnitude (adjoint g ξ) = screwMagnitude ξ := by
  classical
  by_cases hω : ξ.angular = 0
  · have hω' := (adjoint_angular_eq_zero_iff g ξ).mpr hω
    rw [screwMagnitude_of_angular_eq_zero _ hω', screwMagnitude_of_angular_eq_zero _ hω,
      adjoint_linear, hω, map_zero, Vec3.cross_zero, add_zero, Rotation.norm_act]
  · rw [screwMagnitude_of_angular_ne_zero _ (adjoint_angular_ne_zero g ξ hω),
      screwMagnitude_of_angular_ne_zero _ hω, adjoint_angular, Rotation.norm_act]

theorem screwPitch_adjoint (g : RigidTransform) (ξ : Twist) :
    screwPitch (adjoint g ξ) = screwPitch ξ := by
  classical
  by_cases hω : ξ.angular = 0
  · by_cases hξ : ξ = 0
    · simp [hξ]
    have hv : ξ.linear ≠ 0 := fun h ↦ hξ (Twist.ext h hω)
    have hω' := (adjoint_angular_eq_zero_iff g ξ).mpr hω
    have hξ' : adjoint g ξ ≠ 0 := fun h ↦ hξ ((adjoint_eq_zero_iff g ξ).mp h)
    have hv' : (adjoint g ξ).linear ≠ 0 := fun h ↦ hξ' (Twist.ext h hω')
    rw [(screwPitch_eq_infinite_iff _).mpr ⟨hω', hv'⟩,
      (screwPitch_eq_infinite_iff _).mpr ⟨hω, hv⟩]
  · rw [screwPitch_of_angular_ne_zero _ (adjoint_angular_ne_zero g ξ hω),
      screwPitch_of_angular_ne_zero ξ hω, finitePitch_adjoint g ξ hω]

/-- The axis direction rotates; its sign is not replaced by an arbitrary orientation convention. -/
theorem axisDirection_adjoint (g : RigidTransform) (ξ : Twist) :
    axisDirection (adjoint g ξ) = g.applyVector (axisDirection ξ) := by
  classical
  by_cases hω : ξ.angular = 0
  · simp [axisDirection, hω, adjoint_linear, RigidTransform.applyVector]
  · have hRω : g.rotation.act ξ.angular ≠ 0 := adjoint_angular_ne_zero g ξ hω
    simp [axisDirection, hRω, hω, adjoint_angular, RigidTransform.applyVector]

/-- Magnitude normalization commutes with the adjoint, without asserting a six-dimensional norm. -/
theorem normalized_adjoint (g : RigidTransform) (ξ : Twist) :
    normalized (adjoint g ξ) = adjoint g (normalized ξ) := by
  rw [normalized, screwMagnitude_adjoint, normalized, adjoint_smul]

/-- Both the point and the direction in the screw generator follow the correct rigid actions. -/
theorem adjoint_fromScrew (g : RigidTransform) (ω q : Vec3) (pitch : ℝ) :
    adjoint g (fromScrew ω q pitch) =
      fromScrew (g.applyVector ω) (g.applyPoint q) pitch := by
  apply Twist.ext
  · change g.rotation.act (-Vec3.cross ω q + pitch • ω) +
      Vec3.cross g.translation (g.rotation.act ω) =
      -Vec3.cross (g.rotation.act ω) (g.rotation.act q + g.translation) +
        pitch • g.rotation.act ω
    rw [map_add, map_neg, map_smul, Rotation.act_cross, Vec3.cross_add,
      Vec3.cross_anticomm (g.rotation.act ω) g.translation]
    module
  · rfl

/-- The chosen perpendicular point removes exactly the component of an arbitrary axis point
parallel to the direction. -/
theorem axisPoint_fromScrew (ω q : Vec3) (pitch : ℝ) (hω : ω ≠ 0) :
    axisPoint (fromScrew ω q pitch) hω = q -
      (inner ℝ ω q / ‖ω‖ ^ 2) • ω := by
  have hn : ‖ω‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hω)
  change (‖ω‖ ^ 2)⁻¹ • Vec3.cross ω (-Vec3.cross ω q + pitch • ω) = _
  rw [Vec3.cross_add, Vec3.cross_neg, Vec3.cross_smul, cross_self_vec,
    smul_zero, add_zero, cross_cross_self]
  simp only [neg_sub, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul, div_eq_mul_inv]
  module

theorem finiteAxis_fromScrew (ω q : Vec3) (pitch : ℝ) (hω : ω ≠ 0) :
    finiteAxis (fromScrew ω q pitch) hω = axisLine q ω := by
  change axisLine (axisPoint (fromScrew ω q pitch) hω) ω = _
  rw [axisPoint_fromScrew]
  simpa only [sub_eq_add_neg, neg_smul] using
    axisLine_shift q ω (-(inner ℝ ω q / ‖ω‖ ^ 2))

private theorem finiteAxis_congr {ξ η : Twist} (h : ξ = η)
    (hξ : ξ.angular ≠ 0) (hη : η.angular ≠ 0) : finiteAxis ξ hξ = finiteAxis η hη := by
  subst η
  rfl

/-- A rotating twist's entire affine axis follows rigid point action. -/
theorem finiteAxis_adjoint (g : RigidTransform) (ξ : Twist) (hω : ξ.angular ≠ 0) :
    g.applyPoint '' (finiteAxis ξ hω : Set Vec3) =
      (finiteAxis (adjoint g ξ) (adjoint_angular_ne_zero g ξ hω) : Set Vec3) := by
  have hω' : g.applyVector ξ.angular ≠ 0 := adjoint_angular_ne_zero g ξ hω
  have hg := adjoint_fromScrew g ξ.angular (axisPoint ξ hω) (finitePitch ξ hω)
  rw [fromScrew_reconstruction ξ hω] at hg
  have ha := (finiteAxis_congr hg (adjoint_angular_ne_zero g ξ hω) hω').trans
    (finiteAxis_fromScrew _ _ _ hω')
  change g.applyPoint '' (axisLine (axisPoint ξ hω) ξ.angular : Set Vec3) = _
  rw [RigidTransform.image_axisLine]
  exact congrArg (fun L : AffineSubspace ℝ Vec3 ↦ (L : Set Vec3)) ha.symm

/-- The conventional origin axis of pure translation rotates; it is not generally the
full affine image of the old origin axis. -/
theorem screwAxis_adjoint_pure_translation (g : RigidTransform) (v : Vec3) (hv : v ≠ 0) :
    screwAxis (adjoint g ⟨v, 0⟩) = some (axisLine 0 (g.applyVector v)) := by
  have hgv : g.applyVector v ≠ 0 := by
    intro h
    have hi := congrArg g.rotation⁻¹.act h
    exact hv (by simpa only [RigidTransform.applyVector, Rotation.inv_act_act, map_zero] using hi)
  have he : adjoint g ⟨v, 0⟩ = ⟨g.applyVector v, 0⟩ := by
    simp [adjoint, RigidTransform.applyVector]
  rw [he, screwAxis_pure_translation _ hgv]
  rfl

/-- Whole-twist scaling scales the directed vector, including negative and zero scalars. -/
theorem axisDirection_smul (ξ : Twist) (c : ℝ) : axisDirection (c • ξ) = c • axisDirection ξ := by
  classical
  by_cases hc : c = 0
  · simp [hc, axisDirection]
  by_cases hω : ξ.angular = 0
  · have hωc : (c • ξ).angular = 0 := by
      change c • ξ.angular = 0
      rw [hω, smul_zero]
    simp [axisDirection, hω, hωc]
  · simp [axisDirection, hω, hc]

@[simp] theorem axisDirection_neg (ξ : Twist) : axisDirection (-ξ) = -axisDirection ξ := by
  simpa only [neg_one_smul] using axisDirection_smul ξ (-1)

/-- Negative scaling reverses the normalized directed vector. -/
theorem normalized_axisDirection_smul_of_neg (ξ : Twist) (c : ℝ) (hc : c < 0) :
    axisDirection (normalized (c • ξ)) = -axisDirection (normalized ξ) := by
  rw [normalized_smul_of_neg ξ c hc, axisDirection_neg]

end RoboLean.Twist
