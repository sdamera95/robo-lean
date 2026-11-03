import RoboLean.Grasp.HandJacobian

/-!
# Fingertip locations equated with contact locations (MLS Chapter 5, Exercise 12)

MLS Chapter 5, Exercise 12, printed p. 263: "Consider the two-fingered grasp shown in Figure 5.17.
Equate the locations of the fingertips with the contact locations on the box. Differentiate this
algebraic constraint and show that it is equivalent to the answer given in the example at the end
of Section 5." The answer of that example is the grasping constraint `J_h θ̇ = Gᵀ V^b_{po}` of
eq. (5.15) (pp. 236–237, 240–242), built from the contact constraints (5.13) of each finger.

**Formalized, for every hand** (`HandGrasp`, any contact models, fingers and bases):

* the fingertip location `p_{pfᵢ}` equals the contact location `p_{pcᵢ}` exactly when the
  relative pose `g_{fᵢcᵢ}` has zero translation (`fingertipContact_translation_eq_zero_iff`);
* if the locations agree at every time, then at each time the translational part of the
  contact constraint holds: the linear part of `Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ) θ̇` equals the
  linear part of `Ad⁻¹_{g_{ocᵢ}} V^b_{po}` (`linear_adjoint_spatialJacobian_eq_of_location`);
* conversely, if that translational constraint holds at every time and the locations agree at
  one time, they agree at every time (`location_eq_of_linear_adjoint_spatialJacobian_eq`).

Reading (derivation, recorded with the statements). Equating locations is a constraint on the
translation of `g_{fᵢcᵢ}` only. Its derivative gives the three translational rows of the contact
constraint, which are all of eq. (5.13) for a point contact with friction; for the soft-finger
contacts of Figure 5.17 the fourth row (no relative rotation about the contact normal) is not a
consequence of equating locations, so "equivalent" holds for the translational rows. Twist order
`(v, ω)`; Lean joint `l` is the book's joint `l + 1`.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

namespace HandGrasp

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ}

/-- MLS Chapter 5, Exercise 12, printed p. 263: the fingertip location `p_{pfᵢ}` (palm
coordinates, finger base fixed in the palm) equals the contact location `p_{pcᵢ}` exactly when
the relative pose `g_{fᵢcᵢ}` of pp. 235–236 has zero translation. -/
theorem fingertipContact_translation_eq_zero_iff (h : HandGrasp ι m n) (i : ι)
    (θi : Fin (n i) → ℝ) (xo : RigidTransform) :
    (h.fingertipContact i θi xo).translation = 0 ↔
      (h.base i * (h.finger i).fk θi).translation = (xo * h.grasp.frame i).translation := by
  change ((h.base i * (h.finger i).fk θi)⁻¹ * (xo * h.grasp.frame i)).translation = 0 ↔ _
  rw [RigidTransform.mul_translation, RigidTransform.inv_translation, RigidTransform.inv_rotation,
    ← map_neg, ← map_add]
  constructor
  · intro h0
    have h1 := congrArg (h.base i * (h.finger i).fk θi).rotation.act h0
    rw [Rotation.act_inv_act, map_zero] at h1
    exact (add_neg_eq_zero.mp h1).symm
  · intro hAB
    rw [hAB, add_neg_cancel, map_zero]

/-- The translation column of the derivative of a pose that stays at zero translation vanishes
(supporting lemma). -/
private theorem translationDerivative_eq_zero_of_translation {g : ℝ → RigidTransform}
    {D : HomogeneousMatrix} {t : ℝ} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hg : ∀ s, (g s).translation = 0) : RigidTransform.translationDerivative D = 0 := by
  apply WithLp.ofLp_injective
  funext k
  let L := (Matrix.entryLinearMap ℝ ℝ (Sum.inl k : HomogeneousIndex)
    (Sum.inr 0 : HomogeneousIndex)).toContinuousLinearMap
  have hk := L.hasFDerivAt.comp_hasDerivAt t hD
  have hc : (L ∘ fun s => (g s).toHomogeneous) = fun _ => 0 := by
    funext s
    change (g s).toHomogeneous (Sum.inl k) (Sum.inr 0) = 0
    rw [RigidTransform.toHomogeneous_translation, hg s]
    rfl
  rw [hc] at hk
  exact hk.unique (hasDerivAt_const t 0)

/-- **MLS Chapter 5, Exercise 12, printed p. 263, the derivative of the location constraint.**
Along joint and object trajectories with actual derivatives at `t`, if the fingertip location
equals the contact location at every time, then at `t` the translational part of the contact
constraint (5.13) holds: `(Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ) θ̇)_v = (Ad⁻¹_{g_{ocᵢ}} V^b_{po})_v`. -/
theorem linear_adjoint_spatialJacobian_eq_of_location (h : HandGrasp ι m n) (i : ι)
    {θ : ℝ → Fin (n i) → ℝ} {θ' : Fin (n i) → ℝ} {xo : ℝ → RigidTransform}
    {Do : HomogeneousMatrix} {t : ℝ}
    (hθ : ∀ l, HasDerivAt (fun s => θ s l) (θ' l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t)
    (hloc : ∀ s, (h.base i * (h.finger i).fk (θ s)).translation =
      (xo s * h.grasp.frame i).translation) :
    (Twist.adjoint (h.contactFrame (xo t) i)⁻¹
        (∑ l, θ' l • (h.finger i).spatialJacobian (θ t) l)).linear =
      (Twist.adjoint (h.grasp.frame i)⁻¹ (RigidTransform.bodyVelocity xo Do t ho)).linear := by
  obtain ⟨D, hD⟩ := h.hasDerivAt_fingertipContact i hθ ho
  have hb := h.bodyVelocity_fingertipContact i hθ ho hD
  have hzero := translationDerivative_eq_zero_of_translation hD fun s =>
    (fingertipContact_translation_eq_zero_iff h i _ _).mpr (hloc s)
  have hl := congrArg Twist.linear hb
  rw [RigidTransform.bodyVelocity_linear, hzero, map_zero, Twist.sub_linear] at hl
  exact (sub_eq_zero.mp hl.symm).symm

/-- **MLS Chapter 5, Exercise 12, printed p. 263, the converse.** Along joint and object
trajectories differentiable at every time, if the translational part of the contact constraint
(5.13) holds at every time and the fingertip location equals the contact location at one time
`t₀`, then the locations agree at every time. -/
theorem location_eq_of_linear_adjoint_spatialJacobian_eq (h : HandGrasp ι m n) (i : ι)
    {θ : ℝ → Fin (n i) → ℝ} {θ' : ℝ → Fin (n i) → ℝ} {xo : ℝ → RigidTransform}
    {Do : ℝ → HomogeneousMatrix}
    (hθ : ∀ s l, HasDerivAt (fun u => θ u l) (θ' s l) s)
    (ho : ∀ s, HasDerivAt (fun u => (xo u).toHomogeneous) (Do s) s)
    (hc : ∀ s, (Twist.adjoint (h.contactFrame (xo s) i)⁻¹
        (∑ l, θ' s l • (h.finger i).spatialJacobian (θ s) l)).linear =
      (Twist.adjoint (h.grasp.frame i)⁻¹ (RigidTransform.bodyVelocity xo (Do s) s (ho s))).linear)
    (t₀ : ℝ) (h₀ : (h.base i * (h.finger i).fk (θ t₀)).translation =
      (xo t₀ * h.grasp.frame i).translation) (t : ℝ) :
    (h.base i * (h.finger i).fk (θ t)).translation = (xo t * h.grasp.frame i).translation := by
  have hex (s : ℝ) := h.hasDerivAt_fingertipContact i (hθ s) (ho s)
  let D : ℝ → HomogeneousMatrix := fun s => Classical.choose (hex s)
  have hD (s : ℝ) : HasDerivAt (fun u => (h.fingertipContact i (θ u) (xo u)).toHomogeneous)
      (D s) s := Classical.choose_spec (hex s)
  have hzero (s : ℝ) : RigidTransform.translationDerivative (D s) = 0 := by
    have hb := h.bodyVelocity_fingertipContact i (hθ s) (ho s) (hD s)
    have hl := congrArg Twist.linear hb
    rw [RigidTransform.bodyVelocity_linear, Twist.sub_linear, hc s, sub_self] at hl
    have h1 := congrArg (h.fingertipContact i (θ s) (xo s)).rotation.act hl
    rwa [Rotation.act_inv_act, map_zero] at h1
  rw [← fingertipContact_translation_eq_zero_iff]
  apply WithLp.ofLp_injective
  funext k
  let L := (Matrix.entryLinearMap ℝ ℝ (Sum.inl k : HomogeneousIndex)
    (Sum.inr 0 : HomogeneousIndex)).toContinuousLinearMap
  let f : ℝ → ℝ := fun s => (h.fingertipContact i (θ s) (xo s)).translation k
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have hk := L.hasFDerivAt.comp_hasDerivAt s (hD s)
    have h0 : L (D s) = 0 := congrArg (fun v : Vec3 => v k) (hzero s)
    exact hk.congr_deriv h0
  have hconst := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
    (fun s => (hf s).deriv) t t₀
  have h0 := (fingertipContact_translation_eq_zero_iff h i (θ t₀) (xo t₀)).mpr h₀
  change f t = 0
  rw [hconst]
  exact congrArg (fun v : Vec3 => v k) h0

end HandGrasp

end RoboLean
