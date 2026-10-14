import RoboLean.Grasp.PositiveSpanBounds
import RoboLean.Grasp.PlanarWrench

/-!
# Frictionless contact wrenches of a surface and exceptional surfaces

MLS Chapter 5, §4.1, printed p. 230: "Let `Λ(Σ)` denote the set of all wrenches that can be
applied to an object using frictionless point contacts:
`Λ(Σ) = { [n_{cᵢ}; p_{cᵢ} × n_{cᵢ}] : cᵢ ∈ ∂O }`, where `n_{cᵢ}` is the inward pointing unit
normal to `Σ` at the point `cᵢ`, and `p_{cᵢ}` is the contact point relative to the object frame.
A surface `Σ` is an *exceptional surface* if the convex hull of `Λ(Σ)` does not contain a
neighborhood of the origin. An object with an exceptional surface can never be grasped using
only frictionless point contacts. Examples of exceptional surfaces are the sphere in `ℝ³` and the
circle in `ℝ²`."

Model. No boundary of an object is modeled. A "surface" is any set of pairs
`(contact point, inward unit normal)` in object coordinates; nothing checks that the points form
the boundary `∂O` of an object, that the normals are unit vectors or that they point inward.
The statements below hold for every such set.

* Planar (`p = 3`): pairs in `ℝ² × ℝ²`; the wrench of a frictionless contact at `p` with normal
  `n` is `planarWrench p n = (n_x, n_y, p ⊗ n)` (p. 222, with the 2-D cross product of p. 232);
  a grasp of `k` such contacts is the `3 × k` matrix of these columns with the orthant cone of
  p. 224 (Proposition 5.3).
* Spatial (`p = 6`): pairs in `Vec3 × Vec3`; the wrench is `Wrench.pointForce p n = (n, p × n)`
  (Example 5.1, p. 220), read in its six coordinates, force first (`Wrench.coordinates`), with the
  product topology; a grasp is `ContactGrasp.spatial` of frictionless contacts whose frames have
  translation `p` and third axis `R e_z = n`.

"Contains a neighborhood of the origin" is `convexHull ℝ Λ ∈ nhds 0`. Finite-force caveat:
force-closure assumes unbounded contact forces at maintained rigid contacts (MLS p. 214).
-/

noncomputable section

open Matrix

namespace RoboLean.Grasp

/-- The kernel of a nonzero linear functional is not a neighborhood of the origin: points
`t • e` with `t ≠ 0` small and `φ e ≠ 0` lie near `0` and off the kernel. -/
private theorem ker_notMem_nhds {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSMul ℝ E] (φ : E →ₗ[ℝ] ℝ) {e : E} (he : φ e ≠ 0) :
    (LinearMap.ker φ : Set E) ∉ nhds (0 : E) := by
  intro h
  have hc : Continuous fun t : ℝ => t • e := continuous_id.smul continuous_const
  have ht := hc.tendsto' 0 0 (zero_smul ℝ e)
  obtain ⟨t, hts, ht0⟩ :=
    (((ht.eventually h).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {(0 : ℝ)}ᶜ ∈ nhdsWithin (0 : ℝ) {0}ᶜ)).exists
  have hz : φ (t • e) = 0 := hts
  rw [map_smul, smul_eq_mul] at hz
  exact mul_ne_zero ht0 he hz

/-- A set inside the kernel of a nonzero linear functional has a convex hull that is not a
neighborhood of the origin. -/
private theorem convexHull_notMem_nhds_of_subset_ker {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E] (φ : E →ₗ[ℝ] ℝ) {e : E} (he : φ e ≠ 0) {s : Set E}
    (hs : ∀ w ∈ s, φ w = 0) : convexHull ℝ s ∉ nhds (0 : E) := fun h =>
  ker_notMem_nhds φ he (Filter.mem_of_superset h (convexHull_min hs (Submodule.convex _)))

/-- The set `Λ(Σ)` of MLS printed p. 230 for a planar "surface" given as a set of pairs
`(p, n)` (contact point, inward unit normal, in object coordinates): the planar wrenches
`(n_x, n_y, p ⊗ n)` that frictionless point contacts on it can apply (p. 222). Nothing checks
that the pairs describe the boundary of an object or that the normals are inward unit
vectors. -/
def planarContactWrenches (surface : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))) : Set (Fin 3 → ℝ) :=
  (fun c => planarWrench c.1 c.2) '' surface

/-- The set `Λ(Σ)` of MLS printed p. 230 for a spatial "surface" given as a set of pairs
`(p, n)` (contact point, inward unit normal, in object coordinates): the six coordinates, force
first, of the wrenches `(n; p × n)` (`Wrench.pointForce`, Example 5.1, p. 220) that frictionless
point contacts on it can apply. Nothing checks that the pairs describe the boundary of an object
or that the normals are inward unit vectors. -/
def spatialContactWrenches (surface : Set (Vec3 × Vec3)) : Set (Fin 3 ⊕ Fin 3 → ℝ) :=
  (fun c => (Wrench.pointForce c.1 c.2).coordinates) '' surface

/-- An exceptional planar surface, MLS printed p. 230: the convex hull of `Λ(Σ)`
(`planarContactWrenches`) does not contain a neighborhood of the origin of the planar wrench
space `(f_x, f_y, τ)`. -/
def IsPlanarExceptional (surface : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))) : Prop :=
  convexHull ℝ (planarContactWrenches surface) ∉ nhds (0 : Fin 3 → ℝ)

/-- An exceptional spatial surface, MLS printed p. 230: the convex hull of `Λ(Σ)`
(`spatialContactWrenches`, six wrench coordinates, force first) does not contain a neighborhood
of the origin. -/
def IsSpatialExceptional (surface : Set (Vec3 × Vec3)) : Prop :=
  convexHull ℝ (spatialContactWrenches surface) ∉ nhds (0 : Fin 3 ⊕ Fin 3 → ℝ)

/-- The planar grasp matrix of frictionless point contacts at the pairs `c i = (pᵢ, nᵢ)`
(MLS printed pp. 224–226, planar coordinates of p. 222): column `i` is
`planarWrench pᵢ nᵢ = (n_x, n_y, p ⊗ n)`, as in Example 5.4 (p. 226). -/
def planarFrictionlessMatrix {ι : Type*} (c : ι → (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    Matrix (Fin 3) ι ℝ :=
  Matrix.of fun r i => planarWrench (c i).1 (c i).2 r

/-- A planar surface whose normal lines all pass through the object origin (`p ⊗ n = 0` for every
pair) is exceptional (MLS printed p. 230): `Λ(Σ)` lies in the plane `τ = 0`, so its convex hull
contains no neighborhood of the origin. -/
theorem isPlanarExceptional_of_cross2_eq_zero {surface : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))}
    (h : ∀ c ∈ surface, cross2 c.1 c.2 = 0) : IsPlanarExceptional surface := by
  refine convexHull_notMem_nhds_of_subset_ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)
    (e := Pi.single 2 1) (by simp) ?_
  rintro _ ⟨c, hc, rfl⟩
  simp [planarWrench, h c hc]

/-- A spatial surface whose normal lines all pass through the object origin (`p × n = 0` for
every pair) is exceptional (MLS printed p. 230): `Λ(Σ)` lies in the subspace of zero moment, so
its convex hull contains no neighborhood of the origin. -/
theorem isSpatialExceptional_of_cross_eq_zero {surface : Set (Vec3 × Vec3)}
    (h : ∀ c ∈ surface, Vec3.cross c.1 c.2 = 0) : IsSpatialExceptional surface := by
  refine convexHull_notMem_nhds_of_subset_ker
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ⊕ Fin 3 => ℝ) (Sum.inr 0))
    (e := Pi.single (Sum.inr 0) 1) (by simp) ?_
  rintro _ ⟨c, hc, rfl⟩
  simp [Wrench.coordinates, h c hc]

/-- The circle of radius `r` about the object origin with its inward normals `-c/r`, as a set of
(point, normal) pairs (MLS printed p. 230); for `r > 0` the normals are the inward unit
normals. -/
def circleSurface (r : ℝ) : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {c | c.1 0 ^ 2 + c.1 1 ^ 2 = r ^ 2 ∧ c.2 = -r⁻¹ • c.1}

/-- **MLS printed p. 230**: the circle in `ℝ²` is an exceptional surface (here the circle of
radius `r` about the object origin, inward normals `-c/r`, every `r`). -/
theorem isPlanarExceptional_circleSurface (r : ℝ) : IsPlanarExceptional (circleSurface r) := by
  refine isPlanarExceptional_of_cross2_eq_zero fun c hc => ?_
  rw [hc.2, cross2_smul_right, cross2_self, mul_zero]

/-- The sphere of radius `r` about the object origin with its inward normals `-c/r`, as a set of
(point, normal) pairs (MLS printed p. 230); for `r > 0` the normals are the inward unit
normals. -/
def sphereSurface (r : ℝ) : Set (Vec3 × Vec3) :=
  {c | ‖c.1‖ = r ∧ c.2 = -r⁻¹ • c.1}

/-- **MLS printed p. 230**: the sphere in `ℝ³` is an exceptional surface (here the sphere of
radius `r` about the object origin, inward normals `-c/r`, every `r`). -/
theorem isSpatialExceptional_sphereSurface (r : ℝ) : IsSpatialExceptional (sphereSurface r) := by
  refine isSpatialExceptional_of_cross_eq_zero fun c hc => ?_
  rw [hc.2]
  apply WithLp.ofLp_injective
  simp [Vec3.cross_coordinates, cross_self]

/-- **MLS printed p. 230**, planar: "An object with an exceptional surface can never be grasped
using only frictionless point contacts": a planar grasp of frictionless point contacts at pairs
`c i` of an exceptional surface (any finite number of contacts, possibly none) is not
force-closure. Finite-force caveat: unbounded contact forces at maintained rigid contacts
(MLS p. 214). -/
theorem not_forceClosure_of_isPlanarExceptional {surface : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))}
    (hS : IsPlanarExceptional surface) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hc : ∀ i, c i ∈ surface) :
    ¬ ForceClosure (planarFrictionlessMatrix c).mulVecLin (orthantCone ι) := by
  intro hfc
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨f, hf⟩ := hfc.surjective (Pi.single 0 1)
    rw [Subsingleton.elim f 0, map_zero] at hf
    simpa using congrFun hf 0
  · apply hS
    refine Filter.mem_of_superset ((forceClosure_mulVecLin_iff_convexHull_mem_nhds _).mp hfc)
      (convexHull_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨c i, hc i, rfl⟩

/-- **MLS printed p. 230**, spatial: "An object with an exceptional surface can never be grasped
using only frictionless point contacts": a spatial grasp of frictionless point contacts
(Example 5.1, p. 220) whose frames place each contact point `pᵢ` with inward normal
`nᵢ = R_{cᵢ} e_z` on an exceptional surface is not force-closure. Finite-force caveat: unbounded
contact forces at maintained rigid contacts (MLS p. 214). -/
theorem not_isForceClosure_of_isSpatialExceptional {surface : Set (Vec3 × Vec3)}
    (hS : IsSpatialExceptional surface) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frame : ι → RigidTransform)
    (hc : ∀ i, ((frame i).translation, (frame i).rotation.act Rotation.zAxis) ∈ surface) :
    ¬ (ContactGrasp.spatial (fun _ => ContactModel.frictionless) frame).toGrasp.IsForceClosure := by
  intro hfc
  have hp := ((spatial_frictionless_isForceClosure_iff frame).mp hfc).map_linearEquiv
    Wrench.coordinatesEquiv
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨α, -, hα⟩ := hp (Pi.single (Sum.inl 0) 1)
    simpa using congrFun hα (Sum.inl 0)
  · apply hS
    refine Filter.mem_of_superset ((positivelySpans_iff_convexHull_mem_nhds _).mp hp)
      (convexHull_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨_, hc i, rfl⟩

/-- **MLS printed pp. 230–231 with the weak bound of
`exists_finset_mem_interior_convexHull_card_le_sq`**:
a planar surface that is not exceptional admits a force-closure grasp of at most
`(3 + 1)² = 16` frictionless point contacts on it. The printed bound is `2p = 6` contacts, from
Steinitz's theorem; this statement does not prove it. Finite-force caveat: unbounded contact
forces at maintained rigid contacts (MLS p. 214). -/
theorem exists_forceClosure_card_le_sixteen_of_not_isPlanarExceptional
    {surface : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))} (hS : ¬ IsPlanarExceptional surface) :
    ∃ (k : ℕ) (c : Fin k → (Fin 2 → ℝ) × (Fin 2 → ℝ)), k ≤ 16 ∧ (∀ i, c i ∈ surface) ∧
      ForceClosure (planarFrictionlessMatrix c).mulVecLin (orthantCone (Fin k)) := by
  have h0 : (0 : Fin 3 → ℝ) ∈ interior (convexHull ℝ (planarContactWrenches surface)) :=
    mem_interior_iff_mem_nhds.mpr (not_not.mp hS)
  obtain ⟨X, hXS, hXc, hX0⟩ := exists_finset_mem_interior_convexHull_card_le_sq h0
  have hpre : ∀ x : X, ∃ d ∈ surface, planarWrench d.1 d.2 = x := fun x => hXS x.2
  choose d hd hdx using hpre
  set c : Fin X.card → (Fin 2 → ℝ) × (Fin 2 → ℝ) := fun i => d (X.equivFin.symm i)
  have hcol : ∀ i, (planarFrictionlessMatrix c).col i = X.equivFin.symm i := fun i => by
    rw [← hdx]
    rfl
  have hrange : Set.range (planarFrictionlessMatrix c).col = (X : Set (Fin 3 → ℝ)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      rw [hcol i]
      exact (X.equivFin.symm i).2
    · intro hw
      exact ⟨X.equivFin ⟨w, hw⟩, by rw [hcol, Equiv.symm_apply_apply]⟩
  have hne : Nonempty (Fin X.card) := by
    obtain ⟨x, hx⟩ := convexHull_nonempty_iff.mp ⟨0, interior_subset hX0⟩
    exact ⟨X.equivFin ⟨x, hx⟩⟩
  refine ⟨X.card, c, ?_, fun i => hd _, ?_⟩
  · rw [Module.finrank_fin_fun] at hXc
    simpa using hXc
  · rw [forceClosure_mulVecLin_iff_convexHull_mem_nhds, hrange]
    exact mem_interior_iff_mem_nhds.mp hX0

/-- **MLS printed pp. 230–231 with the weak bound of
`exists_finset_mem_interior_convexHull_card_le_sq`**:
a spatial surface that is not exceptional has at most `(6 + 1)² = 49` pairs whose frictionless
contact wrenches `(nᵢ; pᵢ × nᵢ)` positively span the wrench space, so that every spatial grasp
of frictionless point contacts with frames realizing these pairs (translation `pᵢ`, third axis
`nᵢ`) is force-closure (p. 224). The printed bound is `2p = 12` contacts, from Steinitz's
theorem; this statement does not prove it. Finite-force caveat: unbounded contact forces at
maintained rigid contacts (MLS p. 214). -/
theorem exists_positivelySpans_card_le_fortyNine_of_not_isSpatialExceptional
    {surface : Set (Vec3 × Vec3)} (hS : ¬ IsSpatialExceptional surface) :
    ∃ (k : ℕ) (c : Fin k → Vec3 × Vec3), k ≤ 49 ∧ (∀ i, c i ∈ surface) ∧
      PositivelySpans (fun i => Wrench.pointForce (c i).1 (c i).2) ∧
      ∀ frame : Fin k → RigidTransform,
        (∀ i, (frame i).translation = (c i).1 ∧ (frame i).rotation.act Rotation.zAxis = (c i).2) →
        (ContactGrasp.spatial (fun _ => ContactModel.frictionless)
          frame).toGrasp.IsForceClosure := by
  have h0 : (0 : Fin 3 ⊕ Fin 3 → ℝ) ∈ interior (convexHull ℝ (spatialContactWrenches surface)) :=
    mem_interior_iff_mem_nhds.mpr (not_not.mp hS)
  obtain ⟨X, hXS, hXc, hX0⟩ := exists_finset_mem_interior_convexHull_card_le_sq h0
  have hpre : ∀ x : X, ∃ d ∈ surface, (Wrench.pointForce d.1 d.2).coordinates = x :=
    fun x => hXS x.2
  choose d hd hdx using hpre
  set c : Fin X.card → Vec3 × Vec3 := fun i => d (X.equivFin.symm i)
  have hcol : ∀ i, (Wrench.pointForce (c i).1 (c i).2).coordinates = X.equivFin.symm i :=
    fun i => hdx _
  have hrange : Set.range (fun i => (Wrench.pointForce (c i).1 (c i).2).coordinates) =
      (X : Set (Fin 3 ⊕ Fin 3 → ℝ)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      beta_reduce
      rw [hcol i]
      exact (X.equivFin.symm i).2
    · intro hw
      exact ⟨X.equivFin ⟨w, hw⟩, by beta_reduce; rw [hcol, Equiv.symm_apply_apply]⟩
  have hne : Nonempty (Fin X.card) := by
    obtain ⟨x, hx⟩ := convexHull_nonempty_iff.mp ⟨0, interior_subset hX0⟩
    exact ⟨X.equivFin ⟨x, hx⟩⟩
  have hcoord : PositivelySpans fun i => (Wrench.pointForce (c i).1 (c i).2).coordinates := by
    rw [positivelySpans_iff_convexHull_mem_nhds, hrange]
    exact mem_interior_iff_mem_nhds.mp hX0
  have hpos : PositivelySpans fun i => Wrench.pointForce (c i).1 (c i).2 := by
    have hsymm : ∀ F : Wrench, Wrench.coordinatesEquiv.symm F.coordinates = F :=
      Wrench.coordinatesEquiv.symm_apply_apply
    simpa only [hsymm] using hcoord.map_linearEquiv Wrench.coordinatesEquiv.symm
  refine ⟨X.card, c, ?_, fun i => hd _, hpos, fun frame hf => ?_⟩
  · rw [Module.finrank_fintype_fun_eq_card] at hXc
    simpa using hXc
  · rw [spatial_frictionless_isForceClosure_iff]
    have hfr : (fun i => Wrench.pointForce (frame i).translation
        ((frame i).rotation.act Rotation.zAxis)) = fun i => Wrench.pointForce (c i).1 (c i).2 :=
      funext fun i => by rw [(hf i).1, (hf i).2]
    rw [hfr]
    exact hpos

end RoboLean.Grasp
