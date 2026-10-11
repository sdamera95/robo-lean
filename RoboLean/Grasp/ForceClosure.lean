import RoboLean.Grasp.FrictionCone

/-!
# Grasps, force-closure and internal forces

MLS Chapter 5, §§2.2–3.1, printed pp. 220–224: Definition 5.1 (representation of a grasp by a
grasp map `G` and a friction cone `FC`), Definition 5.2 (force-closure), Proposition 5.1
(force-closure iff `G(FC) = ℝ^p`), Definition 5.3 (internal and strictly internal forces) and
Proposition 5.2 (force-closure iff `G` is surjective and a strictly internal force exists).

Conventions. A grasp map is a real linear map `G : E →ₗ[ℝ] W` from contact force coefficients
(the book's `ℝ^m`, here any real vector space `E`) to object wrenches (the book's `ℝ^p`, here any
real vector space `W`: `Wrench` for spatial grasps, `Fin 3 → ℝ` for the planar grasps of
p. 222); a printed matrix `G ∈ ℝ^{p×m}` enters through `Matrix.mulVecLin`. The definitions take
an unbundled pair `(G, FC)` with `FC` any set, so that each theorem states exactly the cone
properties it uses; `Grasp` bundles a map with a `FrictionCone` (Definition 5.1) and its
`IsForceClosure` is the unbundled predicate.

Finite-force caveat (roadmap P6). Force-closure quantifies over contact forces of unbounded
magnitude in an ideal friction cone at contacts that are maintained and rigid (MLS p. 214:
rigid object, rigid-link robot, accurate models; p. 214: contact location fixed). It does not
establish that bounded actuators can produce the forces, that the contacts persist, or any
property of a physical hand.
-/

noncomputable section

open scoped Pointwise

namespace RoboLean

/-- A grasp in the sense of MLS Definition 5.1, printed p. 220: a grasp map `G : ℝ^m → ℝ^p`
(here a real linear map from contact force coefficients `E` to object wrenches `W`) and a friction
cone `FC ⊂ ℝ^m` satisfying properties 1–2 of the definition (`FrictionCone`). The set of object
wrenches the contacts can apply is `G(FC)`. Coefficients are in the contact wrench bases; a
grasp of rigid bodies with fixed, maintained contacts is assumed (MLS p. 214). -/
structure Grasp (E W : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup W] [Module ℝ W] where
  /-- The grasp map `G`, MLS eq. (5.6), printed p. 219. -/
  map : E →ₗ[ℝ] W
  /-- The friction cone `FC`, MLS printed p. 220. -/
  cone : FrictionCone E

namespace Grasp

variable {E W : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup W] [Module ℝ W]

/-- Force-closure, MLS Definition 5.2, printed p. 223: for every external wrench `F_e` on the
object there are contact forces `f_c ∈ FC` with `G f_c = -F_e`. Unbundled: `G` is any linear
grasp map and `FC` any set of contact force coefficients. Finite-force caveat: contact forces are
unbounded in magnitude and the contacts are assumed maintained and rigid (MLS p. 214); the
predicate says nothing about actuator limits or contact persistence. -/
def ForceClosure (G : E →ₗ[ℝ] W) (FC : Set E) : Prop :=
  ∀ Fe : W, ∃ fc ∈ FC, G fc = -Fe

/-- MLS Proposition 5.1, printed p. 223: a grasp is force-closure if and only if `G(FC) = ℝ^p`
(here `G '' FC = univ`). Finite-force caveat: unbounded contact forces, maintained rigid contacts
(MLS p. 214). -/
theorem forceClosure_iff_image_eq_univ (G : E →ₗ[ℝ] W) (FC : Set E) :
    ForceClosure G FC ↔ G '' FC = Set.univ := by
  constructor
  · intro h
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨f, hf, hGf⟩ := h (-w)
    exact ⟨f, hf, by rw [hGf, neg_neg]⟩
  · intro h Fe
    obtain ⟨f, hf, hGf⟩ := (h ▸ Set.mem_univ (-Fe) : -Fe ∈ G '' FC)
    exact ⟨f, hf, hGf⟩

/-- A force-closure grasp map is surjective (MLS Definition 5.2 and Proposition 5.2, printed
pp. 223–224). Finite-force caveat: unbounded contact forces, maintained rigid contacts
(MLS p. 214). -/
theorem ForceClosure.surjective {G : E →ₗ[ℝ] W} {FC : Set E} (h : ForceClosure G FC) :
    Function.Surjective G := fun w => by
  obtain ⟨f, _, hGf⟩ := h (-w)
  exact ⟨f, by rw [hGf, neg_neg]⟩

/-- Force-closure is monotone in the friction cone: enlarging `FC` keeps it (MLS Definition 5.2,
printed p. 223). Finite-force caveat: unbounded contact forces, maintained rigid contacts
(MLS p. 214). -/
theorem ForceClosure.mono {G : E →ₗ[ℝ] W} {FC FC' : Set E} (h : ForceClosure G FC)
    (hsub : FC ⊆ FC') : ForceClosure G FC' := fun Fe => by
  obtain ⟨f, hf, hGf⟩ := h Fe
  exact ⟨f, hsub hf, hGf⟩

/-- Force-closure does not depend on the coordinates of the object wrench space: composing the
grasp map with a linear equivalence `e : W ≃ W'` (for example `Wrench.coordinatesEquiv`, from
wrenches to their six coordinates) keeps it (MLS Definition 5.2, printed p. 223). Finite-force
caveat: unbounded contact forces, maintained rigid contacts (MLS p. 214). -/
theorem forceClosure_linearEquiv_comp {W' : Type*} [AddCommGroup W'] [Module ℝ W']
    (e : W ≃ₗ[ℝ] W') (G : E →ₗ[ℝ] W) (FC : Set E) :
    ForceClosure (e.toLinearMap ∘ₗ G) FC ↔ ForceClosure G FC := by
  constructor
  · intro h Fe
    obtain ⟨f, hf, hGf⟩ := h (e Fe)
    refine ⟨f, hf, e.injective ?_⟩
    simpa using hGf
  · intro h Fe
    obtain ⟨f, hf, hGf⟩ := h (e.symm Fe)
    exact ⟨f, hf, by simp [hGf]⟩

/-- Force-closure does not depend on the coordinates of the contact force space: reparametrizing
the coefficients by a linear equivalence `e : E' ≃ E` and pulling the cone back keeps it
(MLS Definition 5.2, printed p. 223). Finite-force caveat: unbounded contact forces, maintained
rigid contacts (MLS p. 214). -/
theorem forceClosure_comp_linearEquiv {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    (e : E' ≃ₗ[ℝ] E) (G : E →ₗ[ℝ] W) (FC : Set E) :
    ForceClosure (G ∘ₗ e.toLinearMap) (e ⁻¹' FC) ↔ ForceClosure G FC := by
  constructor
  · intro h Fe
    obtain ⟨f, hf, hGf⟩ := h Fe
    exact ⟨e f, hf, hGf⟩
  · intro h Fe
    obtain ⟨f, hf, hGf⟩ := h Fe
    exact ⟨e.symm f, by simpa using hf, by simpa using hGf⟩

/-- An internal force, MLS Definition 5.3, printed p. 223: `f_N ∈ N(G) ∩ FC`, contact forces in
the cone that produce no net object wrench. Unbundled. MLS Table 5.4 (printed p. 239) instead
lists "internal forces" as `f_N ∈ N(G) ∩ int(FC)`, which is Definition 5.3's *strictly* internal
force; this library follows Definition 5.3. -/
def IsInternalForce (G : E →ₗ[ℝ] W) (FC : Set E) (fN : E) : Prop :=
  G fN = 0 ∧ fN ∈ FC

section Topology

variable [TopologicalSpace E]

/-- A strictly internal force, MLS Definition 5.3, printed p. 223: `f_N ∈ N(G)` and
`f_N ∈ int(FC)`. Unbundled. This is what MLS Table 5.4 (printed p. 239) calls an internal
force. -/
def IsStrictlyInternalForce (G : E →ₗ[ℝ] W) (FC : Set E) (fN : E) : Prop :=
  G fN = 0 ∧ fN ∈ interior FC

/-- A strictly internal force is an internal force (MLS Definition 5.3, printed p. 223). -/
theorem IsStrictlyInternalForce.isInternalForce {G : E →ₗ[ℝ] W} {FC : Set E} {fN : E}
    (h : IsStrictlyInternalForce G FC fN) : IsInternalForce G FC fN :=
  ⟨h.1, interior_subset h.2⟩

/-- Adding an interior point of a set closed under addition to a point of it gives an interior
point: `int(FC) + FC ⊂ int(FC)`. This is "from the properties of a cone" in the necessity half
of the proof of MLS Proposition 5.2, printed p. 224; only closure under addition is used. -/
theorem add_mem_interior [IsTopologicalAddGroup E] (C : ConvexCone ℝ E) {x y : E}
    (hx : x ∈ interior (C : Set E)) (hy : y ∈ C) : x + y ∈ interior (C : Set E) := by
  have hopen : IsOpen ((interior (C : Set E)) + {y}) := isOpen_interior.add_right
  have hsub : (interior (C : Set E)) + {y} ⊆ C := by
    rintro _ ⟨z, hz, _, rfl, rfl⟩
    exact C.add_mem (interior_subset hz) hy
  exact interior_maximal hsub hopen ⟨x, hx, y, rfl, rfl⟩

/-- Positive scaling maps the interior of a convex cone into itself (supporting lemma for the
sufficiency half of the proof of MLS Proposition 5.2, printed p. 224, "from the properties of
the friction cone"). -/
theorem smul_mem_interior [ContinuousConstSMul ℝ E] (C : ConvexCone ℝ E) {x : E}
    (hx : x ∈ interior (C : Set E)) {t : ℝ} (ht : 0 < t) : t • x ∈ interior (C : Set E) := by
  have hopen : IsOpen (t • interior (C : Set E)) :=
    (isOpen_interior).smul₀ ht.ne'
  have hsub : t • interior (C : Set E) ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.smul_mem ht (interior_subset hz)
  exact interior_maximal hsub hopen ⟨x, hx, rfl⟩

/-- **MLS Proposition 5.2**, printed p. 224 ("Necessity of internal forces", stated and proved
there as an equivalence): a grasp is force-closure if and only if `G` is surjective and there is a
strictly internal force, `f_N ∈ N(G)` with `f_N ∈ int(FC)`.

Hypotheses, all explicit: `FC` is a convex cone (Definition 5.1, property 2) with nonempty
interior (part of property 1); the coefficient space is a real topological vector space. The
closedness of `FC` (the rest of property 1) is not used. The printed necessity proof chooses
`f₁ ∈ int(FC)` with `G f₁ ≠ 0`; that condition is not needed and not assumed (any interior point
works), so no hypothesis `p ≥ 1` enters. The printed sufficiency proof takes a limit
`(f' + α f_N)/α → f_N`; here continuity of `t ↦ f_N + t f'` at `0` gives the same `α = 1/t`.
Finite-force caveat: force-closure quantifies over unbounded contact forces at maintained rigid
contacts (MLS p. 214) and says nothing about actuator limits. -/
theorem forceClosure_iff_surjective_and_exists_isStrictlyInternalForce
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (G : E →ₗ[ℝ] W) (C : ConvexCone ℝ E)
    (hC : (interior (C : Set E)).Nonempty) :
    ForceClosure G C ↔
      Function.Surjective G ∧ ∃ fN, IsStrictlyInternalForce G C fN := by
  constructor
  · intro h
    refine ⟨h.surjective, ?_⟩
    obtain ⟨f₁, hf₁⟩ := hC
    obtain ⟨f₂, hf₂, hGf₂⟩ := h (G f₁)
    refine ⟨f₁ + f₂, ?_, add_mem_interior C hf₁ hf₂⟩
    rw [map_add, hGf₂, add_neg_cancel]
  · rintro ⟨hsurj, fN, hGfN, hfN⟩ Fe
    obtain ⟨f', hf'⟩ := hsurj (-Fe)
    -- `t ↦ f_N + t • f'` is continuous with value `f_N ∈ int(FC)` at `t = 0`
    have hcont : Continuous fun t : ℝ => fN + t • f' := by fun_prop
    have hev : ∀ᶠ t in nhds (0 : ℝ), fN + t • f' ∈ interior (C : Set E) := by
      have h0 : fN + (0 : ℝ) • f' ∈ interior (C : Set E) := by simpa using hfN
      exact hcont.continuousAt.eventually_mem (isOpen_interior.mem_nhds h0)
    have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        fN + t • f' ∈ interior (C : Set E) ∧ t ∈ Set.Ioi 0 :=
      (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨t, hti, htpos⟩ := hev'.exists
    have htpos' : 0 < t := htpos
    refine ⟨t⁻¹ • (fN + t • f'), C.smul_mem (inv_pos.mpr htpos') (interior_subset hti), ?_⟩
    rw [map_smul, map_add, map_smul, hGfN, hf', zero_add, smul_smul, inv_mul_cancel₀ htpos'.ne',
      one_smul]

end Topology

/-- A grasp (MLS Definition 5.1, printed p. 220) is force-closure, MLS Definition 5.2, printed
p. 223: `ForceClosure g.map g.cone`. Finite-force caveat: unbounded contact forces, maintained
rigid contacts (MLS p. 214). -/
def IsForceClosure [TopologicalSpace E] (g : Grasp E W) : Prop := ForceClosure g.map g.cone

/-- MLS Proposition 5.1, printed p. 223, for a grasp (Definition 5.1): force-closure if and only if
`G(FC) = ℝ^p`. Finite-force caveat: unbounded contact forces, maintained rigid contacts
(MLS p. 214). -/
theorem isForceClosure_iff_image_eq_univ [TopologicalSpace E] (g : Grasp E W) :
    g.IsForceClosure ↔ g.map '' (g.cone : Set E) = Set.univ :=
  forceClosure_iff_image_eq_univ g.map g.cone

/-- **MLS Proposition 5.2**, printed p. 224, for a grasp (Definition 5.1, printed p. 220): the
grasp is force-closure if and only if `G` is surjective and there is a strictly internal force.
The friction cone's Definition 5.1 properties supply every hypothesis of
`forceClosure_iff_surjective_and_exists_isStrictlyInternalForce`. Finite-force caveat:
unbounded contact forces, maintained rigid contacts (MLS p. 214). -/
theorem isForceClosure_iff [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (g : Grasp E W) :
    g.IsForceClosure ↔
      Function.Surjective g.map ∧ ∃ fN, IsStrictlyInternalForce g.map (g.cone : Set E) fN :=
  forceClosure_iff_surjective_and_exists_isStrictlyInternalForce g.map g.cone.toConvexCone
    g.cone.interior_nonempty

end Grasp

end RoboLean
