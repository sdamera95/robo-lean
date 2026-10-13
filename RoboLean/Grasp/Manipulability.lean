import RoboLean.Grasp.HandJacobian

/-!
# Multifingered grasps: manipulability, internal motions, joint torques and prehensile grasps

MLS Chapter 5, §5.2, printed pp. 237–240 (Definitions 5.4–5.5, Proposition 5.8, eq. (5.16),
Table 5.4 and the claims of p. 239), the summary item 6 of p. 257, and Exercise 6, printed
pp. 260–261.

Representation.

* `Grasp.Manipulable J Gt` is Definition 5.5 for any linear maps `J : Θ → E` (the hand Jacobian)
  and `Gt : V → E` (the transpose of the grasp map): every object motion `v` is matched by joint
  rates `θ̇` with `J θ̇ = Gt v`. Proposition 5.8 (`Grasp.manipulable_iff_range_le`) holds at this
  generality.
* `MultifingeredGrasp Θ ι m` is Definition 5.4 at one configuration `(θ, x_o)`: a hand Jacobian
  `J_h : Θ → ℝᵐ` from any real joint-rate space `Θ` (the book's `ℝⁿ`) to the contact coefficients
  `(i : ι) → Fin (m i) → ℝ`, and a spatial grasp (`SpatialGrasp`), which supplies `G` (eq. (5.6)),
  `Gᵀ` (eq. (5.13), `SpatialGrasp.graspTranspose`) and `FC` (the product cone, Definition 5.1).
  `HandGrasp.toMultifingeredGrasp` is the one of a hand with fingers (eq. (5.14)).
* The joint torques of eq. (5.16), `τ = J_hᵀ f_c`, are `MultifingeredGrasp.torque f_c`, the linear
  form `θ̇ ↦ f_c · (J_h θ̇)` on joint rates: the joint force that does the same instantaneous work
  as the contact forces. For a hand it has the components `HandGrasp.handTorque`
  (`HandGrasp.torque_toMultifingeredGrasp`). The work premise of p. 238 is not formalized.

Table 5.4 (printed p. 239), row by row: force-closure `G(FC) = ℝᵖ` is
`Grasp.isForceClosure_iff_image_eq_univ` (E025); manipulable `R(Gᵀ) ⊂ R(J_h)` is
`MultifingeredGrasp.isManipulable_iff_range_le`; "internal forces `f_N ∈ N(G) ∩ int(FC)`" is
E025's `Grasp.IsStrictlyInternalForce` (Definition 5.3's *strictly* internal force; the library
keeps Definition 5.3's names); internal motions `θ̇_N ∈ N(J_h)` is
`MultifingeredGrasp.IsInternalMotion`. The row "structural forces, `G⁺ F_I ∈ N(J_hᵀ)`" uses a `G⁺`
that the book does not define and is not formalized; the text's "structurally dependent forces",
contact forces in `N(J_hᵀ)` (p. 239), are `MultifingeredGrasp.IsStructurallyDependentForce`.

Source observation, summary item 6 (printed p. 257, "A force-closure grasp is manipulable if and
only if `J_h` is surjective") against p. 239 ("If the grasp is manipulable and force-closure, then
it follows that `J_h` is surjective onto the range of `Gᵀ`"). Formal findings:
(a) the "if" direction holds for every multifingered grasp, without force-closure
(`MultifingeredGrasp.IsManipulable.of_surjective`);
(b) the "only if" direction fails for a multifingered grasp in the generality of Definition 5.4
(a force-closure, manipulable grasp whose `J_h` is not surjective:
`Examples.summaryItem6_counterexample`, the soft-finger box grasp of Example 5.2 with `J_h = Gᵀ`);
(c) for the hand Jacobian of a hand (eq. (5.14), block diagonal) whose contact constraint maps
`B_{cᵢ}ᵀ` are surjective, as for every contact model of Table 5.2, manipulability is equivalent to
the surjectivity of `J_h`, with or without force-closure (`HandGrasp.isManipulable_iff_surjective`).
So item 6 holds for the hands of §5 and its force-closure premise is not needed there, while
p. 239's weaker sentence holds for every multifingered grasp (`surjOn_range_graspTranspose`).

Exercise 6 (printed pp. 260–261): a grasp is prehensile if every object wrench is `G f_c` with
`f_c ∈ int(FC)`; the exercise shows `G(FC) = ℝᵖ ⟹ G(int(FC)) = G(FC)` through its steps (a)–(d),
and concludes "a grasp is prehensile if and only if the grasp is force-closure"
(`Grasp.image_interior_eq_image_of_image_eq_univ`, `Grasp.prehensile_iff_forceClosure`). Only the
convex-cone structure of `FC` and a nonempty interior are used; closedness is not.

Finite-force and maintained-contact caveat (E025): force-closure, manipulability and
prehensility quantify over unbounded contact forces and arbitrary joint rates at maintained,
rigid, fixed contacts (MLS p. 214, p. 234); none of them concerns actuator limits, contact
persistence or a physical hand.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Grasp

section Manipulable

variable {Θ E V : Type*} [AddCommGroup Θ] [Module ℝ Θ] [AddCommGroup E] [Module ℝ E]
  [AddCommGroup V] [Module ℝ V]

/-- Manipulability, MLS Definition 5.5, printed p. 237, unbundled: for every object motion `v`
there are joint rates `θ̇` with `J θ̇ = Gt v`, the grasping constraint (5.15) with `J = J_h(θ, x_o)`
and `Gt = Gᵀ`. Joint rates are unbounded; the contacts are assumed maintained (MLS p. 234). -/
def Manipulable (J : Θ →ₗ[ℝ] E) (Gt : V →ₗ[ℝ] E) : Prop :=
  ∀ v, ∃ θ', J θ' = Gt v

/-- **MLS Proposition 5.8**, printed p. 238, unbundled: a grasp is manipulable if and only if
`R(Gᵀ) ⊂ R(J_h)`. -/
theorem manipulable_iff_range_le (J : Θ →ₗ[ℝ] E) (Gt : V →ₗ[ℝ] E) :
    Manipulable J Gt ↔ LinearMap.range Gt ≤ LinearMap.range J := by
  constructor
  · rintro h _ ⟨v, rfl⟩
    obtain ⟨θ', hθ'⟩ := h v
    exact ⟨θ', hθ'⟩
  · intro h v
    exact h ⟨v, rfl⟩

/-- A surjective hand Jacobian gives a manipulable grasp (MLS Definition 5.5, printed p. 237; the
"if" direction of the summary item 6, printed p. 257, without its force-closure premise). -/
theorem Manipulable.of_surjective {J : Θ →ₗ[ℝ] E} (Gt : V →ₗ[ℝ] E)
    (hJ : Function.Surjective J) : Manipulable J Gt :=
  fun v => hJ (Gt v)

end Manipulable

/-! ### Exercise 6: prehensile grasps -/

section Prehensile

variable {E W : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace E]

/-- A prehensile grasp, MLS Exercise 6, printed p. 260: "for any `F_o`, there exists `f_c` such that
`F_o = G f_c` and `f_c ∈ int(FC)`" (desired contact forces strictly inside the friction cone).
Unbundled: `G` any linear grasp map, `FC` any set. Finite-force caveat: contact forces are
unbounded and the contacts maintained and rigid (MLS p. 214). -/
def Prehensile (G : E →ₗ[ℝ] W) (FC : Set E) : Prop :=
  ∀ Fo, ∃ fc, Fo = G fc ∧ fc ∈ interior FC

/-- MLS Exercise 6, step (c), printed p. 261: if `G(FC) = ℝᵖ`, there is `f_N ∈ int(FC)` with
`G f_N = 0` (a strictly internal force, Definition 5.3), for `FC` a convex cone with nonempty
interior; this is the necessity half of Proposition 5.2. -/
theorem exists_isStrictlyInternalForce_of_image_eq_univ [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {G : E →ₗ[ℝ] W} {C : ConvexCone ℝ E}
    (hC : (interior (C : Set E)).Nonempty) (h : G '' (C : Set E) = Set.univ) :
    ∃ fN, IsStrictlyInternalForce G C fN :=
  ((forceClosure_iff_surjective_and_exists_isStrictlyInternalForce G C hC).mp
    ((forceClosure_iff_image_eq_univ G C).mpr h)).2

/-- **MLS Exercise 6, printed pp. 260–261, as printed**: if `G(FC) = ℝᵖ` then
`G(int(FC)) = G(FC)`. Hypotheses: `FC` a convex cone (Definition 5.1, property 2; steps (a) and
(b) are `Grasp.smul_mem_interior` and `Grasp.add_mem_interior`) with nonempty interior (part of
property 1) in a real topological vector space; closedness is not used. Step (c) is
`exists_isStrictlyInternalForce_of_image_eq_univ`; step (d), `G(FC) ⊂ G(int(FC))`, adds the
strictly internal force `f_N` to any `f ∈ FC`. -/
theorem image_interior_eq_image_of_image_eq_univ [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {G : E →ₗ[ℝ] W} {C : ConvexCone ℝ E} (hC : (interior (C : Set E)).Nonempty)
    (h : G '' (C : Set E) = Set.univ) :
    G '' interior (C : Set E) = G '' (C : Set E) := by
  refine (Set.image_mono interior_subset).antisymm ?_
  obtain ⟨fN, hGfN, hfN⟩ := exists_isStrictlyInternalForce_of_image_eq_univ hC h
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨fN + f, add_mem_interior C hfN hf, by rw [map_add, hGfN, zero_add]⟩

/-- **MLS Exercise 6, conclusion**, printed p. 261: "a grasp is prehensile if and only if the grasp
is force-closure", for `FC` a convex cone with nonempty interior (Definition 5.1; closedness not
used). Finite-force caveat: unbounded contact forces at maintained rigid contacts
(MLS p. 214). -/
theorem prehensile_iff_forceClosure [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (G : E →ₗ[ℝ] W) (C : ConvexCone ℝ E) (hC : (interior (C : Set E)).Nonempty) :
    Prehensile G C ↔ ForceClosure G C := by
  constructor
  · intro h Fe
    obtain ⟨fc, hfc, hint⟩ := h (-Fe)
    exact ⟨fc, interior_subset hint, hfc.symm⟩
  · intro h Fo
    have himage := (forceClosure_iff_image_eq_univ G C).mp h
    have hint := image_interior_eq_image_of_image_eq_univ hC himage
    rw [himage] at hint
    obtain ⟨fc, hfc, hGfc⟩ := (hint ▸ Set.mem_univ Fo : Fo ∈ G '' interior (C : Set E))
    exact ⟨fc, hGfc.symm, hfc⟩

/-- A grasp (MLS Definition 5.1) is prehensile, MLS Exercise 6, printed p. 260:
`Prehensile g.map g.cone`. Finite-force caveat: unbounded contact forces at maintained rigid
contacts (MLS p. 214). -/
def IsPrehensile (g : Grasp E W) : Prop := Prehensile g.map g.cone

/-- **MLS Exercise 6, printed pp. 260–261, for a grasp** (Definition 5.1): prehensile if and only
if force-closure; the friction cone's Definition 5.1 properties supply every hypothesis.
Finite-force caveat: unbounded contact forces at maintained rigid contacts (MLS p. 214). -/
theorem isPrehensile_iff_isForceClosure [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (g : Grasp E W) : g.IsPrehensile ↔ g.IsForceClosure :=
  prehensile_iff_forceClosure g.map g.cone.toConvexCone g.cone.interior_nonempty

end Prehensile

end Grasp

namespace SpatialGrasp

variable {ι : Type*} [Fintype ι] {m : ι → ℕ}

/-- The range of `Gᵀ` is orthogonal to the internal forces: if `G f_N = 0`, then
`(Gᵀ V) · f_N = 0` for every object twist `V` (MLS eqs. (5.6), (5.13), printed pp. 219, 236). -/
theorem sum_graspTranspose_mul_eq_zero (g : SpatialGrasp ι m) {fN : (i : ι) → Fin (m i) → ℝ}
    (hfN : g.graspMap fN = 0) (V : Twist) :
    ∑ i, ∑ j, g.graspTranspose V i j * fN i j = 0 := by
  rw [sum_graspTranspose_mul, hfN, Wrench.pair_zero_left]

/-- A nonzero contact force with `G f_N = 0` (for example a strictly internal force of a
force-closure grasp, Proposition 5.2) is not in the range of `Gᵀ`; so `Gᵀ` is not onto the contact
velocities (MLS eqs. (5.6), (5.13), printed pp. 219, 236). -/
theorem not_mem_range_graspTranspose (g : SpatialGrasp ι m) {fN : (i : ι) → Fin (m i) → ℝ}
    (hfN : g.graspMap fN = 0) (hne : fN ≠ 0) : fN ∉ Set.range g.graspTranspose := by
  rintro ⟨V, hV⟩
  have h0 := g.sum_graspTranspose_mul_eq_zero hfN V
  rw [hV] at h0
  apply hne
  have hsq : ∀ i, ∑ j, fN i j * fN i j = 0 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, fN i j * fN i j :=
      fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 i (Finset.mem_univ i)
  funext i j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (fN i j)).mp (hsq i) j
    (Finset.mem_univ j)
  simpa using mul_self_eq_zero.mp hj

end SpatialGrasp

/-- A multifingered grasp, MLS Definition 5.4, printed p. 237, at one configuration `(θ, x_o)`:
the hand Jacobian `J_h(θ, x_o) : ℝⁿ → ℝᵐ` (here from any real joint-rate space `Θ` to the contact
coefficients), and a spatial grasp, which supplies the grasp map `G : ℝᵐ → ℝᵖ` (eq. (5.6)), its
transpose `Gᵀ` on object twists (eq. (5.13)) and the friction cone `FC ⊂ ℝᵐ` satisfying
Definition 5.1 (the product of the contact cones). The spatial grasp's object side is
`Wrench`/`Twist` (`p = 6`); the definition does not require `J_h` to come from fingers
(`HandGrasp.toMultifingeredGrasp` builds the one of a hand). -/
structure MultifingeredGrasp (Θ : Type*) [AddCommGroup Θ] [Module ℝ Θ] (ι : Type*) [Fintype ι]
    (m : ι → ℕ) where
  /-- The hand Jacobian `J_h(θ, x_o)`, MLS printed pp. 236–237. -/
  handJacobian : Θ →ₗ[ℝ] ((i : ι) → Fin (m i) → ℝ)
  /-- The contacts, which give `G`, `Gᵀ` and `FC`, MLS printed pp. 218–220, 236. -/
  grasp : SpatialGrasp ι m

namespace MultifingeredGrasp

variable {Θ : Type*} [AddCommGroup Θ] [Module ℝ Θ] {ι : Type*} [Fintype ι] {m : ι → ℕ}

/-- The multifingered grasp is manipulable, MLS Definition 5.5, printed p. 237: for every object
twist `V^b_{po}` there are joint rates `θ̇` with `J_h θ̇ = Gᵀ V^b_{po}` (eq. (5.15)). Joint rates
are unbounded; contacts are assumed maintained (MLS p. 234). -/
def IsManipulable (mg : MultifingeredGrasp Θ ι m) : Prop :=
  Grasp.Manipulable mg.handJacobian mg.grasp.graspTranspose

/-- The multifingered grasp is force-closure (MLS Definition 5.2, printed p. 223, for its grasp
`(G, FC)`). Finite-force caveat: unbounded contact forces at maintained rigid contacts
(MLS p. 214). -/
def IsForceClosure (mg : MultifingeredGrasp Θ ι m) : Prop :=
  mg.grasp.toGrasp.IsForceClosure

/-- **MLS Proposition 5.8**, printed p. 238: a multifingered grasp is manipulable at its
configuration if and only if `R(Gᵀ) ⊂ R(J_h(θ, x_o))` (Table 5.4, row "Manipulable", p. 239). -/
theorem isManipulable_iff_range_le (mg : MultifingeredGrasp Θ ι m) :
    mg.IsManipulable ↔ LinearMap.range mg.grasp.graspTranspose ≤ LinearMap.range mg.handJacobian :=
  Grasp.manipulable_iff_range_le _ _

/-- A surjective hand Jacobian gives a manipulable grasp, with or without force-closure: the "if"
direction of the summary item 6, MLS printed p. 257. -/
theorem IsManipulable.of_surjective (mg : MultifingeredGrasp Θ ι m)
    (hJ : Function.Surjective mg.handJacobian) : mg.IsManipulable :=
  Grasp.Manipulable.of_surjective _ hJ

/-- **MLS printed p. 239, as printed**: "If the grasp is manipulable and force-closure, then it
follows that `J_h` is surjective onto the range of `Gᵀ`": every contact velocity `Gᵀ V` is `J_h θ̇`
for some `θ̇`. The proof uses manipulability only (it is Proposition 5.8); the force-closure
premise is printed and kept, and is not used. Finite-force caveat (MLS p. 214). -/
theorem surjOn_range_graspTranspose (mg : MultifingeredGrasp Θ ι m) (hm : mg.IsManipulable)
    (_hfc : mg.IsForceClosure) :
    Set.SurjOn mg.handJacobian Set.univ (Set.range mg.grasp.graspTranspose) := by
  rintro _ ⟨V, rfl⟩
  obtain ⟨θ', hθ'⟩ := hm V
  exact ⟨θ', Set.mem_univ _, hθ'⟩

/-- An internal motion, MLS printed p. 238: joint rates `θ̇_N ∈ N(J_h)`, which "result in no
motion of the contacts" (Table 5.4, row "Internal motions", p. 239). -/
def IsInternalMotion (mg : MultifingeredGrasp Θ ι m) (θN : Θ) : Prop :=
  mg.handJacobian θN = 0

/-- Internal motions form the null space of `J_h` (MLS printed p. 238, `θ̇_N ∈ N(J_h)`). -/
theorem isInternalMotion_iff_mem_ker (mg : MultifingeredGrasp Θ ι m) (θN : Θ) :
    mg.IsInternalMotion θN ↔ θN ∈ LinearMap.ker mg.handJacobian :=
  LinearMap.mem_ker.symm

/-- MLS printed p. 238: "Internal motions can be added to a given finger velocity without changing
the velocity of the grasped object": if `J_h θ̇ = Gᵀ V` (eq. (5.15)) and `θ̇_N` is an internal motion,
then `J_h (θ̇ + θ̇_N) = Gᵀ V`. -/
theorem IsInternalMotion.add (mg : MultifingeredGrasp Θ ι m) {θN θ' : Θ} {V : Twist}
    (hN : mg.IsInternalMotion θN) (h : mg.handJacobian θ' = mg.grasp.graspTranspose V) :
    mg.handJacobian (θ' + θN) = mg.grasp.graspTranspose V := by
  rw [map_add, h, hN, add_zero]

/-- With a surjective grasp map (for example a force-closure grasp, `Grasp.ForceClosure.surjective`)
the object twist is determined by the joint rates through eq. (5.15): if `J_h θ̇ = Gᵀ V` and
`J_h (θ̇ + θ̇_N) = Gᵀ V'` with `θ̇_N` an internal motion, then `V' = V` (MLS printed p. 238, the
object velocity does not change). -/
theorem eq_of_isInternalMotion (mg : MultifingeredGrasp Θ ι m)
    (hG : Function.Surjective mg.grasp.graspMap) {θN θ' : Θ} {V V' : Twist}
    (hN : mg.IsInternalMotion θN) (h : mg.handJacobian θ' = mg.grasp.graspTranspose V)
    (h' : mg.handJacobian (θ' + θN) = mg.grasp.graspTranspose V') : V' = V :=
  mg.grasp.graspTranspose_injective hG (by rw [← h', IsInternalMotion.add mg hN h])

/-- The joint torques balancing contact forces `f_c`, MLS eq. (5.16), printed p. 238,
`τ = J_hᵀ f_c`, as the linear form `θ̇ ↦ f_c · (J_h θ̇)` on joint rates (the coefficient dot
product `∑ᵢ ∑ⱼ f_{cᵢ,j} (J_h θ̇)ᵢⱼ`). This is the transpose of `J_h` read through the work pairing:
the joint force whose power on every `θ̇` is the power of the contact forces on the contact
velocities `J_h θ̇`. MLS obtains (5.16) "by equating the work done by the joints and contacts";
that premise is not formalized. MLS requires `f_c ∈ FC` (p. 238); the definition takes any
`f_c`. -/
def torque (mg : MultifingeredGrasp Θ ι m) (fc : (i : ι) → Fin (m i) → ℝ) : Θ →ₗ[ℝ] ℝ where
  toFun θ' := ∑ i, ∑ j, fc i j * mg.handJacobian θ' i j
  map_add' x y := by
    simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The torque form of MLS eq. (5.16), printed p. 238, evaluated on joint rates: the contact power
`f_c · (J_h θ̇)`. -/
theorem torque_apply (mg : MultifingeredGrasp Θ ι m) (fc : (i : ι) → Fin (m i) → ℝ) (θ' : Θ) :
    mg.torque fc θ' = ∑ i, ∑ j, fc i j * mg.handJacobian θ' i j := rfl

/-- **The force and velocity domains of MLS Figure 5.15 agree** (printed p. 238, eqs. (5.15)–(5.16),
with eq. (5.6)): if `J_h θ̇ = Gᵀ V`, the joint power of `τ = J_hᵀ f_c` on `θ̇` is the power
`(G f_c) · V` of the object wrench on the object twist (MLS p. 61 pairing). -/
theorem torque_apply_eq_pair (mg : MultifingeredGrasp Θ ι m) {θ' : Θ} {V : Twist}
    (h : mg.handJacobian θ' = mg.grasp.graspTranspose V) (fc : (i : ι) → Fin (m i) → ℝ) :
    mg.torque fc θ' = Wrench.pair (mg.grasp.graspMap fc) V := by
  rw [torque_apply, h, ← SpatialGrasp.sum_graspTranspose_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Structurally dependent contact forces, MLS printed p. 239: "contact forces which lie in the
null space of `J_hᵀ`", which give `τ = 0` in eq. (5.16). The row "structural forces,
`G⁺ F_I ∈ N(J_hᵀ)`" of Table 5.4 is not formalized (`G⁺` is not defined in the book). -/
def IsStructurallyDependentForce (mg : MultifingeredGrasp Θ ι m)
    (fc : (i : ι) → Fin (m i) → ℝ) : Prop :=
  mg.torque fc = 0

private theorem functional_apply_eq_sum [DecidableEq ι] (φ : ((i : ι) → Fin (m i) → ℝ) →ₗ[ℝ] ℝ)
    (x : (i : ι) → Fin (m i) → ℝ) :
    φ x = ∑ i, ∑ j, x i j *
      φ (ContactGrasp.stack.symm fun c : Σ i, Fin (m i) => if (⟨i, j⟩ : Σ i, Fin (m i)) = c
        then (1 : ℝ) else 0) := by
  have h := LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ ContactGrasp.stack.symm.toLinearMap)
    (ContactGrasp.stack x)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, smul_eq_mul] at h
  rw [h, Fintype.sum_sigma]
  rfl

/-- **MLS printed p. 239**: "If a grasp is not manipulable, then … `J_hᵀ` will have a non-trivial
null space and hence there may exist contact forces `f_c` which give `τ = 0` in equation (5.16)":
a multifingered grasp that is not manipulable has a nonzero structurally dependent contact
force. -/
theorem exists_isStructurallyDependentForce_of_not_isManipulable (mg : MultifingeredGrasp Θ ι m)
    (h : ¬ mg.IsManipulable) :
    ∃ fc : (i : ι) → Fin (m i) → ℝ, fc ≠ 0 ∧ mg.IsStructurallyDependentForce fc := by
  classical
  have hlt : LinearMap.range mg.handJacobian < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => h ?_
    exact IsManipulable.of_surjective mg (LinearMap.range_eq_top.mp htop)
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  refine ⟨fun i j => φ (ContactGrasp.stack.symm fun c : Σ i, Fin (m i) =>
    if (⟨i, j⟩ : Σ i, Fin (m i)) = c then (1 : ℝ) else 0), ?_, ?_⟩
  · intro h0
    apply hφ
    refine LinearMap.ext fun x => ?_
    rw [functional_apply_eq_sum φ x]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have := congrFun (congrFun h0 i) j
    simp only [Pi.zero_apply] at this
    rw [this, mul_zero]
  · refine LinearMap.ext fun θ' => ?_
    rw [torque_apply, LinearMap.zero_apply]
    have hker : φ (mg.handJacobian θ') = 0 := LinearMap.mem_ker.mp (hle ⟨θ', rfl⟩)
    rw [functional_apply_eq_sum φ] at hker
    exact Eq.trans
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _) hker

end MultifingeredGrasp

namespace HandGrasp

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ}

/-- The multifingered grasp of a hand at the configuration `(θ, x_o)`, MLS Definition 5.4, printed
p. 237: the hand Jacobian `J_h(θ, x_o)` of eq. (5.14) and the hand's spatial grasp. -/
def toMultifingeredGrasp (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) : MultifingeredGrasp ((i : ι) → Fin (n i) → ℝ) ι m :=
  ⟨h.handJacobian θ xo, h.grasp⟩

/-- Manipulability of a hand at `(θ, x_o)` (MLS Definition 5.5, printed p. 237) is the existence of
joint rates satisfying the grasping constraint (5.15) for every object twist. -/
theorem isManipulable_iff (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) :
    (h.toMultifingeredGrasp θ xo).IsManipulable ↔
      ∀ V : Twist, ∃ θ', h.GraspingConstraint θ xo θ' V := Iff.rfl

/-- **Summary item 6 of MLS printed p. 257, for hands.** For the hand Jacobian of eq. (5.14) (block
diagonal) of a hand whose contact constraint maps `B_{cᵢ}ᵀ` are onto (true for every contact model
of Table 5.2: `ContactModel.frictionless_constraint_surjective`,
`pointContact_constraint_surjective`, `softFinger_constraint_surjective` in `Grasp/Contact`, and of
every model with linearly independent basis columns:
`constraint_surjective_of_linearIndependent`), the grasp is manipulable
at `(θ, x_o)` if and only if `J_h(θ, x_o)` is surjective. Force-closure is not needed. The
argument uses the block structure: `Gᵢᵀ = B_{cᵢ}ᵀ Ad_{g_{ocᵢ}⁻¹}` is onto `ℝ^{mᵢ}`, so every block of
`J_h` must be onto. For a general multifingered grasp (Definition 5.4) the "only if" direction
fails (`Examples.summaryItem6_counterexample`). -/
theorem isManipulable_iff_surjective (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (hB : ∀ i, Function.Surjective (h.grasp.model i).constraint) :
    (h.toMultifingeredGrasp θ xo).IsManipulable ↔ Function.Surjective (h.handJacobian θ xo) := by
  refine ⟨fun hm y => ?_, fun hJ => MultifingeredGrasp.IsManipulable.of_surjective _ hJ⟩
  have hGt : ∀ i, ∃ V : Twist, h.grasp.graspTranspose V i = y i := by
    intro i
    obtain ⟨W, hW⟩ := hB i (y i)
    exact ⟨Twist.adjoint (h.grasp.frame i) W, by
      rw [SpatialGrasp.graspTranspose_apply, Twist.adjoint_inv_adjoint, hW]⟩
  choose V hV using hGt
  choose θs hθs using fun i => hm (V i)
  refine ⟨fun i => θs i i, funext fun i => ?_⟩
  have hi := congrFun (hθs i) i
  rw [← hV i]
  exact hi

/-- The force-closure form of the summary item 6, MLS printed p. 257, for hands: "A force-closure
grasp is manipulable if and only if `J_h` is surjective", for the hand Jacobian of eq. (5.14) with
onto contact constraint maps. The force-closure premise is printed and kept; the proof does not
use it (`isManipulable_iff_surjective`). Finite-force caveat (MLS p. 214). -/
theorem isManipulable_iff_surjective_of_isForceClosure (h : HandGrasp ι m n)
    (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform)
    (hB : ∀ i, Function.Surjective (h.grasp.model i).constraint)
    (_hfc : (h.toMultifingeredGrasp θ xo).IsForceClosure) :
    (h.toMultifingeredGrasp θ xo).IsManipulable ↔ Function.Surjective (h.handJacobian θ xo) :=
  h.isManipulable_iff_surjective θ xo hB

/-- The torque form of MLS eq. (5.16) of a hand has the components `HandGrasp.handTorque`
(printed p. 238): `τ(θ̇) = ∑ᵢ ∑ₗ τᵢₗ θ̇ᵢₗ` with `τ = J_hᵀ f_c`. -/
theorem torque_toMultifingeredGrasp (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (fc : (i : ι) → Fin (m i) → ℝ) (θ' : (i : ι) → Fin (n i) → ℝ) :
    (h.toMultifingeredGrasp θ xo).torque fc θ' = ∑ i, ∑ l, h.handTorque θ xo fc i l * θ' i l :=
  (h.sum_handTorque_mul θ xo fc θ').symm

end HandGrasp

end RoboLean
