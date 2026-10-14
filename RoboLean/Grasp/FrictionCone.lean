import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt

/-!
# Friction cones: the cone properties of Definition 5.1 and the printed contact cones

MLS Chapter 5, §2.1, printed pp. 215–219, and Definition 5.1, printed p. 220. A contact is
modeled by a wrench basis `B_c ∈ ℝ^{p×m}` and a friction cone `FC_c ⊂ ℝ^m` of contact force
coordinates; MLS requires (p. 218, and again for the whole grasp in Definition 5.1, p. 220):

1. `FC` is a closed subset of `ℝ^m` with non-empty interior;
2. `f₁, f₂ ∈ FC ⟹ α f₁ + β f₂ ∈ FC` for `α, β > 0`.

`FrictionCone E` bundles a Mathlib `ConvexCone ℝ E` (property 2: closure under positive
scaling and under addition) with closedness and nonempty interior (property 1). The carrier `E`
is the space of contact force *coefficients* (the book's `ℝ^m`), not of wrenches: the set of
wrenches a contact can apply is the image `B_c(FC_c)` (`ContactModel.wrenchCone`).

The printed cones (Table 5.2, p. 219; Example 5.3, p. 222; p. 224) are defined here as convex
cones for every coefficient and bundled as friction cones under the positivity hypotheses the
book states (`μ > 0`, p. 216; `γ > 0`, p. 217):

* frictionless point contact `{f ∈ ℝ¹ : f₁ ≥ 0}` (eq. (5.1)),
* point contact with friction `{f ∈ ℝ³ : √(f₁² + f₂²) ≤ μ f₃, f₃ ≥ 0}` (eq. (5.3)),
* soft finger `{f ∈ ℝ⁴ : √(f₁² + f₂²) ≤ μ f₃, f₃ ≥ 0, |f₄| ≤ γ f₃}` (eq. (5.4)),
* planar point contact with friction `{f ∈ ℝ² : |f₁| ≤ μ f₂, f₂ ≥ 0}` (Example 5.3, p. 222),
* the nonnegative orthant `{f ∈ ℝ^k : fᵢ ≥ 0}` of `k` frictionless contacts (p. 224).

MLS asserts properties 1–2 for these cones without proof; they are proved here. Coordinates are
the book's, indexed from `0`: Lean `f 0, f 1, f 2, f 3` are the book's `f₁, f₂, f₃, f₄`. Contact
force coordinates are `Fin m → ℝ` with the product topology, the Euclidean topology of `ℝ^m`.
These are statements about sets of coefficients; they say nothing about whether a physical
contact obeys the Coulomb model (MLS calls it "an empirical model", p. 216).
-/

noncomputable section

namespace RoboLean

/-- A friction cone in the sense of MLS Definition 5.1, printed p. 220 (and the contact
requirements on printed p. 218): a set `FC` of contact force coefficients that (1) is closed
with nonempty interior and (2) is closed under positive combinations `α f₁ + β f₂`, `α, β > 0`.
Property 2 is the Mathlib structure `ConvexCone ℝ E` (closure under positive scaling and under
addition); property 1 is the two fields `isClosed` and `interior_nonempty`. The carrier `E` is
the coefficient space (`ℝ^m` in MLS), with any real topological vector space structure. -/
structure FrictionCone (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] where
  /-- The underlying convex cone: MLS Definition 5.1, property 2, printed p. 220. -/
  toConvexCone : ConvexCone ℝ E
  /-- MLS Definition 5.1, property 1, printed p. 220: `FC` is a closed subset. -/
  isClosed : IsClosed (toConvexCone : Set E)
  /-- MLS Definition 5.1, property 1, printed p. 220: `FC` has non-empty interior. -/
  interior_nonempty : (interior (toConvexCone : Set E)).Nonempty

namespace FrictionCone

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A friction cone is a set of contact force coefficients, MLS Definition 5.1, printed p. 220
(`FC ⊂ ℝ^m`); two friction cones with the same points are equal. -/
instance : SetLike (FrictionCone E) E where
  coe C := C.toConvexCone
  coe_injective := by
    rintro ⟨C, _, _⟩ ⟨D, _, _⟩ h
    have hCD : C = D := SetLike.coe_injective h
    subst hCD
    rfl

/-- The points of a friction cone are the points of its convex cone (MLS Definition 5.1,
printed p. 220). -/
@[simp] theorem coe_toConvexCone (C : FrictionCone E) :
    ((C.toConvexCone : Set E)) = (C : Set E) := rfl

/-- Membership in a friction cone is membership in its convex cone (MLS Definition 5.1,
printed p. 220). -/
@[simp] theorem mem_toConvexCone (C : FrictionCone E) {f : E} :
    f ∈ C.toConvexCone ↔ f ∈ C := Iff.rfl

/-- MLS Definition 5.1, property 1, printed p. 220: a friction cone is closed. -/
theorem isClosed_coe (C : FrictionCone E) : IsClosed (C : Set E) := C.isClosed

/-- MLS Definition 5.1, property 1, printed p. 220: a friction cone has nonempty interior. -/
theorem interior_coe_nonempty (C : FrictionCone E) : (interior (C : Set E)).Nonempty :=
  C.interior_nonempty

/-- MLS Definition 5.1, property 2, printed p. 220, as printed: `f₁, f₂ ∈ FC` implies
`α f₁ + β f₂ ∈ FC` for `α, β > 0`. -/
theorem add_smul_mem (C : FrictionCone E) {f₁ f₂ : E} (h₁ : f₁ ∈ C) (h₂ : f₂ ∈ C)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : α • f₁ + β • f₂ ∈ C :=
  C.toConvexCone.add_mem (C.toConvexCone.smul_mem hα h₁) (C.toConvexCone.smul_mem hβ h₂)

/-- A friction cone is closed under addition (MLS Definition 5.1, property 2, printed p. 220). -/
theorem add_mem (C : FrictionCone E) {f₁ f₂ : E} (h₁ : f₁ ∈ C) (h₂ : f₂ ∈ C) : f₁ + f₂ ∈ C :=
  C.toConvexCone.add_mem h₁ h₂

/-- A friction cone is closed under positive scaling (MLS Definition 5.1, property 2,
printed p. 220). -/
theorem smul_mem (C : FrictionCone E) {f : E} (h : f ∈ C) {α : ℝ} (hα : 0 < α) : α • f ∈ C :=
  C.toConvexCone.smul_mem hα h

/-- A friction cone is convex (from MLS Definition 5.1, property 2, printed p. 220; MLS does
not state it separately). -/
theorem convex (C : FrictionCone E) : Convex ℝ (C : Set E) := C.toConvexCone.convex

/-- A friction cone is nonempty (from MLS Definition 5.1, property 1, printed p. 220). -/
theorem nonempty (C : FrictionCone E) : (C : Set E).Nonempty :=
  C.interior_nonempty.mono interior_subset

/-- A friction cone contains the zero contact force. MLS does not state this; it follows from
Definition 5.1 (printed p. 220): a nonempty closed convex cone contains `0` (Mathlib
`ConvexCone.Pointed.of_nonempty_of_isClosed`). -/
theorem zero_mem [ContinuousSMul ℝ E] (C : FrictionCone E) : (0 : E) ∈ C :=
  ConvexCone.Pointed.of_nonempty_of_isClosed (C := C.toConvexCone) C.nonempty C.isClosed

/-- The product `FC_{c₁} × ⋯ × FC_{c_k}` of finitely many friction cones, MLS printed p. 220
(after equation (5.7)): `f_c = (f_{c₁}, …, f_{c_k})` lies in it exactly when each `f_{cᵢ}` lies
in `FC_{cᵢ}`. It satisfies Definition 5.1 again (closed by `isClosed_set_pi`, interior the
product of the interiors since the index set is finite). Contact `i` has coefficient space
`E i`. -/
def pi {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, TopologicalSpace (E i)] (C : ∀ i, FrictionCone (E i)) : FrictionCone (∀ i, E i) where
  toConvexCone :=
    { carrier := Set.univ.pi fun i => (C i : Set (E i))
      smul_mem' := fun _ hc _ hf i _ => (C i).smul_mem (hf i trivial) hc
      add_mem' := fun _ hf _ hg i _ => (C i).add_mem (hf i trivial) (hg i trivial) }
  isClosed := isClosed_set_pi fun i _ => (C i).isClosed
  interior_nonempty := by
    change (interior (Set.univ.pi fun i => (C i : Set (E i)))).Nonempty
    rw [interior_pi_set Set.finite_univ]
    exact Set.univ_pi_nonempty_iff.mpr fun i => (C i).interior_nonempty

section Pi

variable {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module ℝ (F i)]
  [∀ i, TopologicalSpace (F i)]

/-- Membership in the product cone, MLS printed p. 220: `f_c ∈ FC_{c₁} × ⋯ × FC_{c_k}` exactly
when `f_{cᵢ} ∈ FC_{cᵢ}` for every contact `i`. -/
@[simp] theorem mem_pi (C : ∀ i, FrictionCone (F i)) {f : ∀ i, F i} :
    f ∈ pi C ↔ ∀ i, f i ∈ C i := by
  change f ∈ Set.univ.pi (fun i => (C i : Set (F i))) ↔ _
  simp

/-- The interior of the product cone is the product of the interiors (MLS printed p. 220, with
`int(FC)` of p. 223); a finite index set is used. -/
theorem interior_pi (C : ∀ i, FrictionCone (F i)) :
    interior (pi C : Set (∀ i, F i)) = Set.univ.pi fun i => interior (C i : Set (F i)) :=
  interior_pi_set Set.finite_univ

/-- A contact force vector lies in the interior of the product cone exactly when every contact's
force lies in the interior of its own cone (MLS printed pp. 220 and 223). -/
theorem mem_interior_pi (C : ∀ i, FrictionCone (F i)) {f : ∀ i, F i} :
    f ∈ interior (pi C : Set (∀ i, F i)) ↔ ∀ i, f i ∈ interior (C i : Set (F i)) := by
  rw [interior_pi]
  simp

end Pi

end FrictionCone

namespace Grasp

/-! ### The printed cones as convex cones -/

/-- The nonnegative orthant `{f ∈ ℝ^k : fᵢ ≥ 0}`, the friction cone of `k` frictionless point
contacts, MLS printed p. 224 (and `f₁ ≥ 0` for one contact, eq. (5.1), p. 215). Defined for any
index type. -/
def orthantCone (ι : Type*) : ConvexCone ℝ (ι → ℝ) where
  carrier := {f | ∀ i, 0 ≤ f i}
  smul_mem' := fun _ hc _ hf i => mul_nonneg hc.le (hf i)
  add_mem' := fun _ hf _ hg i => add_nonneg (hf i) (hg i)

/-- Membership in the orthant of MLS printed p. 224: every coefficient is nonnegative. -/
@[simp] theorem mem_orthantCone {ι : Type*} {f : ι → ℝ} : f ∈ orthantCone ι ↔ ∀ i, 0 ≤ f i :=
  Iff.rfl

/-- The friction cone of a point contact with friction, MLS eq. (5.3), printed p. 217:
`{f ∈ ℝ³ : √(f₁² + f₂²) ≤ μ f₃, f₃ ≥ 0}` (Lean `f 0, f 1, f 2` are the book's `f₁, f₂, f₃`;
`f₃` is the normal force, along the contact `z`-axis). Defined for every `μ`; MLS takes
`μ > 0`, the static coefficient of friction (p. 216), which `FrictionCone.pointContact` requires. -/
def pointContactCone (μ : ℝ) : ConvexCone ℝ (Fin 3 → ℝ) where
  carrier := {f | √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2 ∧ 0 ≤ f 2}
  smul_mem' := by
    rintro c hc f ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (c * f 0) ^ 2 + (c * f 1) ^ 2 = c ^ 2 * (f 0 ^ 2 + f 1 ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
      nlinarith
    · simp only [Pi.smul_apply, smul_eq_mul]
      positivity
  add_mem' := by
    rintro f ⟨h₁, h₂⟩ g ⟨h₃, h₄⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply]
      calc √((f 0 + g 0) ^ 2 + (f 1 + g 1) ^ 2)
          ≤ √(f 0 ^ 2 + f 1 ^ 2) + √(g 0 ^ 2 + g 1 ^ 2) := sqrt_add_sq_le _ _ _ _
        _ ≤ μ * (f 2 + g 2) := by linarith
    · simp only [Pi.add_apply]
      linarith
where
  /-- The triangle inequality in the plane, `√((a+c)² + (b+d)²) ≤ √(a²+b²) + √(c²+d²)`
  (supporting lemma for MLS eq. (5.3), p. 217). -/
  sqrt_add_sq_le (a b c d : ℝ) :
      √((a + c) ^ 2 + (b + d) ^ 2) ≤ √(a ^ 2 + b ^ 2) + √(c ^ 2 + d ^ 2) := by
    have key : ∀ x y : ℝ,
        √(x ^ 2 + y ^ 2) = ‖(WithLp.toLp 2 ![x, y] : EuclideanSpace ℝ (Fin 2))‖ := by
      intro x y
      rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_two]
    have hsum : (WithLp.toLp 2 ![a + c, b + d] : EuclideanSpace ℝ (Fin 2)) =
        WithLp.toLp 2 ![a, b] + WithLp.toLp 2 ![c, d] := by
      ext i
      fin_cases i <;> simp
    rw [key, key, key, hsum]
    exact norm_add_le _ _

/-- Membership in the point-contact friction cone, MLS eq. (5.3), printed p. 217. -/
@[simp] theorem mem_pointContactCone {μ : ℝ} {f : Fin 3 → ℝ} :
    f ∈ pointContactCone μ ↔ √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2 ∧ 0 ≤ f 2 := Iff.rfl

/-- The friction cone of a soft-finger contact, MLS eq. (5.4), printed p. 217:
`{f ∈ ℝ⁴ : √(f₁² + f₂²) ≤ μ f₃, f₃ ≥ 0, |f₄| ≤ γ f₃}` (Lean `f 0, …, f 3` are the book's
`f₁, …, f₄`; `f₄` is the torque about the contact normal). Defined for every `μ, γ`; MLS takes
`μ > 0` and the torsional coefficient `γ > 0` (p. 217), which `FrictionCone.softFinger`
requires. -/
def softFingerCone (μ γ : ℝ) : ConvexCone ℝ (Fin 4 → ℝ) where
  carrier := {f | √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2 ∧ 0 ≤ f 2 ∧ |f 3| ≤ γ * f 2}
  smul_mem' := by
    rintro c hc f ⟨h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (c * f 0) ^ 2 + (c * f 1) ^ 2 = c ^ 2 * (f 0 ^ 2 + f 1 ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
      nlinarith
    · simp only [Pi.smul_apply, smul_eq_mul]
      positivity
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
      nlinarith
  add_mem' := by
    rintro f ⟨h₁, h₂, h₃⟩ g ⟨h₄, h₅, h₆⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply]
      calc √((f 0 + g 0) ^ 2 + (f 1 + g 1) ^ 2)
          ≤ √(f 0 ^ 2 + f 1 ^ 2) + √(g 0 ^ 2 + g 1 ^ 2) :=
            pointContactCone.sqrt_add_sq_le _ _ _ _
        _ ≤ μ * (f 2 + g 2) := by linarith
    · simp only [Pi.add_apply]
      linarith
    · simp only [Pi.add_apply]
      calc |f 3 + g 3| ≤ |f 3| + |g 3| := abs_add_le _ _
        _ ≤ γ * (f 2 + g 2) := by linarith

/-- Membership in the soft-finger friction cone, MLS eq. (5.4), printed p. 217. -/
@[simp] theorem mem_softFingerCone {μ γ : ℝ} {f : Fin 4 → ℝ} :
    f ∈ softFingerCone μ γ ↔
      √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2 ∧ 0 ≤ f 2 ∧ |f 3| ≤ γ * f 2 := Iff.rfl

/-- The friction cone of a planar point contact with friction, MLS Example 5.3, printed
p. 222: `{f ∈ ℝ² : |f₁| ≤ μ f₂, f₂ ≥ 0}` (Lean `f 0, f 1` are the book's `f₁, f₂`; in the
planar convention of p. 222 the contact `y`-axis, coefficient `f₂`, is the inward normal).
Defined for every `μ`; `FrictionCone.planarPointContact` requires `μ > 0`. -/
def planarPointContactCone (μ : ℝ) : ConvexCone ℝ (Fin 2 → ℝ) where
  carrier := {f | |f 0| ≤ μ * f 1 ∧ 0 ≤ f 1}
  smul_mem' := by
    rintro c hc f ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
      nlinarith
    · simp only [Pi.smul_apply, smul_eq_mul]
      positivity
  add_mem' := by
    rintro f ⟨h₁, h₂⟩ g ⟨h₃, h₄⟩
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply]
      calc |f 0 + g 0| ≤ |f 0| + |g 0| := abs_add_le _ _
        _ ≤ μ * (f 1 + g 1) := by linarith
    · simp only [Pi.add_apply]
      linarith

/-- Membership in the planar point-contact friction cone, MLS Example 5.3, printed p. 222. -/
@[simp] theorem mem_planarPointContactCone {μ : ℝ} {f : Fin 2 → ℝ} :
    f ∈ planarPointContactCone μ ↔ |f 0| ≤ μ * f 1 ∧ 0 ≤ f 1 := Iff.rfl

/-! ### Closedness and interior points (Definition 5.1, property 1) -/

/-- The orthant of MLS printed p. 224 is closed. -/
theorem isClosed_orthantCone (ι : Type*) : IsClosed (orthantCone ι : Set (ι → ℝ)) := by
  have h : {f : ι → ℝ | ∀ i, 0 ≤ f i} = ⋂ i, {f | 0 ≤ f i} := by
    ext f
    simp
  change IsClosed {f : ι → ℝ | ∀ i, 0 ≤ f i}
  rw [h]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

/-- A coefficient vector with every entry strictly positive lies in the interior of the orthant
of MLS printed p. 224 (finite index type). -/
theorem mem_interior_orthantCone {ι : Type*} [Finite ι] {f : ι → ℝ} (h : ∀ i, 0 < f i) :
    f ∈ interior (orthantCone ι : Set (ι → ℝ)) := by
  have hU : IsOpen (Set.univ.pi fun _ : ι => Set.Ioi (0 : ℝ)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  refine interior_maximal ?_ hU (fun i _ => h i)
  intro g hg i
  exact le_of_lt (hg i trivial)

/-- The point-contact friction cone of MLS eq. (5.3), printed p. 217, is closed. -/
theorem isClosed_pointContactCone (μ : ℝ) : IsClosed (pointContactCone μ : Set (Fin 3 → ℝ)) := by
  change IsClosed ({f : Fin 3 → ℝ | √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2} ∩ {f | 0 ≤ f 2})
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_le continuous_const (continuous_apply 2))

/-- Strict inequalities give interior points of the point-contact friction cone of MLS
eq. (5.3), printed p. 217: `√(f₁² + f₂²) < μ f₃` and `f₃ > 0`. -/
theorem mem_interior_pointContactCone {μ : ℝ} {f : Fin 3 → ℝ}
    (h₁ : √(f 0 ^ 2 + f 1 ^ 2) < μ * f 2) (h₂ : 0 < f 2) :
    f ∈ interior (pointContactCone μ : Set (Fin 3 → ℝ)) := by
  have hU : IsOpen ({g : Fin 3 → ℝ | √(g 0 ^ 2 + g 1 ^ 2) < μ * g 2} ∩ {g | 0 < g 2}) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt continuous_const (continuous_apply 2))
  exact interior_maximal (fun g hg => mem_pointContactCone.2 ⟨hg.1.le, hg.2.le⟩) hU ⟨h₁, h₂⟩

/-- The soft-finger friction cone of MLS eq. (5.4), printed p. 217, is closed. -/
theorem isClosed_softFingerCone (μ γ : ℝ) :
    IsClosed (softFingerCone μ γ : Set (Fin 4 → ℝ)) := by
  change IsClosed ({f : Fin 4 → ℝ | √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2} ∩
    ({f | 0 ≤ f 2} ∩ {f | |f 3| ≤ γ * f 2}))
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter
    ((isClosed_le continuous_const (continuous_apply 2)).inter
      (isClosed_le (by fun_prop) (by fun_prop)))

/-- Strict inequalities give interior points of the soft-finger friction cone of MLS
eq. (5.4), printed p. 217: `√(f₁² + f₂²) < μ f₃`, `f₃ > 0` and `|f₄| < γ f₃`. -/
theorem mem_interior_softFingerCone {μ γ : ℝ} {f : Fin 4 → ℝ}
    (h₁ : √(f 0 ^ 2 + f 1 ^ 2) < μ * f 2) (h₂ : 0 < f 2) (h₃ : |f 3| < γ * f 2) :
    f ∈ interior (softFingerCone μ γ : Set (Fin 4 → ℝ)) := by
  have hU : IsOpen ({g : Fin 4 → ℝ | √(g 0 ^ 2 + g 1 ^ 2) < μ * g 2} ∩
      ({g | 0 < g 2} ∩ {g | |g 3| < γ * g 2})) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (by fun_prop) (by fun_prop)))
  exact interior_maximal
    (fun g hg => mem_softFingerCone.2 ⟨hg.1.le, hg.2.1.le, hg.2.2.le⟩) hU ⟨h₁, h₂, h₃⟩

/-- The planar point-contact friction cone of MLS Example 5.3, printed p. 222, is closed. -/
theorem isClosed_planarPointContactCone (μ : ℝ) :
    IsClosed (planarPointContactCone μ : Set (Fin 2 → ℝ)) := by
  change IsClosed ({f : Fin 2 → ℝ | |f 0| ≤ μ * f 1} ∩ {f | 0 ≤ f 1})
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_le continuous_const (continuous_apply 1))

/-- Strict inequalities give interior points of the planar point-contact friction cone of MLS
Example 5.3, printed p. 222: `|f₁| < μ f₂` and `f₂ > 0`. -/
theorem mem_interior_planarPointContactCone {μ : ℝ} {f : Fin 2 → ℝ} (h₁ : |f 0| < μ * f 1)
    (h₂ : 0 < f 1) : f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) := by
  have hU : IsOpen ({g : Fin 2 → ℝ | |g 0| < μ * g 1} ∩ {g | 0 < g 1}) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt continuous_const (continuous_apply 1))
  exact interior_maximal (fun g hg => mem_planarPointContactCone.2 ⟨hg.1.le, hg.2.le⟩) hU ⟨h₁, h₂⟩

/-- Supporting lemma: from an interior point `f` of the planar friction cone (MLS Example 5.3,
printed p. 222) a small positive step in any direction stays in the cone. -/
private theorem exists_pos_add_smul_mem_planarPointContactCone {μ : ℝ} {f : Fin 2 → ℝ}
    (hf : f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ))) (e : Fin 2 → ℝ) :
    ∃ t : ℝ, 0 < t ∧ f + t • e ∈ planarPointContactCone μ := by
  have hcont : Continuous fun t : ℝ => f + t • e := by fun_prop
  have h0 : f + (0 : ℝ) • e ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) := by
    simpa using hf
  have hev : ∀ᶠ t in nhds (0 : ℝ),
      f + t • e ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) :=
    hcont.continuousAt.eventually_mem (isOpen_interior.mem_nhds h0)
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f + t • e ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) ∧ t ∈ Set.Ioi 0 :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ht, htpos⟩ := hev'.exists
  exact ⟨t, htpos, interior_subset ht⟩

/-- **The interior of the planar friction cone is given by the strict inequality**, converse of
`mem_interior_planarPointContactCone` (MLS Example 5.3, printed p. 222, cone `|f₁| ≤ μ f₂,
f₂ ≥ 0`; `int(FC)` of p. 223): an interior point satisfies `|f₁| < μ f₂`. -/
theorem abs_lt_of_mem_interior_planarPointContactCone {μ : ℝ} {f : Fin 2 → ℝ}
    (hf : f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ))) : |f 0| < μ * f 1 := by
  by_cases h : 0 ≤ f 0
  · obtain ⟨t, ht, hmem⟩ := exists_pos_add_smul_mem_planarPointContactCone hf ![1, 0]
    have h1 := (mem_planarPointContactCone.mp hmem).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at h1
    rw [abs_of_nonneg (by linarith)] at h1
    rw [abs_of_nonneg h]
    linarith
  · replace h : f 0 < 0 := not_le.mp h
    obtain ⟨t, ht, hmem⟩ := exists_pos_add_smul_mem_planarPointContactCone hf ![-1, 0]
    have h1 := (mem_planarPointContactCone.mp hmem).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_neg, mul_one, mul_zero,
      add_zero] at h1
    rw [abs_of_neg (by linarith)] at h1
    rw [abs_of_neg h]
    linarith

/-- **The interior of the planar friction cone**, MLS Example 5.3, printed p. 222 (cone
`|f₁| ≤ μ f₂, f₂ ≥ 0`) with `int(FC)` of p. 223: for `μ > 0`, `f` is an interior point exactly
when `|f₁| < μ f₂` (then `f₂ > 0`). -/
theorem mem_interior_planarPointContactCone_iff {μ : ℝ} (hμ : 0 < μ) {f : Fin 2 → ℝ} :
    f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) ↔ |f 0| < μ * f 1 := by
  refine ⟨abs_lt_of_mem_interior_planarPointContactCone, fun h => ?_⟩
  have hpos : 0 < f 1 := by
    have : 0 < μ * f 1 := lt_of_le_of_lt (abs_nonneg _) h
    exact pos_of_mul_pos_right this hμ.le
  exact mem_interior_planarPointContactCone h hpos

end Grasp

namespace FrictionCone

open Grasp

/-- The friction cone of `k` frictionless point contacts, the orthant `{f ∈ ℝ^k : fᵢ ≥ 0}` of
MLS printed p. 224, as a friction cone (Definition 5.1, p. 220); `ι` is a finite index type. -/
def orthant (ι : Type*) [Finite ι] : FrictionCone (ι → ℝ) where
  toConvexCone := orthantCone ι
  isClosed := isClosed_orthantCone ι
  interior_nonempty := ⟨fun _ => 1, mem_interior_orthantCone fun _ => one_pos⟩

/-- The friction cone of a frictionless point contact, `{f ∈ ℝ¹ : f₁ ≥ 0}`, MLS eq. (5.1),
printed p. 215, and Table 5.2, p. 219: the orthant of `ℝ¹`. -/
def frictionless : FrictionCone (Fin 1 → ℝ) := orthant (Fin 1)

/-- Membership in the frictionless cone, `f₁ ≥ 0`, MLS eq. (5.1), printed p. 215. -/
@[simp] theorem mem_frictionless {f : Fin 1 → ℝ} : f ∈ frictionless ↔ 0 ≤ f 0 := by
  change (∀ i, 0 ≤ f i) ↔ _
  exact ⟨fun h => h 0, fun h i => by rwa [Subsingleton.elim i 0]⟩

/-- Membership in the orthant friction cone of MLS printed p. 224. -/
@[simp] theorem mem_orthant {ι : Type*} [Finite ι] {f : ι → ℝ} :
    f ∈ orthant ι ↔ ∀ i, 0 ≤ f i := Iff.rfl

/-- The friction cone of a point contact with friction, MLS eq. (5.3), printed p. 217, as a
friction cone (Definition 5.1, p. 220), for a coefficient of friction `μ > 0` (p. 216). -/
def pointContact (μ : ℝ) (hμ : 0 < μ) : FrictionCone (Fin 3 → ℝ) where
  toConvexCone := pointContactCone μ
  isClosed := isClosed_pointContactCone μ
  interior_nonempty := ⟨![0, 0, 1], mem_interior_pointContactCone (by simpa using hμ) (by simp)⟩

/-- The friction cone of a soft-finger contact, MLS eq. (5.4), printed p. 217, as a friction
cone (Definition 5.1, p. 220), for `μ > 0` (p. 216) and torsional coefficient `γ > 0` (p. 217). -/
def softFinger (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) : FrictionCone (Fin 4 → ℝ) where
  toConvexCone := softFingerCone μ γ
  isClosed := isClosed_softFingerCone μ γ
  interior_nonempty :=
    ⟨![0, 0, 1, 0], mem_interior_softFingerCone (by simpa using hμ) (by simp) (by simpa using hγ)⟩

/-- The friction cone of a planar point contact with friction, MLS Example 5.3, printed p. 222,
as a friction cone (Definition 5.1, p. 220), for `μ > 0`. -/
def planarPointContact (μ : ℝ) (hμ : 0 < μ) : FrictionCone (Fin 2 → ℝ) where
  toConvexCone := planarPointContactCone μ
  isClosed := isClosed_planarPointContactCone μ
  interior_nonempty := ⟨![0, 1], mem_interior_planarPointContactCone (by simpa using hμ) (by simp)⟩

/-- Membership in the point-contact friction cone, MLS eq. (5.3), printed p. 217. -/
@[simp] theorem mem_pointContact {μ : ℝ} {hμ : 0 < μ} {f : Fin 3 → ℝ} :
    f ∈ pointContact μ hμ ↔ √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2 ∧ 0 ≤ f 2 := Iff.rfl

/-- Membership in the soft-finger friction cone, MLS eq. (5.4), printed p. 217. -/
@[simp] theorem mem_softFinger {μ γ : ℝ} {hμ : 0 < μ} {hγ : 0 < γ} {f : Fin 4 → ℝ} :
    f ∈ softFinger μ γ hμ hγ ↔
      √(f 0 ^ 2 + f 1 ^ 2) ≤ μ * f 2 ∧ 0 ≤ f 2 ∧ |f 3| ≤ γ * f 2 := Iff.rfl

/-- Membership in the planar point-contact friction cone, MLS Example 5.3, printed p. 222. -/
@[simp] theorem mem_planarPointContact {μ : ℝ} {hμ : 0 < μ} {f : Fin 2 → ℝ} :
    f ∈ planarPointContact μ hμ ↔ |f 0| ≤ μ * f 1 ∧ 0 ≤ f 1 := Iff.rfl

end FrictionCone

end RoboLean
