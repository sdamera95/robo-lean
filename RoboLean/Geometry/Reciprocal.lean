import RoboLean.Geometry.Wrench
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Reciprocal twist and wrench subspaces

MLS printed p. 66 defines reciprocity by zero instantaneous power in one common
frame. Printed p. 67 gives the symmetric twist-coordinate reciprocal product.
The system/span discussion on pp. 68–69 and Proposition 2.19 motivate the
annihilator subspaces and dimension-complement laws below (ledger X58–X59 and
X61–X63, restricted to coordinates rather than geometric screw representatives).

These results use the actual force/velocity pairing `Wrench.pair`, without a
positive-definite metric on mixed coordinates. All real coordinate vectors,
including zero and dependent generators, are allowed. Geometric axis distance,
angle, and pitch formulas (X60) are outside this module. Zero power characterizes
an algebraic annihilator; no contact feasibility or possible finite motion is
inferred. The common frame, torque origin, and compatible units are external
conventions, as in the wrench module.

Twists and wrenches are distinct types. The reciprocal product reads a twist as
a wrench through the named coordinate swap `Twist.swapWrench`, not through a type
identity.
-/

noncomputable section

namespace RoboLean

namespace Wrench

/-- Coordinate reciprocity, MLS printed p. 66: a wrench does zero instantaneous
power on a twist. -/
def Reciprocal (F : Wrench) (ξ : Twist) : Prop := pair F ξ = 0

/-- Reciprocity is preserved by compatible wrench transfer and twist adjoint,
MLS printed pp. 63 and 66. -/
theorem reciprocal_transform_adjoint_iff (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    Reciprocal (transform g F) (Twist.adjoint g ξ) ↔ Reciprocal F ξ := by
  simp only [Reciprocal, pair_transform_adjoint]

/-- The pairing map from wrenches to the dual of twists is injective
(MLS printed p. 62, equivalent wrenches). -/
theorem pairing_injective : Function.Injective pairing := by
  intro F G h
  apply ext_pair
  intro ξ
  exact congrArg (fun φ : Module.Dual ℝ Twist => φ ξ) h

/-- The independently defined power pairing identifies wrenches with the full
algebraic dual of twists (MLS printed pp. 61 and 68). This is not a claim about
a physical norm. -/
def pairingEquiv : Wrench ≃ₗ[ℝ] Module.Dual ℝ Twist :=
  pairing.linearEquivOfInjective pairing_injective
    (by simp [finrank_eq_six, Twist, Vec3, Module.finrank_prod])

/-- `pairingEquiv` evaluates to the pairing (MLS printed p. 61). -/
@[simp] theorem pairingEquiv_apply (F : Wrench) (ξ : Twist) :
    pairingEquiv F ξ = pair F ξ := rfl

end Wrench

namespace Twist

/-- The same pairing identifies twists with the algebraic dual of wrenches
(MLS printed pp. 61 and 68). -/
def pairingEquiv : Twist ≃ₗ[ℝ] Module.Dual ℝ Wrench :=
  Wrench.pairing.flip.linearEquivOfInjective (by
    intro ξ η h
    apply Prod.ext
    · apply ext_inner_left ℝ
      intro v
      have hv := congrArg (fun φ : Module.Dual ℝ Wrench => φ ⟨v, 0⟩) h
      simpa [Wrench.pair, linear, angular] using hv
    · apply ext_inner_left ℝ
      intro ω
      have hω := congrArg (fun φ : Module.Dual ℝ Wrench => φ ⟨0, ω⟩) h
      simpa [Wrench.pair, linear, angular] using hω)
    (by simp [Wrench.finrank_eq_six, Twist, Vec3, Module.finrank_prod])

/-- `Twist.pairingEquiv` evaluates to the pairing (MLS printed p. 61). -/
@[simp] theorem pairingEquiv_apply (ξ : Twist) (F : Wrench) :
    pairingEquiv ξ F = Wrench.pair F ξ := rfl

/-- The coordinate swap behind the reciprocal product, MLS printed pp. 66–67:
twist coordinates `(v, ω)` are read as the wrench `(ω, v)`, with force from the
angular part and moment from the linear part. In the proof of Proposition 2.18
(printed p. 67) the twist about a finite screw and the wrench along it have
exactly these swapped components. This is a named linear identification between
two distinct types, not a type identity; it carries no frame, unit, or physical
meaning of its own. -/
def swapWrench : Twist ≃ₗ[ℝ] Wrench where
  toFun ξ := ⟨ξ.angular, ξ.linear⟩
  invFun F := (F.torque, F.force)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The swapped wrench's force is the twist's angular part (MLS printed p. 67). -/
@[simp] theorem swapWrench_force (ξ : Twist) : (swapWrench ξ).force = ξ.angular := rfl

/-- The swapped wrench's moment is the twist's linear part (MLS printed p. 67). -/
@[simp] theorem swapWrench_torque (ξ : Twist) : (swapWrench ξ).torque = ξ.linear := rfl

/-- The inverse swap reads a wrench `(f, τ)` as twist coordinates `(τ, f)`
(MLS printed p. 67). -/
@[simp] theorem swapWrench_symm_apply (F : Wrench) :
    swapWrench.symm F = (F.torque, F.force) := rfl

/-- MLS p. 67 reciprocal product, defined through the actual wrench pairing. -/
def reciprocalProduct (ξ η : Twist) : ℝ := Wrench.pair (swapWrench ξ) η

/-- The reciprocal product in coordinates, `v₁ · ω₂ + v₂ · ω₁`, MLS printed p. 67. -/
theorem reciprocalProduct_eq (ξ η : Twist) :
    reciprocalProduct ξ η = inner ℝ ξ.linear η.angular + inner ℝ η.linear ξ.angular := by
  change inner ℝ ξ.angular η.linear + inner ℝ ξ.linear η.angular = _
  rw [real_inner_comm ξ.angular η.linear, add_comm]

/-- The reciprocal product as a bilinear map (MLS printed p. 67); it is not a
positive inner product. -/
def reciprocalForm : Twist →ₗ[ℝ] Module.Dual ℝ Twist :=
  Wrench.pairing.comp swapWrench.toLinearMap

/-- `reciprocalForm` evaluates to the reciprocal product (MLS printed p. 67). -/
@[simp] theorem reciprocalForm_apply (ξ η : Twist) :
    reciprocalForm ξ η = reciprocalProduct ξ η := rfl

/-- The reciprocal product is symmetric (MLS printed p. 67). -/
theorem reciprocalProduct_symm (ξ η : Twist) :
    reciprocalProduct ξ η = reciprocalProduct η ξ := by
  rw [reciprocalProduct_eq, reciprocalProduct_eq, add_comm]

/-- The reciprocal product is additive in its first argument (MLS printed pp. 67–68). -/
theorem reciprocalProduct_add_left (ξ η ζ : Twist) :
    reciprocalProduct (ξ + η) ζ = reciprocalProduct ξ ζ + reciprocalProduct η ζ :=
  congrArg (fun φ : Module.Dual ℝ Twist => φ ζ) (reciprocalForm.map_add ξ η)

/-- The reciprocal product is homogeneous in its first argument (MLS printed pp. 67–68). -/
theorem reciprocalProduct_smul_left (c : ℝ) (ξ η : Twist) :
    reciprocalProduct (c • ξ) η = c * reciprocalProduct ξ η :=
  congrArg (fun φ : Module.Dual ℝ Twist => φ η) (reciprocalForm.map_smul c ξ)

/-- The reciprocal product is additive in its second argument (MLS printed pp. 67–68). -/
theorem reciprocalProduct_add_right (ξ η ζ : Twist) :
    reciprocalProduct ξ (η + ζ) = reciprocalProduct ξ η + reciprocalProduct ξ ζ :=
  (reciprocalForm ξ).map_add η ζ

/-- The reciprocal product is homogeneous in its second argument (MLS printed pp. 67–68). -/
theorem reciprocalProduct_smul_right (ξ η : Twist) (c : ℝ) :
    reciprocalProduct ξ (c • η) = c * reciprocalProduct ξ η :=
  (reciprocalForm ξ).map_smul c η

/-- The reciprocal form is nondegenerate via an explicit coordinate swap and
the independently established wrench-to-dual equivalence (MLS printed p. 67). -/
def reciprocalDualEquiv : Twist ≃ₗ[ℝ] Module.Dual ℝ Twist :=
  swapWrench.trans Wrench.pairingEquiv

/-- `reciprocalDualEquiv` evaluates to the reciprocal product (MLS printed p. 67). -/
@[simp] theorem reciprocalDualEquiv_apply (ξ η : Twist) :
    reciprocalDualEquiv ξ η = reciprocalProduct ξ η := rfl

/-- Only the zero twist has zero reciprocal product with every twist
(MLS printed p. 67). -/
theorem reciprocalProduct_nondegenerate (ξ : Twist) :
    (∀ η, reciprocalProduct ξ η = 0) ↔ ξ = 0 := by
  constructor
  · intro h
    apply reciprocalDualEquiv.injective
    rw [map_zero]
    apply LinearMap.ext
    intro η
    exact h η
  · rintro rfl
    intro η
    change reciprocalDualEquiv 0 η = 0
    rw [map_zero]
    rfl

/-- Pure linear coordinates have zero reciprocal product with themselves,
regardless of their Euclidean length (MLS printed p. 67). -/
@[simp] theorem reciprocalProduct_pureLinear_self (v : Vec3) :
    reciprocalProduct (v, 0) (v, 0) = 0 := by
  simp [reciprocalProduct_eq, linear, angular]

/-- The algebraic twist-coordinate space has dimension six (MLS printed p. 69). -/
theorem finrank_eq_six : Module.finrank ℝ Twist = 6 := by
  simp [Twist, Vec3, Module.finrank_prod]

end Twist

namespace Reciprocal

/-- Wrenches doing zero power against every twist in a system
(MLS printed pp. 68–69, reciprocal screw system). -/
def wrenches (S : Submodule ℝ Twist) : Submodule ℝ Wrench :=
  S.dualAnnihilator.comap Wrench.pairing

/-- Twists doing zero power against every wrench in a system
(MLS printed pp. 68–69, reciprocal screw system). -/
def twists (T : Submodule ℝ Wrench) : Submodule ℝ Twist :=
  T.dualAnnihilator.comap Wrench.pairing.flip

/-- Membership in the reciprocal wrench system is zero power against every
system twist (MLS printed pp. 68–69). -/
theorem mem_wrenches (S : Submodule ℝ Twist) (F : Wrench) :
    F ∈ wrenches S ↔ ∀ ξ ∈ S, Wrench.pair F ξ = 0 := by
  exact Submodule.mem_dualAnnihilator (W := S) (Wrench.pairing F)

/-- Membership in the reciprocal twist system is zero power against every
system wrench (MLS printed pp. 68–69). -/
theorem mem_twists (T : Submodule ℝ Wrench) (ξ : Twist) :
    ξ ∈ twists T ↔ ∀ F ∈ T, Wrench.pair F ξ = 0 := by
  exact Submodule.mem_dualAnnihilator (W := T) (Wrench.pairing.flip ξ)

/-- Reciprocity against any generating set is equivalent to reciprocity
against its linear span (MLS printed p. 68); no rank or independence assumption
is required. -/
theorem mem_wrenches_span (s : Set Twist) (F : Wrench) :
    F ∈ wrenches (Submodule.span ℝ s) ↔ ∀ ξ ∈ s, Wrench.pair F ξ = 0 := by
  rw [mem_wrenches]
  constructor
  · intro h ξ hξ
    exact h ξ (Submodule.subset_span hξ)
  · intro h
    have hle : Submodule.span ℝ s ≤ (Wrench.pairing F).ker := Submodule.span_le.mpr h
    intro ξ hξ
    exact hle hξ

/-- The generator criterion also holds when the supplied system consists of
wrenches (MLS printed p. 68). -/
theorem mem_twists_span (s : Set Wrench) (ξ : Twist) :
    ξ ∈ twists (Submodule.span ℝ s) ↔ ∀ F ∈ s, Wrench.pair F ξ = 0 := by
  rw [mem_twists]
  constructor
  · intro h F hF
    exact h F (Submodule.subset_span hF)
  · intro h
    have hle : Submodule.span ℝ s ≤ (Wrench.pairing.flip ξ).ker := Submodule.span_le.mpr h
    intro F hF
    exact hle hF

/-- Taking the reciprocal system twice recovers the original twist subspace
(MLS printed pp. 68–69). -/
@[simp] theorem twists_wrenches (S : Submodule ℝ Twist) : twists (wrenches S) = S := by
  ext ξ
  rw [mem_twists]
  constructor
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S ξ).mp
    intro φ hφ
    obtain ⟨F, rfl⟩ := Wrench.pairingEquiv.surjective φ
    exact h F hφ
  · intro hξ F hF
    exact (mem_wrenches S F).mp hF ξ hξ

/-- Taking the reciprocal system twice also recovers any wrench subspace
(MLS printed pp. 68–69). -/
@[simp] theorem wrenches_twists (T : Submodule ℝ Wrench) : wrenches (twists T) = T := by
  ext F
  rw [mem_wrenches]
  constructor
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff T F).mp
    intro φ hφ
    obtain ⟨ξ, rfl⟩ := Twist.pairingEquiv.surjective φ
    exact h ξ hφ
  · intro hF ξ hξ
    exact (mem_twists T ξ).mp hξ F hF

/-- The reciprocal wrench space is exactly the usual algebraic annihilator,
transported through the actual power pairing (MLS printed pp. 68–69). -/
def wrenchesAnnihilatorEquiv (S : Submodule ℝ Twist) :
    wrenches S ≃ₗ[ℝ] S.dualAnnihilator :=
  LinearEquiv.ofSubmodule' Wrench.pairingEquiv S.dualAnnihilator

/-- The reciprocal twist space is likewise an algebraic annihilator
(MLS printed pp. 68–69). -/
def twistsAnnihilatorEquiv (T : Submodule ℝ Wrench) :
    twists T ≃ₗ[ℝ] T.dualAnnihilator :=
  LinearEquiv.ofSubmodule' Twist.pairingEquiv T.dualAnnihilator

/-- MLS Proposition 2.19, printed p. 69, for a twist system and its reciprocal
wrench system. -/
theorem finrank_add_finrank_wrenches (S : Submodule ℝ Twist) :
    Module.finrank ℝ S + Module.finrank ℝ (wrenches S) = 6 := by
  rw [(wrenchesAnnihilatorEquiv S).finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, Twist.finrank_eq_six]

/-- MLS Proposition 2.19, printed p. 69, for a wrench system and its reciprocal
twist system. -/
theorem finrank_add_finrank_twists (T : Submodule ℝ Wrench) :
    Module.finrank ℝ T + Module.finrank ℝ (twists T) = 6 := by
  rw [(twistsAnnihilatorEquiv T).finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq]
  exact Wrench.finrank_eq_six

end Reciprocal

end RoboLean
