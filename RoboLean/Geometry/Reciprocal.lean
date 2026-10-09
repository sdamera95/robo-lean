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
-/

noncomputable section

namespace RoboLean

namespace Wrench

/-- Coordinate reciprocity: a wrench does zero instantaneous power on a twist. -/
def Reciprocal (F : Wrench) (ξ : Twist) : Prop := pair F ξ = 0

theorem reciprocal_transform_adjoint_iff (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    Reciprocal (transform g F) (Twist.adjoint g ξ) ↔ Reciprocal F ξ := by
  simp only [Reciprocal, pair_transform_adjoint]

theorem pairing_injective : Function.Injective pairing := by
  intro F G h
  apply ext_pair
  intro ξ
  exact congrArg (fun φ : Module.Dual ℝ Twist => φ ξ) h

/-- The independently defined power pairing identifies wrenches with the full
algebraic dual of twists. This is not a claim about a physical norm. -/
def pairingEquiv : Wrench ≃ₗ[ℝ] Module.Dual ℝ Twist :=
  pairing.linearEquivOfInjective pairing_injective (by simp)

@[simp] theorem pairingEquiv_apply (F : Wrench) (ξ : Twist) :
    pairingEquiv F ξ = pair F ξ := rfl

end Wrench

namespace Twist

/-- The same pairing identifies twists with the algebraic dual of wrenches. -/
def pairingEquiv : Twist ≃ₗ[ℝ] Module.Dual ℝ Wrench :=
  Wrench.pairing.flip.linearEquivOfInjective (by
    intro ξ η h
    apply Prod.ext
    · apply ext_inner_left ℝ
      intro v
      have hv := congrArg (fun φ : Module.Dual ℝ Wrench => φ (v, 0)) h
      simpa [Wrench.pair, Wrench.force, Wrench.torque, linear, angular] using hv
    · apply ext_inner_left ℝ
      intro ω
      have hω := congrArg (fun φ : Module.Dual ℝ Wrench => φ (0, ω)) h
      simpa [Wrench.pair, Wrench.force, Wrench.torque, linear, angular] using hω) (by simp)

@[simp] theorem pairingEquiv_apply (ξ : Twist) (F : Wrench) :
    pairingEquiv ξ F = Wrench.pair F ξ := rfl

/-- Coordinate swap for interpreting a twist-coordinate screw as a wrench:
angular coordinates become force, and linear coordinates become moment. -/
def swapWrench : Twist ≃ₗ[ℝ] Wrench := LinearEquiv.prodComm ℝ Vec3 Vec3

/-- MLS p. 67 reciprocal product, defined through the actual wrench pairing. -/
def reciprocalProduct (ξ η : Twist) : ℝ := Wrench.pair (swapWrench ξ) η

theorem reciprocalProduct_eq (ξ η : Twist) :
    reciprocalProduct ξ η = inner ℝ ξ.linear η.angular + inner ℝ η.linear ξ.angular := by
  change inner ℝ ξ.angular η.linear + inner ℝ ξ.linear η.angular = _
  rw [real_inner_comm ξ.angular η.linear, add_comm]

/-- The reciprocal product as a bilinear map; it is not a positive inner product. -/
def reciprocalForm : Twist →ₗ[ℝ] Module.Dual ℝ Twist :=
  Wrench.pairing.comp swapWrench.toLinearMap

@[simp] theorem reciprocalForm_apply (ξ η : Twist) :
    reciprocalForm ξ η = reciprocalProduct ξ η := rfl

theorem reciprocalProduct_symm (ξ η : Twist) :
    reciprocalProduct ξ η = reciprocalProduct η ξ := by
  rw [reciprocalProduct_eq, reciprocalProduct_eq, add_comm]

theorem reciprocalProduct_add_left (ξ η ζ : Twist) :
    reciprocalProduct (ξ + η) ζ = reciprocalProduct ξ ζ + reciprocalProduct η ζ :=
  congrArg (fun φ : Module.Dual ℝ Twist => φ ζ) (reciprocalForm.map_add ξ η)

theorem reciprocalProduct_smul_left (c : ℝ) (ξ η : Twist) :
    reciprocalProduct (c • ξ) η = c * reciprocalProduct ξ η :=
  congrArg (fun φ : Module.Dual ℝ Twist => φ η) (reciprocalForm.map_smul c ξ)

theorem reciprocalProduct_add_right (ξ η ζ : Twist) :
    reciprocalProduct ξ (η + ζ) = reciprocalProduct ξ η + reciprocalProduct ξ ζ :=
  (reciprocalForm ξ).map_add η ζ

theorem reciprocalProduct_smul_right (ξ η : Twist) (c : ℝ) :
    reciprocalProduct ξ (c • η) = c * reciprocalProduct ξ η :=
  (reciprocalForm ξ).map_smul c η

/-- The reciprocal form is nondegenerate via an explicit coordinate swap and
the independently established wrench-to-dual equivalence. -/
def reciprocalDualEquiv : Twist ≃ₗ[ℝ] Module.Dual ℝ Twist :=
  swapWrench.trans Wrench.pairingEquiv

@[simp] theorem reciprocalDualEquiv_apply (ξ η : Twist) :
    reciprocalDualEquiv ξ η = reciprocalProduct ξ η := rfl

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
regardless of their Euclidean length. -/
@[simp] theorem reciprocalProduct_pureLinear_self (v : Vec3) :
    reciprocalProduct (v, 0) (v, 0) = 0 := by
  simp [reciprocalProduct_eq, linear, angular]

/-- The algebraic twist-coordinate space has dimension six. -/
theorem finrank_eq_six : Module.finrank ℝ Twist = 6 := by
  simp [Twist, Vec3, Module.finrank_prod]

end Twist

namespace Reciprocal

/-- Wrenches doing zero power against every twist in a system. -/
def wrenches (S : Submodule ℝ Twist) : Submodule ℝ Wrench :=
  S.dualAnnihilator.comap Wrench.pairing

/-- Twists doing zero power against every wrench in a system. -/
def twists (T : Submodule ℝ Wrench) : Submodule ℝ Twist :=
  T.dualAnnihilator.comap Wrench.pairing.flip

theorem mem_wrenches (S : Submodule ℝ Twist) (F : Wrench) :
    F ∈ wrenches S ↔ ∀ ξ ∈ S, Wrench.pair F ξ = 0 := by
  exact Submodule.mem_dualAnnihilator (W := S) (Wrench.pairing F)

theorem mem_twists (T : Submodule ℝ Wrench) (ξ : Twist) :
    ξ ∈ twists T ↔ ∀ F ∈ T, Wrench.pair F ξ = 0 := by
  exact Submodule.mem_dualAnnihilator (W := T) (Wrench.pairing.flip ξ)

/-- Reciprocity against any generating set is equivalent to reciprocity
against its linear span; no rank or independence assumption is required. -/
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

/-- The generator criterion also holds when the supplied system consists of wrenches. -/
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

/-- Taking the reciprocal system twice recovers the original twist subspace. -/
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

/-- Taking the reciprocal system twice also recovers any wrench subspace. -/
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
transported through the actual power pairing. -/
def wrenchesAnnihilatorEquiv (S : Submodule ℝ Twist) :
    wrenches S ≃ₗ[ℝ] S.dualAnnihilator :=
  LinearEquiv.ofSubmodule' Wrench.pairingEquiv S.dualAnnihilator

/-- The reciprocal twist space is likewise an algebraic annihilator. -/
def twistsAnnihilatorEquiv (T : Submodule ℝ Wrench) :
    twists T ≃ₗ[ℝ] T.dualAnnihilator :=
  LinearEquiv.ofSubmodule' Twist.pairingEquiv T.dualAnnihilator

/-- MLS Proposition 2.19, for a twist system and its reciprocal wrench system. -/
theorem finrank_add_finrank_wrenches (S : Submodule ℝ Twist) :
    Module.finrank ℝ S + Module.finrank ℝ (wrenches S) = 6 := by
  rw [(wrenchesAnnihilatorEquiv S).finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, Twist.finrank_eq_six]

/-- MLS Proposition 2.19, for a wrench system and its reciprocal twist system. -/
theorem finrank_add_finrank_twists (T : Submodule ℝ Wrench) :
    Module.finrank ℝ T + Module.finrank ℝ (twists T) = 6 := by
  rw [(twistsAnnihilatorEquiv T).finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq]
  exact Twist.finrank_eq_six

end Reciprocal

end RoboLean
