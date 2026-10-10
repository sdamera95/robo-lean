import RoboLean.Geometry.Hat
import RoboLean.Geometry.Homogeneous

/-!
# Twist coordinates and their homogeneous matrices

MLS §2.3.2, printed pp. 40–41, equations (2.29)–(2.31), distinguishes
twist coordinates `(v, ω)` from the matrix `[hat ω, v; 0, 0]`. The matrix
carrier below is defined independently by skew symmetry and a zero bottom row.
No normalization or nonzero assumption is imposed on either component.

`Twist` is a structure with fields `linear` and `angular`, so it is a type
distinct from `Vec3 × Vec3` and from `Wrench`: a pair of vectors is rejected
where a twist is expected. Its additive group and real vector space structures
are componentwise, transported from `Vec3 × Vec3` along a private component map.
No coercion to or from `Vec3 × Vec3` and no norm or topology are declared.
-/

noncomputable section

namespace RoboLean

open Matrix

/-- Twist coordinates `ξ = (v, ω) ∈ ℝ⁶`, MLS printed p. 41, equation (2.30): the
linear component `v` followed by the angular component `ω`. This is a structure,
hence a type distinct from `Vec3 × Vec3` and from `Wrench`; frames and units are
conventions not enforced by this type, and no norm is declared on it. -/
@[ext]
structure Twist where
  /-- Build a twist from its linear and angular coordinates `(v, ω)`, MLS printed
  p. 41, equation (2.30). -/
  mk ::
  /-- Linear coordinates `v` in the ordering `(v, ω)`, MLS printed p. 41,
  equation (2.30). -/
  linear : Vec3
  /-- Angular coordinates `ω` in the ordering `(v, ω)`, MLS printed p. 41,
  equation (2.30). -/
  angular : Vec3

/-- Two twists are equal when their linear and angular coordinates are equal
(MLS printed p. 41, twist coordinates `(v, ω)`). -/
add_decl_doc Twist.ext

/-- Twists are equal exactly when their linear and angular coordinates are equal
(MLS printed p. 41, twist coordinates `(v, ω)`). -/
add_decl_doc Twist.ext_iff

namespace Twist

/-- The zero twist, with zero linear and angular coordinates (MLS printed p. 41,
twist coordinates). -/
instance instZero : Zero Twist := ⟨⟨0, 0⟩⟩

/-- Componentwise sum of twist coordinates (MLS printed p. 41, twist coordinates). -/
instance instAdd : Add Twist := ⟨fun ξ η => ⟨ξ.linear + η.linear, ξ.angular + η.angular⟩⟩

/-- Componentwise negation of twist coordinates (MLS printed p. 41, twist coordinates). -/
instance instNeg : Neg Twist := ⟨fun ξ => ⟨-ξ.linear, -ξ.angular⟩⟩

/-- Componentwise difference of twist coordinates (MLS printed p. 41, twist coordinates). -/
instance instSub : Sub Twist := ⟨fun ξ η => ⟨ξ.linear - η.linear, ξ.angular - η.angular⟩⟩

/-- Componentwise scalar action on both twist components, for every scalar type
acting on `Vec3` (MLS printed p. 41, twist coordinates). -/
instance instSMul {R : Type*} [SMul R Vec3] : SMul R Twist :=
  ⟨fun c ξ => ⟨c • ξ.linear, c • ξ.angular⟩⟩

/-- The zero twist has zero linear part (MLS printed p. 41, twist coordinates). -/
@[simp] theorem zero_linear : (0 : Twist).linear = 0 := rfl

/-- The zero twist has zero angular part (MLS printed p. 41, twist coordinates). -/
@[simp] theorem zero_angular : (0 : Twist).angular = 0 := rfl

/-- Linear parts add under the componentwise sum (MLS printed p. 41, twist coordinates). -/
@[simp] theorem add_linear (ξ η : Twist) : (ξ + η).linear = ξ.linear + η.linear := rfl

/-- Angular parts add under the componentwise sum (MLS printed p. 41, twist coordinates). -/
@[simp] theorem add_angular (ξ η : Twist) : (ξ + η).angular = ξ.angular + η.angular := rfl

/-- Negation negates the linear part (MLS printed p. 41, twist coordinates). -/
@[simp] theorem neg_linear (ξ : Twist) : (-ξ).linear = -ξ.linear := rfl

/-- Negation negates the angular part (MLS printed p. 41, twist coordinates). -/
@[simp] theorem neg_angular (ξ : Twist) : (-ξ).angular = -ξ.angular := rfl

/-- Linear parts subtract under the componentwise difference (MLS printed p. 41,
twist coordinates). -/
@[simp] theorem sub_linear (ξ η : Twist) : (ξ - η).linear = ξ.linear - η.linear := rfl

/-- Angular parts subtract under the componentwise difference (MLS printed p. 41,
twist coordinates). -/
@[simp] theorem sub_angular (ξ η : Twist) : (ξ - η).angular = ξ.angular - η.angular := rfl

/-- A scalar scales the linear part (MLS printed p. 41, twist coordinates). -/
@[simp] theorem smul_linear {R : Type*} [SMul R Vec3] (c : R) (ξ : Twist) :
    (c • ξ).linear = c • ξ.linear := rfl

/-- A scalar scales the angular part (MLS printed p. 41, twist coordinates). -/
@[simp] theorem smul_angular {R : Type*} [SMul R Vec3] (c : R) (ξ : Twist) :
    (c • ξ).angular = c • ξ.angular := rfl

/-- A twist built from zero components is the zero twist (MLS printed p. 41,
twist coordinates). -/
@[simp] theorem mk_zero_zero : (⟨0, 0⟩ : Twist) = 0 := rfl

/-- A twist built from components is zero exactly when both components are zero
(MLS printed p. 41, twist coordinates). -/
@[simp] theorem mk_eq_zero (v ω : Vec3) : (⟨v, ω⟩ : Twist) = 0 ↔ v = 0 ∧ ω = 0 :=
  Twist.mk.injEq v ω 0 0 ▸ Iff.rfl

/-- Component pair, used only to transport algebraic structure. It is not a
public identification of twists with pairs. -/
private def toProd (ξ : Twist) : Vec3 × Vec3 := (ξ.linear, ξ.angular)

private theorem toProd_injective : Function.Injective toProd := fun _ _ h =>
  Twist.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The componentwise additive group of twists, transported from `Vec3 × Vec3`
(MLS printed p. 41, `ξ ∈ ℝ⁶`). -/
instance instAddCommGroup : AddCommGroup Twist :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The componentwise real vector space of twists, transported from `Vec3 × Vec3`
(MLS printed p. 41, `ξ ∈ ℝ⁶`). -/
instance instModule : Module ℝ Twist :=
  Function.Injective.module ℝ (AddMonoidHom.mk' toProd fun _ _ => rfl) toProd_injective
    fun _ _ => rfl

/-- Linear version of the component pair, used only for finite-dimensionality. -/
private def toProdLinearEquiv : Twist ≃ₗ[ℝ] Vec3 × Vec3 where
  toFun := toProd
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Twists form a finite-dimensional real vector space (MLS printed p. 41, `ξ ∈ ℝ⁶`). -/
instance instFiniteDimensional : FiniteDimensional ℝ Twist :=
  Module.Finite.equiv toProdLinearEquiv.symm

/-- The linear part of a finite sum of twists is the sum of the linear parts
(MLS printed p. 41, twist coordinates). -/
theorem sum_linear {ι : Type*} (s : Finset ι) (f : ι → Twist) :
    (∑ i ∈ s, f i).linear = ∑ i ∈ s, (f i).linear :=
  map_sum (AddMonoidHom.mk' linear fun _ _ => rfl) f s

/-- The angular part of a finite sum of twists is the sum of the angular parts
(MLS printed p. 41, twist coordinates). -/
theorem sum_angular {ι : Type*} (s : Finset ι) (f : ι → Twist) :
    (∑ i ∈ s, f i).angular = ∑ i ∈ s, (f i).angular :=
  map_sum (AddMonoidHom.mk' angular fun _ _ => rfl) f s

end Twist

/-- The independent real matrix submodule `se(3)`, MLS equation (2.29), p. 40, in the
homogeneous form `[ω̂, v; 0, 0]` printed there: upper-left skew block (`so(3)`, equation
(2.10), p. 28), unrestricted translation column, and both lower blocks zero. -/
def se3Submodule : Submodule ℝ HomogeneousMatrix where
  carrier := { M | M.toBlocks₁₁ᵀ = -M.toBlocks₁₁ ∧
    M.toBlocks₂₁ = 0 ∧ M.toBlocks₂₂ = 0 }
  zero_mem' := by
    refine ⟨?_, rfl, rfl⟩
    ext i j
    simp [Matrix.toBlocks₁₁]
  add_mem' := by
    intro A B hA hB
    refine ⟨?_, ?_, ?_⟩
    · change (A.toBlocks₁₁ + B.toBlocks₁₁)ᵀ = -(A.toBlocks₁₁ + B.toBlocks₁₁)
      rw [Matrix.transpose_add, hA.1, hB.1, neg_add]
    · change A.toBlocks₂₁ + B.toBlocks₂₁ = 0
      rw [hA.2.1, hB.2.1, add_zero]
    · change A.toBlocks₂₂ + B.toBlocks₂₂ = 0
      rw [hA.2.2, hB.2.2, add_zero]
  smul_mem' := by
    intro c A hA
    refine ⟨?_, ?_, ?_⟩
    · change (c • A.toBlocks₁₁)ᵀ = -(c • A.toBlocks₁₁)
      rw [Matrix.transpose_smul, hA.1, smul_neg]
    · change c • A.toBlocks₂₁ = 0
      rw [hA.2.1, smul_zero]
    · change c • A.toBlocks₂₂ = 0
      rw [hA.2.2, smul_zero]

/-- Matrices in the independently defined `se(3)` submodule: the twists `ξ̂` of MLS p. 41,
elements of `se(3)` as in equation (2.29), p. 40. -/
abbrev Se3 := ↥se3Submodule

/-- Membership in `se(3)`, MLS equation (2.29), p. 40: a skew upper-left block (`so(3)`,
equation (2.10), p. 28) and a zero bottom row. -/
theorem mem_se3Submodule_iff (M : HomogeneousMatrix) :
    M ∈ se3Submodule ↔ M.toBlocks₁₁ᵀ = -M.toBlocks₁₁ ∧
      M.toBlocks₂₁ = 0 ∧ M.toBlocks₂₂ = 0 := Iff.rfl

namespace Twist

/-- Homogeneous twist matrix `ξ̂ = [ω̂, v; 0, 0]`, the wedge of MLS equation (2.31), p. 41.
Its last entry is zero. -/
def hat (ξ : Twist) : HomogeneousMatrix :=
  fromBlocks (Vec3.hat ξ.angular) (Matrix.of fun i _ => ξ.linear i) 0 0

/-- Extract linear and axial coordinates, the vee of MLS equation (2.30), p. 41.
The reverse inverse law requires the `se(3)` block conditions. -/
def vee (M : HomogeneousMatrix) : Twist :=
  ⟨WithLp.toLp 2 (fun i => M (Sum.inl i) (Sum.inr 0)), Vec3.vee M.toBlocks₁₁⟩

/-- The upper-left block of `ξ̂` is `ω̂`, MLS equation (2.31), p. 41. -/
@[simp]
theorem hat_angular (ξ : Twist) : ξ.hat.toBlocks₁₁ = Vec3.hat ξ.angular := rfl

/-- The translation column of `ξ̂` holds the linear coordinates `v`, MLS equation (2.31),
p. 41. -/
@[simp]
theorem hat_linear (ξ : Twist) (i : Fin 3) :
    ξ.hat (Sum.inl i) (Sum.inr 0) = ξ.linear i := rfl

/-- The lower-left block of `ξ̂` is zero, MLS equation (2.31), p. 41. -/
@[simp]
theorem hat_lowerLeft (ξ : Twist) : ξ.hat.toBlocks₂₁ = 0 := rfl

/-- The lower-right entry of `ξ̂` is zero, MLS equation (2.31), p. 41. -/
@[simp]
theorem hat_lowerRight (ξ : Twist) : ξ.hat.toBlocks₂₂ = 0 := rfl

/-- The wedge of MLS equation (2.31), p. 41, forms a matrix in `se(3)` (equation (2.29),
p. 40) out of any twist coordinates. -/
theorem hat_mem_se3Submodule (ξ : Twist) : ξ.hat ∈ se3Submodule :=
  ⟨Vec3.hat_transpose ξ.angular, rfl, rfl⟩

/-- The vee (2.30) inverts the wedge (2.31), MLS p. 41. -/
@[simp]
theorem vee_hat (ξ : Twist) : vee ξ.hat = ξ := by
  apply Twist.ext
  · rfl
  · exact Vec3.vee_hat ξ.angular

/-- The wedge (2.31) inverts the vee (2.30) on `se(3)`, MLS p. 41. The reverse inverse uses
skew symmetry and the zero bottom row explicitly. -/
theorem hat_vee (M : HomogeneousMatrix) (h : M ∈ se3Submodule) :
    (vee M).hat = M := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨Vec3.hat_vee M.toBlocks₁₁ h.1, ?_, h.2.1.symm, h.2.2.symm⟩
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

/-- Supporting lemma; no direct MLS counterpart. The wedge (2.31), p. 41, is additive; MLS states
the `so(3)` analogue `(v + w)^ = v̂ + ŵ` on p. 28. -/
@[simp]
theorem hat_add (ξ η : Twist) : (ξ + η).hat = ξ.hat + η.hat := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨Vec3.hat_add _ _, ?_, ?_, ?_⟩
  · rfl
  · change (0 : Matrix (Fin 1) (Fin 3) ℝ) = 0 + 0
    rw [add_zero]
  · change (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 + 0
    rw [add_zero]

/-- Supporting lemma; no direct MLS counterpart. The wedge (2.31), p. 41, commutes with real
scalars; supports the linear identification `hatLinearEquiv`. -/
@[simp]
theorem hat_smul (c : ℝ) (ξ : Twist) : (c • ξ).hat = c • ξ.hat := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨Vec3.hat_smul _ _, ?_, ?_, ?_⟩
  · rfl
  · change (0 : Matrix (Fin 1) (Fin 3) ℝ) = c • 0
    rw [smul_zero]
  · change (0 : Matrix (Fin 1) (Fin 1) ℝ) = c • 0
    rw [smul_zero]

/-- Hat and vee identify all twist coordinates `ξ ∈ ℝ⁶` with the independent matrix
carrier `se(3)`, as real vector spaces, MLS p. 41, equations (2.30)–(2.31); this includes zero
and arbitrary axes. -/
def hatLinearEquiv : Twist ≃ₗ[ℝ] Se3 where
  toFun ξ := ⟨ξ.hat, hat_mem_se3Submodule ξ⟩
  invFun M := vee M.val
  left_inv := vee_hat
  right_inv M := Subtype.ext (hat_vee M.val M.property)
  map_add' ξ η := Subtype.ext (hat_add ξ η)
  map_smul' c ξ := Subtype.ext (hat_smul c ξ)

/-- The forward map of `hatLinearEquiv` is the wedge, MLS equation (2.31), p. 41. -/
@[simp]
theorem hatLinearEquiv_apply (ξ : Twist) :
    (hatLinearEquiv ξ).val = ξ.hat := rfl

/-- The inverse map of `hatLinearEquiv` is the vee, MLS equation (2.30), p. 41. -/
@[simp]
theorem hatLinearEquiv_symm_apply (M : Se3) :
    hatLinearEquiv.symm M = vee M.val := rfl

/-- Supporting lemma; no direct MLS counterpart. The wedge (2.31), p. 41, sends the zero twist to
the zero matrix; a consequence of its linearity. -/
@[simp]
theorem hat_zero : (0 : Twist).hat = 0 :=
  congrArg Subtype.val hatLinearEquiv.map_zero

/-- Supporting lemma; no direct MLS counterpart. The wedge (2.31), p. 41, commutes with negation; a
consequence of its linearity. -/
@[simp]
theorem hat_neg (ξ : Twist) : (-ξ).hat = -ξ.hat :=
  congrArg Subtype.val (hatLinearEquiv.map_neg ξ)

/-- The wedge (2.31) is injective, since the vee (2.30) inverts it, MLS p. 41. -/
theorem hat_injective : Function.Injective hat := by
  intro ξ η h
  simpa only [vee_hat] using congrArg vee h

/-- Acting on point coordinates produces the homogeneous velocity vector
`(ω × q + v, 0)`, as in MLS pp. 39–40, equations (2.25)–(2.28). -/
theorem hat_mulVec_point (ξ : Twist) (q : Vec3) :
    ξ.hat *ᵥ homogeneousPoint q =
      homogeneousVector (Vec3.cross ξ.angular q + ξ.linear) := by
  rw [hat, Matrix.fromBlocks_mulVec]
  have hcross := Vec3.hat_mulVec ξ.angular q
  funext i
  cases i with
  | inl i =>
    have hi := congrArg (fun x : ℝ => x + ξ.linear i) (congrFun hcross i)
    simpa [homogeneousPoint, homogeneousVector, Matrix.mulVec, dotProduct,
      Matrix.of_apply] using hi
  | inr i =>
    simp [homogeneousPoint, homogeneousVector, Matrix.zero_mulVec]

end Twist
end RoboLean
