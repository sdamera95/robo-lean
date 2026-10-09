import RoboLean.Geometry.Hat
import RoboLean.Geometry.Homogeneous

/-!
# Twist coordinates and their homogeneous matrices

MLS §2.3.2, printed pp. 40–41, equations (2.29)–(2.31), distinguishes
twist coordinates `(v, ω)` from the matrix `[hat ω, v; 0, 0]`. The matrix
carrier below is defined independently by skew symmetry and a zero bottom row.
No normalization or nonzero assumption is imposed on either component.
-/

noncomputable section

namespace RoboLean

open Matrix

/-- Twist coordinates, with the linear component before the angular component.
The product module is algebraic; its norm is not a physical twist magnitude. -/
abbrev Twist := Vec3 × Vec3

/-- The independent real matrix submodule `se(3)`: upper-left skew block,
unrestricted translation column, and both lower blocks zero. -/
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

/-- Matrices in the independently defined `se(3)` submodule. -/
abbrev Se3 := ↥se3Submodule

theorem mem_se3Submodule_iff (M : HomogeneousMatrix) :
    M ∈ se3Submodule ↔ M.toBlocks₁₁ᵀ = -M.toBlocks₁₁ ∧
      M.toBlocks₂₁ = 0 ∧ M.toBlocks₂₂ = 0 := Iff.rfl

namespace Twist

/-- Linear coordinates `v` in the ordering `(v, ω)`. -/
abbrev linear (ξ : Twist) : Vec3 := ξ.1

/-- Angular coordinates `ω` in the ordering `(v, ω)`. -/
abbrev angular (ξ : Twist) : Vec3 := ξ.2

/-- Homogeneous twist matrix, MLS equation (2.31). Its last entry is zero. -/
def hat (ξ : Twist) : HomogeneousMatrix :=
  fromBlocks (Vec3.hat ξ.angular) (Matrix.of fun i _ => ξ.linear i) 0 0

/-- Extract linear and axial coordinates, MLS equation (2.30).
The reverse inverse law requires the `se(3)` block conditions. -/
def vee (M : HomogeneousMatrix) : Twist :=
  (WithLp.toLp 2 (fun i => M (Sum.inl i) (Sum.inr 0)), Vec3.vee M.toBlocks₁₁)

@[simp]
theorem hat_angular (ξ : Twist) : ξ.hat.toBlocks₁₁ = Vec3.hat ξ.angular := rfl

@[simp]
theorem hat_linear (ξ : Twist) (i : Fin 3) :
    ξ.hat (Sum.inl i) (Sum.inr 0) = ξ.linear i := rfl

@[simp]
theorem hat_lowerLeft (ξ : Twist) : ξ.hat.toBlocks₂₁ = 0 := rfl

@[simp]
theorem hat_lowerRight (ξ : Twist) : ξ.hat.toBlocks₂₂ = 0 := rfl

theorem hat_mem_se3Submodule (ξ : Twist) : ξ.hat ∈ se3Submodule :=
  ⟨Vec3.hat_transpose ξ.angular, rfl, rfl⟩

@[simp]
theorem vee_hat (ξ : Twist) : vee ξ.hat = ξ := by
  apply Prod.ext
  · rfl
  · exact Vec3.vee_hat ξ.angular

/-- The reverse inverse uses skew symmetry and the zero bottom row explicitly. -/
theorem hat_vee (M : HomogeneousMatrix) (h : M ∈ se3Submodule) :
    (vee M).hat = M := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨Vec3.hat_vee M.toBlocks₁₁ h.1, ?_, h.2.1.symm, h.2.2.symm⟩
  ext i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

@[simp]
theorem hat_add (ξ η : Twist) : (ξ + η).hat = ξ.hat + η.hat := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨Vec3.hat_add _ _, ?_, ?_, ?_⟩
  · rfl
  · change (0 : Matrix (Fin 1) (Fin 3) ℝ) = 0 + 0
    rw [add_zero]
  · change (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 + 0
    rw [add_zero]

@[simp]
theorem hat_smul (c : ℝ) (ξ : Twist) : (c • ξ).hat = c • ξ.hat := by
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨Vec3.hat_smul _ _, ?_, ?_, ?_⟩
  · rfl
  · change (0 : Matrix (Fin 1) (Fin 3) ℝ) = c • 0
    rw [smul_zero]
  · change (0 : Matrix (Fin 1) (Fin 1) ℝ) = c • 0
    rw [smul_zero]

/-- Hat and vee identify all twist coordinates with the independent matrix
carrier, as real vector spaces; this includes zero and arbitrary axes. -/
def hatLinearEquiv : Twist ≃ₗ[ℝ] Se3 where
  toFun ξ := ⟨ξ.hat, hat_mem_se3Submodule ξ⟩
  invFun M := vee M.val
  left_inv := vee_hat
  right_inv M := Subtype.ext (hat_vee M.val M.property)
  map_add' ξ η := Subtype.ext (hat_add ξ η)
  map_smul' c ξ := Subtype.ext (hat_smul c ξ)

@[simp]
theorem hatLinearEquiv_apply (ξ : Twist) :
    (hatLinearEquiv ξ).val = ξ.hat := rfl

@[simp]
theorem hatLinearEquiv_symm_apply (M : Se3) :
    hatLinearEquiv.symm M = vee M.val := rfl

@[simp]
theorem hat_zero : (0 : Twist).hat = 0 :=
  congrArg Subtype.val hatLinearEquiv.map_zero

@[simp]
theorem hat_neg (ξ : Twist) : (-ξ).hat = -ξ.hat :=
  congrArg Subtype.val (hatLinearEquiv.map_neg ξ)

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
