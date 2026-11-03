import RoboLean.LieGroups.MatrixLieGroup

/-!
# Translations and left invariant fields on matrix groups, `X_L(G) ≅ T_eG`

MLS Appendix A, §§2.1–2.2, printed pp. 408–410. Left translation `L_g(h) = gh` and right
translation `R_g(h) = hg` (p. 408); p. 409 states `L_g ∘ L_h = L_{gh}`, `R_g ∘ R_h = R_{gh}`, the
inverses `(L_g)⁻¹ = L_{g⁻¹}`, `(R_g)⁻¹ = R_{g⁻¹}`, and that left and right translations commute.
A field `X` is left invariant if `T_hL_g X(h) = X(gh)` (p. 409); for each `ξ ∈ T_eG` the field
`X_ξ(g) = T_eL_g ξ` is left invariant, and `ρ₁(X) = X(e)`, `ρ₂(ξ) = X_ξ` are inverse linear maps, so
`X_L(G) ≅ T_eG` (p. 410).

Reading. Groups are monoids of real square matrices (in the examples, subgroups of `GL(n, ℝ)`),
the tangent map of `L_g` is `X ↦ gX` (left multiplication is linear), and a vector field on `G` is
a map from `G` to matrices. `T_eG` is a submodule `𝔤` of matrices; for the book's examples it is
the matrix Lie algebra of `RoboLean.LieGroup.matrixLieAlgebra`. The left invariant fields with
`X(e) ∈ 𝔤` form a submodule `leftInvariantFields G 𝔤`, linearly equivalent to `𝔤` by `ρ₁` with
inverse `ρ₂` (`leftInvariantFieldsEquiv`). Smoothness of the fields is not stated: a left invariant
field on a matrix group is `g ↦ gX(e)`, which is linear in `g`.

Corrected printing. With `R_g(h) = hg`, `R_g ∘ R_h = R_{hg}`, not `R_{gh}` as printed on p. 409; the
two agree only when `g` and `h` commute, and they differ for two rotations of `SO(3)` about
different axes (`rightTranslation_comp_ne`). The inverse `(R_g)⁻¹ = R_{g⁻¹}` stated after it holds.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace LieGroup

variable {M : Type*} [Monoid M]

/-- Left translation `L_g(h) = gh` (MLS p. 408). -/
def leftTranslation (g : M) (h : M) : M := g * h

/-- Right translation `R_g(h) = hg` (MLS pp. 408–409). -/
def rightTranslation (g : M) (h : M) : M := h * g

/-- MLS p. 409: `L_g ∘ L_h = L_{gh}`. -/
theorem leftTranslation_comp (g h : M) :
    leftTranslation g ∘ leftTranslation h = leftTranslation (g * h) := by
  funext x
  simp [leftTranslation, mul_assoc]

/-- MLS p. 409, corrected printing: `R_g ∘ R_h = R_{hg}` (printed `R_{gh}`). -/
theorem rightTranslation_comp (g h : M) :
    rightTranslation g ∘ rightTranslation h = rightTranslation (h * g) := by
  funext x
  simp [rightTranslation, mul_assoc]

/-- MLS p. 409: left and right translations commute, `L_g ∘ R_h = R_h ∘ L_g`. -/
theorem leftTranslation_comp_rightTranslation (g h : M) :
    leftTranslation g ∘ rightTranslation h = rightTranslation h ∘ leftTranslation g := by
  funext x
  simp [leftTranslation, rightTranslation, mul_assoc]

/-- MLS p. 409: in a group, `(L_g)⁻¹ = L_{g⁻¹}` and `(R_g)⁻¹ = R_{g⁻¹}`: the translations by `g`
and by `g⁻¹` are inverse maps on both sides. -/
theorem translation_inv {G : Type*} [Group G] (g : G) :
    leftTranslation g ∘ leftTranslation g⁻¹ = id ∧ leftTranslation g⁻¹ ∘ leftTranslation g = id ∧
      rightTranslation g ∘ rightTranslation g⁻¹ = id ∧
        rightTranslation g⁻¹ ∘ rightTranslation g = id := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext x <;> simp [leftTranslation, rightTranslation, mul_assoc]

/-- MLS p. 409, corrected printing: `R_g ∘ R_h ≠ R_{gh}` in `SO(3)`, for the quarter turns `g`
about `z` and `h` about `x` (as homogeneous rotation matrices). -/
theorem rightTranslation_comp_ne :
    ∃ g h : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      rightTranslation g ∘ rightTranslation h ≠ rightTranslation (g * h) := by
  let gz : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]
  let hx : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, -1; 0, 1, 0]
  have hgz : gz ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [gz, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [gz, Matrix.det_fin_three]
  have hhx : hx ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hx, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [hx, Matrix.det_fin_three]
  refine ⟨⟨gz, hgz⟩, ⟨hx, hhx⟩, fun hcomp => ?_⟩
  have h1 := congrArg (fun f => ((f 1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ) 0 2) hcomp
  simp [rightTranslation, gz, hx] at h1

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A field on a monoid `G` of real square matrices, a map `X : G → ℝ^{m×m}`, is **left
invariant** when `T_hL_g X(h) = X(gh)` for all `g, h ∈ G` (MLS p. 409), the tangent map of `L_g`
being left multiplication `X ↦ gX`. -/
def IsLeftInvariantOn (G : Submonoid (Matrix m m ℝ)) (X : G → Matrix m m ℝ) : Prop :=
  ∀ g h : G, X (g * h) = (g : Matrix m m ℝ) * X h

/-- **`X_L(G)`** (MLS p. 410): the left invariant fields on `G` whose value at the identity lies in
the subspace `𝔤` of matrices (read as `T_eG`), a submodule of the maps `G → ℝ^{m×m}`. -/
def leftInvariantFields (G : Submonoid (Matrix m m ℝ)) (𝔤 : Submodule ℝ (Matrix m m ℝ)) :
    Submodule ℝ (G → Matrix m m ℝ) where
  carrier := {X | IsLeftInvariantOn G X ∧ X 1 ∈ 𝔤}
  zero_mem' := ⟨fun g h => by simp, 𝔤.zero_mem⟩
  add_mem' := by
    rintro X Y ⟨hX, hX1⟩ ⟨hY, hY1⟩
    exact ⟨fun g h => by simp [hX g h, hY g h, Matrix.mul_add], 𝔤.add_mem hX1 hY1⟩
  smul_mem' := by
    rintro c X ⟨hX, hX1⟩
    exact ⟨fun g h => by simp [hX g h], 𝔤.smul_mem c hX1⟩

/-- MLS p. 410: for `ξ ∈ T_eG` the field `X_ξ(g) = T_eL_g ξ = gξ` is left invariant, and it lies in
`X_L(G)`. -/
theorem mul_mem_leftInvariantFields (G : Submonoid (Matrix m m ℝ))
    (𝔤 : Submodule ℝ (Matrix m m ℝ)) (ξ : Matrix m m ℝ) (hξ : ξ ∈ 𝔤) :
    (fun g : G => (g : Matrix m m ℝ) * ξ) ∈ leftInvariantFields G 𝔤 := by
  refine ⟨fun g h => ?_, by simpa using hξ⟩
  simp [Matrix.mul_assoc]

/-- MLS p. 410: every left invariant field is `X(g) = gX(e)` on `G`, so it takes values in the left
translates `g𝔤` of `T_eG`. -/
theorem eq_mul_apply_one (G : Submonoid (Matrix m m ℝ)) (X : G → Matrix m m ℝ)
    (hX : IsLeftInvariantOn G X) (g : G) : X g = (g : Matrix m m ℝ) * X 1 := by
  simpa using hX g 1

/-- **MLS p. 410: `X_L(G) ≅ T_eG`.** The linear map `ρ₁(X) = X(e)` from the left invariant fields
to `𝔤` has the inverse `ρ₂(ξ) = X_ξ`, `X_ξ(g) = gξ`. -/
def leftInvariantFieldsEquiv (G : Submonoid (Matrix m m ℝ)) (𝔤 : Submodule ℝ (Matrix m m ℝ)) :
    leftInvariantFields G 𝔤 ≃ₗ[ℝ] 𝔤 where
  toFun X := ⟨X.1 1, X.2.2⟩
  invFun ξ := ⟨fun g => (g : Matrix m m ℝ) * ξ, mul_mem_leftInvariantFields G 𝔤 ξ ξ.2⟩
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    apply Subtype.ext
    funext g
    exact (eq_mul_apply_one G X.1 X.2.1 g).symm
  right_inv ξ := by
    apply Subtype.ext
    simp

/-- `ρ₁(X) = X(e)` (MLS p. 410). -/
theorem leftInvariantFieldsEquiv_apply (G : Submonoid (Matrix m m ℝ))
    (𝔤 : Submodule ℝ (Matrix m m ℝ)) (X : leftInvariantFields G 𝔤) :
    (leftInvariantFieldsEquiv G 𝔤 X : Matrix m m ℝ) = X.1 1 := rfl

/-- `ρ₂(ξ) = X_ξ`, `X_ξ(g) = gξ` (MLS p. 410). -/
theorem leftInvariantFieldsEquiv_symm_apply (G : Submonoid (Matrix m m ℝ))
    (𝔤 : Submodule ℝ (Matrix m m ℝ)) (ξ : 𝔤) (g : G) :
    ((leftInvariantFieldsEquiv G 𝔤).symm ξ).1 g = (g : Matrix m m ℝ) * ξ := rfl

end LieGroup

end RoboLean
