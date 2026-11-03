import RoboLean.LieGroups.MatrixLieGroup
import RoboLean.Geometry.TwistAdjoint

/-!
# Dimensions of the book's matrix Lie groups

MLS Appendix A, printed p. 409: `GL(n, ℝ)` is an open subset of `ℝ^{n²}` (Example A.2), "the
dimension of `SO(n)` as a manifold is `n(n − 1)/2`" (Example A.3), and "`SE(3)` is a Lie group of
dimension 6" (Example A.4).

Reading. Without a manifold structure on the subgroups, the dimension of a matrix Lie group is read
as the dimension of its Lie algebra `T_eG` (p. 410), the matrix Lie algebra
`RoboLean.LieGroup.matrixLieAlgebra` of the group. The statements give the `finrank` of the real
span of that set; by the theorems of `RoboLean.LieGroups.MatrixLieGroup` the set is already a
subspace in each case (all matrices, the skew-symmetric matrices, `so(3)`, `se(3)`), so the span
adds nothing. The dimension of Mathlib's manifold `GL(n, ℝ)` is in `RoboLean.LieGroups.Manifold`.
-/

noncomputable section

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RoboLean

namespace LieGroup

/-- The skew-symmetric `n × n` matrices are determined by their entries above the diagonal. -/
private def skewEquiv (n : ℕ) :
    (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule ≃ₗ[ℝ] ({p : Fin n × Fin n // p.1 < p.2} → ℝ) where
  toFun A p := A.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0, by
    rw [LieSubalgebra.mem_toSubmodule, LieAlgebra.Orthogonal.mem_so]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · simp [h, h.not_gt]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    apply Subtype.ext
    have hA : A.1ᵀ = -A.1 :=
      (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ A.1).mp ((LieSubalgebra.mem_toSubmodule _).mp A.2)
    ext i j
    have hij : A.1 j i = -A.1 i j := congrFun (congrFun hA i) j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp only [lt_irrefl, dite_false, Matrix.of_apply]
      linarith
    · simp [h, h.not_gt, hij]
  right_inv f := by
    funext p
    simp [p.2]

/-- The number of strictly ordered pairs of `Fin n` is `n(n − 1)/2`. -/
private theorem card_lt_pairs (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt,
    Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]

/-- **MLS Example A.2, p. 409 (with Example A.6, p. 410): `GL(n, ℝ)` has dimension `n²`**, the
dimension of its Lie algebra `gl(n, ℝ)`. -/
theorem finrank_span_matrixLieAlgebra_generalLinear (n : ℕ) :
    Module.finrank ℝ
        (Submodule.span ℝ (matrixLieAlgebra {g : Matrix (Fin n) (Fin n) ℝ | IsUnit g})) =
      n ^ 2 := by
  rw [matrixLieAlgebra_generalLinear, Submodule.span_univ, finrank_top, Module.finrank_matrix]
  simp [sq]

/-- **MLS Example A.3, p. 409: `SO(n)` has dimension `n(n − 1)/2`**, the dimension of the
skew-symmetric `n × n` matrices. -/
theorem finrank_span_matrixLieAlgebra_specialOrthogonalGroup (n : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ
        (matrixLieAlgebra (Matrix.specialOrthogonalGroup (Fin n) ℝ :
          Set (Matrix (Fin n) (Fin n) ℝ)))) = n * (n - 1) / 2 := by
  have hset : matrixLieAlgebra (Matrix.specialOrthogonalGroup (Fin n) ℝ :
      Set (Matrix (Fin n) (Fin n) ℝ)) =
      ((LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    rw [matrixLieAlgebra_specialOrthogonalGroup_eq_so]
    rfl
  rw [hset, Submodule.span_eq, LinearEquiv.finrank_eq (skewEquiv n),
    Module.finrank_fintype_fun_eq_card, card_lt_pairs]

/-- **MLS Example A.3, p. 409, for `n = 3` (Example A.7, p. 411): `SO(3)` has dimension 3.** -/
theorem finrank_span_matrixLieAlgebra_rotation :
    Module.finrank ℝ (Submodule.span ℝ
        (matrixLieAlgebra (Matrix.specialOrthogonalGroup (Fin 3) ℝ :
          Set (Matrix (Fin 3) (Fin 3) ℝ)))) = 3 := by
  rw [finrank_span_matrixLieAlgebra_specialOrthogonalGroup]

/-- **MLS Example A.4, p. 409 (with Example A.8, p. 411): `SE(3)` is a Lie group of dimension
6**, the dimension of `se(3) ≅ ℝ⁶`. -/
theorem finrank_span_matrixLieAlgebra_rigid :
    Module.finrank ℝ (Submodule.span ℝ (matrixLieAlgebra (Set.range RigidTransform.toHomogeneous))) =
      6 := by
  rw [matrixLieAlgebra_rigid, Submodule.span_eq, ← LinearEquiv.finrank_eq Twist.hatLinearEquiv,
    LinearEquiv.finrank_eq Twist.coordinatesEquiv, Module.finrank_fintype_fun_eq_card]
  simp

end LieGroup

end RoboLean
