import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import RoboLean.Geometry.TwistExp
import RoboLean.LieGroups.MatrixExponential

/-!
# Matrix Lie groups and their Lie algebras

MLS Appendix A, §§2.1–2.3, printed pp. 408–413. A Lie group is a group that is a smooth manifold
with smooth multiplication and inversion (p. 408); the examples of p. 409 are `GL(n, ℝ)`, an open
subset of `ℝ^{n×n}` (Example A.2), `SO(n) = {R ∈ GL(n, ℝ) : RRᵀ = I, det R = +1}` (Example A.3) and
`SE(3)`, the `4 × 4` matrices `[R p; 0 1]` with `R ∈ SO(3)` (Example A.4). The Lie algebra is
`T_eG` (p. 410), and for every `ξ` the curve `φ_ξ(s) = exp(ξ s)` is a one-parameter subgroup of `G`
(p. 412); on `GL(n, ℝ)` the exponential is the matrix exponential (Example A.10, pp. 412–413).

Reading. The book's groups are treated as sets of real square matrices, subgroups of `GL(n, ℝ)`;
no manifold structure is built on them. The Lie algebra of such a set `G` is read at matrix level
as the set of matrices `A` whose one-parameter group `t ↦ exp(tA)` stays in `G`
(`matrixLieAlgebra`), the usual definition for closed subgroups of `GL(n, ℝ)`. The theorems compute
it for the book's examples: all matrices for `GL(n, ℝ)` (Example A.6), the skew-symmetric matrices
for `SO(n)` (Mathlib's Lie subalgebra `so(n)`), the image of the hat map for `SO(3)` (Example A.7,
eq. (A.2)) and the `se(3)` matrices `[ω̂ v; 0 0]` for `SE(3)` (Example A.8). That `SO(n)` and the
image of `SE(3)` are closed subsets of the matrix space is stated as well. The exponential is
Mathlib's `NormedSpace.exp`; derivatives use the operator norm on matrices, the topology of the
closedness statements is the entrywise one (the two agree on finite-dimensional spaces).
-/

noncomputable section

open Matrix

namespace RoboLean

namespace LieGroup

variable {m : Type*} [Fintype m] [DecidableEq m]

section Derivatives

open scoped Matrix.Norms.Operator

/-- Two exponentials `t ↦ exp(tA)` and `t ↦ exp(tB)` that agree for every `t` have the same
derivative `A = B` at `0`. -/
private theorem exp_smul_deriv_unique {A B : Matrix m m ℝ}
    (h : ∀ t : ℝ, NormedSpace.exp (t • A) = NormedSpace.exp (t • B)) : A = B := by
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) A 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) B 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) B (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at this
    rw [show (fun u : ℝ => NormedSpace.exp (u • A)) = fun u => NormedSpace.exp (u • B) from
      funext h]
    exact this
  exact h1.unique h2

/-- If `E exp(tA) = E` for every `t`, then `EA = 0` (the derivative at `0`). -/
private theorem mul_eq_zero_of_mul_exp_smul_eq {A E : Matrix m m ℝ}
    (h : ∀ t : ℝ, E * NormedSpace.exp (t • A) = E) : E * A = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => E * NormedSpace.exp (t • A)) (E * A) 0 := by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)).const_mul E
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
  rw [show (fun t : ℝ => E * NormedSpace.exp (t • A)) = fun _ => E from funext h] at h1
  exact h1.unique (hasDerivAt_const 0 E)

end Derivatives

/-- **The Lie algebra of a group of matrices, at matrix level** (MLS §2.3, p. 412: `exp(ξ s)` is a
one-parameter subgroup of `G`; Example A.10, pp. 412–413: on `GL(n, ℝ)` it is the matrix
exponential). For a set `G` of real square matrices, the matrices `A` with `exp(tA) ∈ G` for every
real `t`. -/
def matrixLieAlgebra (G : Set (Matrix m m ℝ)) : Set (Matrix m m ℝ) :=
  {A | ∀ t : ℝ, NormedSpace.exp (t • A) ∈ G}

/-- **MLS Example A.6, p. 410: the Lie algebra of `GL(n, ℝ)` is `gl(n, ℝ)`, all `n × n` real
matrices.** `GL(n, ℝ)` is the set of invertible matrices (Example A.2, p. 409). -/
theorem matrixLieAlgebra_generalLinear :
    matrixLieAlgebra {g : Matrix m m ℝ | IsUnit g} = Set.univ := by
  ext A
  simp only [matrixLieAlgebra, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact fun t => Matrix.isUnit_exp _

/-- MLS Example A.3, p. 409, with Proposition 2.4 of Chapter 2 (p. 28) for `n = 3`: the matrix
exponential of a real skew-symmetric matrix lies in `SO(n)`, for every finite index type. -/
theorem exp_mem_specialOrthogonalGroup (A : Matrix m m ℝ) (hA : Aᵀ = -A) :
    NormedSpace.exp A ∈ Matrix.specialOrthogonalGroup m ℝ := by
  have horth : (NormedSpace.exp A)ᵀ * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_transpose, hA,
      ← Matrix.exp_add_of_commute (-A) A (Commute.refl A).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' m ℝ).mpr horth, ?_⟩
  have hdet := congrArg Matrix.det horth
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hhalf : NormedSpace.exp A =
      NormedSpace.exp ((1 / 2 : ℝ) • A) * NormedSpace.exp ((1 / 2 : ℝ) • A) := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  have hnonneg : 0 ≤ (NormedSpace.exp A).det := by
    rw [hhalf, Matrix.det_mul]
    exact mul_self_nonneg _
  nlinarith

/-- **MLS Example A.3, p. 409: the Lie algebra of `SO(n)` is `so(n)`, the skew-symmetric
matrices.** For every finite index type, `exp(tA) ∈ SO(n)` for all `t` exactly when `Aᵀ = −A`. -/
theorem matrixLieAlgebra_specialOrthogonalGroup :
    matrixLieAlgebra (Matrix.specialOrthogonalGroup m ℝ : Set (Matrix m m ℝ)) = {A | Aᵀ = -A} := by
  ext A
  simp only [matrixLieAlgebra, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro h
    have key : ∀ t : ℝ, NormedSpace.exp (t • Aᵀ) = NormedSpace.exp (t • -A) := by
      intro t
      have horth : (NormedSpace.exp (t • A))ᵀ * NormedSpace.exp (t • A) = 1 :=
        (Matrix.mem_orthogonalGroup_iff' m ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp (h t)).1
      rw [← Matrix.transpose_smul, Matrix.exp_transpose, smul_neg, Matrix.exp_neg,
        Matrix.inv_eq_left_inv horth]
    exact exp_smul_deriv_unique key
  · intro hA t
    apply exp_mem_specialOrthogonalGroup
    rw [Matrix.transpose_smul, hA, smul_neg]

/-- MLS Example A.3, p. 409: the Lie algebra of `SO(n)` is Mathlib's Lie subalgebra `so(n)` of
`gl(n, ℝ)`, closed under the commutator `[A, B] = AB − BA` of Example A.6. -/
theorem matrixLieAlgebra_specialOrthogonalGroup_eq_so :
    matrixLieAlgebra (Matrix.specialOrthogonalGroup m ℝ : Set (Matrix m m ℝ)) =
      (LieAlgebra.Orthogonal.so m ℝ : Set (Matrix m m ℝ)) := by
  rw [matrixLieAlgebra_specialOrthogonalGroup]
  ext A
  simp [LieAlgebra.Orthogonal.mem_so]

/-- **MLS Example A.7, eq. (A.2), p. 411: the Lie algebra of `SO(3)` is `so(3) = {ω̂ : ω ∈ ℝ³}`**,
the image of the hat map. -/
theorem matrixLieAlgebra_rotation :
    matrixLieAlgebra (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
      Set.range Vec3.hat := by
  rw [matrixLieAlgebra_specialOrthogonalGroup]
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hA
    exact ⟨Vec3.vee A, Vec3.hat_vee A hA⟩
  · rintro ⟨v, rfl⟩
    exact Vec3.hat_transpose v

/-- **MLS Example A.8, p. 411 (with Example A.4, p. 409): the Lie algebra of `SE(3)` is `se(3)`**,
the `4 × 4` matrices `[ω̂ v; 0 0]` (the library's `se3Submodule`, MLS eq. (2.29), p. 40).
`SE(3)` is the set of homogeneous matrices `[R p; 0 1]` of rigid transforms. -/
theorem matrixLieAlgebra_rigid :
    matrixLieAlgebra (Set.range RigidTransform.toHomogeneous) =
      (se3Submodule : Set HomogeneousMatrix) := by
  ext A
  simp only [matrixLieAlgebra, Set.mem_ofPred_eq, Set.mem_range, SetLike.mem_coe]
  constructor
  · intro h
    have hE : (Matrix.fromBlocks 0 0 0 1 : HomogeneousMatrix) * A = 0 := by
      refine mul_eq_zero_of_mul_exp_smul_eq (fun t => ?_)
      obtain ⟨g, hg⟩ := h t
      rw [← hg]
      unfold RigidTransform.toHomogeneous
      rw [Matrix.fromBlocks_multiply]
      simp
    have hblocks := congrArg (fun M : HomogeneousMatrix => (M.toBlocks₂₁, M.toBlocks₂₂)) hE
    rw [← Matrix.fromBlocks_toBlocks A, Matrix.fromBlocks_multiply] at hblocks
    simp only [Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, Prod.mk.injEq] at hblocks
    have h21 : A.toBlocks₂₁ = 0 := by
      rw [hblocks.1]
      rfl
    have h22 : A.toBlocks₂₂ = 0 := by
      rw [hblocks.2]
      rfl
    refine ⟨?_, h21, h22⟩
    have hrot : A.toBlocks₁₁ ∈
        matrixLieAlgebra (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
      intro t
      obtain ⟨g, hg⟩ := h t
      have hA : t • A = Matrix.fromBlocks (t • A.toBlocks₁₁) (t • A.toBlocks₁₂) 0 0 := by
        conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
        rw [h21, h22, Matrix.fromBlocks_smul]
        simp only [smul_zero]
      have hblock := (exp_upper_block_diagonal (t • A.toBlocks₁₁) (t • A.toBlocks₁₂) 0).1
      rw [← hA, ← hg, RigidTransform.toHomogeneous_rotation] at hblock
      rw [← hblock]
      exact g.rotation.property
    rw [matrixLieAlgebra_specialOrthogonalGroup] at hrot
    exact hrot
  · intro hA t
    refine ⟨Twist.exp (Twist.vee A) t, ?_⟩
    rw [Twist.toHomogeneous_exp, Twist.hat_vee A hA]

/-- MLS Example A.8, p. 411: the Lie algebra of `SE(3)` is the image `{ξ̂ : ξ = (v, ω) ∈ ℝ⁶}` of
the twist hat map of eq. (2.31), p. 41. -/
theorem matrixLieAlgebra_rigid_eq_range_hat :
    matrixLieAlgebra (Set.range RigidTransform.toHomogeneous) = Set.range Twist.hat := by
  rw [matrixLieAlgebra_rigid]
  ext M
  simp only [SetLike.mem_coe, Set.mem_range]
  constructor
  · intro hM
    exact ⟨Twist.vee M, Twist.hat_vee M hM⟩
  · rintro ⟨ξ, rfl⟩
    exact (Twist.hatLinearEquiv ξ).property

/-- MLS Example A.3, p. 409: `SO(n)` is a closed subset of the matrix space (entrywise topology),
so a closed subgroup of `GL(n, ℝ)`. -/
theorem isClosed_specialOrthogonalGroup :
    IsClosed (Matrix.specialOrthogonalGroup m ℝ : Set (Matrix m m ℝ)) := by
  have hset : (Matrix.specialOrthogonalGroup m ℝ : Set (Matrix m m ℝ)) =
      {A | Aᵀ * A = 1} ∩ {A | A.det = 1} := by
    ext A
    simp only [SetLike.mem_coe, Matrix.mem_specialOrthogonalGroup_iff,
      Matrix.mem_orthogonalGroup_iff', Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  exact (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).inter
    (isClosed_eq continuous_id.matrix_det continuous_const)

/-- MLS Example A.4, p. 409: the homogeneous matrices `[R p; 0 1]` of `SE(3)` form a closed subset
of the `4 × 4` matrices (entrywise topology), so `SE(3)` is a closed subgroup of `GL(4, ℝ)`. -/
theorem isClosed_range_toHomogeneous :
    IsClosed (Set.range RigidTransform.toHomogeneous) := by
  have hset : Set.range RigidTransform.toHomogeneous =
      {M : HomogeneousMatrix | M.toBlocks₁₁ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ} ∩
        ({M | M.toBlocks₂₁ = 0} ∩ {M | M.toBlocks₂₂ = 1}) := by
    ext M
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.rotation.property, rfl, rfl⟩
    · rintro ⟨hR, h21, h22⟩
      refine ⟨⟨⟨M.toBlocks₁₁, hR⟩, WithLp.toLp 2 (fun i => M (Sum.inl i) (Sum.inr 0))⟩, ?_⟩
      conv_rhs => rw [← Matrix.fromBlocks_toBlocks M, h21, h22]
      unfold RigidTransform.toHomogeneous
      congr 1
      ext i j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl
  rw [hset]
  have hc11 : Continuous fun M : HomogeneousMatrix => M.toBlocks₁₁ :=
    continuous_matrix fun i j => (continuous_apply_apply _ _)
  have hc21 : Continuous fun M : HomogeneousMatrix => M.toBlocks₂₁ :=
    continuous_matrix fun i j => (continuous_apply_apply _ _)
  have hc22 : Continuous fun M : HomogeneousMatrix => M.toBlocks₂₂ :=
    continuous_matrix fun i j => (continuous_apply_apply _ _)
  exact (isClosed_specialOrthogonalGroup.preimage hc11).inter
    ((isClosed_eq hc21 continuous_const).inter (isClosed_eq hc22 continuous_const))

end LieGroup

end RoboLean
