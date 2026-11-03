import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# `GL(n, ℝ)` as a Lie group in Mathlib's sense

MLS Appendix A, printed pp. 408–410. A Lie group is a group and a smooth manifold with smooth
multiplication and inversion (p. 408); `GL(n, ℝ)` is an open subset of `ℝ^{n²}`, and "both
operations are smooth since the formulas for the product and inverse of matrices are smooth in
the matrix components" (Example A.2, p. 409); its Lie algebra is `T_eG ≅ ℝ^{n×n}` with the bracket
(A.1) of left invariant fields (p. 410, Example A.6).

Bridge. Mathlib builds the Lie group structure on the units `Rˣ` of a complete normed algebra `R`,
charted by the open embedding `Rˣ → R`, and the Lie algebra `GroupLieAlgebra I G = T_eG` with the
bracket of left invariant fields `mlieBracket` at the identity, which is (A.1). The pin does not
give this structure on the units of `Matrix (Fin n) (Fin n) ℝ` directly: the matrix space carries
the entrywise topology while its operator-norm ring structure carries a different (equal but not
definitionally equal) topology, and instance search fails. It does apply to the endomorphisms of
Euclidean space, `EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)`, which Mathlib's
`Matrix.toEuclideanCLM` identifies with the `n × n` real matrices as a star algebra. Here
`EuclideanGL n` is that unit group, `generalLinearEquiv` the group isomorphism with Mathlib's
`GL (Fin n) ℝ` of invertible matrices, and the theorems record what Mathlib then gives: the Lie
group property for every smoothness order, smooth multiplication and inversion, and a Lie algebra
of dimension `n²` linearly equivalent to the matrices. That Mathlib's bracket on this Lie algebra
is the commutator `AB − BA` of Example A.6 is `RoboLean.LieGroup.groupLieAlgebraEquiv_bracket`
(`RoboLean.LieGroups.ManifoldBracket`).
-/

noncomputable section

open scoped Manifold ContDiff

namespace RoboLean

namespace LieGroup

/-- The real algebra of linear endomorphisms of `ℝⁿ` (Euclidean norm, operator norm), Mathlib's
model of `ℝ^{n×n}` for the manifold `GL(n, ℝ)` (MLS Example A.2, p. 409). -/
abbrev EuclideanEnd (n : ℕ) : Type := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)

/-- **`GL(n, ℝ)` as Mathlib's Lie group** (MLS Example A.2, p. 409): the units of `EuclideanEnd n`. -/
abbrev EuclideanGL (n : ℕ) : Type := (EuclideanEnd n)ˣ

set_option synthInstance.maxHeartbeats 400000 in
/-- The charts of `GL(n, ℝ)` as an open subset of `ℝ^{n×n}` (MLS Example A.2, p. 409): Mathlib's
chart of the units of a complete normed algebra, restated at this type so that instance search
finds it within the default limits. -/
instance instChartedSpaceEuclideanGL (n : ℕ) : ChartedSpace (EuclideanEnd n) (EuclideanGL n) :=
  Units.instChartedSpace

/-- **MLS Example A.2, p. 409: the invertible `n × n` real matrices and Mathlib's Lie group
`EuclideanGL n` are isomorphic groups**, through `Matrix.toEuclideanCLM`. -/
def generalLinearEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) ℝ ≃* EuclideanGL n :=
  Units.mapEquiv (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toRingEquiv.toMulEquiv

/-- `generalLinearEquiv` sends an invertible matrix `g` to the endomorphism `x ↦ gx` (MLS
Example A.2, p. 409). -/
theorem generalLinearEquiv_val (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    ((generalLinearEquiv n g : EuclideanGL n) : EuclideanEnd n) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (g : Matrix (Fin n) (Fin n) ℝ) := rfl

/-- **MLS p. 408 and Example A.2, p. 409: `GL(n, ℝ)` is a Lie group**, of every smoothness order
(Mathlib's `LieGroup` on the units of a complete normed algebra). -/
theorem lieGroup_euclideanGL (n : ℕ) (k : ℕ∞ω) :
    LieGroup 𝓘(ℝ, EuclideanEnd n) k (EuclideanGL n) := by
  infer_instance

/-- MLS Example A.2, p. 409: matrix multiplication on `GL(n, ℝ)` is smooth (of every order). -/
theorem contMDiff_mul_euclideanGL (n : ℕ) (k : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, EuclideanEnd n).prod 𝓘(ℝ, EuclideanEnd n)) 𝓘(ℝ, EuclideanEnd n) k
      (fun p : EuclideanGL n × EuclideanGL n => p.1 * p.2) := by
  have := lieGroup_euclideanGL n k
  exact contMDiff_mul 𝓘(ℝ, EuclideanEnd n) k

/-- MLS Example A.2, p. 409: matrix inversion on `GL(n, ℝ)` is smooth (of every order). -/
theorem contMDiff_inv_euclideanGL (n : ℕ) (k : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanEnd n) 𝓘(ℝ, EuclideanEnd n) k (fun g : EuclideanGL n => g⁻¹) := by
  have := lieGroup_euclideanGL n k
  exact contMDiff_inv 𝓘(ℝ, EuclideanEnd n) k

/-- MLS Example A.6, p. 410: the Lie algebra `T_eGL(n, ℝ)` of Mathlib's Lie group is linearly
equivalent to the `n × n` real matrices `gl(n, ℝ)`. -/
def groupLieAlgebraEquiv (n : ℕ) :
    GroupLieAlgebra 𝓘(ℝ, EuclideanEnd n) (EuclideanGL n) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.symm

/-- **MLS Examples A.2 and A.6, pp. 409–410: the Lie algebra of `GL(n, ℝ)` has dimension `n²`**, so
the Lie group `GL(n, ℝ)` has dimension `n²`. -/
theorem finrank_groupLieAlgebra_euclideanGL (n : ℕ) :
    Module.finrank ℝ (GroupLieAlgebra 𝓘(ℝ, EuclideanEnd n) (EuclideanGL n)) = n ^ 2 := by
  rw [LinearEquiv.finrank_eq (groupLieAlgebraEquiv n), Module.finrank_matrix]
  simp [sq]

end LieGroup

end RoboLean
