import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import RoboLean.LieGroups.TwistForms

/-!
# Manipulability measures and the choice of tool frame

MLS Appendix A, §3.2, Examples A.26 and A.27, printed pp. 429–430 and 432. Representing the body
manipulator Jacobian in two tool frames related by `h ∈ SE(3)` gives `J₁(θ) = Ad_h J₂(θ)`
(p. 430). Since `Ad_h` does not preserve the Euclidean metric of `ℝ⁶ ≅ se(3)`, the minimum
singular value and the condition number depend on the frame (p. 430); the determinant does not,
`det J₁ = det Ad_h det J₂ = det J₂` (p. 432).

The statements are about `6 × 6` matrices with rows in twist coordinates `(v, ω)` and are not tied
to a particular manipulator. Singular values are Mathlib's `LinearMap.singularValues` of the
Euclidean linear map of the matrix (the convention of the library's manipulability measures,
MLS p. 128): decreasing, index `0` the largest, index `5` the smallest. The frame-dependence
witness is `J = I` and `h = (e₁, I)`: the squared singular values of `Ad_h` have product
`det(Ad_hᵀ Ad_h) = 1` and sum `trace(Ad_hᵀ Ad_h) = 8`, so they cannot all equal `1`.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Twist

/-- The smallest singular value `σ_min(J)` of a `6 × 6` matrix on twist coordinates, Mathlib's
singular value of index `5` of the Euclidean linear map (MLS p. 128, `μ₁ = σ_min(J)`; Example A.26,
printed p. 430). -/
def minSingularValueSix (J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) : ℝ :=
  (Matrix.toEuclideanLin J).singularValues 5

/-- The largest singular value `σ_max(J)` of a `6 × 6` matrix on twist coordinates, Mathlib's
singular value of index `0` (MLS p. 128; Example A.26, printed p. 430). -/
def maxSingularValueSix (J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) : ℝ :=
  (Matrix.toEuclideanLin J).singularValues 0

private theorem finrank_six : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)) = 6 := by simp

private theorem adjoint_comp_toEuclideanLin (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A =
      Matrix.toEuclideanLin (Aᵀ * A) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (toLpLin_mul 2 2 2 Aᵀ A).symm

private theorem trace_toEuclideanLin (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    LinearMap.trace ℝ _ (Matrix.toEuclideanLin A) = A.trace := by
  rw [show Matrix.toEuclideanLin A = Matrix.toLpLin 2 2 A from rfl, Matrix.toLpLin_eq_toLin]
  exact Matrix.trace_toLin_eq _ _

/-- The squared singular values of a `6 × 6` matrix `A` sum to `trace(Aᵀ A)` and multiply to
`det(Aᵀ A)` (supporting lemma for MLS Example A.26, printed p. 430). -/
private theorem sum_prod_sq_singularValues (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    ∑ i : Fin 6, (Matrix.toEuclideanLin A).singularValues i ^ 2 = (Aᵀ * A).trace ∧
      ∏ i : Fin 6, (Matrix.toEuclideanLin A).singularValues i ^ 2 = (Aᵀ * A).det := by
  set T := Matrix.toEuclideanLin A
  have hS := T.isSymmetric_adjoint_comp_self
  have hsq (i : Fin 6) := T.sq_singularValues_fin finrank_six i
  simp only [hsq]
  constructor
  · have e1 : LinearMap.trace ℝ _ (LinearMap.adjoint T ∘ₗ T) = (Aᵀ * A).trace := by
      rw [adjoint_comp_toEuclideanLin, trace_toEuclideanLin]
    simpa using (hS.trace_eq_sum_eigenvalues finrank_six).symm.trans e1
  · have e2 : LinearMap.det (LinearMap.adjoint T ∘ₗ T) = (Aᵀ * A).det := by
      rw [adjoint_comp_toEuclideanLin]
      exact LinearMap.det_toLpLin 2 (Aᵀ * A)
    simpa using (hS.det_eq_prod_eigenvalues finrank_six).symm.trans e2

/-- The singular values of the identity are all `1` (supporting lemma). -/
private theorem singularValues_one (i : Fin 6) :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)).singularValues i = 1 := by
  set T := Matrix.toEuclideanLin (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
  have hsq := T.sq_singularValues_fin finrank_six i
  have hev := T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues finrank_six i
  have hS : LinearMap.adjoint T ∘ₗ T = 1 := by
    rw [adjoint_comp_toEuclideanLin, Matrix.transpose_one, Matrix.mul_one]
    exact toLpLin_one 2
  have h1 : T.isSymmetric_adjoint_comp_self.eigenvalues finrank_six i = 1 := by
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have e := (LinearMap.congr_fun hS v).symm.trans hv.apply_eq_smul
    rw [Module.End.one_apply] at e
    have e' : v = T.isSymmetric_adjoint_comp_self.eigenvalues finrank_six i • v := by
      simpa using e
    have : (1 - T.isSymmetric_adjoint_comp_self.eigenvalues finrank_six i) • v = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr e'
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hv.2
  rw [h1] at hsq
  have hnn := T.singularValues_nonneg i
  nlinarith

/-- `det(Ad_hᵀ Ad_h) = 1` and `trace(Ad_hᵀ Ad_h) = 8` for `h = (e₁, I)` (supporting lemma for
MLS Example A.26, printed p. 430; the display of p. 422). -/
private theorem trace_det_e1 :
    ((adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩)ᵀ *
        adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩).trace = 8 ∧
      ((adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩)ᵀ *
        adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩).det = 1 := by
  constructor
  · rw [adjointMatrix_transpose_mul_self]
    simp [Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_three, Vec3.hat]
    norm_num
  · rw [Matrix.det_mul, Matrix.det_transpose, det_adjointMatrix, mul_one]

/-- MLS Example A.27, printed p. 432: the determinant of the Jacobian is frame invariant,
`det(Ad_h J) = det Ad_h det J = det J`. Rows in twist coordinates `(v, ω)`. -/
theorem det_adjointMatrix_mul (h : RigidTransform) (J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    (adjointMatrix h * J).det = J.det := by
  rw [Matrix.det_mul, det_adjointMatrix, one_mul]

/-- MLS Example A.26, printed p. 430, "`σ_min(J₁(θ)) ≠ σ_min(J₂(θ))` in general" for
`J₁ = Ad_h J₂`: for `J₂ = I` and `h = (e₁, I)`, `σ_min(Ad_h J₂) ≠ σ_min(J₂) = 1`. -/
theorem minSingularValueSix_adjointMatrix_ne :
    minSingularValueSix (adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩ * 1) ≠
      minSingularValueSix 1 := by
  rw [Matrix.mul_one]
  obtain ⟨hsum, hprod⟩ := sum_prod_sq_singularValues (adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩)
  obtain ⟨htr, hdet⟩ := trace_det_e1
  rw [htr] at hsum
  rw [hdet] at hprod
  intro hmin
  unfold minSingularValueSix at hmin
  set A := adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩
  set σ := (Matrix.toEuclideanLin A).singularValues
  have h5 : σ 5 = 1 := by
    rw [hmin]; simpa using singularValues_one 5
  have hge (i : Fin 6) : 1 ≤ σ i ^ 2 := by
    have : σ 5 ≤ σ i := (Matrix.toEuclideanLin A).singularValues_antitone (by omega)
    nlinarith [(Matrix.toEuclideanLin A).singularValues_nonneg i]
  have hle (j : Fin 6) : σ j ^ 2 ≤ 1 := by
    rw [← hprod, ← Finset.mul_prod_erase Finset.univ (fun i : Fin 6 => σ i ^ 2)
      (Finset.mem_univ j)]
    have : 1 ≤ ∏ i ∈ Finset.univ.erase j, σ i ^ 2 :=
      Finset.one_le_prod₀ fun i _ => hge i
    nlinarith [hge j]
  have : ∑ i : Fin 6, σ i ^ 2 = ∑ _i : Fin 6, (1 : ℝ) :=
    Finset.sum_congr rfl fun i _ => le_antisymm (hle i) (hge i)
  rw [this] at hsum
  simp at hsum

/-- MLS Example A.26, printed p. 430, "a similar result holds for the condition number": for
`J₂ = I` and `h = (e₁, I)`, the inverse condition number `σ_min / σ_max` of `Ad_h J₂` differs from
that of `J₂`, which is `1`. -/
theorem inverseConditionNumberSix_adjointMatrix_ne :
    minSingularValueSix (adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩ * 1) /
        maxSingularValueSix (adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩ * 1) ≠
      minSingularValueSix 1 / maxSingularValueSix 1 := by
  rw [Matrix.mul_one]
  have hone : minSingularValueSix 1 / maxSingularValueSix 1 = 1 := by
    rw [minSingularValueSix, maxSingularValueSix]
    rw [show (5 : ℕ) = ((5 : Fin 6) : ℕ) from rfl, show (0 : ℕ) = ((0 : Fin 6) : ℕ) from rfl,
      singularValues_one, singularValues_one, div_one]
  rw [hone]
  obtain ⟨hsum, hprod⟩ := sum_prod_sq_singularValues (adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩)
  obtain ⟨htr, hdet⟩ := trace_det_e1
  rw [htr] at hsum
  rw [hdet] at hprod
  intro hratio
  set A := adjointMatrix ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩
  set σ := (Matrix.toEuclideanLin A).singularValues
  have hmax : σ 0 ≠ 0 := by
    intro h0
    rw [minSingularValueSix, maxSingularValueSix] at hratio
    change σ 5 / σ 0 = 1 at hratio
    rw [h0, div_zero] at hratio
    exact zero_ne_one hratio
  have heq : σ 5 = σ 0 := by
    rw [minSingularValueSix, maxSingularValueSix] at hratio
    change σ 5 / σ 0 = 1 at hratio
    rwa [div_eq_one_iff_eq hmax] at hratio
  have hall (i : Fin 6) : σ i ^ 2 = σ 0 ^ 2 := by
    have h1 : σ 5 ≤ σ i := (Matrix.toEuclideanLin A).singularValues_antitone (by omega)
    have h2 : σ i ≤ σ 0 := (Matrix.toEuclideanLin A).singularValues_antitone (by omega)
    rw [le_antisymm h2 (heq ▸ h1)]
  have hc : σ 0 ^ 2 = 1 := by
    have : ∏ i : Fin 6, σ i ^ 2 = (σ 0 ^ 2) ^ 6 := by
      rw [Finset.prod_congr rfl fun i _ => hall i]
      simp
    rw [hprod] at this
    have hnn : 0 ≤ σ 0 ^ 2 := sq_nonneg _
    exact ((pow_eq_one_iff_of_nonneg hnn (by norm_num)).mp this.symm)
  have : ∑ i : Fin 6, σ i ^ 2 = 6 := by
    rw [Finset.sum_congr rfl fun i _ => (hall i).trans hc]
    simp
  linarith

end Twist

end RoboLean
