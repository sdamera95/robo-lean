import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Frame-invariant metrics on `ℝⁿ`

MLS Appendix A, §3.2, printed pp. 423–424. A bilinear form on `ℝⁿ` is written through its matrix
`Ψ` in an orthonormal basis, `Ψ(v, w) = vᵀ Ψ w` (p. 423). It is invariant under change of
coordinate frames when `Ψ(R v₁, R v₂) = Ψ(v₁, v₂)` for every rotation `R ∈ SO(n)`, equation
(A.8), which is equivalent to `Ψ R = R Ψ` for every `R ∈ SO(n)`, equation (A.9).

Lemma A.2 (a symmetric matrix commuting with every rotation is a multiple of the identity) is
proved here from two families of rotations, the quarter turns in a coordinate plane and the half
turns about a coordinate axis, rather than through an eigenvector and the transitivity of `SO(n)`
on the unit sphere as printed. The quarter turns alone give the lemma for every `n` when `Ψ` is
symmetric; with the half turns the symmetry hypothesis can be dropped when `n ≥ 3`, which is the
form the proof of Proposition A.5 (p. 426) uses for the off-diagonal block `B`. For `n = 2` the
symmetry hypothesis is needed: the rotation by a right angle commutes with every rotation of the
plane.

Proposition A.3 is stated as: a symmetric matrix is a positive definite frame-invariant metric
exactly when it is a positive multiple `α I` of the identity, the scalar `α` being the choice of
length scale (p. 424).
-/

noncomputable section

open Matrix

namespace RoboLean

namespace InvariantMetric

variable {n : ℕ}

/-- Invariance of the bilinear form `Ψ(v, w) = vᵀ Ψ w` under change of coordinate frames,
MLS equation (A.8), printed p. 423: `Ψ(R v₁, R v₂) = Ψ(v₁, v₂)` for all `v₁, v₂ ∈ ℝⁿ` and
`R ∈ SO(n)`. Column vectors; `Ψ` is the matrix of the form in an orthonormal basis. -/
def IsFrameInvariant (Ψ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ R ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, ∀ v w : Fin n → ℝ,
    (R *ᵥ v) ⬝ᵥ (Ψ *ᵥ (R *ᵥ w)) = v ⬝ᵥ (Ψ *ᵥ w)

/-- Equation (A.8) is equivalent to equation (A.9), MLS printed p. 423: the form `vᵀ Ψ w` is
invariant under every rotation exactly when `Ψ R = R Ψ` for every `R ∈ SO(n)`. -/
theorem isFrameInvariant_iff_commute (Ψ : Matrix (Fin n) (Fin n) ℝ) :
    IsFrameInvariant Ψ ↔ ∀ R ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, Ψ * R = R * Ψ := by
  have key (R : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
      (R *ᵥ v) ⬝ᵥ (Ψ *ᵥ (R *ᵥ w)) = v ⬝ᵥ ((Rᵀ * Ψ * R) *ᵥ w) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hform (A B : Matrix (Fin n) (Fin n) ℝ) :
      (∀ v w : Fin n → ℝ, v ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ (B *ᵥ w)) ↔ A = B := by
    constructor
    · intro h
      ext i j
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h (Pi.single i 1) (Pi.single j 1)
    · rintro rfl v w
      rfl
  constructor
  · intro h R hR
    have hRt : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hR.1
    have hRR : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hR.1
    have h1 : Rᵀ * Ψ * R = Ψ := (hform _ _).mp fun v w => by rw [← key]; exact h R hR v w
    calc Ψ * R = (R * Rᵀ) * (Ψ * R) := by rw [hRR, Matrix.one_mul]
      _ = R * (Rᵀ * Ψ * R) := by simp only [Matrix.mul_assoc]
      _ = R * Ψ := by rw [h1]
  · intro h R hR v w
    have hRt : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hR.1
    have h1 : Rᵀ * Ψ * R = Ψ := by
      rw [Matrix.mul_assoc, h R hR, ← Matrix.mul_assoc, hRt, Matrix.one_mul]
    rw [key, h1]

/-- The reflection reversing the `i`-th coordinate, `diag(1, …, -1, …, 1)`: an orthogonal matrix
of determinant `-1`. Supporting matrix for Lemma A.2, MLS printed p. 423. -/
def signFlip (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun k => if k = i then -1 else 1

/-- The quarter turn in the coordinate plane of `eᵢ, eⱼ`, sending `eᵢ ↦ eⱼ` and `eⱼ ↦ -eᵢ` and
fixing the other basis vectors: the transposition permutation matrix followed by the reflection
of the `j`-th coordinate. Supporting rotation for Lemma A.2, MLS printed p. 423. -/
def quarterTurn (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (Equiv.swap i j).permMatrix ℝ * signFlip j

/-- The half turn reversing the `i`-th and `j`-th coordinates, `diag` with `-1` at `i` and `j`.
Supporting rotation for Lemma A.2 without symmetry when `n ≥ 3` (MLS printed pp. 423, 426). -/
def halfTurn (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  signFlip i * signFlip j

/-- A permutation matrix is orthogonal, `Pᵀ P = I` (supporting lemma for Lemma A.2, MLS printed
p. 423; orthogonality as in MLS equation (2.1), p. 23). -/
theorem permMatrix_mem_orthogonalGroup (σ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

/-- A coordinate reflection is orthogonal (supporting lemma for Lemma A.2, MLS printed p. 423;
orthogonality as in MLS equation (2.1), p. 23). -/
theorem signFlip_mem_orthogonalGroup (i : Fin n) :
    signFlip i ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ, signFlip, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with k
  split_ifs <;> norm_num

/-- A coordinate reflection has determinant `-1` (supporting lemma for Lemma A.2, MLS printed
p. 423). -/
theorem det_signFlip (i : Fin n) : (signFlip i).det = -1 := by
  rw [signFlip, Matrix.det_diagonal, Finset.prod_ite_eq']
  simp

/-- A quarter turn in a coordinate plane is a rotation, `quarterTurn i j ∈ SO(n)` for `i ≠ j`
(MLS printed p. 23, `SO(n)` as orthogonal matrices of determinant `+1`). -/
theorem quarterTurn_mem {i j : Fin n} (hij : i ≠ j) :
    quarterTurn i j ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · exact Submonoid.mul_mem _ (permMatrix_mem_orthogonalGroup _) (signFlip_mem_orthogonalGroup j)
  · rw [quarterTurn, Matrix.det_mul, Matrix.det_permutation, Equiv.Perm.sign_swap hij,
      det_signFlip]
    norm_num

/-- A half turn about a coordinate axis is a rotation, `halfTurn i j ∈ SO(n)` (MLS printed
p. 23, `SO(n)` as orthogonal matrices of determinant `+1`); for `i = j` it is the identity. -/
theorem halfTurn_mem (i j : Fin n) :
    halfTurn i j ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · exact Submonoid.mul_mem _ (signFlip_mem_orthogonalGroup i) (signFlip_mem_orthogonalGroup j)
  · rw [halfTurn, Matrix.det_mul, det_signFlip, det_signFlip]
    norm_num

private theorem quarterTurn_apply (i j a b : Fin n) :
    quarterTurn i j a b = (if Equiv.swap i j a = b then 1 else 0) * (if b = j then -1 else 1) := by
  simp [quarterTurn, signFlip, Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

private theorem quarterTurn_col_i {i j : Fin n} (hij : i ≠ j) (c : Fin n) :
    quarterTurn i j c i = if c = j then 1 else 0 := by
  rw [quarterTurn_apply]
  simp [Equiv.swap_apply_eq_iff, hij]

private theorem quarterTurn_row_i (i j c : Fin n) :
    quarterTurn i j i c = if c = j then -1 else 0 := by
  rw [quarterTurn_apply, Equiv.swap_apply_left]
  by_cases hc : c = j
  · simp [hc]
  · simp [hc, Ne.symm hc]

private theorem quarterTurn_row_j {i j : Fin n} (hij : i ≠ j) (c : Fin n) :
    quarterTurn i j j c = if c = i then 1 else 0 := by
  rw [quarterTurn_apply, Equiv.swap_apply_right]
  by_cases hc : c = i
  · subst hc; simp [hij]
  · simp [hc, Ne.symm hc]

/-- The two relations that a matrix commuting with the quarter turn of the plane of `eᵢ, eⱼ`
satisfies: `Ψᵢⱼ = -Ψⱼᵢ` and `Ψᵢᵢ = Ψⱼⱼ`. Supporting lemma for Lemma A.2, MLS printed p. 423. -/
private theorem entries_of_commute_quarterTurn (Ψ : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hij : i ≠ j) (h : Ψ * quarterTurn i j = quarterTurn i j * Ψ) :
    Ψ i j = -Ψ j i ∧ Ψ i i = Ψ j j := by
  have h1 := congrFun (congrFun h i) i
  have h2 := congrFun (congrFun h j) i
  simp only [Matrix.mul_apply, quarterTurn_col_i hij, quarterTurn_row_i,
    quarterTurn_row_j hij, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_mul] at h1 h2
  exact ⟨h1, h2.symm⟩

/-- MLS Lemma A.2, printed p. 423: a symmetric `n × n` matrix that commutes with every rotation,
`Ψ R = R Ψ` for all `R ∈ SO(n)` (equation (A.9)), is a scalar multiple `α I` of the identity.
Proved from the quarter turns of the coordinate planes; every `n`, including `n ≤ 1`. -/
theorem eq_smul_one_of_commute (Ψ : Matrix (Fin n) (Fin n) ℝ) (hsymm : Ψᵀ = Ψ)
    (hcomm : ∀ R ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, Ψ * R = R * Ψ) :
    ∃ α : ℝ, Ψ = α • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hrel {i j : Fin n} (hij : i ≠ j) := entries_of_commute_quarterTurn Ψ hij
    (hcomm _ (quarterTurn_mem hij))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, Matrix.ext fun i => i.elim0⟩
  · refine ⟨Ψ ⟨0, hn⟩ ⟨0, hn⟩, Matrix.ext fun a b => ?_⟩
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      simp only [ite_true, mul_one]
      by_cases ha : a = ⟨0, hn⟩
      · rw [ha]
      · exact (hrel ha).2
    · simp only [hab, ite_false, mul_zero]
      have hs : Ψ b a = Ψ a b := by
        simpa using congrFun (congrFun hsymm a) b
      have := (hrel hab).1
      linarith

/-- Lemma A.2 without the symmetry hypothesis in dimension `n ≥ 3`: every `n × n` matrix that
commutes with every rotation is a scalar multiple of the identity. This is the step "letting
`p = 0` … we obtain `B = β I`" in the proof of Proposition A.5, MLS printed p. 426, where the block
`B` need not be symmetric. Proved from the quarter and half turns of the coordinate planes. -/
theorem eq_smul_one_of_commute_of_three_le (hn : 3 ≤ n) (Ψ : Matrix (Fin n) (Fin n) ℝ)
    (hcomm : ∀ R ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, Ψ * R = R * Ψ) :
    ∃ α : ℝ, Ψ = α • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hoff {a b : Fin n} (hab : a ≠ b) : Ψ a b = 0 := by
    obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a, b} : Finset (Fin n))) (t := Finset.univ) (by
        rw [Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
    have ham : a ≠ m := fun h => hm (by simp [h])
    have hbm : b ≠ m := fun h => hm (by simp [h])
    have h := congrFun (congrFun (hcomm _ (halfTurn_mem a m)) a) b
    simp [halfTurn, signFlip, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal,
      Matrix.diagonal_mul, ham, hab.symm, hbm] at h
    linarith
  refine eq_smul_one_of_commute Ψ ?_ hcomm
  ext a b
  by_cases hab : a = b
  · subst hab; rfl
  · rw [Matrix.transpose_apply, hoff hab, hoff (Ne.symm hab)]

/-- Every scalar multiple `α I` of the identity is frame invariant in the sense of
equation (A.8), MLS printed p. 423 (the converse of Lemma A.2). -/
theorem smul_one_isFrameInvariant (α : ℝ) :
    IsFrameInvariant (α • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [isFrameInvariant_iff_commute]
  intro R _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- MLS Proposition A.3, printed p. 424: up to a choice of length scale, `ℝⁿ` has a unique
positive definite metric invariant under change of coordinate frames. Stated as: a matrix `Ψ`
is a positive definite metric (symmetric with `vᵀ Ψ v > 0` for `v ≠ 0`, Mathlib's `PosDef`,
p. 423's definition of a metric) that is frame invariant (A.8) exactly when `Ψ = α I` with
`α > 0`, the length scale. -/
theorem posDef_isFrameInvariant_iff (Ψ : Matrix (Fin n) (Fin n) ℝ) :
    (Ψ.PosDef ∧ IsFrameInvariant Ψ) ↔ ∃ α : ℝ, 0 < α ∧ Ψ = α • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  constructor
  · rintro ⟨hpos, hinv⟩
    have hsymm : Ψᵀ = Ψ := by
      have := hpos.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    obtain ⟨α, hα⟩ := eq_smul_one_of_commute Ψ hsymm ((isFrameInvariant_iff_commute Ψ).mp hinv)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨1, one_pos, Matrix.ext fun i => i.elim0⟩
    · refine ⟨α, ?_, hα⟩
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hpos).2
        (x := Pi.single ⟨0, hn⟩ 1) (by simp)
      simpa [hα, Matrix.smul_mulVec, dotProduct, Pi.single_apply] using h
  · rintro ⟨α, hα, rfl⟩
    exact ⟨Matrix.PosDef.one.smul hα, smul_one_isFrameInvariant α⟩

end InvariantMetric

end RoboLean
