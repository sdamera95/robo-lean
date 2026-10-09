import RoboLean.Geometry.Twist
import RoboLean.Geometry.RotationExp
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Actual matrix exponentials of twists

MLS Proposition 2.8, printed pp. 41–42, states that every real twist
exponentiates to a homogeneous rigid transformation. The proof here transports
the exponential power series through matrix entries: the angular block is its
own matrix exponential, and the last row is `[0 1]`. It needs no normalization,
nonzero-axis assumption, or closed-form translation formula.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

private def matrixEntry {n : Type*} [Fintype n] (i j : n) :
    Matrix n n ℝ →L[ℝ] ℝ :=
  (show Matrix n n ℝ →ₗ[ℝ] ℝ from
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

private theorem exp_entry_of_pow_entry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m m ℝ) (N : Matrix n n ℝ) (i j : m) (k l : n)
    (h : ∀ a : ℕ, (M ^ a) i j = (N ^ a) k l) :
    NormedSpace.exp M i j = NormedSpace.exp N k l := by
  have hM := (matrixEntry i j).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M)
  have hN := (matrixEntry k l).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) N)
  change HasSum (fun a : ℕ => (a.factorial⁻¹ : ℝ) * (M ^ a) i j)
    (NormedSpace.exp M i j) at hM
  change HasSum (fun a : ℕ => (a.factorial⁻¹ : ℝ) * (N ^ a) k l)
    (NormedSpace.exp N k l) at hN
  simp_rw [h] at hM
  exact hM.unique hN

private theorem upper_block_pow
    (A : Matrix (Fin 3) (Fin 3) ℝ) (B : Matrix (Fin 3) (Fin 1) ℝ)
    (D : Matrix (Fin 1) (Fin 1) ℝ) (n : ℕ) :
    ∃ C : Matrix (Fin 3) (Fin 1) ℝ,
      (Matrix.fromBlocks A B 0 D) ^ n = Matrix.fromBlocks (A ^ n) C 0 (D ^ n) := by
  induction n with
  | zero => exact ⟨0, by simp only [pow_zero]; exact Matrix.fromBlocks_one.symm⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨A ^ n * B + C * D, ?_⟩
    rw [pow_succ, hC, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, pow_succ]

/-- The diagonal blocks of an upper block-triangular exponential are the
exponentials of the diagonal blocks. Its lower-left block remains zero. -/
theorem exp_upper_block_diagonal
    (A : Matrix (Fin 3) (Fin 3) ℝ) (B : Matrix (Fin 3) (Fin 1) ℝ)
    (D : Matrix (Fin 1) (Fin 1) ℝ) :
    (NormedSpace.exp (Matrix.fromBlocks A B 0 D)).toBlocks₁₁ = NormedSpace.exp A ∧
    (NormedSpace.exp (Matrix.fromBlocks A B 0 D)).toBlocks₂₁ = 0 ∧
    (NormedSpace.exp (Matrix.fromBlocks A B 0 D)).toBlocks₂₂ = NormedSpace.exp D := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    apply exp_entry_of_pow_entry _ A (Sum.inl i) (Sum.inl j) i j
    intro n
    obtain ⟨C, hC⟩ := upper_block_pow A B D n
    rw [hC]
    rfl
  · ext i j
    have h := exp_entry_of_pow_entry (Matrix.fromBlocks A B 0 D)
      (0 : HomogeneousMatrix) (Sum.inr i) (Sum.inl j) (Sum.inr i) (Sum.inl j) (by
        intro n
        obtain ⟨C, hC⟩ := upper_block_pow A B D n
        rw [hC]
        cases n <;> simp)
    simpa [Matrix.toBlocks₂₁] using h
  · ext i j
    apply exp_entry_of_pow_entry _ D (Sum.inr i) (Sum.inr j) i j
    intro n
    obtain ⟨C, hC⟩ := upper_block_pow A B D n
    rw [hC]
    rfl

namespace Twist

/-- Actual exponential block identities for every twist, including zero and
pure translation. The translation block is unrestricted here. -/
theorem matrix_exp_blocks (ξ : Twist) (t : ℝ) :
    (NormedSpace.exp (t • ξ.hat)).toBlocks₁₁ =
      NormedSpace.exp (t • Vec3.hat ξ.angular) ∧
    (NormedSpace.exp (t • ξ.hat)).toBlocks₂₁ = 0 ∧
    (NormedSpace.exp (t • ξ.hat)).toBlocks₂₂ = 1 := by
  have h := exp_upper_block_diagonal (t • Vec3.hat ξ.angular)
    (t • Matrix.of fun i (_ : Fin 1) => ξ.linear i) 0
  simpa only [hat, Matrix.fromBlocks_smul, smul_zero, NormedSpace.exp_zero] using h

/-- MLS Proposition 2.8: the matrix exponential of every real twist satisfies
the independent homogeneous `SE(3)` constraints, with determinant `+1`. -/
theorem matrix_exp_mem (ξ : Twist) (t : ℝ) :
    (NormedSpace.exp (t • ξ.hat)).toBlocks₁₁ ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧
    (NormedSpace.exp (t • ξ.hat)).toBlocks₂₁ = 0 ∧
    (NormedSpace.exp (t • ξ.hat)).toBlocks₂₂ = 1 := by
  obtain ⟨hR, hL, hD⟩ := matrix_exp_blocks ξ t
  refine ⟨?_, hL, hD⟩
  rw [hR]
  exact (Rotation.exp ξ.angular t).property

/-- A constant twist generates a rigid displacement via the actual matrix
exponential. Its active interpretation uses one fixed reference frame. -/
def exp (ξ : Twist) (t : ℝ) : RigidTransform :=
  HomogeneousTransform.toRigidTransform
    ⟨NormedSpace.exp (t • ξ.hat), matrix_exp_mem ξ t⟩

@[simp] theorem toHomogeneous_exp (ξ : Twist) (t : ℝ) :
    (exp ξ t).toHomogeneous = NormedSpace.exp (t • ξ.hat) :=
  HomogeneousTransform.toRigidTransform_toHomogeneous _

@[simp] theorem exp_rotation (ξ : Twist) (t : ℝ) :
    (exp ξ t).rotation = Rotation.exp ξ.angular t := by
  apply Subtype.ext
  exact (matrix_exp_blocks ξ t).1

@[simp] theorem exp_zero (ξ : Twist) : exp ξ 0 = 1 := by
  apply RigidTransform.toHomogeneous_injective
  simp

@[simp] theorem exp_zero_twist (t : ℝ) : exp 0 t = 1 := by
  apply RigidTransform.toHomogeneous_injective
  simp

/-- One-parameter composition for one arbitrary constant twist. -/
theorem exp_add (ξ : Twist) (s t : ℝ) : exp ξ (s + t) = exp ξ s * exp ξ t := by
  apply RigidTransform.toHomogeneous_injective
  simp only [toHomogeneous_exp, RigidTransform.toHomogeneous_mul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl ξ.hat).smul_left s).smul_right t)

@[simp] theorem exp_neg (ξ : Twist) (t : ℝ) : exp ξ (-t) = (exp ξ t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← exp_add, neg_add_cancel, exp_zero]

/-- Both linear and angular components scale together. This identity has no
normalization premise, and covers zero factors as well. -/
theorem exp_smul (c : ℝ) (ξ : Twist) (t : ℝ) : exp (c • ξ) t = exp ξ (t * c) := by
  apply RigidTransform.toHomogeneous_injective
  simp [hat_smul, smul_smul]

end Twist
end RoboLean
