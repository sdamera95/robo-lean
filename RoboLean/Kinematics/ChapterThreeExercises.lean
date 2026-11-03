import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# MLS Chapter 3, Exercise 12: the task-oriented manipulability measure

MLS Chapter 3, Exercise 12, printed p. 150: for a Jacobian `J : ℝⁿ → ℝᵖ` (`p = 3` or `6`) and a task
ellipsoid with principal axes of lengths `α₁, …, αₚ`, scaled by `β`,
`E_β = {y : (y₁/α₁)² + ⋯ + (yₚ/αₚ)² ≤ β}`, the exercise defines
`μ_t(θ) := max{β : J(θ)(B₁) ⊂ E_β}` with `B₁` the closed unit ball, and asks to characterize it.

Reading. `E_β` grows with `β`, so the set `{β : J(B₁) ⊂ E_β}` is closed upwards and has no maximum
(`not_bddAbove_setOf_image_subset_taskEllipsoid`); the printed `max` is read as the least such `β`,
the smallest scaling of the task ellipsoid that contains the image of the unit ball. With the
scaling `S y = (y₁/α₁, …, yₚ/αₚ)` (`taskScaling`), that least value is `‖S ∘ J‖²`, the squared
operator norm (`isLeast_setOf_image_subset_taskEllipsoid`); for equal axes `αᵢ = a` it is
`‖J‖² / a²`. The operator norm is the largest singular value (`opNorm_eq_singularValues_zero`), so
`μ_t` is the square of the largest singular value of `S ∘ J`, and for equal axes `σ_max(J)² / a²`.
In general it is not a function of the singular values of `J` and the `αᵢ` alone: it also depends on
how the principal directions of `J(B₁)` sit relative to the axes of the task ellipsoid. The
statements hold for every `n`, `p` and every real `αᵢ`, with Lean's `y / 0 = 0`.
-/

noncomputable section

open Metric

namespace RoboLean

variable {n p : ℕ}

/-- The task ellipsoid `E_β = {y : (y₁/α₁)² + ⋯ + (yₚ/αₚ)² ≤ β}` of MLS Exercise 12, p. 150, with
principal axes along the coordinate axes of lengths `α₁, …, αₚ`, scaled by `β`. -/
def taskEllipsoid (α : Fin p → ℝ) (β : ℝ) : Set (EuclideanSpace ℝ (Fin p)) :=
  {y | ∑ i, (y i / α i) ^ 2 ≤ β}

/-- The scaling `y ↦ (y₁/α₁, …, yₚ/αₚ)` that carries the task ellipsoid of MLS Exercise 12,
p. 150, to a ball: `E_β` is the set where its norm squared is at most `β`. -/
def taskScaling (α : Fin p → ℝ) : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.diagonal fun i => (α i)⁻¹))

/-- MLS Exercise 12, p. 150: `‖S y‖² = (y₁/α₁)² + ⋯ + (yₚ/αₚ)²` for the task scaling `S`. -/
theorem norm_taskScaling_apply_sq (α : Fin p → ℝ) (y : EuclideanSpace ℝ (Fin p)) :
    ‖taskScaling α y‖ ^ 2 = ∑ i, (y i / α i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [taskScaling, Matrix.mulVec_diagonal, div_eq_inv_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← abs_inv, ← abs_mul, sq_abs]

/-- **MLS Exercise 12, p. 150: when the image of the unit ball fits in the task ellipsoid.** For
every linear map `J` (a Jacobian, MLS p. 115) and every `β`, `J(B₁) ⊂ E_β` exactly when
`‖S ∘ J‖² ≤ β`, with `S` the task scaling and `‖·‖` the operator norm. -/
theorem image_closedBall_subset_taskEllipsoid_iff
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (α : Fin p → ℝ) (β : ℝ) :
    J '' closedBall 0 1 ⊆ taskEllipsoid α β ↔ ‖(taskScaling α).comp J‖ ^ 2 ≤ β := by
  constructor
  · intro hsub
    have hmem : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖taskScaling α (J x)‖ ^ 2 ≤ β := fun x hx => by
      have h : ∑ i, (J x i / α i) ^ 2 ≤ β := hsub ⟨x, hx, rfl⟩
      rwa [← norm_taskScaling_apply_sq] at h
    have hβ : 0 ≤ β := by
      have h := hmem 0 (by simp)
      simpa using h
    have hle : ‖(taskScaling α).comp J‖ ≤ √β := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _) fun x hx => ?_
      rw [ContinuousLinearMap.comp_apply]
      exact (Real.le_sqrt (norm_nonneg _) hβ).mpr (hmem x (by simp [hx]))
    calc ‖(taskScaling α).comp J‖ ^ 2 ≤ √β ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = β := Real.sq_sqrt hβ
  · rintro h _ ⟨x, hx, rfl⟩
    show ∑ i, (J x i / α i) ^ 2 ≤ β
    rw [← norm_taskScaling_apply_sq]
    have h1 : ‖(taskScaling α).comp J x‖ ≤ ‖(taskScaling α).comp J‖ * 1 :=
      ContinuousLinearMap.le_opNorm_of_le _ (mem_closedBall_zero_iff.mp hx)
    rw [mul_one, ContinuousLinearMap.comp_apply] at h1
    calc ‖taskScaling α (J x)‖ ^ 2 ≤ ‖(taskScaling α).comp J‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ β := h

/-- **MLS Exercise 12, p. 150: the printed maximum does not exist.** The set
`{β : J(B₁) ⊂ E_β}` is not bounded above: it is the half-line from `‖S ∘ J‖²`. -/
theorem not_bddAbove_setOf_image_subset_taskEllipsoid
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (α : Fin p → ℝ) :
    ¬ BddAbove {β | J '' closedBall 0 1 ⊆ taskEllipsoid α β} := by
  rintro ⟨M, hM⟩
  have h₁ := le_max_left M (‖(taskScaling α).comp J‖ ^ 2)
  have h₂ := le_max_right M (‖(taskScaling α).comp J‖ ^ 2)
  have hm : max M (‖(taskScaling α).comp J‖ ^ 2) + 1 ∈
      {β | J '' closedBall 0 1 ⊆ taskEllipsoid α β} :=
    (image_closedBall_subset_taskEllipsoid_iff J α _).mpr (by linarith)
  linarith [hM hm]

/-- **MLS Exercise 12, p. 150: the task-oriented manipulability, read as the least `β`.** The
least `β` with `J(B₁) ⊂ E_β` is `‖S ∘ J‖²`, the squared operator norm of the Jacobian followed by
the task scaling. -/
theorem isLeast_setOf_image_subset_taskEllipsoid
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (α : Fin p → ℝ) :
    IsLeast {β | J '' closedBall 0 1 ⊆ taskEllipsoid α β} (‖(taskScaling α).comp J‖ ^ 2) := by
  exact ⟨(image_closedBall_subset_taskEllipsoid_iff J α _).mpr le_rfl,
    fun β hβ => (image_closedBall_subset_taskEllipsoid_iff J α β).mp hβ⟩

/-- **MLS Exercise 12, p. 150, for a task ellipsoid with equal axes.** If every `αᵢ = a`, the
least `β` with `J(B₁) ⊂ E_β` is `‖J‖² / a²` (for `a = 0` both sides are `0` in Lean's
convention). -/
theorem norm_taskScaling_comp_of_const
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (a : ℝ) :
    ‖(taskScaling fun _ : Fin p => a).comp J‖ ^ 2 = ‖J‖ ^ 2 / a ^ 2 := by
  have hS : (taskScaling fun _ : Fin p => a) = a⁻¹ • ContinuousLinearMap.id ℝ _ := by
    ext y i
    simp [taskScaling, Matrix.mulVec_diagonal]
  rw [hS, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow, div_eq_inv_mul]

/-- **MLS p. 128 (singular values as the square roots of the eigenvalues of `JᵀJ`) and Exercise 12,
p. 150: the operator norm is the largest singular value.** For a linear map `T` between
finite-dimensional real inner product spaces, `E` nontrivial, `‖T‖ = σ_max(T)`, the first singular
value of Mathlib's `LinearMap.singularValues` (square roots of the eigenvalues of `T*T`, in
decreasing order). -/
theorem opNorm_eq_singularValues_zero {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial E] (T : E →L[ℝ] F) :
    ‖T‖ = (T : E →ₗ[ℝ] F).singularValues 0 := by
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set A : E →ₗ[ℝ] F := (T : E →ₗ[ℝ] F) with hA
  set σ := A.singularValues 0 with hσ
  have hσ0 : 0 ≤ σ := A.singularValues_nonneg 0
  have hS := A.isSymmetric_adjoint_comp_self
  have hσsq : σ ^ 2 = hS.eigenvalues rfl ⟨0, hn⟩ := A.sq_singularValues_of_lt rfl hn
  have key : ∀ x : E, ‖T x‖ ^ 2 = inner ℝ ((LinearMap.adjoint A ∘ₗ A) x) x := by
    intro x
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
    rfl
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ hσ0 fun x => ?_
    set b := hS.eigenvectorBasis rfl
    have hsum : inner ℝ ((LinearMap.adjoint A ∘ₗ A) x) x =
        ∑ i, hS.eigenvalues rfl i * (inner ℝ x (b i) * inner ℝ (b i) x) := by
      rw [← b.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hS x (b i), hS.apply_eigenvectorBasis, real_inner_smul_right]
      simp only [RCLike.ofReal_real_eq_id, id]
      ring
    have hle : ∑ i, hS.eigenvalues rfl i * (inner ℝ x (b i) * inner ℝ (b i) x) ≤
        ∑ i, hS.eigenvalues rfl ⟨0, hn⟩ * (inner ℝ x (b i) * inner ℝ (b i) x) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine mul_le_mul_of_nonneg_right (hS.eigenvalues_antitone rfl (Fin.mk_le_mk.mpr
        (Nat.zero_le _))) ?_
      rw [real_inner_comm x (b i)]
      exact mul_self_nonneg _
    have hx : ∑ i, hS.eigenvalues rfl ⟨0, hn⟩ * (inner ℝ x (b i) * inner ℝ (b i) x) =
        σ ^ 2 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, b.sum_inner_mul_inner, real_inner_self_eq_norm_sq, hσsq]
    have h2 : ‖T x‖ ^ 2 ≤ (σ * ‖x‖) ^ 2 := by
      rw [key, hsum, mul_pow]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  · obtain ⟨v, hv⟩ := (A.hasEigenvalue_adjoint_comp_self_sq_singularValues hn).exists_hasEigenvector
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
    have h1 : ‖T v‖ ^ 2 = σ ^ 2 * ‖v‖ ^ 2 := by
      rw [key, hv.apply_eq_smul, real_inner_smul_left, real_inner_self_eq_norm_sq]
      simp [hσ]
    have h2 : ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
    have h3 : σ ^ 2 * ‖v‖ ^ 2 ≤ (‖T‖ * ‖v‖) ^ 2 := by
      rw [← h1]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : σ ^ 2 ≤ ‖T‖ ^ 2 := by
      rw [mul_pow] at h3
      exact le_of_mul_le_mul_right h3 (by positivity)
    exact (pow_le_pow_iff_left₀ hσ0 (norm_nonneg _) two_ne_zero).mp h4

/-- **MLS Exercise 12, p. 150, in terms of singular values.** For `n ≠ 0`, the least `β` with
`J(B₁) ⊂ E_β` is `σ_max(S ∘ J)²`, the square of the largest singular value of the Jacobian followed
by the task scaling `S y = (yᵢ/αᵢ)ᵢ`. -/
theorem isLeast_setOf_image_subset_taskEllipsoid_singularValues (hn : n ≠ 0)
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (α : Fin p → ℝ) :
    IsLeast {β | J '' closedBall 0 1 ⊆ taskEllipsoid α β}
      ((((taskScaling α).comp J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)).singularValues 0 ^ 2) := by
  have : NeZero n := ⟨hn⟩
  rw [← opNorm_eq_singularValues_zero]
  exact isLeast_setOf_image_subset_taskEllipsoid J α

/-- **MLS Exercise 12, p. 150, for equal axes, in terms of singular values.** For `n ≠ 0` and every
`αᵢ = a`, the least `β` with `J(B₁) ⊂ E_β` is `σ_max(J)² / a²`. -/
theorem isLeast_setOf_image_subset_taskEllipsoid_const (hn : n ≠ 0)
    (J : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (a : ℝ) :
    IsLeast {β | J '' closedBall 0 1 ⊆ taskEllipsoid (fun _ => a) β}
      ((J : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)).singularValues 0 ^ 2 / a ^ 2) := by
  have : NeZero n := ⟨hn⟩
  rw [← opNorm_eq_singularValues_zero, ← norm_taskScaling_comp_of_const]
  exact isLeast_setOf_image_subset_taskEllipsoid J fun _ => a

end RoboLean
