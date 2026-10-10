import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Quadratic comparison bounds

Two-sided bounds of the form `a * ‖y‖ ^ 2 ≤ Q y ≤ b * ‖y‖ ^ 2` for degree-two homogeneous
continuous functions, uniformly over a compact parameter set, and their specialization to
quadratic forms `v ⬝ᵥ (A *ᵥ v)` of real square matrices.

These are the comparison bounds that MLS Theorem 4.5 (printed p. 183) asks of a Lyapunov function,
for the quadratic forms that MLS Definition 4.4 (printed p. 182) uses. The norm is the ambient norm
of the space; on `Fin n → ℝ` this is Mathlib's sup norm, not the Euclidean norm, which is why the
bounds are obtained from compactness of the unit sphere rather than from eigenvalues.
-/

open Matrix

namespace RoboLean
namespace QuadraticBounds

variable {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E]

omit [ProperSpace E] in
/-- A degree-two homogeneous function vanishes at the origin. -/
private lemma apply_zero_of_hom {Q : E → ℝ} (hhom : ∀ (c : ℝ) y, Q (c • y) = c ^ 2 * Q y) :
    Q 0 = 0 := by
  simpa using hhom 0 0

omit [ProperSpace E] in
/-- The normalized vector `‖y‖⁻¹ • y` of a nonzero `y` lies on the unit sphere. -/
private lemma inv_norm_smul_mem_sphere {y : E} (hy : y ≠ 0) :
    ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 := by
  have h : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]

omit [ProperSpace E] in
/-- Homogeneity rewrites `Q y` as `‖y‖ ^ 2` times the value at the normalized vector. -/
private lemma apply_eq_sq_norm_mul {Q : E → ℝ} (hhom : ∀ (c : ℝ) y, Q (c • y) = c ^ 2 * Q y)
    {y : E} (hy : y ≠ 0) : Q y = ‖y‖ ^ 2 * Q (‖y‖⁻¹ • y) := by
  have h : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [← hhom, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- Uniform lower bound for a family of degree-two homogeneous functions: if `Q p y` is jointly
continuous in `(p, y)`, satisfies `Q p (c • y) = c ^ 2 * Q p y`, and is positive at every nonzero
`y` for every parameter `p` in the compact set `K`, then some `a > 0` gives
`a * ‖y‖ ^ 2 ≤ Q p y` for all `p ∈ K` and all `y`. Supports the lower comparison bound of
MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4 (printed p. 182).
The norm is the ambient norm of `E` (the sup norm on `Fin n → ℝ`). -/
theorem exists_pos_mul_sq_norm_le {K : Set P} (hK : IsCompact K) {Q : P → E → ℝ}
    (hQ : Continuous fun z : P × E => Q z.1 z.2)
    (hhom : ∀ p (c : ℝ) y, Q p (c • y) = c ^ 2 * Q p y)
    (hpos : ∀ p ∈ K, ∀ y, y ≠ 0 → 0 < Q p y) :
    ∃ a > 0, ∀ p ∈ K, ∀ y, a * ‖y‖ ^ 2 ≤ Q p y := by
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  obtain ⟨a, ha, hmin⟩ := hS.exists_forall_le' (f := fun z : P × E => Q z.1 z.2)
    hQ.continuousOn (a := 0) fun z hz => by
      refine hpos z.1 hz.1 z.2 ?_
      have h1 : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
      intro h0
      simp [h0] at h1
  refine ⟨a, ha, fun p hp y => ?_⟩
  by_cases hy : y = 0
  · simp [hy, apply_zero_of_hom (hhom p)]
  · rw [apply_eq_sq_norm_mul (hhom p) hy, mul_comm a]
    exact mul_le_mul_of_nonneg_left
      (hmin (p, ‖y‖⁻¹ • y) ⟨hp, inv_norm_smul_mem_sphere hy⟩) (sq_nonneg _)

/-- Uniform upper bound for a family of degree-two homogeneous functions: if `Q p y` is jointly
continuous in `(p, y)` and satisfies `Q p (c • y) = c ^ 2 * Q p y`, then some `b > 0` gives
`Q p y ≤ b * ‖y‖ ^ 2` for all `p` in the compact set `K` and all `y`. Supports the upper
comparison bound of MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4
(printed p. 182). The norm is the ambient norm of `E` (the sup norm on `Fin n → ℝ`). -/
theorem exists_le_mul_sq_norm {K : Set P} (hK : IsCompact K) {Q : P → E → ℝ}
    (hQ : Continuous fun z : P × E => Q z.1 z.2)
    (hhom : ∀ p (c : ℝ) y, Q p (c • y) = c ^ 2 * Q p y) :
    ∃ b > 0, ∀ p ∈ K, ∀ y, Q p y ≤ b * ‖y‖ ^ 2 := by
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  obtain ⟨M, hM⟩ := hS.bddAbove_image (f := fun z : P × E => Q z.1 z.2) hQ.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le one_pos (le_max_left _ _), fun p hp y => ?_⟩
  by_cases hy : y = 0
  · simp [hy, apply_zero_of_hom (hhom p)]
  · rw [apply_eq_sq_norm_mul (hhom p) hy, mul_comm (max 1 M)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact (hM ⟨(p, ‖y‖⁻¹ • y), ⟨hp, inv_norm_smul_mem_sphere hy⟩, rfl⟩).trans (le_max_right _ _)

/-- Lower bound for one degree-two homogeneous function: if `Q` is continuous, satisfies
`Q (c • y) = c ^ 2 * Q y` and is positive at every nonzero `y`, then some `a > 0` gives
`a * ‖y‖ ^ 2 ≤ Q y`. Supports the lower comparison bound of MLS Theorem 4.5 (printed p. 183) for
quadratic forms as in MLS Definition 4.4 (printed p. 182). The norm is the ambient norm of `E`
(the sup norm on `Fin n → ℝ`). -/
theorem exists_pos_mul_sq_norm_le_of_continuous {Q : E → ℝ} (hQ : Continuous Q)
    (hhom : ∀ (c : ℝ) y, Q (c • y) = c ^ 2 * Q y) (hpos : ∀ y, y ≠ 0 → 0 < Q y) :
    ∃ a > 0, ∀ y, a * ‖y‖ ^ 2 ≤ Q y := by
  obtain ⟨a, ha, h⟩ := exists_pos_mul_sq_norm_le (P := Unit) isCompact_univ
    (Q := fun _ => Q) (hQ.comp continuous_snd) (fun _ => hhom) (fun _ _ => hpos)
  exact ⟨a, ha, h () (Set.mem_univ _)⟩

/-- Upper bound for one degree-two homogeneous function: if `Q` is continuous and satisfies
`Q (c • y) = c ^ 2 * Q y`, then some `b > 0` gives `Q y ≤ b * ‖y‖ ^ 2`. Supports the upper
comparison bound of MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4
(printed p. 182). The norm is the ambient norm of `E` (the sup norm on `Fin n → ℝ`). -/
theorem exists_le_mul_sq_norm_of_continuous {Q : E → ℝ} (hQ : Continuous Q)
    (hhom : ∀ (c : ℝ) y, Q (c • y) = c ^ 2 * Q y) :
    ∃ b > 0, ∀ y, Q y ≤ b * ‖y‖ ^ 2 := by
  obtain ⟨b, hb, h⟩ := exists_le_mul_sq_norm (P := Unit) isCompact_univ
    (Q := fun _ => Q) (hQ.comp continuous_snd) (fun _ => hhom)
  exact ⟨b, hb, h () (Set.mem_univ _)⟩

variable {n : ℕ}

/-- The quadratic form `v ↦ v ⬝ᵥ (A *ᵥ v)` is degree-two homogeneous. -/
private lemma dotProduct_mulVec_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (v : Fin n → ℝ) :
    (c • v) ⬝ᵥ (A *ᵥ (c • v)) = c ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Uniform lower bound for a continuous family of positive definite matrices: if `A p` depends
continuously on `p` and is positive definite for every `p` in the compact set `K`, then some
`a > 0` gives `a * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A p *ᵥ v)` for all `p ∈ K` and all `v`. Supports the lower
comparison bound of MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4
(printed p. 182). The norm is Mathlib's sup norm on `Fin n → ℝ`. -/
theorem exists_pos_mul_sq_norm_le_dotProduct_mulVec {K : Set P} (hK : IsCompact K)
    {A : P → Matrix (Fin n) (Fin n) ℝ} (hA : Continuous A) (hpos : ∀ p ∈ K, (A p).PosDef) :
    ∃ a > 0, ∀ p ∈ K, ∀ v : Fin n → ℝ, a * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A p *ᵥ v) :=
  exists_pos_mul_sq_norm_le hK (Q := fun p v => v ⬝ᵥ (A p *ᵥ v))
    (continuous_snd.dotProduct ((hA.comp continuous_fst).matrix_mulVec continuous_snd))
    (fun p => dotProduct_mulVec_smul (A p))
    (fun p hp v hv => by simpa using (hpos p hp).dotProduct_mulVec_pos hv)

/-- Lower bound for one positive definite matrix: if `A` is positive definite, then some `a > 0`
gives `a * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A *ᵥ v)` for all `v`. Supports the lower comparison bound of
MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4 (printed p. 182).
The norm is Mathlib's sup norm on `Fin n → ℝ`. -/
theorem posDef_exists_pos_mul_sq_norm_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ a > 0, ∀ v : Fin n → ℝ, a * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A *ᵥ v) := by
  obtain ⟨a, ha, h⟩ := exists_pos_mul_sq_norm_le_dotProduct_mulVec (P := Unit) isCompact_univ
    (A := fun _ => A) continuous_const (fun _ _ => hA)
  exact ⟨a, ha, h () (Set.mem_univ _)⟩

/-- Upper bound of a quadratic form by the norm: for every real square matrix `B` there is
`b > 0` with `v ⬝ᵥ (B *ᵥ v) ≤ b * ‖v‖ ^ 2` for all `v`. Supports the upper comparison bound of
MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4 (printed p. 182).
The norm is Mathlib's sup norm on `Fin n → ℝ`. -/
theorem exists_dotProduct_mulVec_le_mul_sq_norm (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ b > 0, ∀ v : Fin n → ℝ, v ⬝ᵥ (B *ᵥ v) ≤ b * ‖v‖ ^ 2 :=
  exists_le_mul_sq_norm_of_continuous (Q := fun v => v ⬝ᵥ (B *ᵥ v))
    (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
    (dotProduct_mulVec_smul B)

/-- Comparison of a positive definite quadratic form with an arbitrary quadratic form: if `A` is
positive definite and `B` is any real square matrix, then some `c > 0` gives
`c * (v ⬝ᵥ (B *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v)` for all `v`. Supports the quadratic comparison bounds of
MLS Theorem 4.5 (printed p. 183) for quadratic forms as in MLS Definition 4.4 (printed p. 182);
the proof passes through Mathlib's sup norm on `Fin n → ℝ`. -/
theorem exists_pos_mul_dotProduct_mulVec_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ c > 0, ∀ v : Fin n → ℝ, c * (v ⬝ᵥ (B *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v) := by
  obtain ⟨a, ha, hlow⟩ := posDef_exists_pos_mul_sq_norm_le hA
  obtain ⟨b, hb, hup⟩ := exists_dotProduct_mulVec_le_mul_sq_norm B
  refine ⟨a / b, div_pos ha hb, fun v => ?_⟩
  calc a / b * (v ⬝ᵥ (B *ᵥ v)) ≤ a / b * (b * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hup v) (div_pos ha hb).le
    _ = a * ‖v‖ ^ 2 := by field_simp
    _ ≤ v ⬝ᵥ (A *ᵥ v) := hlow v

end QuadraticBounds
end RoboLean
