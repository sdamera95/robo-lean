import RoboLean.Nonholonomic.OptimalInputs
import RoboLean.Control.StateTransition
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix

/-!
# Skew-symmetric linear systems are rotations: MLS Exercise 6 of Chapter 8 and (8.17)

MLS Chapter 8, Exercise 6, printed pp. 392–393: "if `u` satisfies the differential equation
`u̇ = Ω(t) u` for some `Ω ∈ so(m)`, then the solution of `u` is of the form `u(t) = U(t) u(0)` for
some `U(t) ∈ SO(m)`"; the proof of Proposition 8.4 (p. 373) uses it as (8.17) for the optimal
input, whose derivative is (8.16) `u̇ = Ω(q, p) u`.

**What is formalized.** The rotation `U(t)` is the matrix of the library's state-transition map
`Φ(t, 0)` of `ż = Ω(t) z` (`IsStateTransition`, MLS p. 184). For `Ω(t)` skew-symmetric at every
`t ≥ 0`, `Φ(t, s)` preserves the dot product (the derivative of `Φ(t, s)x ⬝ Φ(t, s)y` vanishes), so
its matrix is orthogonal, and its determinant is `1` by continuity from `Φ(s, s) = 1`
(`IsStateTransition.clmMatrix_mem_specialOrthogonalGroup`). Every solution on `[0, T]` is
`u(t) = Φ(t, 0) u(0)` (`IsStateTransition.eq_apply_of_hasDerivAt`). The book's form
(`exists_specialOrthogonal_of_skew`): for `Ω` continuous and skew on `[0, T]` there is one family
`U(t) ∈ SO(m)`, `t ∈ [0, T]`, with `u(t) = U(t) u(0)` for every solution `u`. Applied to (8.16):
the optimal input of Proposition 8.4 is `u(t) = U(t) u(0)` with `U(t) ∈ SO(m)` (8.17), for input
fields with continuous derivatives (`optimalInput_eq_mulVec`), and its norm is constant by that
route (`optimalInput_dotProduct_self_of_specialOrthogonal`).

**Conventions and added hypotheses.** Vectors are `Fin m → ℝ` with the Euclidean dot product
`⬝ᵥ`; a matrix acts as the continuous linear map `x ↦ Ω x` (`matrixCLM`) and a continuous linear
map has the matrix `clmMatrix` (Mathlib's `LinearMap.toMatrix'`); `SO(m)` is Mathlib's
`Matrix.specialOrthogonalGroup (Fin m) ℝ`. The book states no regularity of `Ω`; the state-
transition map exists for `Ω` continuous (`exists_isStateTransition`), which is assumed for the
book's form; for (8.17) it follows from fields with continuous derivatives along a differentiable
curve `(q, p)`. For one solution alone, norm preservation already gives some rotation taking
`u(0)` to `u(t)`; the content here is that one `U(t)` serves every solution.
-/

noncomputable section

open Set Filter Topology Matrix VectorField RoboLean.Stability

namespace RoboLean
namespace Nonholonomic

variable {m : ℕ}

/-- **A matrix as a continuous linear map,** `x ↦ Ω x` on `Fin m → ℝ` (MLS Exercise 6 of
Chapter 8, pp. 392–393, writes `u̇ = Ω(t) u` with matrices). -/
def matrixCLM (Ω : Matrix (Fin m) (Fin m) ℝ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' Ω)

/-- `matrixCLM Ω x = Ω x` (MLS Exercise 6 of Chapter 8, pp. 392–393). -/
@[simp]
theorem matrixCLM_apply (Ω : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    matrixCLM Ω x = Ω *ᵥ x := by
  simp [matrixCLM, Matrix.toLin'_apply]

/-- **The matrix of a continuous linear map of `Fin m → ℝ`** (Mathlib's `LinearMap.toMatrix'`),
the form in which MLS Exercise 6 of Chapter 8 (pp. 392–393) writes `U(t)`. -/
def clmMatrix (L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) : Matrix (Fin m) (Fin m) ℝ :=
  LinearMap.toMatrix' (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))

/-- `clmMatrix L x = L x` (for MLS Exercise 6 of Chapter 8, pp. 392–393). -/
@[simp]
theorem clmMatrix_mulVec (L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (x : Fin m → ℝ) :
    clmMatrix L *ᵥ x = L x := by
  rw [clmMatrix, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

/-- **A skew-symmetric matrix is orthogonal to the identity in the dot product:**
`(Ω x) ⬝ y + x ⬝ (Ω y) = 0` for `Ωᵀ = −Ω` (MLS Exercise 6 of Chapter 8, pp. 392–393,
`Ω ∈ so(m)`). -/
theorem mulVec_dotProduct_add_dotProduct_mulVec_of_skew {Ω : Matrix (Fin m) (Fin m) ℝ}
    (hΩ : Ωᵀ = -Ω) (x y : Fin m → ℝ) : (Ω *ᵥ x) ⬝ᵥ y + x ⬝ᵥ (Ω *ᵥ y) = 0 := by
  have h : x ⬝ᵥ (Ω *ᵥ y) = -((Ω *ᵥ x) ⬝ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hΩ, Matrix.neg_mulVec,
      neg_dotProduct]
  rw [h, add_neg_cancel]

/-- **A matrix preserving the dot product is orthogonal:** if `(M x) ⬝ (M y) = x ⬝ y` for all
`x, y`, then `M ∈ O(m)` (for MLS Exercise 6 of Chapter 8, pp. 392–393). -/
theorem mem_orthogonalGroup_of_dotProduct {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : ∀ x y, (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ y) : M ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  have h := hM (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, single_dotProduct, one_mul] at h
  rw [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply] at *
  rw [← h]
  simp only [Matrix.col, dotProduct, Matrix.transpose_apply]

/-- **An orthogonal matrix preserves the dot product,** `(U x) ⬝ (U y) = x ⬝ y` (for MLS
Proposition 8.4, p. 373: "from this fact the statement of the proposition follows"). -/
theorem mulVec_dotProduct_mulVec_of_mem_orthogonalGroup {U : Matrix (Fin m) (Fin m) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin m) ℝ) (x y : Fin m → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hU
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- The derivative of a dot product of two curves, within a set. -/
private theorem hasDerivWithinAt_dotProduct {u v : ℝ → Fin m → ℝ} {u' v' : Fin m → ℝ}
    {S : Set ℝ} {t : ℝ} (hu : HasDerivWithinAt u u' S t) (hv : HasDerivWithinAt v v' S t) :
    HasDerivWithinAt (fun τ => u τ ⬝ᵥ v τ) (u' ⬝ᵥ v t + u t ⬝ᵥ v') S t := by
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivWithinAt_pi.1 hu i).mul (hasDerivWithinAt_pi.1 hv i)
  convert h using 1
  · funext τ
    simp [dotProduct]
  · simp only [dotProduct, ← Finset.sum_add_distrib]

/-- `clmMatrix` is continuous (a linear map between finite-dimensional spaces). -/
private theorem continuous_clmMatrix : Continuous (clmMatrix (m := m)) := by
  have : (clmMatrix (m := m)) = ((LinearMap.toMatrix' : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) ≃ₗ[ℝ]
      Matrix (Fin m) (Fin m) ℝ).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)) := by
    ext L
    rfl
  rw [this]
  exact LinearMap.continuous_of_finiteDimensional _

/-- `matrixCLM` is continuous (a linear map between finite-dimensional spaces). -/
private theorem continuous_matrixCLM : Continuous (matrixCLM (m := m)) := by
  have : (matrixCLM (m := m)) = ((LinearMap.toContinuousLinearMap :
      ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) ≃ₗ[ℝ] ((Fin m → ℝ) →L[ℝ] (Fin m → ℝ))).toLinearMap.comp
      (Matrix.toLin' : Matrix (Fin m) (Fin m) ℝ ≃ₗ[ℝ] _).toLinearMap) := by
    ext Ω
    rfl
  rw [this]
  exact LinearMap.continuous_of_finiteDimensional _

/-- `clmMatrix 1 = 1`. -/
private theorem clmMatrix_one : clmMatrix (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) = 1 := by
  ext i j
  simp [clmMatrix, LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply]

/-- The determinant of an orthogonal matrix is `±1`. -/
private theorem det_sq_of_mem_orthogonalGroup {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin m) ℝ) : M.det = 1 ∨ M.det = -1 := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hM
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have : (M.det - 1) * (M.det + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · left; linarith
  · right; linarith

namespace IsStateTransition

variable {Ω : ℝ → Matrix (Fin m) (Fin m) ℝ} {Φ : ℝ → ℝ → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)}

/-- **MLS Exercise 6 of Chapter 8, pp. 392–393: the state-transition map of `ż = Ω(t) z`
preserves the dot product** when `Ω(t)` is skew-symmetric for `t ≥ 0`:
`Φ(t, s)x ⬝ Φ(t, s)y = x ⬝ y` for `t, s ≥ 0` (`Φ` as in MLS p. 184, `IsStateTransition`). -/
theorem dotProduct_eq_of_skew (h : IsStateTransition (fun t => matrixCLM (Ω t)) Φ)
    (hΩ : ∀ t, 0 ≤ t → (Ω t)ᵀ = -Ω t) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x y : Fin m → ℝ) :
    Φ t s x ⬝ᵥ Φ t s y = x ⬝ᵥ y := by
  set f : ℝ → ℝ := fun τ => Φ τ s x ⬝ᵥ Φ τ s y with hf
  have hd : ∀ τ, 0 ≤ τ → HasDerivWithinAt f 0 (Ici 0) τ := by
    intro τ hτ
    have hx := (h.hasDerivWithinAt τ s hτ hs).clm_apply (hasDerivWithinAt_const τ _ x)
    have hy := (h.hasDerivWithinAt τ s hτ hs).clm_apply (hasDerivWithinAt_const τ _ y)
    have := hasDerivWithinAt_dotProduct hx hy
    convert this using 1
    simp only [mul_apply_eq_comp, map_zero, add_zero, matrixCLM_apply]
    rw [mulVec_dotProduct_add_dotProduct_mulVec_of_skew (hΩ τ hτ)]
  have hconst : ∀ r, 0 ≤ r → f r = f 0 := by
    intro r hr
    refine constant_of_has_deriv_right_zero (fun τ hτ => (hd τ hτ.1).continuousWithinAt.mono
      (Icc_subset_Ici_self)) (fun τ hτ => (hd τ hτ.1).mono (Ici_subset_Ici.2 hτ.1)) r ⟨hr, le_rfl⟩
  have h1 := hconst t ht
  have h2 := hconst s hs
  have h3 : f s = x ⬝ᵥ y := by
    simp only [hf, h.self_eq_one s hs, one_apply_eq_self]
  change f t = x ⬝ᵥ y
  rw [h1, ← h2, h3]

/-- **MLS Exercise 6 of Chapter 8, pp. 392–393: `Φ(t, s)` is a rotation,** its matrix lies
in `SO(m)` for `t, s ≥ 0`, when `Ω(t)` is skew-symmetric for `t ≥ 0`: orthogonal by
`dotProduct_eq_of_skew`, determinant `1` by continuity in `t` from `Φ(s, s) = 1`. -/
theorem clmMatrix_mem_specialOrthogonalGroup (h : IsStateTransition (fun t => matrixCLM (Ω t)) Φ)
    (hΩ : ∀ t, 0 ≤ t → (Ω t)ᵀ = -Ω t) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    clmMatrix (Φ t s) ∈ Matrix.specialOrthogonalGroup (Fin m) ℝ := by
  have horth : ∀ τ, 0 ≤ τ → clmMatrix (Φ τ s) ∈ Matrix.orthogonalGroup (Fin m) ℝ := fun τ hτ =>
    mem_orthogonalGroup_of_dotProduct fun x y => by
      rw [clmMatrix_mulVec, clmMatrix_mulVec, dotProduct_eq_of_skew h hΩ hτ hs]
  refine Matrix.mem_specialOrthogonalGroup_iff.2 ⟨horth t ht, ?_⟩
  set D : ℝ → ℝ := fun τ => (clmMatrix (Φ τ s)).det with hD
  have hDc : ContinuousOn D (Ici 0) :=
    (continuous_id.matrix_det).comp_continuousOn
      (continuous_clmMatrix.comp_continuousOn (h.continuousOn hs))
  have hDs : D s = 1 := by
    simp only [hD, h.self_eq_one s hs, clmMatrix_one, Matrix.det_one]
  rcases det_sq_of_mem_orthogonalGroup (horth t ht) with h1 | h1
  · exact h1
  exfalso
  obtain ⟨c, hc, hc0⟩ := isPreconnected_Ici.intermediate_value (show t ∈ Ici (0 : ℝ) from ht)
    (show s ∈ Ici (0 : ℝ) from hs) hDc (show (0 : ℝ) ∈ Icc (D t) (D s) by
      rw [hDs]
      exact ⟨by simp only [hD]; linarith, zero_le_one⟩)
  rcases det_sq_of_mem_orthogonalGroup (horth c hc) with h2 | h2
  · simp only [hD] at hc0; linarith
  · simp only [hD] at hc0; linarith

/-- **Solutions on `[0, T]` are `u(t) = Φ(t, 0) u(0)`** (MLS eq. (8.17), p. 373, and Exercise 6 of
Chapter 8, pp. 392–393, for the linear time-varying system `u̇ = A(t) u` with
state-transition map `Φ` of MLS p. 184): if `u̇(t) = A(t) u(t)` for `t ∈ [0, T]`, then
`u(t) = Φ(t, 0) u(0)` there. A local form of `IsStateTransition.eq_of_isSolution`, for solutions
on a bounded interval. -/
theorem eq_apply_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {Ψ : ℝ → ℝ → E →L[ℝ] E} (h : IsStateTransition A Ψ)
    {u : ℝ → E} {T : ℝ} (hu : ∀ t ∈ Icc 0 T, HasDerivAt u (A t (u t)) t) :
    ∀ t ∈ Icc 0 T, u t = Ψ t 0 (u 0) := by
  intro t ht
  have hw : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun σ => Ψ 0 σ (u σ)) 0 (Ici 0) τ := by
    intro τ hτ
    have h1 := (h.hasDerivWithinAt_snd le_rfl hτ.1).clm_apply (hu τ hτ).hasDerivWithinAt
    convert h1 using 1
    simp [mul_apply_eq_comp]
  have hc := constant_of_has_deriv_right_zero (f := fun σ => Ψ 0 σ (u σ)) (a := 0) (b := T)
    (fun τ hτ => (hw τ hτ).continuousWithinAt.mono Icc_subset_Ici_self)
    (fun τ hτ => (hw τ (Ico_subset_Icc_self hτ)).mono (Ici_subset_Ici.2 hτ.1)) t ht
  simp only [h.self_eq_one 0 le_rfl, one_apply_eq_self] at hc
  calc u t = Ψ t 0 (Ψ 0 t (u t)) := by
        rw [← mul_apply_eq_comp, h.mul_eq_one ht.1 le_rfl, one_apply_eq_self]
    _ = Ψ t 0 (u 0) := by rw [hc]

end IsStateTransition

/-- **MLS Exercise 6 of Chapter 8, pp. 392–393, in the book's form:** for `Ω` continuous on
`[0, T]` with `Ω(t)` skew-symmetric there, there are `U(t) ∈ SO(m)`, `t ∈ [0, T]`, such that every
solution of `u̇ = Ω(t) u` on `[0, T]` is `u(t) = U(t) u(0)`. `U(t)` is the matrix of the
state-transition map `Φ(t, 0)` (MLS p. 184) of `Ω` extended by `Ω(T)` after `T`. Continuity of
`Ω` is an added hypothesis (the book states none). -/
theorem exists_specialOrthogonal_of_skew {Ω : ℝ → Matrix (Fin m) (Fin m) ℝ} {T : ℝ}
    (hΩc : ContinuousOn Ω (Icc 0 T)) (hΩ : ∀ t ∈ Icc 0 T, (Ω t)ᵀ = -Ω t) :
    ∃ U : ℝ → Matrix (Fin m) (Fin m) ℝ,
      (∀ t ∈ Icc 0 T, U t ∈ Matrix.specialOrthogonalGroup (Fin m) ℝ) ∧
      ∀ u : ℝ → Fin m → ℝ, (∀ t ∈ Icc 0 T, HasDerivAt u (Ω t *ᵥ u t) t) →
        ∀ t ∈ Icc 0 T, u t = U t *ᵥ u 0 := by
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨fun _ => 1, fun t ht => absurd (ht.1.trans ht.2) hT,
      fun _ _ t ht => absurd (ht.1.trans ht.2) hT⟩
  have hmaps : ∀ t, 0 ≤ t → min t T ∈ Icc 0 T := fun t ht => ⟨le_min ht hT, min_le_right _ _⟩
  have hcont : ContinuousOn (fun t => matrixCLM (Ω (min t T))) (Ici 0) :=
    continuous_matrixCLM.comp_continuousOn
      (hΩc.comp (continuous_id.min continuous_const).continuousOn fun t ht => hmaps t ht)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_matrixCLM.comp_continuousOn hΩc)
  obtain ⟨Φ, hΦ⟩ := exists_isStateTransition hcont (M := M) fun t ht => hM _ (hmaps t ht)
  refine ⟨fun t => clmMatrix (Φ t 0), fun t ht =>
    IsStateTransition.clmMatrix_mem_specialOrthogonalGroup hΦ (fun τ hτ => hΩ _ (hmaps τ hτ))
      ht.1 le_rfl,
    fun u hu t ht => ?_⟩
  rw [clmMatrix_mulVec]
  refine IsStateTransition.eq_apply_of_hasDerivAt hΦ (fun τ hτ => ?_) t ht
  simp only [matrixCLM_apply, min_eq_left hτ.2]
  exact hu τ hτ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS p. 373: `t ↦ Ω(q(t), p(t))` is continuous** along a continuous curve `(q, p)` when the
input fields have continuous derivatives (`C¹`; MLS: smooth), so that (8.16) has a state-transition
map. -/
theorem continuousOn_optimalOmega {g : Fin m → E → E} (hg : ∀ i, ContDiff ℝ 1 (g i))
    {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ} {s : Set ℝ} (hq : ContinuousOn q s) (hp : ContinuousOn p s) :
    ContinuousOn (fun t => optimalOmega g (q t) (p t)) s := by
  have hb : ∀ i j, Continuous (lieBracket ℝ (g i) (g j)) := by
    intro i j
    have h1 := ((hg j).continuous_fderiv one_ne_zero).clm_apply (hg i).continuous
    have h2 := ((hg i).continuous_fderiv one_ne_zero).clm_apply (hg j).continuous
    exact h1.sub h2
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [optimalOmega, Matrix.of_apply]
  exact hp.clm_apply ((hb i j).comp_continuousOn hq)

/-- **MLS Proposition 8.4, p. 373, eq. (8.17): the optimal input is `u(t) = U(t) u(0)` with
`U(t) ∈ SO(m)`.** Along a curve `(q, p)` on `[0, T]` with `q̇ = Σ gᵢ(q) uᵢ` and `ṗ = −∂H/∂q`
(8.12), for the input (8.13) and input fields with continuous derivatives: (8.16) and Exercise 6
(`exists_specialOrthogonal_of_skew`). The necessary conditions replace optimality, and the rank
condition is not used. -/
theorem optimalInput_eq_mulVec {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ} {T : ℝ}
    (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t) :
    ∃ U : ℝ → Matrix (Fin m) (Fin m) ℝ, ∀ t ∈ Icc 0 T,
      U t ∈ Matrix.specialOrthogonalGroup (Fin m) ℝ ∧
        optimalInput g q p t = U t *ᵥ optimalInput g q p 0 := by
  have hqc : ContinuousOn q (Icc 0 T) := fun t ht => (hq t ht).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Icc 0 T) := fun t ht => (hp t ht).continuousAt.continuousWithinAt
  obtain ⟨U, hU, hsol⟩ := exists_specialOrthogonal_of_skew
    (Ω := fun t => optimalOmega g (q t) (p t)) (continuousOn_optimalOmega hg hqc hpc)
    fun t _ => optimalOmega_transpose _ _ _
  have hdiff : ∀ i, ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (g i) (q t) := fun i t _ =>
    (hg i).differentiable one_ne_zero _
  exact ⟨U, fun t ht => ⟨hU t ht, hsol _ (hasDerivAt_optimalInput hdiff hq hp) t ht⟩⟩

/-- **MLS Proposition 8.4, p. 373, by the book's route:** the norm of the optimal input is
constant because `u(t) = U(t) u(0)` with `U(t) ∈ SO(m)` (8.17), under the hypotheses of
`optimalInput_eq_mulVec`. -/
theorem optimalInput_dotProduct_self_of_specialOrthogonal {g : Fin m → E → E} {q : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {T : ℝ} (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t) :
    ∀ t ∈ Icc 0 T, optimalInput g q p t ⬝ᵥ optimalInput g q p t =
      optimalInput g q p 0 ⬝ᵥ optimalInput g q p 0 := by
  obtain ⟨U, hU⟩ := optimalInput_eq_mulVec hg hq hp
  intro t ht
  obtain ⟨hUt, he⟩ := hU t ht
  rw [he]
  exact mulVec_dotProduct_mulVec_of_mem_orthogonalGroup
    (Matrix.mem_specialOrthogonalGroup_iff.1 hUt).1 _ _

end Nonholonomic
end RoboLean
