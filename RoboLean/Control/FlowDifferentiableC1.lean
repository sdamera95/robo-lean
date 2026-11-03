import RoboLean.Control.FlowDifferentiable

/-!
# The derivative of a flow is continuous in the initial state (MLS pp. 179 and 322–323)

**What MLS uses.** MLS asserts that "for each fixed `t`, `φ^f_t` is a local diffeomorphism of
`ℝⁿ` onto itself" (pp. 322–323) and, for Theorem 4.5 (p. 183), differentiates the solution in its
initial state. A local diffeomorphism in the usual sense, and the inverse function theorem behind
it, ask a derivative that is continuous in the point.

**Proved here.** For a flow `φ` differentiable in the initial state (`IsDifferentiableFlow`) whose
field has a derivative `Df` continuous and bounded by `K` on `[0, ∞) × E`, the derivative
`x ↦ D(t, s, x)` of `x ↦ φ(t, s, x)` is continuous for `0 ≤ s ≤ t`
(`IsDifferentiableFlow.continuous_fderiv`), so `φ(t, s, ·)` is strictly differentiable at every
point (`IsDifferentiableFlow.hasStrictFDerivAt`), the hypothesis of Mathlib's inverse function
theorem. Route: `Δ(τ) = D(τ, s, x') − D(τ, s, x)` solves
`Δ' = Df(τ, φ(τ, s, x')) Δ + (Df(τ, φ(τ, s, x')) − Df(τ, φ(τ, s, x))) D(τ, s, x)` with
`Δ(s) = 0`; the trajectories stay within `e^{K(t − s)} ‖x' − x‖` of each other (mean value
inequality with Grönwall's bound on `D`), `Df` is uniformly continuous near the compact arc
`{(τ, φ(τ, s, x)) : s ≤ τ ≤ t}`, and Grönwall's inequality bounds `Δ(t)`.

**Conventions.** As in `Control/FlowDerivative`: time first, `φ t s x` the state at time `t` of the
solution from `x` at time `s`, derivatives in the state Fréchet derivatives with the operator norm.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform continuity near a compact set (for the estimate behind MLS pp. 322–323): a continuous
map `g` moves points within `δ` of a compact set `C` by less than `η`. -/
private theorem exists_dist_lt_of_isCompact' {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {g : X → Y} (hg : Continuous g) {C : Set X} (hC : IsCompact C) {η : ℝ}
    (hη : 0 < η) : ∃ δ > 0, ∀ p ∈ C, ∀ q, dist p q < δ → dist (g p) (g q) < η := by
  obtain ⟨δ, hδ, h⟩ := Metric.mem_uniformity_dist.1
    (hC.uniformContinuousAt_of_continuousAt g (fun a _ => hg.continuousAt)
      (Metric.dist_mem_uniformity hη))
  exact ⟨δ, hδ, fun p hp q hpq => h hpq hp⟩

namespace IsDifferentiableFlow

variable {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E} {φ : ℝ → ℝ → E → E}
  {D : ℝ → ℝ → E → E →L[ℝ] E}

/-- **The derivative of the flow in the initial state is continuous (MLS pp. 322–323, `φ^f_t` a
local diffeomorphism; for Theorem 4.5, p. 183):** if `φ` is a flow differentiable in the initial
state with derivative `D` (`IsDifferentiableFlow`, time first) and `Df` is continuous on
`[0, ∞) × E` with `‖Df(t, y)‖ ≤ K` there, then `x ↦ D(t, s, x)` is continuous for `0 ≤ s ≤ t`. -/
theorem continuous_fderiv (h : IsDifferentiableFlow f Df φ D) {K : NNReal}
    (hDfc : ContinuousOn (fun p : ℝ × E => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Continuous (D t s) := by
  have hlip : ∀ τ, 0 ≤ τ → LipschitzWith K (f τ) := fun τ hτ =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (h.hasFDerivAt_field τ hτ y).differentiableAt)
      fun y => by
        rw [(h.hasFDerivAt_field τ hτ y).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
        exact hK τ hτ y
  set E₁ := Real.exp (K * (t - s)) with hE₁def
  set M := Real.exp (((K : ℝ) + 1) * (t - s)) with hMdef
  have hE₁ : 0 < E₁ := Real.exp_pos _
  have hM : 0 < M := Real.exp_pos _
  -- the bound on the derivative along `[s, t]`
  have hDb : ∀ τ ∈ Icc s t, ∀ y, ‖D τ s y‖ ≤ E₁ := fun τ hτ y =>
    (h.norm_fderiv_le_exp hlip hs hτ.1 y).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) K.2))
  -- the trajectories stay close, by the mean value inequality
  have hzy : ∀ τ ∈ Icc s t, ∀ x x' : E, ‖φ τ s x' - φ τ s x‖ ≤ E₁ * ‖x' - x‖ :=
    fun τ hτ x x' => convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y _ => (h.hasFDerivAt τ s hs hτ.1 y).hasFDerivWithinAt) (fun y _ => hDb τ hτ y)
      (mem_univ x) (mem_univ x')
  -- the derivative of the field, extended to negative times
  have hDf'c : Continuous fun p : ℝ × E => Df (max p.1 0) p.2 :=
    hDfc.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      fun p => ⟨le_max_right p.1 0, mem_univ _⟩
  rw [Metric.continuous_iff]
  intro x ε hε
  set η := ε / (2 * (E₁ * M)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδη⟩ := exists_dist_lt_of_isCompact' hDf'c
    (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk
      ((h.continuousOn_trajectory hs x).mono Icc_subset_Ici_self))) hη
  refine ⟨δ / E₁, div_pos hδ hE₁, fun x' hx' => ?_⟩
  rw [dist_eq_norm] at hx' ⊢
  have hxE : E₁ * ‖x' - x‖ < δ := by
    rw [mul_comm]
    exact (lt_div_iff₀ hE₁).1 hx'
  -- the derivative of the field is close along the two trajectories
  have hDfη : ∀ τ ∈ Icc s t, ‖Df τ (φ τ s x') - Df τ (φ τ s x)‖ < η := by
    intro τ hτ
    have hd : dist ((τ, φ τ s x) : ℝ × E) (τ, φ τ s x') < δ := by
      rw [Prod.dist_eq, dist_self, dist_comm, dist_eq_norm]
      exact max_lt hδ (((hzy τ hτ x x').trans_lt hxE))
    have := hδη _ ⟨τ, hτ, rfl⟩ _ hd
    simp only [id_eq, max_eq_left (hs.trans hτ.1)] at this
    rwa [dist_eq_norm, norm_sub_rev] at this
  -- the difference of the derivatives and its right derivative
  have hΔc : ContinuousOn (fun τ => D τ s x' - D τ s x) (Icc s t) :=
    ((h.continuousOn_fderiv hs x').sub (h.continuousOn_fderiv hs x)).mono Icc_subset_Ici_self
  have hΔ' : ∀ τ ∈ Ico s t, HasDerivWithinAt (fun τ => D τ s x' - D τ s x)
      (Df τ (φ τ s x') * D τ s x' - Df τ (φ τ s x) * D τ s x) (Ici τ) τ := fun τ hτ =>
    ((h.variational τ s hs hτ.1 x').sub (h.variational τ s hs hτ.1 x)).mono
      (Ici_subset_Ici.2 hτ.1)
  have hbound : ∀ τ ∈ Ico s t,
      ‖Df τ (φ τ s x') * D τ s x' - Df τ (φ τ s x) * D τ s x‖
        ≤ ((K : ℝ) + 1) * ‖D τ s x' - D τ s x‖ + η * E₁ := by
    intro τ hτ
    have hτ' : τ ∈ Icc s t := Ico_subset_Icc_self hτ
    have heq : Df τ (φ τ s x') * D τ s x' - Df τ (φ τ s x) * D τ s x =
        Df τ (φ τ s x') * (D τ s x' - D τ s x) + (Df τ (φ τ s x') - Df τ (φ τ s x)) * D τ s x :=
      by noncomm_ring
    have hA : ‖Df τ (φ τ s x') * (D τ s x' - D τ s x)‖ ≤ ((K : ℝ) + 1) * ‖D τ s x' - D τ s x‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((hK τ (hs.trans hτ'.1) _).trans (by linarith)) (norm_nonneg _))
    have hB : ‖(Df τ (φ τ s x') - Df τ (φ τ s x)) * D τ s x‖ ≤ η * E₁ :=
      (norm_mul_le _ _).trans (mul_le_mul (hDfη τ hτ').le (hDb τ hτ' x) (norm_nonneg _) hη.le)
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hA hB)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hΔc hΔ' (δ := 0)
    (by simp [h.fderiv_self s hs]) hbound t ⟨hst, le_rfl⟩
  simp only [gronwallBound_of_K_ne_0 (by positivity : (K : ℝ) + 1 ≠ 0), zero_mul, zero_add,
    ← hMdef] at hg
  have hε0 : 0 ≤ η * E₁ := by positivity
  have h1 : η * E₁ / ((K : ℝ) + 1) ≤ η * E₁ := div_le_self hε0 (by linarith [K.coe_nonneg])
  have h2 : η * E₁ * M = ε / 2 := by
    rw [hηdef]
    field_simp
  have h3 : η * E₁ / ((K : ℝ) + 1) * (M - 1) ≤ η * E₁ * M := by
    nlinarith [div_nonneg hε0 (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
  linarith

/-- **The flow is strictly differentiable in the initial state (MLS pp. 322–323, the hypothesis of
the inverse function theorem behind "`φ^f_t` is a local diffeomorphism"):** under the hypotheses of
`continuous_fderiv`, `φ(t, s, ·)` has the strict Fréchet derivative `D(t, s, x)` at every `x`, for
`0 ≤ s ≤ t`. Time first. -/
theorem hasStrictFDerivAt (h : IsDifferentiableFlow f Df φ D) {K : NNReal}
    (hDfc : ContinuousOn (fun p : ℝ × E => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : E) :
    HasStrictFDerivAt (φ t s) (D t s x) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Eventually.of_forall fun y => h.hasFDerivAt t s hs hst y)
    (h.continuous_fderiv hDfc hK hs hst).continuousAt

end IsDifferentiableFlow

end Stability
end RoboLean
