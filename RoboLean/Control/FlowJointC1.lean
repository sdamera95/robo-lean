import RoboLean.Control.FlowDifferentiableC1

/-!
# The derivative of a flow is jointly continuous in time and initial state (MLS pp. 322–323)

**Why.** The constructions behind MLS's flow statements (the local diffeomorphisms `φ^f_t` of
pp. 322–323, and the composed flows `φ^{g_k}_{t_k} ∘ ⋯ ∘ φ^{g_1}_{t_1}(q)` of Propositions 7.6–7.7,
pp. 330–331) differentiate flows in the time and the state together, which asks a derivative
continuous in both.

**Proved here.** For a flow `φ` differentiable in the initial state (`IsDifferentiableFlow`) whose
field has a derivative `Df` continuous and bounded by `K` on `[0, ∞) × E`, and an initial time
`s ≥ 0`, the map `(t, x) ↦ D(t, s, x)` is continuous on `[s, ∞) × E`
(`IsDifferentiableFlow.continuousOn_fderiv_prod`). Route: the Grönwall estimate of
`continuous_fderiv` holds uniformly for `t` in a compact interval `[s, T]`, and `t ↦ D(t, s, x₀)`
is continuous (`continuousOn_fderiv`).

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
private theorem exists_dist_lt_of_isCompact_joint {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {g : X → Y} (hg : Continuous g) {C : Set X} (hC : IsCompact C) {η : ℝ}
    (hη : 0 < η) : ∃ δ > 0, ∀ p ∈ C, ∀ q, dist p q < δ → dist (g p) (g q) < η := by
  obtain ⟨δ, hδ, h⟩ := Metric.mem_uniformity_dist.1
    (hC.uniformContinuousAt_of_continuousAt g (fun a _ => hg.continuousAt)
      (Metric.dist_mem_uniformity hη))
  exact ⟨δ, hδ, fun p hp q hpq => h hpq hp⟩

namespace IsDifferentiableFlow

variable {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E} {φ : ℝ → ℝ → E → E}
  {D : ℝ → ℝ → E → E →L[ℝ] E}

/-- The estimate behind MLS pp. 322–323, uniform in the time on `[s, T]`: for `x` and `ε > 0`
there is `δ > 0` with `‖D(t, s, x') − D(t, s, x)‖ < ε` for `‖x' − x‖ < δ` and `t ∈ [s, T]`. -/
private theorem exists_norm_fderiv_sub_lt (h : IsDifferentiableFlow f Df φ D) {K : NNReal}
    (hDfc : ContinuousOn (fun p : ℝ × E => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) {s T : ℝ} (hs : 0 ≤ s) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x' : E, ‖x' - x‖ < δ → ∀ t ∈ Icc s T, ‖D t s x' - D t s x‖ < ε := by
  have hlip : ∀ τ, 0 ≤ τ → LipschitzWith K (f τ) := fun τ hτ =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (h.hasFDerivAt_field τ hτ y).differentiableAt)
      fun y => by
        rw [(h.hasFDerivAt_field τ hτ y).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
        exact hK τ hτ y
  set E₁ := Real.exp (K * (T - s)) with hE₁def
  set M := Real.exp (((K : ℝ) + 1) * (T - s)) with hMdef
  have hE₁ : 0 < E₁ := Real.exp_pos _
  have hM : 0 < M := Real.exp_pos _
  -- the bound on the derivative along `[s, T]`
  have hDb : ∀ τ ∈ Icc s T, ∀ y, ‖D τ s y‖ ≤ E₁ := fun τ hτ y =>
    (h.norm_fderiv_le_exp hlip hs hτ.1 y).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) K.2))
  -- the trajectories stay close, by the mean value inequality
  have hzy : ∀ τ ∈ Icc s T, ∀ x x' : E, ‖φ τ s x' - φ τ s x‖ ≤ E₁ * ‖x' - x‖ :=
    fun τ hτ x x' => convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y _ => (h.hasFDerivAt τ s hs hτ.1 y).hasFDerivWithinAt) (fun y _ => hDb τ hτ y)
      (mem_univ x) (mem_univ x')
  -- the derivative of the field, extended to negative times
  have hDf'c : Continuous fun p : ℝ × E => Df (max p.1 0) p.2 :=
    hDfc.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      fun p => ⟨le_max_right p.1 0, mem_univ _⟩
  set η := ε / (2 * (E₁ * M)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδη⟩ := exists_dist_lt_of_isCompact_joint hDf'c
    (isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk
      ((h.continuousOn_trajectory hs x).mono Icc_subset_Ici_self))) hη
  refine ⟨δ / E₁, div_pos hδ hE₁, fun x' hx' t ht => ?_⟩
  have hxE : E₁ * ‖x' - x‖ < δ := by
    rw [mul_comm]
    exact (lt_div_iff₀ hE₁).1 hx'
  -- the derivative of the field is close along the two trajectories
  have hDfη : ∀ τ ∈ Icc s T, ‖Df τ (φ τ s x') - Df τ (φ τ s x)‖ < η := by
    intro τ hτ
    have hd : dist ((τ, φ τ s x) : ℝ × E) (τ, φ τ s x') < δ := by
      rw [Prod.dist_eq, dist_self, dist_comm, dist_eq_norm]
      exact max_lt hδ (((hzy τ hτ x x').trans_lt hxE))
    have := hδη _ ⟨τ, hτ, rfl⟩ _ hd
    simp only [id_eq, max_eq_left (hs.trans hτ.1)] at this
    rwa [dist_eq_norm, norm_sub_rev] at this
  -- the difference of the derivatives and its right derivative
  have hΔc : ContinuousOn (fun τ => D τ s x' - D τ s x) (Icc s T) :=
    ((h.continuousOn_fderiv hs x').sub (h.continuousOn_fderiv hs x)).mono Icc_subset_Ici_self
  have hΔ' : ∀ τ ∈ Ico s T, HasDerivWithinAt (fun τ => D τ s x' - D τ s x)
      (Df τ (φ τ s x') * D τ s x' - Df τ (φ τ s x) * D τ s x) (Ici τ) τ := fun τ hτ =>
    ((h.variational τ s hs hτ.1 x').sub (h.variational τ s hs hτ.1 x)).mono
      (Ici_subset_Ici.2 hτ.1)
  have hbound : ∀ τ ∈ Ico s T,
      ‖Df τ (φ τ s x') * D τ s x' - Df τ (φ τ s x) * D τ s x‖
        ≤ ((K : ℝ) + 1) * ‖D τ s x' - D τ s x‖ + η * E₁ := by
    intro τ hτ
    have hτ' : τ ∈ Icc s T := Ico_subset_Icc_self hτ
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
  have hε0 : 0 ≤ η * E₁ := by positivity
  have hg := (norm_le_gronwallBound_of_norm_deriv_right_le hΔc hΔ' (δ := 0)
    (by simp [h.fderiv_self s hs]) hbound t ht).trans
    (gronwallBound_mono le_rfl hε0 (by positivity) (by linarith [ht.2] : t - s ≤ T - s))
  simp only [gronwallBound_of_K_ne_0 (by positivity : (K : ℝ) + 1 ≠ 0), zero_mul, zero_add,
    ← hMdef] at hg
  have h1 : η * E₁ / ((K : ℝ) + 1) ≤ η * E₁ := div_le_self hε0 (by linarith [K.coe_nonneg])
  have h2 : η * E₁ * M = ε / 2 := by
    rw [hηdef]
    field_simp
  have h3 : η * E₁ / ((K : ℝ) + 1) * (M - 1) ≤ η * E₁ * M := by
    nlinarith [div_nonneg hε0 (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
  linarith

/-- **The derivative of the flow is jointly continuous in the time and the initial state (MLS
pp. 322–323, for the flows of Propositions 7.6–7.7, pp. 330–331):** if `φ` is a flow differentiable
in the initial state with derivative `D` (`IsDifferentiableFlow`, time first) and `Df` is
continuous on `[0, ∞) × E` with `‖Df(t, y)‖ ≤ K` there, then for every `s ≥ 0` the map
`(t, x) ↦ D(t, s, x)` is continuous on `[s, ∞) × E`. -/
theorem continuousOn_fderiv_prod (h : IsDifferentiableFlow f Df φ D) {K : NNReal}
    (hDfc : ContinuousOn (fun p : ℝ × E => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun p : ℝ × E => D p.1 s p.2) (Ici s ×ˢ univ) := by
  intro p hp
  obtain ⟨t₀, x₀⟩ := p
  have ht₀ : s ≤ t₀ := hp.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := h.exists_norm_fderiv_sub_lt hDfc hK hs (T := t₀ + 1) x₀
    (half_pos hε)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1
    (h.continuousOn_fderiv hs x₀ t₀ ht₀) (ε / 2) (half_pos hε)
  refine ⟨min 1 (min δ₁ δ₂), by positivity, fun q hq hqd => ?_⟩
  obtain ⟨t, x⟩ := q
  have hts : s ≤ t := hq.1
  rw [Prod.dist_eq] at hqd
  have hdt : dist t t₀ < min 1 (min δ₁ δ₂) := (le_max_left _ _).trans_lt hqd
  have hdx : dist x x₀ < min 1 (min δ₁ δ₂) := (le_max_right _ _).trans_lt hqd
  have htT : t ≤ t₀ + 1 := by
    have := (abs_lt.1 (Real.dist_eq t t₀ ▸ hdt.trans_le (min_le_left _ _))).2
    linarith
  have hx₁ : ‖x - x₀‖ < δ₁ := by
    rw [← dist_eq_norm]
    exact hdx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have e₁ := h₁ x hx₁ t ⟨hts, htT⟩
  have e₂ := h₂ (mem_Ici.2 hts) (hdt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  simp only at e₂ ⊢
  rw [dist_eq_norm] at e₂ ⊢
  calc ‖D t s x - D t₀ s x₀‖ = ‖(D t s x - D t s x₀) + (D t s x₀ - D t₀ s x₀)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖D t s x - D t s x₀‖ + ‖D t s x₀ - D t₀ s x₀‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e₁ e₂
    _ = ε := add_halves ε

end IsDifferentiableFlow

end Stability
end RoboLean
