import RoboLean.Control.FlowDerivative
import RoboLean.Control.GlobalFlowTimeVarying

/-!
# Differentiable dependence of solutions on the initial state (MLS p. 179, for Theorem 4.5, p. 183)

**What MLS assumes.** For `ẋ = f(x, t)` (eq. (4.31), p. 179) MLS assumes "the standard conditions
for the existence and uniqueness of solutions", for instance that `f(x, t)` is Lipschitz continuous
in `x`, uniformly in `t`, and piecewise continuous in `t`. The fourth bound of Theorem 4.5 (p. 183),
`‖∂V/∂x (x, t)‖ ≤ α₄‖x‖`, concerns the derivative of the converse Lyapunov function in the state,
and for `V(x, t) = ∫_t^{t+T} ‖s(τ, x, t)‖² dτ` it needs the derivative of the solution
`s(τ, x, t)` in its initial state `x`; MLS gives no proof of the theorem.

**Formalized here: differentiable dependence on initial conditions.** For a field `f(t, x)` (time
first) on a real Banach space that is continuous in `t`, has the Fréchet derivative `Df(t, y)` in
`y`, with `Df` continuous in `(t, y)` and bounded in operator norm by `K`, for `t ≥ 0`, there are a
flow `φ` and a derivative `D` with `IsDifferentiableFlow f Df φ D` (`exists_isDifferentiableFlow`):
the solutions exist for all forward time and are unique, `(t, s, x) ↦ φ(t, s, x)` is continuous,
`x ↦ φ(t, s, x)` has the derivative `D(t, s, x)`, and `D(·, s, x)` solves the variational equation
`∂D/∂t = Df(t, φ(t, s, x)) D` with `D(s, s, x) = 1`. The autonomous case is
`exists_isDifferentiableFlow_autonomous`.

Route. The field is extended to negative times by its value at `0`; the solutions are the global
solutions of `RoboLean.Control.GlobalFlowTimeVarying` (`f(t, ·)` is `K`-Lipschitz by the mean value
inequality); `D(·, s, x)` is the state-transition matrix of `A(τ) = Df(τ, φ(τ, s, x))`
(`exists_isStateTransition`, `A` continuous and bounded). The derivative in the initial state is
`hasFDerivAt_of_variational`: for `z(τ) = φ(τ, s, x + h)` and `y(τ) = φ(τ, s, x)`, the remainder
`r(τ) = z(τ) − y(τ) − D(τ, s, x) h` satisfies `ṙ = A(τ) r + ρ(τ)` with
`ρ = f(τ, z) − f(τ, y) − Df(τ, y)(z − y)`; Grönwall's bound for two solutions gives
`‖z(τ) − y(τ)‖ ≤ e^{K(τ − s)} ‖h‖`, the mean value inequality and the uniform continuity of `Df`
near the compact arc `{(τ, y(τ)) : s ≤ τ ≤ t}` give `‖ρ(τ)‖ ≤ η e^{K(t − s)} ‖h‖` for small `h`,
and Grönwall's inequality for `r` gives `‖r(t)‖ ≤ η e^{K(t − s)} e^{(K + 1)(t − s)} ‖h‖`.

**Hypotheses against MLS.** MLS allows piecewise continuity in `t` and asks Lipschitz continuity
in `x`; here `f` is continuous in `t` (so that solutions have a derivative at every time, as
`IsSolution` asks) and continuously differentiable in `x` with a bounded derivative, the standard
hypotheses of differentiable dependence. A bounded derivative is the same as a global Lipschitz
bound for a differentiable field, so the uniform-in-`t` Lipschitz condition of p. 179 is kept.

**Conventions.** As in `RoboLean.Stability`: time first, solutions `IsSolution` (continuous on
`[s, ∞)`, an actual derivative at every `t > s`), initial times `s ≥ 0`; derivatives in the state
are Fréchet derivatives, continuous linear maps `E →L[ℝ] E` multiplied by composition.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform continuity near a compact set (for the remainder estimate behind MLS Theorem 4.5,
p. 183): a continuous map `g` moves points within `δ` of a compact set `C` by less than `η`. -/
private theorem exists_dist_lt_of_isCompact {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {g : X → Y} (hg : Continuous g) {C : Set X} (hC : IsCompact C) {η : ℝ}
    (hη : 0 < η) : ∃ δ > 0, ∀ p ∈ C, ∀ q, dist p q < δ → dist (g p) (g q) < η := by
  obtain ⟨δ, hδ, h⟩ := Metric.mem_uniformity_dist.1
    (hC.uniformContinuousAt_of_continuousAt g (fun a _ => hg.continuousAt)
      (Metric.dist_mem_uniformity hη))
  exact ⟨δ, hδ, fun p hp q hpq => h hpq hp⟩

/-- At every time `τ ≥ s` a solution of a field continuous in `(t, x)` has the right derivative
`f(τ, x(τ))` (MLS eq. (4.31), p. 179); at `τ = s` it follows from the limit of the derivatives. -/
private theorem IsSolution.hasDerivWithinAt_Ici_of_continuous {f : ℝ → E → E}
    (hf : Continuous fun p : ℝ × E => f p.1 p.2) {s : ℝ} {x : ℝ → E} (hx : IsSolution f s x)
    {τ : ℝ} (hτ : s ≤ τ) : HasDerivWithinAt x (f τ (x τ)) (Ici τ) τ := by
  rcases eq_or_lt_of_le hτ with h | h
  · subst h
    have hcw : ContinuousWithinAt x (Ioi s) s := (hx.1 s self_mem_Ici).mono Ioi_subset_Ici_self
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi s)
      (fun t ht => (hx.2 t ht).differentiableAt.differentiableWithinAt) hcw self_mem_nhdsWithin ?_
    have hlim : Tendsto (fun t => f t (x t)) (𝓝[>] s) (𝓝 (f s (x s))) :=
      (hf.tendsto (s, x s)).comp (continuousWithinAt_id.prodMk hcw).tendsto
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((hx.2 t ht).deriv).symm
  · exact (hx.2 τ h).hasDerivWithinAt

/-- **The derivative of a solution in its initial state from the variational equation (MLS p. 179,
for the fourth bound of Theorem 4.5, p. 183).** Let `f(t, ·)` have the Fréchet derivative
`Df(t, y)` at every `y` for every real `t`, with `Df` continuous in `(t, y)` and `‖Df(t, y)‖ ≤ K`.
Let `γ x` be a solution of `ẋ = f(x, t)` on the whole time axis with `γ x s = x`, for every `x`. If
`Φ(s) = 1` and `Φ` solves the variational equation `Φ' = Df(τ, γ x τ) Φ` on `[s, ∞)`, then for
`t ≥ s` the map `y ↦ γ y t` has the derivative `Φ(t)` at `x`. Time first. -/
theorem hasFDerivAt_of_variational {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E} {K : NNReal}
    (hDf : ∀ t y, HasFDerivAt (f t) (Df t y) y)
    (hDfc : Continuous fun p : ℝ × E => Df p.1 p.2) (hK : ∀ t y, ‖Df t y‖ ≤ K)
    {s : ℝ} {γ : E → ℝ → E} (hγs : ∀ x, γ x s = x)
    (hγ : ∀ x t, HasDerivAt (γ x) (f t (γ x t)) t)
    {x : E} {Φ : ℝ → E →L[ℝ] E} (hΦs : Φ s = 1)
    (hΦ : ∀ t, s ≤ t → HasDerivWithinAt Φ (Df t (γ x t) * Φ t) (Ici s) t)
    {t : ℝ} (hst : s ≤ t) : HasFDerivAt (fun y => γ y t) (Φ t) x := by
  have hlip : ∀ τ, LipschitzWith K (f τ) := fun τ =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hDf τ y).differentiableAt) fun y => by
      rw [(hDf τ y).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hK τ y
  have hγc : ∀ y, Continuous (γ y) := fun y =>
    continuous_iff_continuousAt.2 fun τ => (hγ y τ).continuousAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  set E₁ := Real.exp (K * (t - s)) with hE₁def
  set M := Real.exp (((K : ℝ) + 1) * (t - s)) with hMdef
  have hE₁ : 0 < E₁ := Real.exp_pos _
  have hM1 : 1 ≤ M := Real.one_le_exp (mul_nonneg (by positivity) (sub_nonneg.2 hst))
  set η := c / (E₁ * M) with hηdef
  have hη : 0 < η := by positivity
  -- uniform continuity of `Df` near the compact arc `{(τ, γ x τ) : s ≤ τ ≤ t}`
  obtain ⟨δ, hδ, hδη⟩ := exists_dist_lt_of_isCompact hDfc
    (isCompact_Icc.image (continuous_id.prodMk (hγc x))) hη
  have hball : ∀ᶠ h in 𝓝 (0 : E), ‖h‖ < δ / E₁ := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (div_pos hδ hE₁)] with h hh
    simpa using hh
  filter_upwards [hball] with h hh
  have hhE : ‖h‖ * E₁ < δ := (lt_div_iff₀ hE₁).1 hh
  -- Grönwall's bound for the two solutions
  have hzy : ∀ τ ∈ Icc s t, ‖γ (x + h) τ - γ x τ‖ ≤ ‖h‖ * E₁ := by
    intro τ hτ
    have h1 := dist_le_of_trajectories_ODE (v := f) (K := K) (δ := ‖h‖) hlip
      (hγc (x + h)).continuousOn (fun τ _ => (hγ (x + h) τ).hasDerivWithinAt)
      (hγc x).continuousOn (fun τ _ => (hγ x τ).hasDerivWithinAt)
      (by rw [hγs, hγs, dist_eq_norm, add_sub_cancel_left]) τ hτ
    rw [dist_eq_norm] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left (by linarith [hτ.2]) K.2
  -- the defect of the linearization, by the mean value inequality
  have hρ : ∀ τ ∈ Icc s t, ‖f τ (γ (x + h) τ) - f τ (γ x τ) - Df τ (γ x τ) (γ (x + h) τ - γ x τ)‖
      ≤ η * ‖γ (x + h) τ - γ x τ‖ := by
    intro τ hτ
    refine (convex_closedBall (γ x τ)
      ‖γ (x + h) τ - γ x τ‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f' := Df τ) (fun w _ => (hDf τ w).hasFDerivWithinAt) (fun w hw => ?_)
      (Metric.mem_closedBall_self (norm_nonneg _)) (by rw [Metric.mem_closedBall, dist_eq_norm])
    have hw' : dist w (γ x τ) ≤ ‖γ (x + h) τ - γ x τ‖ := Metric.mem_closedBall.1 hw
    have hd : dist ((τ, γ x τ) : ℝ × E) (τ, w) < δ := by
      rw [Prod.dist_eq, dist_self, dist_comm]
      exact lt_of_le_of_lt (max_le (dist_nonneg.trans hw') hw') ((hzy τ hτ).trans_lt hhE)
    have := hδη _ ⟨τ, hτ, rfl⟩ _ hd
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le
  -- the remainder and its derivative
  have hΦc : ContinuousOn Φ (Icc s t) := fun τ hτ =>
    ((hΦ τ hτ.1).continuousWithinAt).mono Icc_subset_Ici_self
  have hrc : ContinuousOn (fun τ => γ (x + h) τ - γ x τ - Φ τ h) (Icc s t) :=
    ((hγc (x + h)).continuousOn.sub (hγc x).continuousOn).sub (hΦc.clm_apply continuousOn_const)
  have hr' : ∀ τ ∈ Ico s t, HasDerivWithinAt (fun τ => γ (x + h) τ - γ x τ - Φ τ h)
      (f τ (γ (x + h) τ) - f τ (γ x τ) - (Df τ (γ x τ) * Φ τ) h) (Ici τ) τ := by
    intro τ hτ
    have h1 := ((hΦ τ hτ.1).mono (Ici_subset_Ici.2 hτ.1)).clm_apply (hasDerivWithinAt_const τ _ h)
    have h2 := ((hγ (x + h) τ).hasDerivWithinAt.sub (hγ x τ).hasDerivWithinAt).sub h1
    convert h2 using 1
    simp
  have hbound : ∀ τ ∈ Ico s t,
      ‖f τ (γ (x + h) τ) - f τ (γ x τ) - (Df τ (γ x τ) * Φ τ) h‖
        ≤ ((K : ℝ) + 1) * ‖γ (x + h) τ - γ x τ - Φ τ h‖ + η * (‖h‖ * E₁) := by
    intro τ hτ
    have hτ' : τ ∈ Icc s t := Ico_subset_Icc_self hτ
    have heq : f τ (γ (x + h) τ) - f τ (γ x τ) - (Df τ (γ x τ) * Φ τ) h =
        (f τ (γ (x + h) τ) - f τ (γ x τ) - Df τ (γ x τ) (γ (x + h) τ - γ x τ)) +
          Df τ (γ x τ) (γ (x + h) τ - γ x τ - Φ τ h) := by
      simp only [mul_apply_eq_comp, map_sub]
      abel
    have hA : ‖Df τ (γ x τ) (γ (x + h) τ - γ x τ - Φ τ h)‖ ≤
        K * ‖γ (x + h) τ - γ x τ - Φ τ h‖ :=
      ((Df τ (γ x τ)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK _ _) (norm_nonneg _))
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have := hρ τ hτ'
    have := hzy τ hτ'
    nlinarith [norm_nonneg (γ (x + h) τ - γ x τ - Φ τ h), hη.le]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hrc hr' (δ := 0)
    (by simp [hγs, hΦs]) hbound t ⟨hst, le_rfl⟩
  simp only [gronwallBound_of_K_ne_0 (by positivity : (K : ℝ) + 1 ≠ 0), zero_mul, zero_add] at hg
  refine hg.trans ?_
  have hε : 0 ≤ η * (‖h‖ * E₁) := by positivity
  have h1 : η * (‖h‖ * E₁) / ((K : ℝ) + 1) ≤ η * (‖h‖ * E₁) :=
    div_le_self hε (by linarith [K.coe_nonneg])
  have h2 : η * (‖h‖ * E₁) * M = c * ‖h‖ := by
    rw [hηdef]
    field_simp
  calc η * (‖h‖ * E₁) / ((K : ℝ) + 1) * (Real.exp (((K : ℝ) + 1) * (t - s)) - 1)
      ≤ η * (‖h‖ * E₁) * M := by
        rw [← hMdef]
        nlinarith [div_nonneg hε (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
    _ = c * ‖h‖ := h2

/-- **Differentiable dependence on initial conditions (MLS's standing assumption, p. 179, and the
fourth bound of Theorem 4.5, p. 183).** On a real Banach space, let `f(t, x)` (time first) be
continuous in `t ≥ 0` for every `x`, let `f(t, ·)` have the Fréchet derivative `Df(t, y)` at every
`y` for `t ≥ 0`, with `Df` continuous on `[0, ∞) × E` and `‖Df(t, y)‖ ≤ K` there. Then there are a
flow `φ` (`φ t s x` the state at time `t` of the solution from `x` at time `s`) and `D` with
`IsDifferentiableFlow f Df φ D`: existence and uniqueness of solutions from every `s ≥ 0`, joint
continuity of `(t, s, x) ↦ φ t s x`, the derivative `D t s x` of `x ↦ φ t s x`, `D s s x = 1`, and
the variational equation `∂D/∂t = Df(t, φ t s x) D`. MLS asks Lipschitz continuity in `x` and
piecewise continuity in `t`; here continuity in `t` and a continuous bounded derivative in `x`. -/
theorem exists_isDifferentiableFlow [CompleteSpace E] {f : ℝ → E → E}
    {Df : ℝ → E → E →L[ℝ] E} {K : NNReal} (hf : ∀ x, ContinuousOn (fun t => f t x) (Ici 0))
    (hDf : ∀ t, 0 ≤ t → ∀ y, HasFDerivAt (f t) (Df t y) y)
    (hDfc : ContinuousOn (fun p : ℝ × E => Df p.1 p.2) (Ici 0 ×ˢ univ))
    (hK : ∀ t, 0 ≤ t → ∀ y, ‖Df t y‖ ≤ K) :
    ∃ φ : ℝ → ℝ → E → E, ∃ D : ℝ → ℝ → E → E →L[ℝ] E, IsDifferentiableFlow f Df φ D := by
  -- the field and its derivative extended to negative times by their values at `0`
  set f' : ℝ → E → E := fun t => f (max t 0) with hf'def
  set Df' : ℝ → E → E →L[ℝ] E := fun t => Df (max t 0) with hDf'def
  have hfeq : ∀ t, 0 ≤ t → f' t = f t := fun t ht => by simp only [hf'def, max_eq_left ht]
  have hDfeq : ∀ t, 0 ≤ t → Df' t = Df t := fun t ht => by simp only [hDf'def, max_eq_left ht]
  have hDf'd : ∀ t y, HasFDerivAt (f' t) (Df' t y) y := fun t y => hDf _ (le_max_right t 0) y
  have hDf'c : Continuous fun p : ℝ × E => Df' p.1 p.2 :=
    hDfc.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      fun p => ⟨le_max_right p.1 0, mem_univ _⟩
  have hK' : ∀ t y, ‖Df' t y‖ ≤ K := fun t y => hK _ (le_max_right t 0) y
  have hlip : ∀ t, LipschitzWith K (f' t) := fun t =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hDf'd t y).differentiableAt) fun y => by
      rw [(hDf'd t y).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hK' t y
  have hc : ∀ x, Continuous fun t => f' t x := fun x =>
    (hf x).comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  have hf'c : Continuous fun p : ℝ × E => f' p.1 p.2 :=
    continuous_prod_of_continuous_lipschitzWith' (fun p : ℝ × E => f' p.1 p.2) K hlip hc
  -- global solutions and the state-transition matrices of the linearizations
  choose γ hγs hγ using fun s x => exists_global_solution_of_lipschitzWith hlip hc s x
  have hγc : ∀ s x, Continuous (γ s x) := fun s x =>
    continuous_iff_continuousAt.2 fun t => (hγ s x t).continuousAt
  have hA : ∀ s x, ContinuousOn (fun τ => Df' τ (γ s x τ)) (Ici 0) := fun s x =>
    (hDf'c.comp (continuous_id.prodMk (hγc s x))).continuousOn
  choose Φ hΦ using fun s x => exists_isStateTransition (hA s x) (M := K) fun t _ => hK' t _
  refine ⟨fun t s x => γ s x t, fun t s x => Φ s x t s, hDf, fun s _ x => hγs s x,
    fun s hs x => ⟨(hγc s x).continuousOn, fun t ht => ?_⟩, ?_, ?_, ?_,
    fun s hs x => (hΦ s x).self_eq_one s hs, ?_⟩
  · -- existence
    rw [← hfeq t (hs.trans ht.le)]
    exact hγ s x t
  · -- uniqueness
    intro s hs x hx t hst
    have hxf : IsSolution f' s x :=
      ⟨hx.1, fun τ hτ => by rw [hfeq τ (hs.trans hτ.le)]; exact hx.2 τ hτ⟩
    have h1 := dist_le_of_trajectories_ODE (v := f') (K := K) (δ := 0) hlip
      (hx.1.mono Icc_subset_Ici_self)
      (fun τ hτ => IsSolution.hasDerivWithinAt_Ici_of_continuous hf'c hxf hτ.1)
      (hγc s (x s)).continuousOn (fun τ _ => (hγ s (x s) τ).hasDerivWithinAt)
      (by rw [hγs, dist_self]) t ⟨hst, le_rfl⟩
    rw [zero_mul] at h1
    exact dist_le_zero.1 h1
  · -- joint continuity
    rintro ⟨t₀, s₀, x₀⟩ hp₀
    have hb : ∀ p ∈ {p : ℝ × ℝ × E | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1},
        ‖γ p.2.1 p.2.2 p.1 - γ s₀ x₀ p.1‖ ≤
          ‖p.2.2 - γ s₀ x₀ p.2.1‖ * Real.exp (K * (p.1 - p.2.1)) := by
      rintro ⟨t, s, x⟩ ⟨-, hst⟩
      have h1 := dist_le_of_trajectories_ODE (v := f') (K := K) (δ := ‖x - γ s₀ x₀ s‖) hlip
        (hγc s x).continuousOn (fun τ _ => (hγ s x τ).hasDerivWithinAt)
        (hγc s₀ x₀).continuousOn (fun τ _ => (hγ s₀ x₀ τ).hasDerivWithinAt)
        (by rw [hγs, dist_eq_norm]) t ⟨hst, le_rfl⟩
      rwa [dist_eq_norm] at h1
    have hgc : Continuous fun p : ℝ × ℝ × E =>
        ‖p.2.2 - γ s₀ x₀ p.2.1‖ * Real.exp (K * (p.1 - p.2.1)) := by
      have := hγc s₀ x₀
      fun_prop
    have hg : Tendsto (fun p : ℝ × ℝ × E =>
        ‖p.2.2 - γ s₀ x₀ p.2.1‖ * Real.exp (K * (p.1 - p.2.1)))
        (𝓝[{p : ℝ × ℝ × E | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1}] (t₀, s₀, x₀)) (𝓝 0) := by
      convert (hgc.tendsto (t₀, s₀, x₀)).mono_left nhdsWithin_le_nhds using 2
      simp [hγs]
    have h1 := squeeze_zero_norm' (eventually_nhdsWithin_of_forall hb) hg
    have h2 : Tendsto (fun p : ℝ × ℝ × E => γ s₀ x₀ p.1)
        (𝓝[{p : ℝ × ℝ × E | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1}] (t₀, s₀, x₀)) (𝓝 (γ s₀ x₀ t₀)) :=
      (((hγc s₀ x₀).comp continuous_fst).tendsto (t₀, s₀, x₀)).mono_left nhdsWithin_le_nhds
    have h3 := h1.add h2
    simp only [sub_add_cancel, zero_add] at h3
    exact h3
  · -- the derivative in the initial state
    intro t s hs hst x
    exact hasFDerivAt_of_variational hDf'd hDf'c hK' (γ := γ s) (x := x)
      (Φ := fun τ => Φ s x τ s) (hγs s) (hγ s)
      ((hΦ s x).self_eq_one s hs)
      (fun τ hτ => ((hΦ s x).hasDerivWithinAt τ s (hs.trans hτ) hs).mono (Ici_subset_Ici.2 hs))
      hst
  · -- the variational equation
    intro t s hs hst x
    have h1 := ((hΦ s x).hasDerivWithinAt t s (hs.trans hst) hs).mono (Ici_subset_Ici.2 hs)
    rwa [hDfeq t (hs.trans hst)] at h1

/-- **Differentiable dependence on initial conditions for an autonomous field (MLS p. 179, for
Theorem 4.5, p. 183).** On a real Banach space, if `F` has the Fréchet derivative `DF y` at every
`y`, with `DF` continuous and `‖DF y‖ ≤ K`, then the system `ẋ = F(x)`, written `fun _ => F` (time
first, ignored), has a flow differentiable in the initial state:
`IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D` for some `φ` and `D`. -/
theorem exists_isDifferentiableFlow_autonomous [CompleteSpace E] {F : E → E}
    {DF : E → E →L[ℝ] E} {K : NNReal} (hDF : ∀ y, HasFDerivAt F (DF y) y) (hDFc : Continuous DF)
    (hK : ∀ y, ‖DF y‖ ≤ K) :
    ∃ φ : ℝ → ℝ → E → E, ∃ D : ℝ → ℝ → E → E →L[ℝ] E,
      IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D :=
  exists_isDifferentiableFlow (fun _ => continuousOn_const) (fun _ _ y => hDF y)
    (hDFc.comp continuous_snd).continuousOn (fun _ _ y => hK y)

end Stability
end RoboLean
