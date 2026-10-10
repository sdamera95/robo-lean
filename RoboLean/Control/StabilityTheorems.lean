import RoboLean.Control.Stability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Further Lyapunov theorems: global notions, Theorem 4.4(4), Theorem 4.5 local form

MLS Chapter 4, Section 4, printed pp. 180–184, continuing `RoboLean.Control.Stability` (E016)
with the same conventions (system `f t x` with time first, solutions `IsSolution`, initial times
`t₀ ≥ 0`, comparison functions `IsClassK` with `α(0) = 0`).

**What MLS prints (read this session).**

* p. 180: "We say an equilibrium point `x*` is globally stable if it is stable for all initial
  conditions `x₀ ∈ ℝⁿ`"; p. 181: exponential stability "implies uniform, asymptotic stability".
* Theorem 4.4(4), p. 183: "If `V(x, t)` is positive definite and decrescent, and `−V̇(x, t)` is
  positive definite, then the origin of the system is globally uniformly asymptotically stable."
  Definition 4.6 (decrescent, p. 182) bounds `V ≤ β(‖x‖)` only on a ball `B_ε`.
* Theorem 4.5, p. 183, with the bounds `α₁‖x‖² ≤ V ≤ α₂‖x‖²`, `V̇ ≤ −α₃‖x‖²` for `‖x‖ ≤ ε`, and
  the rate bounds `m ≤ (α₂/α₁)^{1/2}`, `α ≥ α₃/(2α₂)` of p. 184.

**Formalized.**

* `GloballyAsymptoticallyStableAt` (stable at `t₀`, and every solution from `t₀` converges) and
  `GloballyUniformlyAsymptoticallyStable` (uniformly stable, uniformly bounded, and uniformly
  globally attractive: for every `r, η > 0` one time `T` works for all `t₀ ≥ 0` and all solutions
  starting within `r`). MLS gives no formal definition of either; these are the standard ones
  (Khalil, Vidyasagar), a choice of this increment;
* Theorem 4.4(4) in two forms. Under MLS's literal hypotheses (`V` positive definite with
  `α(p) → ∞`, decrescent on a ball, `−V̇` positive definite): the origin is uniformly asymptotically
  stable and globally asymptotically stable at every `t₀ ≥ 0`
  (`globallyAsymptoticallyStableAt_of_lyapunov`). With `V ≤ β(‖x‖)` for **all** `x` (global
  decrescence, a hypothesis MLS does not state): globally uniformly asymptotically stable
  (`globallyUniformlyAsymptoticallyStable_of_lyapunov`). Whether the uniform global conclusion
  holds with decrescence on a ball only is not settled here: the time to reach a small ball is
  bounded by `V(t₀, x₀)/γ`, which local decrescence does not bound uniformly in `t₀` for large
  `x₀`; no counterexample was constructed;
* Theorem 4.5 sufficiency in its local form (`exponentiallyStable_of_quadratic_lyapunov_local`),
  with the rate bounds of p. 184 for every solution starting within
  `min ε (ε √(α₁/α₂))` (`norm_le_of_quadratic_lyapunov_local`);
* MLS p. 181: exponential stability implies uniform stability and uniform asymptotic stability.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Global notions (MLS pp. 180–183) -/

/-- **Global asymptotic stability at `t₀` (MLS p. 180):** `xe` is stable at `t₀` (Definition 4.1)
and every solution from `t₀`, whatever its initial condition, converges to `xe`. -/
def GloballyAsymptoticallyStableAt (f : ℝ → E → E) (xe : E) (t₀ : ℝ) : Prop :=
  StableAt f xe t₀ ∧ ∀ x, IsSolution f t₀ x → Tendsto x atTop (𝓝 xe)

/-- Global asymptotic stability implies asymptotic stability (Definition 4.2, MLS p. 180). -/
theorem GloballyAsymptoticallyStableAt.asymptoticallyStableAt {f : ℝ → E → E} {xe : E} {t₀ : ℝ}
    (h : GloballyAsymptoticallyStableAt f xe t₀) : AsymptoticallyStableAt f xe t₀ :=
  ⟨h.1, 1, one_pos, fun x hx _ => h.2 x hx⟩

/-- **Global uniform asymptotic stability (MLS Theorem 4.4(4) and Table 4.1, p. 183):** `xe` is
uniformly stable, solutions are uniformly bounded (for every `r > 0` a bound `B`, independent of
`t₀ ≥ 0`, for all solutions starting within `r` of `xe`), and uniformly globally attractive (for
every `r, η > 0` a time `T`, independent of `t₀ ≥ 0` and of the solution, after which every
solution starting within `r` stays within `η`). MLS gives no formal definition; this is the
standard one. -/
def GloballyUniformlyAsymptoticallyStable (f : ℝ → E → E) (xe : E) : Prop :=
  UniformlyStable f xe ∧
    (∀ r > 0, ∃ B > 0, ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ < r →
      ∀ t, t₀ ≤ t → ‖x t - xe‖ < B) ∧
    (∀ r > 0, ∀ η > 0, ∃ T ≥ 0, ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ < r →
      ∀ t, t₀ + T ≤ t → ‖x t - xe‖ < η)

/-- Global uniform asymptotic stability implies uniform asymptotic stability (MLS p. 180). -/
theorem GloballyUniformlyAsymptoticallyStable.uniformlyAsymptoticallyStable {f : ℝ → E → E}
    {xe : E} (h : GloballyUniformlyAsymptoticallyStable f xe) :
    UniformlyAsymptoticallyStable f xe := by
  refine ⟨h.1, 1, one_pos, fun η hη => ?_⟩
  obtain ⟨T, hT, hT'⟩ := h.2.2 1 one_pos η hη
  exact ⟨T, hT, hT'⟩

/-- Global uniform asymptotic stability implies global asymptotic stability at every initial
time `t₀ ≥ 0` (MLS p. 180). -/
theorem GloballyUniformlyAsymptoticallyStable.globallyAsymptoticallyStableAt {f : ℝ → E → E}
    {xe : E} (h : GloballyUniformlyAsymptoticallyStable f xe) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    GloballyAsymptoticallyStableAt f xe t₀ := by
  refine ⟨h.1.stableAt ht₀, fun x hx => Metric.tendsto_atTop.mpr fun η hη => ?_⟩
  obtain ⟨T, -, hT⟩ := h.2.2 (‖x t₀ - xe‖ + 1) (by positivity) η hη
  exact ⟨t₀ + T, fun t ht => by
    rw [dist_eq_norm]
    exact hT t₀ ht₀ x hx (by linarith) t ht⟩

/-! ### Exponential stability is uniform (MLS p. 181) -/

/-- **MLS p. 181: exponential stability implies uniform stability.** The `δ` of
`ExponentiallyStable.stableAt` does not depend on the initial time. -/
theorem ExponentiallyStable.uniformlyStable {f : ℝ → E → E} {xe : E}
    (h : ExponentiallyStable f xe) : UniformlyStable f xe := by
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := h
  intro ε' hε'
  refine ⟨min ε (ε' / m), lt_min hε (div_pos hε' hm), fun t₀ ht₀ x hx hx0 t ht => ?_⟩
  have hb := h t₀ ht₀ x hx (hx0.le.trans (min_le_left _ _)) t ht
  have he : Real.exp (-α * (t - t₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 : ‖x t₀ - xe‖ < ε' / m := hx0.trans_le (min_le_right _ _)
  have h2 : m * ‖x t₀ - xe‖ < ε' := by rwa [lt_div_iff₀ hm, mul_comm] at h1
  calc ‖x t - xe‖ ≤ m * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖ := hb
    _ ≤ m * 1 * ‖x t₀ - xe‖ := by gcongr
    _ < ε' := by rwa [mul_one]

/-- **MLS p. 181: exponential stability implies uniform asymptotic stability.** With the
constants `m, α, ε` of Definition 4.3, every solution starting within `ε` is within `η` after the
time `T = max 0 (log (m ε / η) / α)`, independent of `t₀ ≥ 0`. -/
theorem ExponentiallyStable.uniformlyAsymptoticallyStable {f : ℝ → E → E} {xe : E}
    (h : ExponentiallyStable f xe) : UniformlyAsymptoticallyStable f xe := by
  refine ⟨h.uniformlyStable, ?_⟩
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := h
  refine ⟨ε, hε, fun η hη => ?_⟩
  set T := max 0 (Real.log (m * ε / η) / α) with hT
  refine ⟨T, le_max_left _ _, fun t₀ ht₀ x hx hx0 t ht => ?_⟩
  have hb := h t₀ ht₀ x hx hx0.le t (by linarith [le_max_left 0 (Real.log (m * ε / η) / α)])
  have hTt : Real.log (m * ε / η) / α ≤ t - t₀ := by
    have := le_max_right 0 (Real.log (m * ε / η) / α)
    linarith
  have hlog : Real.log (m * ε / η) ≤ α * (t - t₀) := by
    rw [div_le_iff₀ hα] at hTt
    linarith
  have hexp : m * ε / η ≤ Real.exp (α * (t - t₀)) :=
    (Real.log_le_iff_le_exp (by positivity)).mp hlog
  have hkey : m * ε * Real.exp (-α * (t - t₀)) ≤ η := by
    have h1 : m * ε ≤ η * Real.exp (α * (t - t₀)) := by
      rw [div_le_iff₀ hη] at hexp
      linarith
    have h2 : Real.exp (-α * (t - t₀)) * Real.exp (α * (t - t₀)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-α * (t - t₀))).le
    calc m * ε * Real.exp (-α * (t - t₀)) ≤ η * Real.exp (α * (t - t₀)) *
          Real.exp (-α * (t - t₀)) := h3
      _ = η := by rw [mul_assoc, mul_comm (Real.exp _), h2, mul_one]
  calc ‖x t - xe‖ ≤ m * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖ := hb
    _ < m * Real.exp (-α * (t - t₀)) * ε := by
        have : 0 < m * Real.exp (-α * (t - t₀)) := by positivity
        exact mul_lt_mul_of_pos_left hx0 this
    _ = m * ε * Real.exp (-α * (t - t₀)) := by ring
    _ ≤ η := hkey

/-! ### Theorem 4.4(4) (MLS p. 183) -/

/-- **The decrease step of MLS Theorem 4.4(3)–(4), p. 183.** Let `V ≥ 0` be continuous on
`ℝ₊ × E` with derivative `V̇` along the solutions on all of `E`, and `V̇(t, y) ≤ −κ` whenever
`‖y‖ ≥ ρ`, with `κ > 0`. Every solution from `t₀ ≥ 0` comes within `ρ` of the origin at some time
`s ∈ [t₀, t₀ + T]` for every `T > V(t₀, x(t₀))/κ`. -/
theorem exists_norm_lt_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hnn : ∀ t, 0 ≤ t → ∀ y, 0 ≤ V t y) (hVdot : HasDerivAlongSolutions f V Vdot univ)
    {ρ κ : ℝ} (hκ : 0 < κ) (hdec : ∀ t, 0 ≤ t → ∀ y : E, ρ ≤ ‖y‖ → Vdot t y ≤ -κ)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution f t₀ x) {T : ℝ}
    (hT : V t₀ (x t₀) < κ * T) : ∃ s, t₀ ≤ s ∧ s ≤ t₀ + T ∧ ‖x s‖ < ρ := by
  by_contra hne
  push Not at hne
  have hT0 : 0 < T := by
    have := hnn t₀ ht₀ (x t₀)
    by_contra hT0
    push Not at hT0
    nlinarith
  set W : ℝ → E → ℝ := fun s y => V s y + κ * s with hW
  have hWc : ContinuousOn (fun p : ℝ × E => W p.1 p.2) (Ici 0 ×ˢ univ) :=
    hcont.add (continuous_const.mul continuous_fst).continuousOn
  have hWd : HasDerivAlongSolutions f W (fun s y => Vdot s y + κ) {y | ρ ≤ ‖y‖} := by
    intro s₀ hs₀ z hz s hs _
    have h2 := (hVdot s₀ hs₀ z hz s hs (mem_univ _)).add ((hasDerivAt_id s).const_mul κ)
    rw [mul_one] at h2
    exact h2
  have hWneg : ∀ s, 0 ≤ s → ∀ y ∈ {y : E | ρ ≤ ‖y‖}, Vdot s y + κ ≤ 0 := by
    intro s hs y hy
    have := hdec s hs y hy
    linarith
  have hanti := antitoneOn_of_isSolution hWc hWd hWneg ht₀ hx (convex_Icc t₀ (t₀ + T))
    Icc_subset_Ici_self (by
      intro s hs
      rw [interior_Icc] at hs
      exact ⟨hs.1, hne s hs.1.le hs.2.le⟩)
  have h1 := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t₀ ≤ t₀ + T)
  simp only [hW] at h1
  have := hnn (t₀ + T) (by linarith) (x (t₀ + T))
  nlinarith

/-- **MLS Theorem 4.4(4), p. 183, under its literal hypotheses.** If `V` is positive definite
(Definition 4.5: `α(‖x‖) ≤ V(t, x)` for all `x`, `α(p) → ∞`) and decrescent (Definition 4.6, on a
ball), and `−V̇` is positive definite, where `V̇` is the derivative of `V` along the solutions on
all of `E`, then the origin is uniformly asymptotically stable and globally asymptotically stable
at every initial time `t₀ ≥ 0`. The uniformity of the global convergence (MLS's conclusion
"globally uniformly asymptotically stable") is proved in
`globallyUniformlyAsymptoticallyStable_of_lyapunov` under global decrescence. -/
theorem globallyAsymptoticallyStableAt_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    (hV : PositiveDefinite V) (hdec : Decrescent V) (hVdot' : PositiveDefinite fun t y => -Vdot t y)
    (hVdot : HasDerivAlongSolutions f V Vdot univ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    UniformlyAsymptoticallyStable f 0 ∧ GloballyAsymptoticallyStableAt f 0 t₀ := by
  obtain ⟨hcont, α, hα, -, hb⟩ := hV
  obtain ⟨hcont', γ, hγ, -, hbγ⟩ := hVdot'
  have hlpd : LocallyPositiveDefinite V :=
    ⟨hcont, 1, one_pos, α, hα, fun t ht => ⟨(hb t ht).1, fun y _ => (hb t ht).2 y⟩⟩
  have hlpd' : LocallyPositiveDefinite fun t y => -Vdot t y :=
    ⟨hcont', 1, one_pos, γ, hγ, fun t ht => ⟨(hbγ t ht).1, fun y _ => (hbγ t ht).2 y⟩⟩
  have hUAS := uniformlyAsymptoticallyStable_of_lyapunov hlpd hdec hlpd' one_pos
    (hVdot.mono (subset_univ _))
  refine ⟨hUAS, hUAS.1.stableAt ht₀, fun x hx => ?_⟩
  have hnn : ∀ t, 0 ≤ t → ∀ y, 0 ≤ V t y := by
    intro t ht y
    have h1 := (hb t ht).2 y
    have h2 := hα.le le_rfl (norm_nonneg y)
    rw [hα.2.2] at h2
    linarith
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  obtain ⟨δ, hδ, hstay⟩ := hUAS.1 η hη
  have hκ : 0 < γ δ := hγ.pos hδ
  have hdecr : ∀ t, 0 ≤ t → ∀ y : E, δ ≤ ‖y‖ → Vdot t y ≤ -γ δ := by
    intro t ht y hy
    have h1 := (hbγ t ht).2 y
    have h2 := hγ.le hδ.le hy
    linarith
  obtain ⟨s, hs₀, -, hs⟩ := exists_norm_lt_of_lyapunov hcont hnn hVdot hκ hdecr ht₀ hx
    (T := V t₀ (x t₀) / γ δ + 1) (by
      rw [mul_add, mul_div_cancel₀ _ hκ.ne', mul_one]
      linarith)
  refine ⟨s, fun t ht => ?_⟩
  rw [dist_eq_norm]
  exact hstay s (ht₀.trans hs₀) x (hx.mono hs₀) (by simpa using hs) t ht

/-- **MLS Theorem 4.4(4), p. 183, with global decrescence.** If `V` is positive definite
(Definition 4.5), `V(t, x) ≤ β(‖x‖)` for **all** `x` and `t ≥ 0` with `β` a comparison function
(decrescence on the whole space; MLS's Definition 4.6 asks it only on a ball, and this stronger
hypothesis is added), and `−V̇` is positive definite, where `V̇` is the derivative along the
solutions on all of `E`, then the origin is globally uniformly asymptotically stable. -/
theorem globallyUniformlyAsymptoticallyStable_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    (hV : PositiveDefinite V) {β : ℝ → ℝ} (hβ : IsClassK β)
    (hup : ∀ t, 0 ≤ t → ∀ y : E, V t y ≤ β ‖y‖)
    (hVdot' : PositiveDefinite fun t y => -Vdot t y)
    (hVdot : HasDerivAlongSolutions f V Vdot univ) :
    GloballyUniformlyAsymptoticallyStable f 0 := by
  obtain ⟨hcont, α, hα, hαtop, hb⟩ := hV
  obtain ⟨hcont', γ, hγ, -, hbγ⟩ := hVdot'
  have hlpd : LocallyPositiveDefinite V :=
    ⟨hcont, 1, one_pos, α, hα, fun t ht => ⟨(hb t ht).1, fun y _ => (hb t ht).2 y⟩⟩
  have hdec : Decrescent V := ⟨hcont, 1, one_pos, β, hβ, fun t ht y _ => hup t ht y⟩
  have hneg : ∀ t, 0 ≤ t → ∀ y ∈ Metric.ball (0 : E) 1, Vdot t y ≤ 0 := by
    intro t ht y _
    have h1 := (hbγ t ht).2 y
    have h2 := hγ.le le_rfl (norm_nonneg y)
    rw [hγ.2.2] at h2
    linarith
  have hUS := uniformlyStable_of_lyapunov hlpd hdec one_pos (hVdot.mono (subset_univ _)) hneg
  have hnn : ∀ t, 0 ≤ t → ∀ y, 0 ≤ V t y := by
    intro t ht y
    have h1 := (hb t ht).2 y
    have h2 := hα.le le_rfl (norm_nonneg y)
    rw [hα.2.2] at h2
    linarith
  have hnegU : ∀ t, 0 ≤ t → ∀ y ∈ (univ : Set E), Vdot t y ≤ 0 := by
    intro t ht y _
    have h1 := (hbγ t ht).2 y
    have h2 := hγ.le le_rfl (norm_nonneg y)
    rw [hγ.2.2] at h2
    linarith
  -- `V` does not increase along solutions
  have hmono : ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ∀ t, t₀ ≤ t → V t (x t) ≤ V t₀ (x t₀) := by
    intro t₀ ht₀ x hx t ht
    have hanti := antitoneOn_of_isSolution hcont hVdot hnegU ht₀ hx (convex_Ici t₀) subset_rfl
      (by
        intro s hs
        rw [interior_Ici] at hs
        exact ⟨hs, mem_univ _⟩)
    exact hanti self_mem_Ici ht ht
  refine ⟨hUS, fun r hr => ?_, fun r hr η hη => ?_⟩
  · -- uniform boundedness
    obtain ⟨B, hB⟩ := (hαtop.eventually_gt_atTop (β r)).exists_forall_of_atTop
    set B' := max B 1 with hB'
    refine ⟨B', lt_of_lt_of_le one_pos (le_max_right _ _), fun t₀ ht₀ x hx hx0 t ht => ?_⟩
    rw [sub_zero] at hx0 ⊢
    by_contra hcon
    push Not at hcon
    have h1 : α B' ≤ α ‖x t‖ := hα.le (by positivity) hcon
    have h2 := (hb t (ht₀.trans ht)).2 (x t)
    have h3 := hmono t₀ ht₀ x hx t ht
    have h4 := hup t₀ ht₀ (x t₀)
    have h5 : β ‖x t₀‖ ≤ β r := hβ.le (norm_nonneg _) hx0.le
    have h6 := hB B' (le_max_left _ _)
    linarith
  · -- uniform global attractivity
    obtain ⟨δ, hδ, hstay⟩ := hUS η hη
    have hκ : 0 < γ δ := hγ.pos hδ
    have hdecr : ∀ t, 0 ≤ t → ∀ y : E, δ ≤ ‖y‖ → Vdot t y ≤ -γ δ := by
      intro t ht y hy
      have h1 := (hbγ t ht).2 y
      have h2 := hγ.le hδ.le hy
      linarith
    have hβr : 0 ≤ β r := by
      have := hβ.le le_rfl hr.le
      rwa [hβ.2.2] at this
    refine ⟨β r / γ δ + 1, by positivity, fun t₀ ht₀ x hx hx0 t ht => ?_⟩
    rw [sub_zero] at hx0
    have hV0 : V t₀ (x t₀) < γ δ * (β r / γ δ + 1) := by
      have h4 := hup t₀ ht₀ (x t₀)
      have h5 : β ‖x t₀‖ ≤ β r := hβ.le (norm_nonneg _) hx0.le
      rw [mul_add, mul_div_cancel₀ _ hκ.ne', mul_one]
      linarith
    obtain ⟨s, hs₀, hsT, hs⟩ := exists_norm_lt_of_lyapunov hcont hnn hVdot hκ hdecr ht₀ hx hV0
    exact hstay s (ht₀.trans hs₀) x (hx.mono hs₀) (by simpa using hs) t (hsT.trans ht)

/-! ### Theorem 4.5, local form (MLS pp. 183–184) -/

/-- **The rate bound of MLS Theorem 4.5 (p. 184) for a solution that stays in a region `U`.**
If on `U` the bounds `a₁‖y‖² ≤ V(t, y) ≤ a₂‖y‖²` and `V̇(t, y) ≤ −a₃‖y‖²` hold for `t ≥ 0`, `V̇`
is the derivative along the solutions in `U`, and the solution from `t₀ ≥ 0` stays in `U`, then
`‖x(t)‖ ≤ √(a₂/a₁) e^{−(a₃/(2a₂))(t − t₀)} ‖x(t₀)‖` for `t ≥ t₀`. -/
theorem norm_le_of_quadratic_lyapunov_of_mem {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) {U : Set E}
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hlow : ∀ t, 0 ≤ t → ∀ y ∈ U, a₁ * ‖y‖ ^ 2 ≤ V t y)
    (hup : ∀ t, 0 ≤ t → ∀ y ∈ U, V t y ≤ a₂ * ‖y‖ ^ 2)
    (hVdot : HasDerivAlongSolutions f V Vdot U)
    (hdec : ∀ t, 0 ≤ t → ∀ y ∈ U, Vdot t y ≤ -(a₃ * ‖y‖ ^ 2))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution f t₀ x) (hin : ∀ s, t₀ ≤ s → x s ∈ U)
    {t : ℝ} (ht : t₀ ≤ t) :
    ‖x t‖ ≤ Real.sqrt (a₂ / a₁) * Real.exp (-(a₃ / (2 * a₂)) * (t - t₀)) * ‖x t₀‖ := by
  set k := a₃ / a₂ with hk
  set g : ℝ → ℝ := fun s => Real.exp (k * (s - t₀)) * V s (x s) with hg
  have hgc : ContinuousOn g (Ici t₀) := by
    have h1 : ContinuousOn (fun s => (s, x s)) (Ici t₀) := continuousOn_id.prodMk hx.1
    have h2 : ContinuousOn (fun s => V s (x s)) (Ici t₀) :=
      hcont.comp h1 fun s hs => ⟨ht₀.trans hs, mem_univ _⟩
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const))).continuousOn.mul h2
  have hanti : AntitoneOn g (Ici t₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀) hgc
      (f' := fun s => k * Real.exp (k * (s - t₀)) * V s (x s) +
        Real.exp (k * (s - t₀)) * Vdot s (x s)) ?_ ?_
    · intro s hs
      rw [interior_Ici] at hs
      have he : HasDerivAt (fun s => Real.exp (k * (s - t₀))) (Real.exp (k * (s - t₀)) * k) s := by
        have := ((hasDerivAt_id s).sub_const t₀).const_mul k
        simpa using this.exp
      have hv := hVdot t₀ ht₀ x hx s hs (hin s (le_of_lt hs))
      refine HasDerivAt.hasDerivWithinAt ?_
      convert he.mul hv using 1
      ring
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 ≤ s := ht₀.trans (le_of_lt hs)
      have hU := hin s (le_of_lt hs)
      have h1 := hup s hs0 (x s) hU
      have h2 := hdec s hs0 (x s) hU
      have hepos := Real.exp_pos (k * (s - t₀))
      have h3 : k * V s (x s) + Vdot s (x s) ≤ 0 := by
        have : k * (a₂ * ‖x s‖ ^ 2) = a₃ * ‖x s‖ ^ 2 := by
          rw [hk]; field_simp
        have hk0 : 0 < k := div_pos ha₃ ha₂
        nlinarith
      nlinarith
  have hgt : g t ≤ g t₀ := hanti self_mem_Ici ht ht
  have hg0 : g t₀ = V t₀ (x t₀) := by simp [hg]
  have hVt : V t (x t) ≤ Real.exp (-(k * (t - t₀))) * (a₂ * ‖x t₀‖ ^ 2) := by
    have h1 : Real.exp (k * (t - t₀)) * V t (x t) ≤ a₂ * ‖x t₀‖ ^ 2 := by
      have := hup t₀ ht₀ (x t₀) (hin t₀ le_rfl)
      rw [hg0] at hgt
      exact hgt.trans this
    have h2 : V t (x t) = Real.exp (-(k * (t - t₀))) * (Real.exp (k * (t - t₀)) * V t (x t)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hsq : ‖x t‖ ^ 2 ≤
      (Real.sqrt (a₂ / a₁) * Real.exp (-(a₃ / (2 * a₂)) * (t - t₀)) * ‖x t₀‖) ^ 2 := by
    have h1 : a₁ * ‖x t‖ ^ 2 ≤ Real.exp (-(k * (t - t₀))) * (a₂ * ‖x t₀‖ ^ 2) :=
      (hlow t (ht₀.trans ht) (x t) (hin t ht)).trans hVt
    have h2 : (Real.sqrt (a₂ / a₁) * Real.exp (-(a₃ / (2 * a₂)) * (t - t₀)) * ‖x t₀‖) ^ 2 =
        a₂ / a₁ * Real.exp (-(k * (t - t₀))) * ‖x t₀‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos ha₂ ha₁).le, ← Real.exp_nat_mul]
      congr 2
      rw [hk]
      push_cast
      field_simp
    rw [h2]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha₁]
    nlinarith
  have hnn : 0 ≤ Real.sqrt (a₂ / a₁) * Real.exp (-(a₃ / (2 * a₂)) * (t - t₀)) * ‖x t₀‖ := by
    positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp hsq

/-- **MLS Theorem 4.5, sufficiency, local form, with the rate bounds of p. 184.** Let `V` be
continuous on `ℝ₊ × E` with `a₁‖y‖² ≤ V(t, y) ≤ a₂‖y‖²` and `V̇(t, y) ≤ −a₃‖y‖²` for `‖y‖ ≤ ε`
and `t ≥ 0`, where `V̇` is the derivative along the solutions in the ball of radius `ε`. Every
solution from `t₀ ≥ 0` with `‖x(t₀)‖ < min ε (ε √(a₁/a₂))` stays in that ball and satisfies
`‖x(t)‖ ≤ √(a₂/a₁) e^{−(a₃/(2a₂))(t − t₀)} ‖x(t₀)‖` for `t ≥ t₀`. The bound `‖∂V/∂x‖ ≤ a₄‖x‖`
is used only by the converse and is not assumed. -/
theorem norm_le_of_quadratic_lyapunov_local {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    {a₁ a₂ a₃ ε : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (hε : 0 < ε)
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hlow : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y)
    (hup : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → V t y ≤ a₂ * ‖y‖ ^ 2)
    (hVdot : HasDerivAlongSolutions f V Vdot (Metric.ball 0 ε))
    (hdec : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution f t₀ x)
    (hx₀ : ‖x t₀‖ < min ε (ε * Real.sqrt (a₁ / a₂))) {t : ℝ} (ht : t₀ ≤ t) :
    ‖x t‖ ≤ Real.sqrt (a₂ / a₁) * Real.exp (-(a₃ / (2 * a₂)) * (t - t₀)) * ‖x t₀‖ := by
  have hneg : ∀ t, 0 ≤ t → ∀ y ∈ Metric.ball (0 : E) ε, Vdot t y ≤ 0 := by
    intro t ht y hy
    rw [mem_ball_zero_iff] at hy
    have := hdec t ht y hy.le
    have : 0 ≤ a₃ * ‖y‖ ^ 2 := by positivity
    linarith
  have hlowα : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → (fun r => a₁ * r ^ 2) ‖y‖ ≤ V t y :=
    fun t ht y hy => hlow t ht y hy
  have hx0ε : ‖x t₀‖ < ε := hx₀.trans_le (min_le_left _ _)
  have hV0 : V t₀ (x t₀) < (fun r => a₁ * r ^ 2) ε := by
    have h1 := hup t₀ ht₀ (x t₀) hx0ε.le
    have h2 : ‖x t₀‖ < ε * Real.sqrt (a₁ / a₂) := hx₀.trans_le (min_le_right _ _)
    have h3 : ‖x t₀‖ ^ 2 < (ε * Real.sqrt (a₁ / a₂)) ^ 2 :=
      pow_lt_pow_left₀ h2 (norm_nonneg _) two_ne_zero
    rw [mul_pow, Real.sq_sqrt (div_pos ha₁ ha₂).le] at h3
    have h4 : a₂ * ‖x t₀‖ ^ 2 < a₂ * (ε ^ 2 * (a₁ / a₂)) := mul_lt_mul_of_pos_left h3 ha₂
    have h5 : a₂ * (ε ^ 2 * (a₁ / a₂)) = a₁ * ε ^ 2 := by field_simp
    simp only
    linarith
  have hin : ∀ s, t₀ ≤ s → x s ∈ Metric.ball (0 : E) ε := by
    intro s hs
    rw [mem_ball_zero_iff]
    exact norm_lt_of_lyapunov (α := fun r => a₁ * r ^ 2) hcont hVdot hneg subset_rfl hlowα ht₀ hx
      hx0ε hV0 s hs
  exact norm_le_of_quadratic_lyapunov_of_mem ha₁ ha₂ ha₃ hcont
    (fun t ht y hy => hlow t ht y (mem_ball_zero_iff.mp hy).le)
    (fun t ht y hy => hup t ht y (mem_ball_zero_iff.mp hy).le) hVdot
    (fun t ht y hy => hdec t ht y (mem_ball_zero_iff.mp hy).le) ht₀ hx hin ht

/-- **MLS Theorem 4.5, sufficiency, local form (p. 183):** under the hypotheses of
`norm_le_of_quadratic_lyapunov_local` the origin is exponentially stable (Definition 4.3), with
`m = √(a₂/a₁)`, `α = a₃/(2a₂)` and initial radius `min ε (ε √(a₁/a₂)) / 2`. -/
theorem exponentiallyStable_of_quadratic_lyapunov_local {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    {a₁ a₂ a₃ ε : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (hε : 0 < ε)
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hlow : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y)
    (hup : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → V t y ≤ a₂ * ‖y‖ ^ 2)
    (hVdot : HasDerivAlongSolutions f V Vdot (Metric.ball 0 ε))
    (hdec : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) :
    ExponentiallyStable f 0 := by
  have hρ : 0 < min ε (ε * Real.sqrt (a₁ / a₂)) :=
    lt_min hε (mul_pos hε (Real.sqrt_pos.mpr (div_pos ha₁ ha₂)))
  refine ⟨Real.sqrt (a₂ / a₁), Real.sqrt_pos.mpr (div_pos ha₂ ha₁), a₃ / (2 * a₂),
    div_pos ha₃ (by positivity), min ε (ε * Real.sqrt (a₁ / a₂)) / 2, by positivity,
    fun t₀ ht₀ x hx hx0 t ht => ?_⟩
  rw [sub_zero] at hx0 ⊢
  have hx0' : ‖x t₀‖ < min ε (ε * Real.sqrt (a₁ / a₂)) := by linarith
  simpa using norm_le_of_quadratic_lyapunov_local ha₁ ha₂ ha₃ hε hcont hlow hup hVdot hdec ht₀
    hx hx0' ht

end Stability
end RoboLean
