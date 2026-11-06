import RoboLean.Surfaces.LinesOfCurvature
import RoboLean.Nonholonomic.FlowBoxSmooth

/-!
# Theorem 5.9: orthogonal charts exist locally (MLS p. 244)

**What MLS prints.** Printed p. 244: "A coordinate chart is an orthogonal coordinate chart if `c_u`
and `c_v` are orthogonal. **Theorem 5.9.** Locally, there exists an orthogonal chart for all
regular surfaces. The proof can be found in any standard book on differential geometry."

**Proved here.** The named statement of the library, `OrthogonalChartStatement`
(`Surfaces/LinesOfCurvature`), holds (`orthogonalChartStatement`): for a chart `c` smooth on an
open `U ⊂ ℝ²` with injective differential and every `α₀ ∈ U`, a smooth reparametrization `θ`,
injective on an open `V`, with `θ(V)` a neighbourhood of `α₀`, makes `c ∘ θ` an orthogonal chart on
`V` (`exists_orthogonal_reparametrization`).

**Route (one flow, no umbilics).** In the parameter plane the field
`Y = −(g₁₂ / g₁₁) e₁ + e₂`, with `g₁₁ = ⟨c_u, c_u⟩` and `g₁₂ = ⟨c_u, c_v⟩`, is smooth on `U`, has
second component `1`, and `c` carries it to `c_v − (g₁₂ / g₁₁) c_u`, orthogonal to `c_u`. Cut off
outside a small ball about `α₀`, it has a smooth two-sided flow `Φ` in the time and the point
together (`contDiff_twoSidedFlow_of_hasCompactSupport`). The reparametrization is
`θ(β) = Φ(β₂ − α₀₂, (β₁, α₀₂))`: the `β₂`-lines are integral curves of `Y`, and since `Y` has second
component `1` near `α₀` the flow raises the second coordinate at unit rate, so `θ(β)₂ = β₂` and the
`β₁`-lines are horizontal. Hence `(c ∘ θ)_u` is a multiple of `c_u` and `(c ∘ θ)_v` is `c` applied
to `Y`, orthogonal to it. The differential of `θ` is `e₁` and `Y(α₀)` on the coordinate vectors at
`α₀`, invertible, so `θ` is open at `α₀`; the classical route through lines of curvature
(`Surfaces/LinesOfCurvature`) needs non-umbilic points and is not used.

**Hypotheses against MLS.** As in the named statement: the chart is smooth on an open set with
injective differential (MLS's regular surface, conditions 1 and 3 of p. 243 with smoothness for
"differentiable"); the reparametrization is smooth and injective on `V` with an image that is a
neighbourhood of `α₀`; `IsOrthogonalChartOn` asks twice continuous differentiability.

**Conventions.** Charts `(Fin 2 → ℝ) → Vec3`, partial derivatives `partialU`, `partialV` (MLS
p. 243), orthogonality `IsOrthogonalAt` (p. 244); flows as in `Nonholonomic/FlowBoxSmooth` (time
first, `twoSidedFlow` from flows of the field and its negative).
-/

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace RoboLean
namespace Surface

open Nonholonomic Stability

/-- **Orthogonal reparametrization near a point (MLS Theorem 5.9, p. 244):** for a chart `c` smooth
on an open `U ⊂ ℝ²` with injective differential and `α₀ ∈ U`, there are an open set `V`, a smooth
map `θ`, injective on `V` with `θ(V) ⊂ U` a neighbourhood of `α₀`, and `β₀ ∈ V` with
`θ(β₀) = α₀`, such that `c ∘ θ` is an orthogonal chart on `V` (`IsOrthogonalChartOn`). -/
theorem exists_orthogonal_reparametrization {c : (Fin 2 → ℝ) → Vec3} {U : Set (Fin 2 → ℝ)}
    (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c U)
    (hinj : ∀ α ∈ U, Function.Injective (fderiv ℝ c α)) {α₀ : Fin 2 → ℝ} (hα₀ : α₀ ∈ U) :
    ∃ (V : Set (Fin 2 → ℝ)) (θ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (β₀ : Fin 2 → ℝ),
      β₀ ∈ V ∧ θ β₀ = α₀ ∧ ContDiffOn ℝ ∞ θ V ∧ Set.InjOn θ V ∧ Set.MapsTo θ V U ∧
        θ '' V ∈ 𝓝 α₀ ∧ IsOrthogonalChartOn (c ∘ θ) V := by
  classical
  set e₀ : Fin 2 → ℝ := Pi.single 0 1 with he₀
  set e₁ : Fin 2 → ℝ := Pi.single 1 1 with he₁
  -- the metric coefficients and the field `Y` orthogonal to `c_u` under `c`
  have hcd : ∀ α ∈ U, DifferentiableAt ℝ c α := fun α hα =>
    (hc.contDiffAt (hU.mem_nhds hα)).differentiableAt (by simp)
  have hfd : ContDiffOn ℝ ∞ (fun α => fderiv ℝ c α) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hc).2
  set cu : (Fin 2 → ℝ) → Vec3 := fun α => fderiv ℝ c α e₀ with hcu_def
  set cv : (Fin 2 → ℝ) → Vec3 := fun α => fderiv ℝ c α e₁ with hcv_def
  have hcu : ContDiffOn ℝ ∞ cu U := hfd.clm_apply contDiffOn_const
  have hcv : ContDiffOn ℝ ∞ cv U := hfd.clm_apply contDiffOn_const
  have hcu0 : ∀ α ∈ U, cu α ≠ 0 := fun α hα h0 => by
    have h1 := hinj α hα (show fderiv ℝ c α e₀ = fderiv ℝ c α 0 by rw [map_zero]; exact h0)
    have h2 := congrFun h1 0
    simp [he₀] at h2
  have hg₁₁ : ∀ α ∈ U, inner ℝ (cu α) (cu α) ≠ 0 := fun α hα =>
    inner_self_ne_zero.2 (hcu0 α hα)
  set Y : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
    fun α => (-(inner ℝ (cu α) (cv α) / inner ℝ (cu α) (cu α))) • e₀ + e₁ with hY_def
  have hY : ContDiffOn ℝ ∞ Y U :=
    ((((hcu.inner ℝ hcv).div (hcu.inner ℝ hcu) hg₁₁).neg).smul contDiffOn_const).add
      contDiffOn_const
  have hY1 : ∀ α, Y α 1 = 1 := fun α => by simp [hY_def, he₀, he₁]
  have hYorth : ∀ α ∈ U, inner ℝ (cu α) (fderiv ℝ c α (Y α)) = 0 := fun α hα => by
    have h := hg₁₁ α hα
    simp only [hY_def, map_add, map_smul, inner_add_right, inner_smul_right]
    field_simp
    ring
  -- the field cut off outside a ball about `α₀`
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU α₀ hα₀
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  let ρ : ContDiffBump α₀ := ⟨r, 2 * r, hr0, by linarith⟩
  set X : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun α => ρ α • Y α with hX_def
  have hXc : ContDiff ℝ ∞ X := by
    refine contDiff_iff_contDiffAt.2 fun α => ?_
    by_cases hα : α ∈ U
    · exact ρ.contDiffAt.smul (hY.contDiffAt (hU.mem_nhds hα))
    · have h2 : 2 * r < dist α α₀ := by
        by_contra h
        exact hα (hεU (by rw [mem_ball]; linarith [not_lt.1 h]))
      have hfar : (fun _ => (0 : Fin 2 → ℝ)) =ᶠ[𝓝 α] X := by
        filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
          h2] with β hβ
        have hβ' : ρ.rOut ≤ dist β α₀ := le_of_lt (by simpa using hβ)
        simp only [hX_def]
        rw [ρ.zero_of_le_dist hβ', zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hfar.symm
  have hXs : HasCompactSupport X := ρ.hasCompactSupport.smul_right (f' := Y)
  have hXY : ∀ α ∈ ball α₀ r, X α = Y α := fun α hα => by
    simp only [hX_def, ρ.one_of_mem_closedBall (ball_subset_closedBall hα), one_smul]
  have hballU : ball α₀ r ⊆ U := fun α hα => hεU (ball_subset_ball (by linarith) hα)
  -- its smooth two-sided flow and the reparametrization
  obtain ⟨φ, φ', D, D', hφ, hφ', hΦ⟩ := contDiff_twoSidedFlow_of_hasCompactSupport hXc hXs
  have hΦ0 : ∀ p, twoSidedFlow φ φ' 0 p = p := twoSidedFlow_zero hφ
  have hcurve : ∀ p t, HasDerivAt (fun s => twoSidedFlow φ φ' s p) (X (twoSidedFlow φ φ' t p)) t :=
    fun p t => isIntegralCurve_twoSidedFlow hφ hφ' p t
  set θ : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
    fun β => twoSidedFlow φ φ' (β 1 - α₀ 1) (α₀ + (β 0 - α₀ 0) • e₀) with hθ_def
  have hβ : ∀ i : Fin 2, ContDiff ℝ ∞ fun β : Fin 2 → ℝ => β i := fun i => contDiff_apply ℝ _ i
  have hθc : ContDiff ℝ ∞ θ := hΦ.comp
    (((hβ 1).sub contDiff_const).prodMk
      (contDiff_const.add (((hβ 0).sub contDiff_const).smul contDiff_const)))
  have hθd : ∀ β, DifferentiableAt ℝ θ β := fun β => (hθc.differentiable (by simp)) β
  have hθα₀ : θ α₀ = α₀ := by simp [hθ_def, hΦ0]
  -- near `α₀` the flow stays in the ball where `X = Y`
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuousAt_iff.1
    (hΦ.continuous.continuousAt (x := ((0 : ℝ), α₀))) r hr0
  have hpdist : ∀ β ∈ ball α₀ δ, dist (α₀ + (β 0 - α₀ 0) • e₀) α₀ < δ := fun β hβ => by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he₀, Pi.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, ← Real.dist_eq]
    exact (dist_le_pi_dist β α₀ 0).trans_lt hβ
  have hreg : ∀ β ∈ ball α₀ δ, ∀ s ∈ Ioo (-δ) δ,
      twoSidedFlow φ φ' s (α₀ + (β 0 - α₀ 0) • e₀) ∈ ball α₀ r := by
    intro β hβ s hs
    have hq : dist ((s, α₀ + (β 0 - α₀ 0) • e₀) : ℝ × (Fin 2 → ℝ)) (0, α₀) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, sub_zero]
      exact max_lt (abs_lt.2 hs) (hpdist β hβ)
    have h1 := hδr hq
    simp only [hΦ0] at h1
    exact h1
  have hmem : ∀ β ∈ ball α₀ δ, β 1 - α₀ 1 ∈ Ioo (-δ) δ := fun β hβ => by
    have h := (dist_le_pi_dist β α₀ 1).trans_lt hβ
    rw [Real.dist_eq] at h
    exact abs_lt.1 h
  have hθball : ∀ β ∈ ball α₀ δ, θ β ∈ ball α₀ r := fun β hβ => hreg β hβ _ (hmem β hβ)
  -- the flow raises the second coordinate at unit rate, so `θ(β)₂ = β₂`
  have hsecond : ∀ β ∈ ball α₀ δ, θ β 1 = β 1 := by
    intro β hβ
    set p := α₀ + (β 0 - α₀ 0) • e₀ with hp
    have hp1 : p 1 = α₀ 1 := by simp [hp, he₀]
    have hgd : ∀ s, HasDerivAt (fun s => twoSidedFlow φ φ' s p 1 - s)
        (X (twoSidedFlow φ φ' s p) 1 - 1) s := fun s =>
      ((hasDerivAt_pi.1 (hcurve p s)) 1).sub (hasDerivAt_id s)
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s _ => (hgd s).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [(hgd s).deriv, hXY _ (hreg β hβ s hs), hY1, sub_self]
        rfl)
      (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩) (hmem β hβ)
    simp only [hΦ0, hp1, sub_zero] at hconst
    show twoSidedFlow φ φ' (β 1 - α₀ 1) p 1 = β 1
    linarith
  -- the partial derivatives of `θ`
  have hpartV : ∀ β, partialV θ β = X (θ β) := by
    intro β
    refine partialV_eq_of_hasDerivAt (hθd β) ?_
    have e : (fun s : ℝ => θ (β + s • e₁)) =
        fun s => twoSidedFlow φ φ' (s + (β 1 - α₀ 1)) (α₀ + (β 0 - α₀ 0) • e₀) := by
      funext s
      simp only [hθ_def, he₁, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, mul_one, mul_zero,
        add_zero]
      congr 1
      ring
    rw [e]
    have h1 := (hcurve (α₀ + (β 0 - α₀ 0) • e₀) (0 + (β 1 - α₀ 1))).scomp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).add_const (β 1 - α₀ 1))
    simpa [Function.comp_def, hθ_def] using h1
  have hpartU0 : partialU θ α₀ = e₀ := by
    refine partialU_eq_of_hasDerivAt (hθd α₀) ?_
    have e : (fun s : ℝ => θ (α₀ + s • e₀)) = fun s => α₀ + s • e₀ := by
      funext s
      simp [hθ_def, he₀, hΦ0]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e₀).const_add α₀
  have hpartU1 : ∀ β ∈ ball α₀ δ, partialU θ β 1 = 0 := by
    intro β hβ
    have h1 : HasDerivAt (fun s : ℝ => θ (β + s • e₀) 1) (partialU θ β 1) 0 :=
      hasDerivAt_pi.1 (hasDerivAt_lineU (hθd β)) 1
    have hev : (fun _ : ℝ => β 1) =ᶠ[𝓝 0] fun s : ℝ => θ (β + s • e₀) 1 := by
      have hcl : Continuous fun s : ℝ => β + s • e₀ := by fun_prop
      have hmem' : ∀ᶠ s in 𝓝 (0 : ℝ), β + s • e₀ ∈ ball α₀ δ :=
        hcl.continuousAt.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hβ)
      filter_upwards [hmem'] with s hs
      rw [hsecond _ hs]
      simp [he₀]
    exact h1.unique ((hasDerivAt_const (0 : ℝ) (β 1)).congr_of_eventuallyEq hev.symm)
  -- the open set `V`
  have hacont : Continuous fun β => partialU θ β 0 :=
    (continuous_apply 0).comp ((hθc.continuous_fderiv (by simp)).clm_apply continuous_const)
  set V := ball α₀ δ ∩ {β | partialU θ β 0 ≠ 0} with hV
  have hVo : IsOpen V := isOpen_ball.inter (isOpen_ne_fun hacont continuous_const)
  have hα₀V : α₀ ∈ V := ⟨mem_ball_self hδ, by simp [hpartU0, he₀]⟩
  have hmaps : MapsTo θ V U := fun β hβ => hballU (hθball β hβ.1)
  have hX1 : ∀ β ∈ V, X (θ β) 1 = 1 := fun β hβ => by rw [hXY _ (hθball β hβ.1), hY1]
  have hθinj : ∀ β ∈ V, Function.Injective (fderiv ℝ θ β) := by
    intro β hβ
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    rw [fderiv_apply_eq, hpartV] at hv
    have e1 := congrFun hv 1
    have e0 := congrFun hv 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpartU1 β hβ.1,
      hX1 β hβ] at e1 e0
    have hv1 : v 1 = 0 := by linarith
    rw [hv1, zero_mul, add_zero] at e0
    have hv0 : v 0 = 0 := (mul_eq_zero.1 e0).resolve_right hβ.2
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
  have hinjθ : InjOn θ V := by
    intro β hβ β' hβ' heq
    have h1 : β 1 = β' 1 := by rw [← hsecond β hβ.1, ← hsecond β' hβ'.1, heq]
    have hp : α₀ + (β 0 - α₀ 0) • e₀ = α₀ + (β' 0 - α₀ 0) • e₀ := by
      have h2 := congrArg (twoSidedFlow φ φ' (-(β 1 - α₀ 1))) heq
      simp only [hθ_def, ← h1] at h2
      rwa [twoSidedFlow_add hφ hφ', twoSidedFlow_add hφ hφ', neg_add_cancel, hΦ0, hΦ0] at h2
    have h0 : β 0 = β' 0 := by
      have h3 := congrFun hp 0
      simpa [he₀] using h3
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have himage : θ '' V ∈ 𝓝 α₀ := by
    set A := (LinearEquiv.ofInjectiveEndo (fderiv ℝ θ α₀ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
      (hθinj α₀ hα₀V)).toContinuousLinearEquiv with hA_def
    have hA : HasStrictFDerivAt θ (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) α₀ := by
      have h := (hθc.contDiffAt (x := α₀)).hasStrictFDerivAt (by simp)
      convert h using 1
      exact ContinuousLinearMap.ext fun v => rfl
    have h1 := hA.map_nhds_eq_of_equiv
    rw [hθα₀] at h1
    rw [← h1]
    exact image_mem_map (hVo.mem_nhds hα₀V)
  -- `c ∘ θ` is an orthogonal chart on `V`
  have hcθ : ContDiffOn ℝ ∞ (c ∘ θ) V := hc.comp hθc.contDiffOn hmaps
  have hfc : ∀ β ∈ V, fderiv ℝ (c ∘ θ) β = (fderiv ℝ c (θ β)).comp (fderiv ℝ θ β) :=
    fun β hβ => fderiv_comp β (hcd _ (hmaps hβ)) (hθd β)
  refine ⟨V, θ, α₀, hα₀V, hθα₀, hθc.contDiffOn, hinjθ, hmaps, himage,
    ⟨hVo, hcθ.of_le (by simp), fun β hβ => ?_, fun β hβ => ?_⟩⟩
  · rw [hfc β hβ, ContinuousLinearMap.coe_comp]
    exact (hinj _ (hmaps hβ)).comp (hθinj β hβ)
  · have hw : partialU θ β = partialU θ β 0 • e₀ := by
      funext i
      fin_cases i
      · simp [he₀]
      · simp [he₀, hpartU1 β hβ.1]
    have hu : partialU (c ∘ θ) β = partialU θ β 0 • cu (θ β) := by
      simp only [partialU, hfc β hβ, ContinuousLinearMap.comp_apply]
      rw [show fderiv ℝ θ β (Pi.single 0 1) = partialU θ β 0 • e₀ from hw, map_smul]
      simp [he₀, hcu_def]
    have hv : partialV (c ∘ θ) β = fderiv ℝ c (θ β) (Y (θ β)) := by
      simp only [partialV, hfc β hβ, ContinuousLinearMap.comp_apply]
      rw [show fderiv ℝ θ β (Pi.single 1 1) = partialV θ β from rfl, hpartV,
        hXY _ (hθball β hβ.1)]
    show inner ℝ (partialU (c ∘ θ) β) (partialV (c ∘ θ) β) = 0
    rw [hu, hv, inner_smul_left, hYorth _ (hmaps hβ), mul_zero]

/-- **MLS Theorem 5.9, p. 244, proved:** "Locally, there exists an orthogonal chart for all regular
surfaces", as the library's named statement `OrthogonalChartStatement` (smooth charts on open sets
with injective differential, smooth injective reparametrizations onto neighbourhoods). -/
theorem orthogonalChartStatement : OrthogonalChartStatement :=
  fun _ _ hU hc hinj _ hα₀ => exists_orthogonal_reparametrization hU hc hinj hα₀

end Surface
end RoboLean
