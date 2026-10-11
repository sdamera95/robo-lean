import RoboLean.Control.GlobalFlow
import RoboLean.Control.StabilityTheorems
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The converse of the exponential stability theorem, three bounds (MLS Theorem 4.5, p. 183)

**What MLS prints (read this session, p. 183).** Theorem 4.5: "`x* = 0` is an exponentially stable
equilibrium point of `ẋ = f(x, t)` if and only if there exists an `ε > 0` and a function `V(x, t)`
which satisfies `α₁‖x‖² ≤ V(x, t) ≤ α₂‖x‖²`, `V̇|_{ẋ = f(x, t)} ≤ −α₃‖x‖²`,
`‖∂V/∂x (x, t)‖ ≤ α₄‖x‖` for some positive constants `α₁, α₂, α₃, α₄`, and `‖x‖ ≤ ε`." MLS gives no
proof (it cites [102]).

**Formalized here: the "only if" direction with the first three bounds, for autonomous systems
with a globally Lipschitz field** (MLS's standing assumption, p. 179), and the resulting
equivalence (`exponentiallyStable_iff_exists_quadratic_lyapunov`). From exponential stability with
constants `m, α, ε` the function
`V(x) = ∫₀^T ‖φ(τ, x)‖² dτ`, `T = max 1 (log(2m²)/(2α))`,
built from the solution flow `φ` (`exists_hasFlow_of_lipschitzWith`), satisfies, for `‖x‖ ≤ ε`,
`T e^{−2KT} ‖x‖² ≤ V(x) ≤ T m² ‖x‖²` (the lower bound by Grönwall's inequality backwards in time,
for every `x`, with `K` the Lipschitz constant) and `V̇(x) = ‖φ(T, x)‖² − ‖x‖² ≤ −½ ‖x‖²` along
every solution; `V` is continuous (`exists_quadratic_lyapunov_of_exponentiallyStable`).

**Not formalized: the fourth bound `‖∂V/∂x‖ ≤ α₄‖x‖`.** It needs `V` differentiable in `x`, i.e.
differentiable dependence of solutions on initial conditions, which the pinned Mathlib does not
provide (E019's assessment; `Mathlib/Analysis/ODE` has no `fderiv` of a flow). Time-varying
systems are not covered (the flow interface is autonomous). The sufficiency direction (all three
bounds, local form) is E019's `exponentiallyStable_of_quadratic_lyapunov_local`; the fourth bound
is not needed there.

Conventions: as in `RoboLean.Stability` (system `fun _ => F`, solutions `IsSolution`, initial
times `t₀ ≥ 0`, `V̇` as the derivative along solutions `HasDerivAlongSolutions`); `E` is a real
Banach space and `‖·‖` its norm.
-/

noncomputable section

open Set Filter Topology intervalIntegral

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Grönwall's inequality backwards in time** (used for the lower bound in the converse of MLS
Theorem 4.5, p. 183): if `F` is `K`-Lipschitz with `F(0) = 0` and `φ` is a flow of `ẋ = F(x)`, then
`‖x‖ ≤ e^{Kτ} ‖φ(τ, x)‖` for every `x` and `τ ≥ 0`. -/
theorem HasFlow.norm_le_exp_mul_norm {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ) {K : NNReal}
    (hF : LipschitzWith K F) (hF0 : F 0 = 0) (x : E) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖x‖ ≤ Real.exp (K * τ) * ‖φ τ x‖ := by
  have hcont : ContinuousOn (fun s => φ (τ - s) x) (Icc 0 τ) := by
    refine (h.continuousOn_trajectory x).comp (continuous_const.sub continuous_id).continuousOn ?_
    intro s hs
    simp only [mem_Ici]
    linarith [hs.2]
  have hder : ∀ s ∈ Ico 0 τ, HasDerivWithinAt (fun s => φ (τ - s) x) (-F (φ (τ - s) x)) (Ici s)
      s := by
    intro s hs
    have hpos : 0 < τ - s := by linarith [hs.2]
    have h1 := (h.isSolution x).2 (τ - s) hpos
    have h2 : HasDerivAt (fun s => τ - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub τ
    have h3 := h1.scomp s h2
    simpa [Function.comp_def] using h3.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico 0 τ, ‖-F (φ (τ - s) x)‖ ≤ K * ‖φ (τ - s) x‖ + 0 := by
    intro s _
    rw [norm_neg, add_zero]
    have := hF.norm_sub_le (φ (τ - s) x) 0
    rwa [hF0, sub_zero, sub_zero] at this
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder le_rfl hbound τ
    ⟨hτ, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero, sub_self, h.map_zero] at key
  linarith [mul_comm (‖φ 0 x‖) (Real.exp (K * τ))]

/-- **The converse of MLS Theorem 4.5 (p. 183), first three bounds, for autonomous systems with a
globally Lipschitz field.** On a real Banach space, if `F` is Lipschitz and the origin of
`ẋ = F(x)` is exponentially stable (Definition 4.3), there are a continuous `V`, its derivative
`V̇` along every solution (on the whole space), and constants `a₁, a₂, a₃, ε > 0` with
`a₁‖x‖² ≤ V(x) ≤ a₂‖x‖²` and `V̇(x) ≤ −a₃‖x‖²` for `‖x‖ ≤ ε`. The fourth bound of the theorem,
`‖∂V/∂x‖ ≤ α₄‖x‖`, is not proved (module docstring). -/
theorem exists_quadratic_lyapunov_of_exponentiallyStable [CompleteSpace E] {F : E → E}
    {K : NNReal} (hF : LipschitzWith K F) (hexp : ExponentiallyStable (fun _ => F) 0) :
    ∃ V Vdot : E → ℝ, ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ ε > 0, Continuous V ∧
      (∀ y : E, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V y ∧ V y ≤ a₂ * ‖y‖ ^ 2) ∧
      HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) univ ∧
      ∀ y : E, ‖y‖ ≤ ε → Vdot y ≤ -(a₃ * ‖y‖ ^ 2) := by
  obtain ⟨φ, hφ⟩ := exists_hasFlow_of_lipschitzWith hF
  obtain ⟨m, hm, α, hα, ε, hε, hexp⟩ := hexp
  -- decay of the flow near the origin
  have hdecay : ∀ y : E, ‖y‖ ≤ ε → ∀ τ, 0 ≤ τ → ‖φ τ y‖ ≤ m * Real.exp (-α * τ) * ‖y‖ := by
    intro y hy τ hτ
    have := hexp 0 le_rfl (fun t => φ t y) (hφ.isSolution y) (by simpa [hφ.map_zero] using hy) τ hτ
    simpa [hφ.map_zero] using this
  -- the origin is a rest point
  have hF0 : F 0 = 0 := by
    have hz : ∀ τ, 0 ≤ τ → φ τ 0 = 0 := fun τ hτ => by
      have := hdecay 0 (by simp [hε.le]) τ hτ
      simpa using this
    have hd := (hφ.isSolution 0).2 1 one_pos
    have hc : HasDerivAt (fun t => φ t (0 : E)) 0 1 := by
      refine (hasDerivAt_const (1 : ℝ) (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds one_pos] with t ht
      exact hz t (le_of_lt ht)
    have := hd.unique hc
    simp only [hz 1 zero_le_one] at this
    exact this
  set T : ℝ := max 1 (Real.log (2 * m ^ 2) / (2 * α)) with hTdef
  have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT2 : m ^ 2 * Real.exp (-(2 * α) * T) ≤ 1 / 2 := by
    have h1 : Real.log (2 * m ^ 2) ≤ 2 * α * T := by
      have := le_max_right 1 (Real.log (2 * m ^ 2) / (2 * α))
      rw [← hTdef, div_le_iff₀ (by positivity)] at this
      linarith
    have h2 : Real.exp (-(2 * α) * T) ≤ Real.exp (-Real.log (2 * m ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity)] at h2
    calc m ^ 2 * Real.exp (-(2 * α) * T) ≤ m ^ 2 * (2 * m ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg m)
      _ = 1 / 2 := by field_simp
  -- the trajectories are continuous on `[0, ∞)`
  have htraj : ∀ y, ContinuousOn (fun τ => ‖φ τ y‖ ^ 2) (Ici 0) := fun y =>
    (continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn
      (hφ.continuousOn_trajectory y))
  have hint : ∀ y {a b : ℝ}, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun τ => ‖φ τ y‖ ^ 2) MeasureTheory.volume a b := by
    intro y a b ha hb
    refine ((htraj y).mono ?_).intervalIntegrable
    intro τ hτ
    exact le_trans (le_min ha hb) hτ.1
  set V : E → ℝ := fun y => ∫ τ in (0 : ℝ)..T, ‖φ τ y‖ ^ 2 with hVdef
  set Vdot : E → ℝ := fun y => ‖φ T y‖ ^ 2 - ‖y‖ ^ 2 with hVdotdef
  refine ⟨V, Vdot, T * Real.exp (-(2 * K * T)), by positivity, T * m ^ 2, by positivity, 1 / 2,
    by norm_num, ε, hε, ?_, fun y hy => ⟨?_, ?_⟩, ?_, fun y hy => ?_⟩
  · -- continuity of `V`: the flow is jointly continuous on `E × [0, T]`
    have hlip : ∀ τ ∈ Icc (0 : ℝ) T, LipschitzWith (Real.toNNReal (Real.exp (K * T))) (φ τ) := by
      intro τ hτ
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have h1 := (hφ.isSolution x).dist_le_of_lipschitzWith hF (hφ.isSolution y) hτ.1
      rw [hφ.map_zero, hφ.map_zero, sub_zero] at h1
      rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
      calc dist (φ τ x) (φ τ y) ≤ dist x y * Real.exp (K * τ) := h1
        _ ≤ dist x y * Real.exp (K * T) := by gcongr; exact hτ.2
        _ = Real.exp (K * T) * dist x y := mul_comm _ _
    have hjoint : ContinuousOn (fun p : E × ℝ => φ p.2 p.1) (univ ×ˢ Icc 0 T) :=
      continuousOn_prod_of_continuousOn_lipschitzOnWith (fun p : E × ℝ => φ p.2 p.1)
        (Real.toNNReal (Real.exp (K * T)))
        (fun x _ => (hφ.continuousOn_trajectory x).mono fun τ hτ => hτ.1)
        (fun τ hτ => (hlip τ hτ).lipschitzOnWith)
    set ψ : E × ℝ → E := fun p => φ (projIcc 0 T hT.le p.2) p.1 with hψdef
    have hψ : Continuous ψ := by
      have hg : Continuous fun p : E × ℝ => (p.1, (projIcc 0 T hT.le p.2 : ℝ)) :=
        continuous_fst.prodMk (continuous_subtype_val.comp
          ((continuous_projIcc (h := hT.le)).comp continuous_snd))
      exact hjoint.comp_continuous hg fun p => ⟨mem_univ _, Subtype.mem _⟩
    have hVψ : V = fun y => ∫ τ in (0 : ℝ)..T, ‖ψ (y, τ)‖ ^ 2 := by
      funext y
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le hT.le] at hτ
      simp only [hψdef, projIcc_of_mem hT.le hτ]
    have hc : Continuous (Function.uncurry fun (y : E) (τ : ℝ) => ‖ψ (y, τ)‖ ^ 2) :=
      ((continuous_norm.comp hψ).pow 2).congr fun p => rfl
    rw [hVψ]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 T
  · -- lower bound
    have hlow : ∀ τ ∈ Icc (0 : ℝ) T, Real.exp (-(2 * K * T)) * ‖y‖ ^ 2 ≤ ‖φ τ y‖ ^ 2 := by
      intro τ hτ
      have h1 := hφ.norm_le_exp_mul_norm hF hF0 y hτ.1
      have h2 : Real.exp (K * τ) ≤ Real.exp (K * T) := Real.exp_le_exp.mpr (by gcongr; exact hτ.2)
      have h3 : ‖y‖ ≤ Real.exp (K * T) * ‖φ τ y‖ :=
        h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      have h4 : ‖y‖ ^ 2 ≤ Real.exp (K * T) ^ 2 * ‖φ τ y‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg y) h3 2
        rwa [mul_pow] at this
      have h5 : Real.exp (-(2 * K * T)) * Real.exp (K * T) ^ 2 = 1 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        simp only [Nat.cast_ofNat]
        ring_nf
        exact Real.exp_zero
      calc Real.exp (-(2 * K * T)) * ‖y‖ ^ 2 ≤
            Real.exp (-(2 * K * T)) * (Real.exp (K * T) ^ 2 * ‖φ τ y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
        _ = ‖φ τ y‖ ^ 2 := by rw [← mul_assoc, h5, one_mul]
    have := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const
      (hint y le_rfl hT.le) hlow
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    calc T * Real.exp (-(2 * K * T)) * ‖y‖ ^ 2 = T * (Real.exp (-(2 * K * T)) * ‖y‖ ^ 2) := by
          ring
      _ ≤ V y := this
  · -- upper bound
    have hup : ∀ τ ∈ Icc (0 : ℝ) T, ‖φ τ y‖ ^ 2 ≤ m ^ 2 * ‖y‖ ^ 2 := by
      intro τ hτ
      have h1 := hdecay y hy τ hτ.1
      have h2 : Real.exp (-α * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
      have h3 : ‖φ τ y‖ ≤ m * ‖y‖ := by
        calc ‖φ τ y‖ ≤ m * Real.exp (-α * τ) * ‖y‖ := h1
          _ ≤ m * 1 * ‖y‖ := by gcongr
          _ = m * ‖y‖ := by ring
      have := pow_le_pow_left₀ (norm_nonneg _) h3 2
      rwa [mul_pow] at this
    have := intervalIntegral.integral_mono_on hT.le (hint y le_rfl hT.le) intervalIntegrable_const
      hup
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    calc V y ≤ T * (m ^ 2 * ‖y‖ ^ 2) := this
      _ = T * m ^ 2 * ‖y‖ ^ 2 := by ring
  · -- the derivative along solutions
    intro t₀ ht₀ x hx t ht _
    set g : ℝ → ℝ := fun σ => ‖φ σ (x t₀)‖ ^ 2 with hgdef
    have hgc : ContinuousOn g (Ioi 0) := (htraj (x t₀)).mono Ioi_subset_Ici_self
    have hG : ∀ r, t₀ < r → V (x r) =
        (∫ σ in (0 : ℝ)..(r - t₀ + T), g σ) - ∫ σ in (0 : ℝ)..(r - t₀), g σ := by
      intro r hr
      have hxr : x r = φ (r - t₀) (x t₀) := hφ.eq_of_isSolution t₀ ht₀ x hx r hr.le
      have h1 : V (x r) = ∫ τ in (0 : ℝ)..T, g (τ + (r - t₀)) := by
        simp only [hVdef, hxr, hgdef]
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le hT.le] at hτ
        rw [hφ.map_add (by linarith) hτ.1]
      rw [h1, intervalIntegral.integral_comp_add_right, zero_add,
        intervalIntegral.integral_interval_sub_left (hint (x t₀) le_rfl (by linarith))
          (hint (x t₀) le_rfl (by linarith)), add_comm T]
    have hderiv : ∀ c : ℝ, 0 ≤ c → HasDerivAt (fun r => ∫ σ in (0 : ℝ)..(r - t₀ + c), g σ)
        (g (t - t₀ + c)) t := by
      intro c hc
      have hb : 0 < t - t₀ + c := by linarith
      have h1 := intervalIntegral.integral_hasDerivAt_right (hint (x t₀) le_rfl hb.le)
        (hgc.stronglyMeasurableAtFilter isOpen_Ioi _ hb)
        (hgc.continuousAt (Ioi_mem_nhds hb))
      have h2 : HasDerivAt (fun r : ℝ => r - t₀ + c) 1 t := by
        simpa using ((hasDerivAt_id t).sub_const t₀).add_const c
      have h3 := h1.comp t h2
      rw [mul_one] at h3
      exact h3
    have hd := (hderiv T hT.le).sub (hderiv 0 le_rfl)
    simp only [add_zero] at hd
    have hval : g (t - t₀ + T) - g (t - t₀) = Vdot (x t) := by
      have hxt : x t = φ (t - t₀) (x t₀) := hφ.eq_of_isSolution t₀ ht₀ x hx t ht.le
      simp only [hgdef, hVdotdef, hxt]
      rw [add_comm, hφ.map_add (by linarith) hT.le]
    rw [hval] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with r hr
    simpa using hG r hr
  · -- the decrease bound
    have h1 := hdecay y hy T hT.le
    have h2 : ‖φ T y‖ ^ 2 ≤ m ^ 2 * Real.exp (-(2 * α) * T) * ‖y‖ ^ 2 := by
      have e : Real.exp (-α * T) ^ 2 = Real.exp (-(2 * α) * T) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rwa [mul_pow, mul_pow, e] at this
    have h3 : m ^ 2 * Real.exp (-(2 * α) * T) * ‖y‖ ^ 2 ≤ 1 / 2 * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hT2 (sq_nonneg _)
    simp only [hVdotdef]
    linarith

/-- **MLS Theorem 4.5 (p. 183) with its first three bounds, for autonomous systems with a globally
Lipschitz field (MLS p. 179).** On a real Banach space, with `F` Lipschitz, the origin of
`ẋ = F(x)` is exponentially stable (Definition 4.3) if and only if there are a continuous
time-invariant `V`, its derivative `V̇` along the solutions, and constants `a₁, a₂, a₃, ε > 0`
with `a₁‖x‖² ≤ V(x) ≤ a₂‖x‖²` and `V̇(x) ≤ −a₃‖x‖²` for `‖x‖ ≤ ε`. "If": E019's local sufficiency
(`exponentiallyStable_of_quadratic_lyapunov_local`); "only if":
`exists_quadratic_lyapunov_of_exponentiallyStable`. The fourth bound `‖∂V/∂x‖ ≤ α₄‖x‖` of the
printed theorem is not part of this statement (module docstring). -/
theorem exponentiallyStable_iff_exists_quadratic_lyapunov [CompleteSpace E] {F : E → E}
    {K : NNReal} (hF : LipschitzWith K F) :
    ExponentiallyStable (fun _ => F) 0 ↔
      ∃ V Vdot : E → ℝ, ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ ε > 0, Continuous V ∧
        (∀ y : E, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V y ∧ V y ≤ a₂ * ‖y‖ ^ 2) ∧
        HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) univ ∧
        ∀ y : E, ‖y‖ ≤ ε → Vdot y ≤ -(a₃ * ‖y‖ ^ 2) := by
  refine ⟨exists_quadratic_lyapunov_of_exponentiallyStable hF, ?_⟩
  rintro ⟨V, Vdot, a₁, ha₁, a₂, ha₂, a₃, ha₃, ε, hε, hV, hb, hVdot, hdec⟩
  exact exponentiallyStable_of_quadratic_lyapunov_local (V := fun _ => V) (Vdot := fun _ => Vdot)
    ha₁ ha₂ ha₃ hε (hV.comp continuous_snd).continuousOn (fun _ _ y hy => (hb y hy).1)
    (fun _ _ y hy => (hb y hy).2) (hVdot.mono (subset_univ _)) (fun _ _ y hy => hdec y hy)

end Stability
end RoboLean
