import RoboLean.Control.FlowDerivative
import RoboLean.Control.LinearizationTimeVarying
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The converse of the exponential stability theorem with all four bounds (MLS Theorem 4.5, p. 183)

**What MLS states.** Theorem 4.5 (p. 183): "`x* = 0` is an exponentially stable equilibrium point of
`ẋ = f(x, t)` if and only if there exists an `ε > 0` and a function `V(x, t)` which satisfies
`α₁‖x‖² ≤ V(x, t) ≤ α₂‖x‖²`, `V̇|_{ẋ = f(x, t)} ≤ −α₃‖x‖²`, `‖∂V/∂x (x, t)‖ ≤ α₄‖x‖` for some
positive constants `α₁, α₂, α₃, α₄`, and `‖x‖ ≤ ε`." MLS gives no proof; its standing assumption (p.
179) is that `f(x, t)` is Lipschitz in `x`, uniformly in `t`.

**Formalized here**, on `ℝⁿ` with the sup norm, for time-varying (and so for autonomous) fields
`f(t, x)` that are `K`-Lipschitz in `x` for `t ≥ 0` and have a solution flow differentiable in the
initial state with the variational equation (`IsDifferentiableFlow`, a hypothesis: differentiable
dependence on initial conditions is not in the pinned Mathlib):

* the "only if" direction with all four bounds
  (`exists_lyapunov_of_exponentiallyStable_of_isDifferentiableFlow`): from exponential stability
  with constants `m, α, ε`, the function `V(t, x) = ∫₀^T ‖φ(t + u, t, x)‖₂² du` (`flowLyapunov`, the
  Euclidean norm), `T = 1 + log(2nm² + 1)/(2α)`, satisfies for `‖x‖ ≤ ε/2` and `t ≥ 0`:
  `T e^{−2KT} ‖x‖² ≤ V ≤ (Tnm² + 1) ‖x‖²`, `V̇ = ‖φ(t + T, t, x)‖₂² − ‖x‖₂² ≤ −½ ‖x‖²` along every
  solution (`flowLyapunovRate`), and `x ↦ V(t, x)` has a Fréchet derivative with
  `‖∂V/∂x‖ ≤ (2Tnm e^{KT} + 1) ‖x‖`; `V` is continuous on `[0, ∞) × ℝⁿ`;
* the equivalence (`exponentiallyStable_iff_exists_lyapunov_of_isDifferentiableFlow`), the "if"
  direction being the local form of Theorem 4.5 (`exponentiallyStable_of_quadratic_lyapunov_local`);
* the linear time-varying case with every hypothesis discharged: for `ż = A(t)z` with a
  state-transition matrix and `A` bounded on `[0, ∞)`, the same equivalence
  (`IsStateTransition.exponentiallyStable_iff_exists_lyapunov`).

**Conventions.** Time first (`f t x` for MLS's `f(x, t)`, `V t x` for `V(x, t)`); `V̇` is the
derivative along solutions (`HasDerivAlongSolutions`); `∂V/∂x` is the Fréchet derivative of
`x ↦ V(t, x)` and `‖∂V/∂x‖` its operator norm for the sup norm on `ℝⁿ`; the quadratic bounds use the
sup norm `‖x‖`, the construction the dot product (`‖x‖² ≤ x ⬝ x ≤ n‖x‖²`), so that `V` is
differentiable. The bounds are stated on `‖x‖ ≤ ε/2` for the `ε` of Definition 4.3, so that the
derivative is taken inside the ball where the exponential estimate holds.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean
namespace Stability

variable {n : ℕ}

/-- **The converse Lyapunov function of MLS Theorem 4.5 (p. 183):** for a flow `φ` (`φ t s x` the
state at time `t` of the solution from `x` at time `s`) and a horizon `T`,
`V(t, x) = ∫₀^T ‖φ(t + u, t, x)‖₂² du = ∫_t^{t+T} ‖s(τ, x, t)‖₂² dτ`, with the Euclidean dot product
on `ℝⁿ`. Time first. -/
def flowLyapunov (φ : ℝ → ℝ → (Fin n → ℝ) → Fin n → ℝ) (T t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..T, φ (t + u) t x ⬝ᵥ φ (t + u) t x

/-- **The derivative of the converse Lyapunov function along solutions (MLS Theorem 4.5, p. 183):**
`V̇(t, x) = ‖φ(t + T, t, x)‖₂² − ‖x‖₂²` (Euclidean dot product). Time first. -/
def flowLyapunovRate (φ : ℝ → ℝ → (Fin n → ℝ) → Fin n → ℝ) (T t : ℝ) (x : Fin n → ℝ) : ℝ :=
  φ (t + T) t x ⬝ᵥ φ (t + T) t x - x ⬝ᵥ x

/-- The linear functional `h ↦ a ⬝ h` on `ℝⁿ`. -/
private def dotL (a : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

/-- `dotL a h = a ⬝ h`. -/
private theorem dotL_apply (a h : Fin n → ℝ) : dotL a h = a ⬝ᵥ h := by
  simp [dotL, dotProduct]

/-- `‖h ↦ a ⬝ h‖ ≤ n ‖a‖` for the sup norm. -/
private theorem norm_dotL_le (a : Fin n → ℝ) : ‖dotL a‖ ≤ n * ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => by
    rw [dotL_apply, Real.norm_eq_abs]
    exact Control.abs_dotProduct_le a h

/-- `a ↦ (h ↦ a ⬝ h)` is continuous. -/
private theorem continuous_dotL : Continuous (dotL (n := n)) := by
  unfold dotL
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- The derivative of `z ↦ g(z) ⬝ g(z)` is `2 g(y) ⬝ G(·)`. -/
private theorem hasFDerivAt_dotProduct_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Fin n → ℝ} {G : E →L[ℝ] (Fin n → ℝ)} {y : E} (hg : HasFDerivAt g G y) :
    HasFDerivAt (fun z => g z ⬝ᵥ g z) ((2 : ℝ) • (dotL (g y)).comp G) y := by
  have hgi : ∀ i, HasFDerivAt (fun z => g z i) ((ContinuousLinearMap.proj i).comp G) y :=
    fun i => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt).comp y hg
  have hs := HasFDerivAt.sum (u := Finset.univ) fun i _ => (hgi i).mul (hgi i)
  convert hs using 1
  · funext z
    simp [dotProduct, Finset.sum_apply]
  · ext v
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, dotL_apply,
      _root_.sum_apply, _root_.add_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **The converse of MLS Theorem 4.5 (p. 183) with all four bounds, for time-varying fields with a
differentiable flow.** On `ℝⁿ` (sup norm), let `f(t, ·)` be `K`-Lipschitz for `t ≥ 0` (MLS p. 179)
and let `φ` be a solution flow of `ẋ = f(x, t)` differentiable in the initial state with the
variational equation (`IsDifferentiableFlow`). If the origin is exponentially stable (Definition
4.3), there are `V`, its derivative `V̇` along every solution, a Fréchet derivative `∂V/∂x` and
constants `a₁, a₂, a₃, a₄, ε > 0` with `V` continuous on `[0, ∞) × ℝⁿ` and, for `t ≥ 0` and
`‖x‖ ≤ ε`: `a₁‖x‖² ≤ V(t, x) ≤ a₂‖x‖²`, `V̇(t, x) ≤ −a₃‖x‖²`, `x ↦ V(t, x)` has the derivative
`∂V/∂x (t, x)` at `x`, and `‖∂V/∂x (t, x)‖ ≤ a₄‖x‖` (operator norm). -/
theorem exists_lyapunov_of_exponentiallyStable_of_isDifferentiableFlow
    {f : ℝ → (Fin n → ℝ) → Fin n → ℝ} {Df : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {φ : ℝ → ℝ → (Fin n → ℝ) → Fin n → ℝ}
    {D : ℝ → ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hφ : IsDifferentiableFlow f Df φ D) {K : NNReal} (hf : ∀ t, 0 ≤ t → LipschitzWith K (f t))
    (hexp : ExponentiallyStable f 0) :
    ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
      ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
        ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
        HasDerivAlongSolutions f V Vdot univ ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
        ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ := by
  obtain ⟨m, hm, α, hα, ε, hε, hexp⟩ := hexp
  -- the exponential estimate along the flow
  have hdecay : ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ∀ u, 0 ≤ u →
      ‖φ (t + u) t y‖ ≤ m * Real.exp (-α * u) * ‖y‖ := by
    intro t ht y hy u hu
    have := hexp t ht (fun τ => φ τ t y) (hφ.isSolution t ht y)
      (by simpa [hφ.self_eq t ht] using hy) (t + u) (by linarith)
    simpa [hφ.self_eq t ht] using this
  -- the origin is a rest point, so `‖f(τ, y)‖ ≤ K ‖y‖` for `τ > 0`
  have hzero : ∀ s, 0 ≤ s → ∀ τ, s ≤ τ → φ τ s 0 = 0 := by
    intro s hs τ hτ
    have := hexp s hs (fun τ => φ τ s 0) (hφ.isSolution s hs 0)
      (by simp [hφ.self_eq s hs, hε.le]) τ hτ
    simpa [hφ.self_eq s hs] using this
  have hf0 : ∀ τ, 0 < τ → f τ 0 = 0 := by
    intro τ hτ
    have hd := (hφ.isSolution 0 le_rfl 0).2 τ hτ
    have hc : HasDerivAt (fun r => φ r 0 (0 : Fin n → ℝ)) 0 τ := by
      refine (hasDerivAt_const τ (0 : Fin n → ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hτ] with r hr
      exact hzero 0 le_rfl r hr.le
    have := hd.unique hc
    simp only [hzero 0 le_rfl τ hτ.le] at this
    exact this
  have hlin : ∀ τ, 0 < τ → ∀ y, ‖f τ y‖ ≤ K * ‖y‖ := by
    intro τ hτ y
    have := (hf τ hτ.le).norm_sub_le y 0
    rwa [hf0 τ hτ, sub_zero, sub_zero] at this
  -- the horizon `T` with `n (m e^{−αT})² ≤ 1/2`
  set Dn : ℝ := 2 * n * m ^ 2 + 1 with hDndef
  have hDn : 0 < Dn := by positivity
  set T : ℝ := 1 + Real.log Dn / (2 * α) with hTdef
  have hT : 0 < T := by
    have : 0 ≤ Real.log Dn := Real.log_nonneg (by simp only [hDndef]; nlinarith [sq_nonneg m])
    positivity
  have hsmall : (n : ℝ) * (m * Real.exp (-(α * T))) ^ 2 ≤ 1 / 2 := by
    have h1 : Real.exp (-(α * T)) ^ 2 = Real.exp (-(2 * α)) / Dn := by
      have harg : -(α * T) + -(α * T) = -(2 * α) + -Real.log Dn := by
        rw [hTdef]
        field_simp
        ring
      rw [sq, ← Real.exp_add, harg, Real.exp_add, Real.exp_neg (Real.log Dn), Real.exp_log hDn,
        div_eq_mul_inv]
    have h2 : Real.exp (-(2 * α)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hCe : m ^ 2 * Real.exp (-(2 * α)) ≤ m ^ 2 := by
      nlinarith [sq_nonneg m, Real.exp_pos (-(2 * α))]
    rw [mul_pow, h1]
    calc (n : ℝ) * (m ^ 2 * (Real.exp (-(2 * α)) / Dn))
        = n * (m ^ 2 * Real.exp (-(2 * α))) / Dn := by ring
      _ ≤ n * m ^ 2 / Dn :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCe (Nat.cast_nonneg n)) hDn.le
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hDn, hDndef]
        linarith
  -- continuity of the integrands
  have htraj : ∀ t, 0 ≤ t → ∀ y, ContinuousOn (fun u => φ (t + u) t y) (Ici 0) := by
    intro t ht y
    refine (hφ.continuousOn_trajectory ht y).comp (continuous_const.add continuous_id).continuousOn
      fun u hu => ?_
    simp only [mem_Ici] at hu ⊢
    linarith
  have hsq : ∀ t, 0 ≤ t → ∀ y,
      ContinuousOn (fun u => φ (t + u) t y ⬝ᵥ φ (t + u) t y) (Ici 0) := fun t ht y =>
    (continuous_id.dotProduct continuous_id).comp_continuousOn (htraj t ht y)
  have hsub : uIcc 0 T ⊆ Ici (0 : ℝ) := by
    rw [uIcc_of_le hT.le]
    exact Icc_subset_Ici_self
  have hint : ∀ t, 0 ≤ t → ∀ y, IntervalIntegrable
      (fun u => φ (t + u) t y ⬝ᵥ φ (t + u) t y) MeasureTheory.volume 0 T := fun t ht y =>
    ((hsq t ht y).mono hsub).intervalIntegrable
  refine ⟨flowLyapunov φ T, flowLyapunovRate φ T,
    fun t y => ∫ u in (0 : ℝ)..T, (2 : ℝ) • (dotL (φ (t + u) t y)).comp (D (t + u) t y),
    T * Real.exp (-(2 * (K * T))), by positivity, T * (n * m ^ 2) + 1, by positivity, 1 / 2,
    by norm_num, 2 * (T * (n * (m * Real.exp (K * T)))) + 1, by positivity, ε / 2, by positivity,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of `V` on `[0, ∞) × ℝⁿ`, from the continuity of the flow
    set G : (ℝ × (Fin n → ℝ)) → ℝ → ℝ := fun p u =>
      φ (max p.1 0 + (projIcc 0 T hT.le u : ℝ)) (max p.1 0) p.2 ⬝ᵥ
        φ (max p.1 0 + (projIcc 0 T hT.le u : ℝ)) (max p.1 0) p.2 with hGdef
    have hin : Continuous fun q : (ℝ × (Fin n → ℝ)) × ℝ =>
        (max q.1.1 0 + (projIcc 0 T hT.le q.2 : ℝ), max q.1.1 0, q.1.2) := by
      have h1 : Continuous fun q : (ℝ × (Fin n → ℝ)) × ℝ => max q.1.1 0 :=
        (continuous_fst.comp continuous_fst).max continuous_const
      have h2 : Continuous fun q : (ℝ × (Fin n → ℝ)) × ℝ => (projIcc 0 T hT.le q.2 : ℝ) :=
        continuous_subtype_val.comp ((continuous_projIcc (h := hT.le)).comp continuous_snd)
      exact (h1.add h2).prodMk (h1.prodMk (continuous_snd.comp continuous_fst))
    have hw := hφ.continuousOn.comp_continuous hin fun q =>
      ⟨le_max_right _ _, le_add_of_nonneg_right (projIcc 0 T hT.le q.2).2.1⟩
    have hGc : Continuous (Function.uncurry G) :=
      ((continuous_id.dotProduct continuous_id).comp hw).congr fun q => rfl
    refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) hGc 0 T).continuousOn.congr fun p hp => ?_
    have hp0 : 0 ≤ p.1 := hp.1
    simp only [flowLyapunov]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hT.le] at hu
    simp only [hGdef, max_eq_left hp0, projIcc_of_mem hT.le hu]
  · -- the quadratic bounds
    intro t ht y hy
    have hyε : ‖y‖ ≤ ε := hy.trans (by linarith)
    constructor
    · have hlow : ∀ u ∈ Icc (0 : ℝ) T,
          Real.exp (-(2 * (K * T))) * ‖y‖ ^ 2 ≤ φ (t + u) t y ⬝ᵥ φ (t + u) t y := by
        intro u hu
        have h1 := hφ.norm_le_exp_mul_norm hlin ht (by linarith [hu.1] : t ≤ t + u) y
        rw [add_sub_cancel_left] at h1
        have h2 : Real.exp (K * u) ≤ Real.exp (K * T) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 K.2)
        have h3 : ‖y‖ ≤ Real.exp (K * T) * ‖φ (t + u) t y‖ :=
          h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
        have h4 : ‖y‖ ^ 2 ≤ Real.exp (K * T) ^ 2 * ‖φ (t + u) t y‖ ^ 2 := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg y) h3 2
        have h5 : Real.exp (-(2 * (K * T))) * Real.exp (K * T) ^ 2 = 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          simp only [Nat.cast_ofNat]
          ring_nf
          exact Real.exp_zero
        calc Real.exp (-(2 * (K * T))) * ‖y‖ ^ 2
            ≤ Real.exp (-(2 * (K * T))) * (Real.exp (K * T) ^ 2 * ‖φ (t + u) t y‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
          _ = ‖φ (t + u) t y‖ ^ 2 := by rw [← mul_assoc, h5, one_mul]
          _ ≤ _ := Control.sq_norm_le_dotProduct_self _
      have := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const (hint t ht y) hlow
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
      calc T * Real.exp (-(2 * (K * T))) * ‖y‖ ^ 2
          = T * (Real.exp (-(2 * (K * T))) * ‖y‖ ^ 2) := by ring
        _ ≤ flowLyapunov φ T t y := this
    · have hup : ∀ u ∈ Icc (0 : ℝ) T,
          φ (t + u) t y ⬝ᵥ φ (t + u) t y ≤ n * m ^ 2 * ‖y‖ ^ 2 := by
        intro u hu
        have h1 := hdecay t ht y hyε u hu.1
        have h2 : Real.exp (-α * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
        have h3 : ‖φ (t + u) t y‖ ≤ m * ‖y‖ :=
          calc ‖φ (t + u) t y‖ ≤ m * Real.exp (-α * u) * ‖y‖ := h1
            _ ≤ m * 1 * ‖y‖ := by gcongr
            _ = m * ‖y‖ := by ring
        calc φ (t + u) t y ⬝ᵥ φ (t + u) t y ≤ n * ‖φ (t + u) t y‖ ^ 2 :=
              Control.dotProduct_self_le_mul_sq_norm _
          _ ≤ n * (m * ‖y‖) ^ 2 := by gcongr
          _ = n * m ^ 2 * ‖y‖ ^ 2 := by ring
      have := intervalIntegral.integral_mono_on hT.le (hint t ht y) intervalIntegrable_const hup
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
      calc flowLyapunov φ T t y ≤ T * (n * m ^ 2 * ‖y‖ ^ 2) := this
        _ ≤ (T * (n * m ^ 2) + 1) * ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
  · -- the derivative along solutions, by the composition law and the fundamental theorem
    intro t₀ ht₀ x hx t ht _
    set g : ℝ → ℝ := fun σ => φ σ t₀ (x t₀) ⬝ᵥ φ σ t₀ (x t₀) with hgdef
    have hgc : ContinuousOn g (Ici t₀) :=
      (continuous_id.dotProduct continuous_id).comp_continuousOn
        (hφ.continuousOn_trajectory ht₀ (x t₀))
    have hgi : ∀ b, t₀ ≤ b → IntervalIntegrable g MeasureTheory.volume t₀ b := fun b hb =>
      (hgc.mono (by rw [uIcc_of_le hb]; exact Icc_subset_Ici_self)).intervalIntegrable
    have hxr : ∀ r, t₀ ≤ r → x r = φ r t₀ (x t₀) := fun r hr =>
      hφ.eq_of_isSolution t₀ ht₀ x hx r hr
    have hG : ∀ r, t₀ < r → flowLyapunov φ T r (x r) =
        (∫ σ in t₀..(r + T), g σ) - ∫ σ in t₀..r, g σ := by
      intro r hr
      have h1 : flowLyapunov φ T r (x r) = ∫ u in (0 : ℝ)..T, g (r + u) := by
        simp only [flowLyapunov, hgdef, hxr r hr.le]
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [uIcc_of_le hT.le] at hu
        rw [hφ.eq_comp ht₀ hr.le (by linarith [hu.1] : r ≤ r + u)]
      rw [h1, intervalIntegral.integral_comp_add_left, add_zero,
        intervalIntegral.integral_interval_sub_left (hgi _ (by linarith)) (hgi _ hr.le)]
    have hderiv : ∀ c : ℝ, 0 ≤ c → HasDerivAt (fun r => ∫ σ in t₀..(r + c), g σ) (g (t + c)) t := by
      intro c hc
      have hb : t₀ < t + c := by linarith
      have h1 := intervalIntegral.integral_hasDerivAt_right (hgi _ hb.le)
        ((hgc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi _ hb)
        (hgc.continuousAt (Ici_mem_nhds hb))
      have h2 : HasDerivAt (fun r : ℝ => r + c) 1 t := by
        simpa using (hasDerivAt_id t).add_const c
      have h3 := h1.comp t h2
      rw [mul_one] at h3
      exact h3
    have hd := (hderiv T hT.le).sub (hderiv 0 le_rfl)
    simp only [add_zero] at hd
    have hval : g (t + T) - g t = flowLyapunovRate φ T t (x t) := by
      simp only [hgdef, flowLyapunovRate, hxr t ht.le]
      rw [hφ.eq_comp ht₀ ht.le (by linarith : t ≤ t + T)]
    rw [hval] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact hG r hr
  · -- the decrease bound
    intro t ht y hy
    have hyε : ‖y‖ ≤ ε := hy.trans (by linarith)
    have h1 := hdecay t ht y hyε T hT.le
    have h3 : φ (t + T) t y ⬝ᵥ φ (t + T) t y ≤ 1 / 2 * ‖y‖ ^ 2 := by
      have hΦy : ‖φ (t + T) t y‖ ≤ m * Real.exp (-(α * T)) * ‖y‖ := by
        simpa [neg_mul] using h1
      calc φ (t + T) t y ⬝ᵥ φ (t + T) t y ≤ n * ‖φ (t + T) t y‖ ^ 2 :=
            Control.dotProduct_self_le_mul_sq_norm _
        _ ≤ n * (m * Real.exp (-(α * T)) * ‖y‖) ^ 2 := by gcongr
        _ = n * (m * Real.exp (-(α * T))) ^ 2 * ‖y‖ ^ 2 := by ring
        _ ≤ 1 / 2 * ‖y‖ ^ 2 := by gcongr
    have h4 := Control.sq_norm_le_dotProduct_self y
    simp only [flowLyapunovRate]
    linarith
  all_goals
    have hDc : ∀ t, 0 ≤ t → ∀ z, ContinuousOn (fun u => D (t + u) t z) (Ici 0) := by
      intro t ht z
      refine (hφ.continuousOn_fderiv ht z).comp (continuous_const.add continuous_id).continuousOn
        fun u hu => ?_
      simp only [mem_Ici] at hu ⊢
      linarith
    have hF'c : ∀ t, 0 ≤ t → ∀ z, ContinuousOn
        (fun u => (2 : ℝ) • (dotL (φ (t + u) t z)).comp (D (t + u) t z)) (Ici 0) := by
      intro t ht z
      have h := (continuous_dotL.comp_continuousOn (htraj t ht z)).clm_comp (hDc t ht z)
      exact h.const_smul (2 : ℝ)
    have hF'b : ∀ t, 0 ≤ t → ∀ z : Fin n → ℝ, ‖z‖ ≤ ε → ∀ u ∈ Icc (0 : ℝ) T,
        ‖(2 : ℝ) • (dotL (φ (t + u) t z)).comp (D (t + u) t z)‖ ≤
          2 * (n * (m * ‖z‖)) * Real.exp (K * T) := by
      intro t ht z hz u hu
      have h1 : ‖φ (t + u) t z‖ ≤ m * ‖z‖ := by
        have := hdecay t ht z hz u hu.1
        have h2 : Real.exp (-α * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
        calc ‖φ (t + u) t z‖ ≤ m * Real.exp (-α * u) * ‖z‖ := this
          _ ≤ m * 1 * ‖z‖ := by gcongr
          _ = m * ‖z‖ := by ring
      have h2 : ‖D (t + u) t z‖ ≤ Real.exp (K * T) := by
        have := hφ.norm_fderiv_le_exp hf ht (by linarith [hu.1] : t ≤ t + u) z
        rw [add_sub_cancel_left] at this
        exact this.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 K.2))
      rw [norm_smul, Real.norm_two]
      have h3 := (ContinuousLinearMap.opNorm_comp_le (dotL (φ (t + u) t z)) (D (t + u) t z)).trans
        (mul_le_mul ((norm_dotL_le _).trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n))) h2
          (norm_nonneg _) (by positivity))
      nlinarith
    have hIoc : uIoc (0 : ℝ) T ⊆ Icc 0 T := by
      rw [uIoc_of_le hT.le]
      exact Ioc_subset_Icc_self
  · -- the derivative in the initial state, by differentiation under the integral sign
    intro t ht y hy
    have hmeas : ∀ᶠ z in 𝓝 y, MeasureTheory.AEStronglyMeasurable
        (fun u => φ (t + u) t z ⬝ᵥ φ (t + u) t z) (MeasureTheory.volume.restrict (uIoc 0 T)) :=
      Eventually.of_forall fun z =>
        ((hsq t ht z).mono (hIoc.trans Icc_subset_Ici_self)).aestronglyMeasurable measurableSet_uIoc
    have hmeas' : MeasureTheory.AEStronglyMeasurable
        (fun u => (2 : ℝ) • (dotL (φ (t + u) t y)).comp (D (t + u) t y))
        (MeasureTheory.volume.restrict (uIoc 0 T)) :=
      ((hF'c t ht y).mono (hIoc.trans Icc_subset_Ici_self)).aestronglyMeasurable measurableSet_uIoc
    have hbd : ∀ᵐ u ∂MeasureTheory.volume, u ∈ uIoc 0 T → ∀ z ∈ Metric.ball y (ε / 2),
        ‖(2 : ℝ) • (dotL (φ (t + u) t z)).comp (D (t + u) t z)‖ ≤
          2 * (n * (m * ε)) * Real.exp (K * T) := by
      refine Eventually.of_forall fun u hu z hz => ?_
      have hzε : ‖z‖ ≤ ε := by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        have := norm_le_norm_add_norm_sub' z y
        linarith
      refine (hF'b t ht z hzε u (hIoc hu)).trans ?_
      gcongr
    have hdiff : ∀ᵐ u ∂MeasureTheory.volume, u ∈ uIoc 0 T → ∀ z ∈ Metric.ball y (ε / 2),
        HasFDerivAt (fun z => φ (t + u) t z ⬝ᵥ φ (t + u) t z)
          ((2 : ℝ) • (dotL (φ (t + u) t z)).comp (D (t + u) t z)) z :=
      Eventually.of_forall fun u hu z _ => hasFDerivAt_dotProduct_self
        (hφ.hasFDerivAt (t + u) t ht (by linarith [(hIoc hu).1]) z)
    exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds y (by positivity)) hmeas (hint t ht y) hmeas' hbd
      intervalIntegrable_const hdiff
  · -- the fourth bound `‖∂V/∂x‖ ≤ a₄ ‖x‖`
    intro t ht y hy
    have hyε : ‖y‖ ≤ ε := hy.trans (by linarith)
    have := intervalIntegral.norm_integral_le_of_norm_le_const fun u hu =>
      hF'b t ht y hyε u (hIoc hu)
    rw [sub_zero, abs_of_pos hT] at this
    refine this.trans ?_
    have hy0 := norm_nonneg y
    have hE := Real.exp_pos (K * T)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hT.le (Nat.cast_nonneg n)) hm.le) hE.le]

/-- **MLS Theorem 4.5 (p. 183) with all four bounds, as an equivalence, for time-varying fields with
a differentiable flow.** On `ℝⁿ` (sup norm), with `f(t, ·)` `K`-Lipschitz for `t ≥ 0` (MLS p. 179)
and a solution flow differentiable in the initial state with the variational equation
(`IsDifferentiableFlow`), the origin of `ẋ = f(x, t)` is exponentially stable (Definition 4.3) if
and only if there are `V`, `V̇`, `∂V/∂x` and constants `a₁, a₂, a₃, a₄, ε > 0` with `V` continuous
on `[0, ∞) × ℝⁿ`, `a₁‖x‖² ≤ V(t, x) ≤ a₂‖x‖²`, `V̇(t, x) ≤ −a₃‖x‖²` along the solutions,
`∂V/∂x (t, x)` the derivative of `x ↦ V(t, x)` and `‖∂V/∂x (t, x)‖ ≤ a₄‖x‖`, for `t ≥ 0` and
`‖x‖ ≤ ε`. "Only if": `exists_lyapunov_of_exponentiallyStable_of_isDifferentiableFlow`; "if": the
local form of Theorem 4.5 (`exponentiallyStable_of_quadratic_lyapunov_local`), which does not use
the fourth bound. -/
theorem exponentiallyStable_iff_exists_lyapunov_of_isDifferentiableFlow
    {f : ℝ → (Fin n → ℝ) → Fin n → ℝ} {Df : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {φ : ℝ → ℝ → (Fin n → ℝ) → Fin n → ℝ}
    {D : ℝ → ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hφ : IsDifferentiableFlow f Df φ D) {K : NNReal} (hf : ∀ t, 0 ≤ t → LipschitzWith K (f t)) :
    ExponentiallyStable f 0 ↔
      ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
        ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
          ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
          HasDerivAlongSolutions f V Vdot univ ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
          ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ := by
  refine ⟨exists_lyapunov_of_exponentiallyStable_of_isDifferentiableFlow hφ hf, ?_⟩
  rintro ⟨V, Vdot, DV, a₁, ha₁, a₂, ha₂, a₃, ha₃, a₄, -, ε, hε, hc, hb, hd, hdec, -, -⟩
  exact exponentiallyStable_of_quadratic_lyapunov_local ha₁ ha₂ ha₃ hε hc
    (fun t ht y hy => (hb t ht y hy).1) (fun t ht y hy => (hb t ht y hy).2)
    (hd.mono (subset_univ _)) hdec

/-- **MLS Theorem 4.5 (p. 183) with all four bounds for linear time-varying systems (eq. (4.40), p.
184), every hypothesis discharged.** If `Φ` is a state-transition matrix of `ż = A(t)z` on `ℝⁿ` (sup
norm) and `A` is bounded (`‖A(t)‖ ≤ M` for `t ≥ 0`), the origin is exponentially stable if and only
if there are `V`, `V̇`, `∂V/∂x` and constants with the four bounds of the theorem on `‖x‖ ≤ ε`, as
in `exponentiallyStable_iff_exists_lyapunov_of_isDifferentiableFlow`. The differentiable flow is
`φ(t, s, x) = Φ(t, s) x` with `∂φ/∂x = Φ(t, s)` (`IsStateTransition.isDifferentiableFlow`). -/
theorem IsStateTransition.exponentiallyStable_iff_exists_lyapunov
    {A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hΦ : IsStateTransition A Φ) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) :
    ExponentiallyStable (fun t z => A t z) 0 ↔
      ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
        ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
          ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
          HasDerivAlongSolutions (fun t z => A t z) V Vdot univ ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
          (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
          ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ := by
  refine exponentiallyStable_iff_exists_lyapunov_of_isDifferentiableFlow hΦ.isDifferentiableFlow
    (K := M.toNNReal) fun t ht => (A t).lipschitzWith.weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hM t ht).trans (le_max_left _ _)

end Stability
end RoboLean
