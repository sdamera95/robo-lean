import RoboLean.Control.MatrixExponentialSpectrum
import RoboLean.Control.StabilityTheorems
import RoboLean.Control.SolutionFlow
import RoboLean.Control.QuadraticBounds
import RoboLean.Control.MatrixAnalysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Stability by linearization (MLS Theorem 4.6, printed pp. 184–185)

**What MLS prints (read this session, pp. 184–185).** For `ẋ = f(x, t)` with `f(0, t) = 0` for
all `t ≥ 0` (4.37), `A(t) = ∂f(x, t)/∂x |_{x=0}` (4.38) and the remainder
`f₁(x, t) = f(x, t) − A(t)x`, the linearization `ż = A(t)z` (4.40) is called uniform if
`lim_{‖x‖→0} sup_{t≥0} ‖f₁(x, t)‖/‖x‖ = 0` (4.39). "Theorem 4.6. Stability by linearization.
Consider the system (4.37) and assume [(4.39)]. Further, let `A(·)` defined in equation (4.38) be
bounded. If 0 is a uniformly asymptotically stable equilibrium point of (4.40) then it is a
locally uniformly asymptotically stable equilibrium point of (4.37)." (p. 184). And (p. 185): "If
the system (4.37) is time-invariant, then the indirect method says that if the eigenvalues of
`A = ∂f(x)/∂x |_{x=0}` are in the open left half complex plane, then the origin is asymptotically
stable." MLS gives no proof.

**Formalized here.**

* The uniform linearization (4.39) (`IsUniformLinearization f A`, with `A : ℝ → (E →L[ℝ] E)`), and
  for an autonomous field it is Fréchet differentiability at `0`
  (`isUniformLinearization_of_hasFDerivAt`).
* Linear systems `ż = Lz` on a Banach space: a decay bound `‖exp(tL)‖ ≤ C e^{−αt}` gives global
  exponential stability (`globallyExponentiallyStable_of_norm_exp_le`); uniform asymptotic
  stability gives such a bound (`exists_norm_exp_smul_le_of_uniformlyAsymptoticallyStable`), so
  the two are equivalent (`uniformlyAsymptoticallyStable_iff_globallyExponentiallyStable`).
* Theorem 4.6 for a constant linearization `A(t) ≡ L` on `ℝⁿ`, with `f` itself allowed to depend on
  time: if `ż = Lz` decays exponentially, the origin of `ẋ = f(x, t)` is exponentially stable
  (`exponentiallyStable_of_isUniformLinearization`); with MLS's hypothesis, uniform asymptotic
  stability of `ż = Lz`, the printed conclusion follows
  (`uniformlyAsymptoticallyStable_of_isUniformLinearization`). The constant `A` is bounded, as the
  theorem asks.
* The time-invariant criterion of p. 185: if every eigenvalue of `A` has negative real part
  (`Control.IsHurwitz A`), then `ż = Az` is globally exponentially stable
  (`Control.IsHurwitz.globallyExponentiallyStable`), and for `ẋ = F(x)` with `F(0) = 0` and
  derivative `A` at `0` the origin is exponentially stable
  (`Control.IsHurwitz.exponentiallyStable_of_hasFDerivAt`), hence asymptotically stable as printed
  (`Control.IsHurwitz.asymptoticallyStableAt_of_hasFDerivAt`).

**Route.** From the decay bound, the finite-horizon Gramian `P = 2∫₀^T exp(sL)ᵀ exp(sL) ds`
(entries are scalar integrals) is positive definite and satisfies
`2 xᵀP(Lx) = 2(‖exp(TL)x‖₂² − ‖x‖₂²) ≤ −‖x‖²` for `T` large (fundamental theorem of calculus;
`exists_posDef_lyapunov_of_norm_exp_le`). Then `V(x) = xᵀPx` is a Lyapunov function for the
nonlinear system on a small ball, where `‖f(t, x) − Lx‖ ≤ γ‖x‖`, and the local form of Theorem 4.5
(`exponentiallyStable_of_quadratic_lyapunov_local`, E019) concludes. No continuity of `f` is used:
`V̇` is computed along each solution from its derivative.

**Not formalized: Theorem 4.6 with a time-varying `A(t)`.** Its proof needs uniform asymptotic
stability of `ż = A(t)z` to give a uniform exponential bound and a Lyapunov function `xᵀP(t)x`,
i.e. solutions of `ż = A(t)z` from every `(t₀, z₀)` (the state-transition matrix) and their
dependence on `t₀`; the flow interface `HasFlow` is autonomous and the pinned Mathlib has no
state-transition matrix. `IsUniformLinearization` already takes a time-dependent `A`.

**Conventions.** As in `RoboLean.Stability`: time first (`f t x` for MLS's `f(x, t)`), solutions
`IsSolution`, initial times `t₀ ≥ 0`, sup norm on `Fin n → ℝ`. MLS's `∂f/∂x|_{x=0}` is read as the
Fréchet derivative at `0` (`HasFDerivAt`), which for an autonomous field with `F(0) = 0` is exactly
(4.39). The linear map of a real matrix `A` is `LinearMap.toContinuousLinearMap (Matrix.toLin' A)`,
`x ↦ A x`; `‖·‖` on such maps is the operator norm. Exponential stability is MLS Definition 4.3 as
formalized in E016 (constants independent of `t₀`); it implies uniform asymptotic stability.
-/

noncomputable section

open Set Filter Topology NormedSpace Matrix

namespace RoboLean

namespace Control

variable {n : ℕ}

/-- **The sup norm squared is at most the Euclidean norm squared** on `ℝⁿ`: `‖v‖² ≤ v ⬝ v`. Used
in the proof of MLS Theorem 4.6 (p. 184) to compare the Lyapunov function of the linearization
with the sup norm of the state. -/
theorem sq_norm_le_dotProduct_self (v : Fin n → ℝ) : ‖v‖ ^ 2 ≤ v ⬝ᵥ v := by
  have h0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h : ‖v‖ ≤ Real.sqrt (v ⬝ᵥ v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    nlinarith
  calc ‖v‖ ^ 2 ≤ Real.sqrt (v ⬝ᵥ v) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = v ⬝ᵥ v := Real.sq_sqrt h0

/-- **The Euclidean norm squared is at most `n` times the sup norm squared** on `ℝⁿ`:
`v ⬝ v ≤ n ‖v‖²`. Used in the proof of MLS Theorem 4.6 (p. 184). -/
theorem dotProduct_self_le_mul_sq_norm (v : Fin n → ℝ) : v ⬝ᵥ v ≤ n * ‖v‖ ^ 2 := by
  have h : ∀ i, v i * v i ≤ ‖v‖ ^ 2 := by
    intro i
    have h1 : |v i| ≤ ‖v‖ := by simpa using norm_le_pi_norm v i
    nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = n * ‖v‖ ^ 2 := by simp

/- A bilinear form on `ℝⁿ` is bounded with a positive constant (sup norms): the bound `κ ≥ 0` of
`exists_abs_dotProduct_mulVec_le` (`Control/MatrixAnalysis`) raised to `κ + 1 > 0`. -/
private theorem exists_pos_abs_dotProduct_mulVec_le (P : Matrix (Fin n) (Fin n) ℝ) :
    ∃ K > 0, ∀ x y : Fin n → ℝ, |x ⬝ᵥ (P *ᵥ y)| ≤ K * ‖x‖ * ‖y‖ := by
  obtain ⟨κ, hκ, h⟩ := exists_abs_dotProduct_mulVec_le P
  refine ⟨κ + 1, by linarith, fun x y => (h x y).trans ?_⟩
  gcongr
  linarith

end Control

namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The uniform linearization (MLS eq. (4.39), p. 184):** the remainder `f(x, t) − A(t)x` is small
compared with `‖x‖` uniformly in `t ≥ 0`, i.e. for every `γ > 0` there is `r > 0` with
`‖f(t, x) − A(t)x‖ ≤ γ‖x‖` for all `t ≥ 0` and `‖x‖ ≤ r`. This is MLS's
`lim_{‖x‖→0} sup_{t≥0} ‖f₁(x, t)‖/‖x‖ = 0`. It implies `f(t, 0) = 0` for `t ≥ 0`, which MLS
assumes for (4.37) (`IsUniformLinearization.isEquilibrium_zero`). `A(t)` is a continuous linear
map, time first. -/
def IsUniformLinearization (f : ℝ → E → E) (A : ℝ → E →L[ℝ] E) : Prop :=
  ∀ γ > 0, ∃ r > 0, ∀ t, 0 ≤ t → ∀ x : E, ‖x‖ ≤ r → ‖f t x - A t x‖ ≤ γ * ‖x‖

/-- A system with a uniform linearization (4.39) has the origin as a rest point for `t ≥ 0`: MLS's
standing assumption `f(0, t) = 0` of (4.37), p. 184. -/
theorem IsUniformLinearization.isEquilibrium_zero {f : ℝ → E → E} {A : ℝ → E →L[ℝ] E}
    (h : IsUniformLinearization f A) {t : ℝ} (ht : 0 ≤ t) : f t 0 = 0 := by
  obtain ⟨r, hr, h⟩ := h 1 one_pos
  have := h t ht 0 (by simpa using hr.le)
  simpa using this

/-- **For a time-invariant system, (4.39) is differentiability at the origin (MLS p. 185).** If
`F(0) = 0` and `F` has the Fréchet derivative `A` at `0`, then `ż = Az` is a uniform linearization
of `ẋ = F(x)` (written `fun _ => F`, time first). -/
theorem isUniformLinearization_of_hasFDerivAt {F : E → E} {A : E →L[ℝ] E} (hF0 : F 0 = 0)
    (hF : HasFDerivAt F A 0) : IsUniformLinearization (fun _ => F) (fun _ => A) := by
  intro γ hγ
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hF.isLittleO.def hγ)
  refine ⟨r / 2, by positivity, fun t _ x hx => ?_⟩
  have hd : dist x 0 < r := by
    rw [dist_zero_right]
    linarith
  simpa [hF0] using hball hd

section Linear

variable [CompleteSpace E]

/-- **A linear system with a decaying exponential is globally exponentially stable** (MLS
Definition 4.3, p. 181, for `ż = Lz`, eq. (4.40) with constant `A`): if `‖exp(tL)‖ ≤ C e^{−αt}` for
`t ≥ 0` with `α > 0`, then every solution satisfies `‖z(t)‖ ≤ max(C, 1) e^{−α(t − t₀)} ‖z(t₀)‖`.
Solutions are unique and equal to `exp((t − t₀)L) z(t₀)` (`hasFlow_linear`). `E` is a real Banach
space. -/
theorem globallyExponentiallyStable_of_norm_exp_le (L : E →L[ℝ] E) {C α : ℝ} (hα : 0 < α)
    (h : ∀ t, 0 ≤ t → ‖exp (t • L)‖ ≤ C * Real.exp (-(α * t))) :
    GloballyExponentiallyStable (fun _ x => L x) 0 := by
  have hflow := hasFlow_linear L
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), α, hα,
    fun t₀ ht₀ x hx t ht => ?_⟩
  have heq := hflow.eq_of_isSolution t₀ ht₀ x hx t ht
  simp only [sub_zero]
  rw [heq]
  have hd := h (t - t₀) (by linarith)
  have he : Real.exp (-(α * (t - t₀))) = Real.exp (-α * (t - t₀)) := by ring_nf
  calc ‖exp ((t - t₀) • L) (x t₀)‖ ≤ ‖exp ((t - t₀) • L)‖ * ‖x t₀‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * Real.exp (-(α * (t - t₀))) * ‖x t₀‖ := by gcongr
    _ ≤ max C 1 * Real.exp (-α * (t - t₀)) * ‖x t₀‖ := by
        rw [he]
        gcongr
        exact le_max_left _ _

/-- **Uniform asymptotic stability of a linear system gives exponential decay** (for MLS
Theorem 4.6, p. 184, with constant `A`): if the origin of `ż = Lz` is uniformly asymptotically
stable (MLS p. 180), then `‖exp(tL)‖ ≤ C e^{−αt}` for some `C` and `α > 0`. By linearity the
uniform attraction of a ball gives `‖exp(TL)‖ ≤ 1/2` for one time `T > 0`, and the powers of
`exp(TL)` give the rate `α = (log 2)/T`. `E` is a real Banach space. -/
theorem exists_norm_exp_smul_le_of_uniformlyAsymptoticallyStable (L : E →L[ℝ] E)
    (h : UniformlyAsymptoticallyStable (fun _ x => L x) 0) :
    ∃ C α, 0 < α ∧ ∀ t, 0 ≤ t → ‖exp (t • L)‖ ≤ C * Real.exp (-(α * t)) := by
  obtain ⟨-, δ, hδ, hatt⟩ := h
  obtain ⟨T₀, hT₀, hT⟩ := hatt (δ / 4) (by positivity)
  have hflow := hasFlow_linear L
  have hTpos : 0 < T₀ + 1 := by linarith
  have hhalf : ‖exp ((T₀ + 1) • L)‖ ≤ 1 / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
      set c := δ / (2 * ‖y‖) with hc
      have hcpos : 0 < c := by positivity
      have hcy : ‖c • y‖ = δ / 2 := by
        rw [norm_smul, Real.norm_of_nonneg hcpos.le, hc]
        field_simp
      have hsol := hflow.isSolution (c • y)
      have h0 : exp ((0 : ℝ) • L) (c • y) = c • y := by simp
      have := hT 0 le_rfl (fun t => exp (t • L) (c • y)) hsol
        (by rw [h0, sub_zero, hcy]; linarith)
        (T₀ + 1) (by linarith)
      rw [sub_zero, map_smul, norm_smul, Real.norm_of_nonneg hcpos.le, hc] at this
      have h1 : δ / (2 * ‖y‖) * ‖exp ((T₀ + 1) • L) y‖ < δ / 4 := this
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)] at h1
      nlinarith
  have he : Real.exp (-(Real.log 2 / (T₀ + 1) * (T₀ + 1))) = 1 / 2 := by
    rw [div_mul_cancel₀ _ hTpos.ne', Real.exp_neg, Real.exp_log two_pos, one_div]
  have hpow : ∀ k : ℕ, ‖exp ((T₀ + 1) • L) ^ k‖ ≤
      1 * Real.exp (-(Real.log 2 / (T₀ + 1) * (T₀ + 1))) ^ k := by
    intro k
    rw [he, one_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    · exact (norm_pow_le' _ hk).trans (pow_le_pow_left₀ (norm_nonneg _) hhalf k)
  obtain ⟨K, hK⟩ := Control.exists_norm_exp_smul_le_of_norm_pow_le L hTpos hpow
  exact ⟨K, Real.log 2 / (T₀ + 1), div_pos (Real.log_pos one_lt_two) hTpos, hK⟩

/-- **For a linear system, uniform asymptotic stability is global exponential stability** (MLS
p. 180–181 notions for `ż = Lz`). The converse direction is MLS's remark that exponential stability
implies uniform asymptotic stability (p. 181). `E` is a real Banach space. -/
theorem uniformlyAsymptoticallyStable_iff_globallyExponentiallyStable (L : E →L[ℝ] E) :
    UniformlyAsymptoticallyStable (fun _ x => L x) 0 ↔
      GloballyExponentiallyStable (fun _ x => L x) 0 := by
  refine ⟨fun h => ?_, fun h => h.exponentiallyStable.uniformlyAsymptoticallyStable⟩
  obtain ⟨C, α, hα, hd⟩ := exists_norm_exp_smul_le_of_uniformlyAsymptoticallyStable L h
  exact globallyExponentiallyStable_of_norm_exp_le L hα hd

end Linear

/-- **Exponential stability does not depend on linear coordinates** (used to apply MLS Theorem 4.6
on a state space other than `ℝⁿ`, e.g. `ℝ × ℝ` in MLS Example 4.6): if `e : E ≃ E'` is a continuous
linear equivalence and the origin of the transported system `ẏ = e(f(t, e⁻¹y))` is exponentially
stable, so is the origin of `ẋ = f(t, x)`; the constants change by the norms of `e` and `e⁻¹`. -/
theorem ExponentiallyStable.of_continuousLinearEquiv {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {f : ℝ → E → E} (e : E ≃L[ℝ] E')
    (h : ExponentiallyStable (fun t y => e (f t (e.symm y))) 0) : ExponentiallyStable f 0 := by
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := h
  set a := ‖(e : E →L[ℝ] E')‖ + 1 with ha
  set b := ‖(e.symm : E' →L[ℝ] E)‖ + 1 with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hle : ∀ y : E, ‖e y‖ ≤ a * ‖y‖ := fun y =>
    ((e : E →L[ℝ] E').le_opNorm y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hle' : ∀ z : E', ‖e.symm z‖ ≤ b * ‖z‖ := fun z =>
    ((e.symm : E' →L[ℝ] E).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  refine ⟨b * m * a, by positivity, α, hα, ε / a, by positivity, fun t₀ ht₀ x hx hx0 t ht => ?_⟩
  have hsol : IsSolution (fun t y => e (f t (e.symm y))) t₀ (fun s => e (x s)) := by
    refine ⟨e.continuous.comp_continuousOn hx.1, fun s hs => ?_⟩
    have := e.hasFDerivAt.comp_hasDerivAt s (hx.2 s hs)
    simpa [Function.comp_def] using this
  simp only [sub_zero] at hx0 ⊢
  have h0 : ‖e (x t₀)‖ ≤ ε := by
    calc ‖e (x t₀)‖ ≤ a * ‖x t₀‖ := hle _
      _ ≤ a * (ε / a) := by gcongr
      _ = ε := by field_simp
  have hbound := h t₀ ht₀ _ hsol (by simpa using h0) t ht
  simp only [sub_zero] at hbound
  calc ‖x t‖ = ‖e.symm (e (x t))‖ := by simp
    _ ≤ b * ‖e (x t)‖ := hle' _
    _ ≤ b * (m * Real.exp (-α * (t - t₀)) * ‖e (x t₀)‖) := by gcongr
    _ ≤ b * (m * Real.exp (-α * (t - t₀)) * (a * ‖x t₀‖)) := by gcongr; exact hle _
    _ = b * m * a * Real.exp (-α * (t - t₀)) * ‖x t₀‖ := by ring

section Lyapunov

variable {n : ℕ}

/-- **A quadratic Lyapunov function for a decaying linear system** (the Lyapunov function behind
the indirect method, MLS §4.3, p. 184): if `‖exp(tL)‖ ≤ C e^{−αt}` for `t ≥ 0` with `α > 0`, there
is a positive definite `P` with `2 xᵀP(Lx) ≤ −‖x‖²` for all `x ∈ ℝⁿ` (sup norm). `P` is twice the
finite-horizon Gramian `∫₀^T exp(sL)ᵀ exp(sL) ds` with `T = 1 + log(2nC'² + 1)/(2α)`,
`C' = max(C, 0)`; the inequality is the fundamental theorem of calculus for
`s ↦ ‖exp(sL)x‖₂²`. MLS does not print this construction. -/
theorem exists_posDef_lyapunov_of_norm_exp_le (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {C α : ℝ}
    (hα : 0 < α) (hdec : ∀ t, 0 ≤ t → ‖exp (t • L)‖ ≤ C * Real.exp (-(α * t))) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧ ∀ x, 2 * (x ⬝ᵥ (P *ᵥ L x)) ≤ -‖x‖ ^ 2 := by
  let _ : NormedAlgebra ℚ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  have hd : ∀ (y : Fin n → ℝ) (s : ℝ),
      HasDerivAt (fun u : ℝ => exp (u • L) y) (exp (s • L) (L y)) s := by
    intro y s
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) L s
    simpa using h1.clm_apply (hasDerivAt_const s y)
  have hc : ∀ y : Fin n → ℝ, Continuous fun s : ℝ => exp (s • L) y :=
    fun y => continuous_iff_continuousAt.mpr fun s => (hd y s).continuousAt
  -- a horizon `T` with `n (C' e^{−αT})² ≤ 1/2`
  set C' := max C 0 with hC'
  have hdec' : ∀ t, 0 ≤ t → ‖exp (t • L)‖ ≤ C' * Real.exp (-(α * t)) := fun t ht =>
    (hdec t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  set D : ℝ := 2 * n * C' ^ 2 + 1 with hDdef
  have hD : 0 < D := by positivity
  set T : ℝ := 1 + Real.log D / (2 * α) with hTdef
  have hT : 0 < T := by
    have : 0 ≤ Real.log D := Real.log_nonneg (by simp only [hDdef]; nlinarith [sq_nonneg C'])
    positivity
  have hsmall : (n : ℝ) * (C' * Real.exp (-(α * T))) ^ 2 ≤ 1 / 2 := by
    have h1 : Real.exp (-(α * T)) ^ 2 = Real.exp (-(2 * α)) / D := by
      have harg : -(α * T) + -(α * T) = -(2 * α) + -Real.log D := by
        rw [hTdef]
        field_simp
        ring
      rw [sq, ← Real.exp_add, harg, Real.exp_add, Real.exp_neg (Real.log D), Real.exp_log hD,
        div_eq_mul_inv]
    have h2 : Real.exp (-(2 * α)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hCe : C' ^ 2 * Real.exp (-(2 * α)) ≤ C' ^ 2 := by
      nlinarith [sq_nonneg C', Real.exp_pos (-(2 * α))]
    rw [mul_pow, h1]
    calc (n : ℝ) * (C' ^ 2 * (Real.exp (-(2 * α)) / D))
        = n * (C' ^ 2 * Real.exp (-(2 * α))) / D := by ring
      _ ≤ n * C' ^ 2 / D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCe (Nat.cast_nonneg n)) hD.le
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hD, hDdef]
        linarith
  -- the finite-horizon Gramian `G = ∫₀^T exp(sL)ᵀ exp(sL) ds`
  set G : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ∫ s in (0 : ℝ)..T, exp (s • L) (Pi.single i 1) ⬝ᵥ exp (s • L) (Pi.single j 1) with hG
  have hint : ∀ y z : Fin n → ℝ, IntervalIntegrable
      (fun s => exp (s • L) y ⬝ᵥ exp (s • L) z) MeasureTheory.volume 0 T :=
    fun y z => ((hc y).dotProduct (hc z)).intervalIntegrable 0 T
  have hexpand : ∀ (x y : Fin n → ℝ) (s : ℝ), exp (s • L) x ⬝ᵥ exp (s • L) y =
      ∑ i, ∑ j, x i * y j * (exp (s • L) (Pi.single i 1) ⬝ᵥ exp (s • L) (Pi.single j 1)) := by
    intro x y s
    have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have hy : y = ∑ j, y j • Pi.single j (1 : ℝ) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    conv_lhs => rw [hx, hy]
    simp only [map_sum, map_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbil : ∀ x y : Fin n → ℝ,
      x ⬝ᵥ (G *ᵥ y) = ∫ s in (0 : ℝ)..T, exp (s • L) x ⬝ᵥ exp (s • L) y := by
    intro x y
    simp_rw [hexpand x y]
    have hcont : ∀ i j : Fin n, Continuous fun s : ℝ =>
        exp (s • L) (Pi.single i 1) ⬝ᵥ exp (s • L) (Pi.single j 1) :=
      fun i j => (hc _).dotProduct (hc _)
    have hint1 : ∀ i j : Fin n, IntervalIntegrable (fun s : ℝ => x i * y j *
        (exp (s • L) (Pi.single i 1) ⬝ᵥ exp (s • L) (Pi.single j 1))) MeasureTheory.volume 0 T :=
      fun i j => (continuous_const.mul (hcont i j)).intervalIntegrable 0 T
    have hint2 : ∀ i : Fin n, IntervalIntegrable (fun s : ℝ => ∑ j, x i * y j *
        (exp (s • L) (Pi.single i 1) ⬝ᵥ exp (s • L) (Pi.single j 1))) MeasureTheory.volume 0 T :=
      fun i => (continuous_finsetSum _ fun j _ =>
        continuous_const.mul (hcont i j)).intervalIntegrable 0 T
    rw [intervalIntegral.integral_finsetSum fun i _ => hint2 i]
    have hout : x ⬝ᵥ (G *ᵥ y) = ∑ i, ∑ j, x i * y j * G i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hout]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => hint1 i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
  have hftc : ∀ x : Fin n → ℝ, ∫ s in (0 : ℝ)..T, 2 * (exp (s • L) x ⬝ᵥ exp (s • L) (L x)) =
      exp (T • L) x ⬝ᵥ exp (T • L) x - x ⬝ᵥ x := by
    intro x
    have hder : ∀ s ∈ Set.uIcc (0 : ℝ) T, HasDerivAt
        (fun u => exp (u • L) x ⬝ᵥ exp (u • L) x)
        (2 * (exp (s • L) x ⬝ᵥ exp (s • L) (L x))) s := by
      intro s _
      have := Control.hasDerivAt_dotProduct (hd x s) (hd x s)
      convert this using 1
      rw [dotProduct_comm (exp (s • L) (L x))]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((continuous_const.mul ((hc x).dotProduct (hc (L x)))).intervalIntegrable 0 T)]
    simp
  have hsymm : ∀ i j, G i j = G j i := by
    intro i j
    simp only [hG]
    congr 1
    funext s
    exact dotProduct_comm _ _
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x) := by
    intro x hx
    rw [hbil]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint x x) (fun s _ => ?_) hT
    have hne : exp (s • L) x ≠ 0 := by
      intro h0
      apply hx
      have hcomm : Commute ((-s) • L) (s • L) :=
        ((Commute.refl L).smul_left (-s)).smul_right s
      have hinv : (exp ((-s) • L) * exp (s • L)) x = x := by
        rw [← exp_add_of_commute hcomm, ← add_smul, neg_add_cancel, zero_smul, exp_zero]
        rfl
      have hx' : x = exp ((-s) • L) (exp (s • L) x) := hinv.symm
      rw [hx', h0, map_zero]
    have h1 := Control.sq_norm_le_dotProduct_self (exp (s • L) x)
    have h2 : 0 < ‖exp (s • L) x‖ := norm_pos_iff.mpr hne
    nlinarith
  refine ⟨(2 : ℝ) • G, ?_, fun x => ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, hsymm j i]
    · rw [star_trivial, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      have := hpos x hx
      positivity
  · have h1 : 2 * (x ⬝ᵥ (((2 : ℝ) • G) *ᵥ L x)) =
        2 * (exp (T • L) x ⬝ᵥ exp (T • L) x - x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hbil, ← hftc,
        intervalIntegral.integral_const_mul]
    have h2 : exp (T • L) x ⬝ᵥ exp (T • L) x ≤ 1 / 2 * ‖x‖ ^ 2 := by
      have hE : ‖exp (T • L) x‖ ≤ C' * Real.exp (-(α * T)) * ‖x‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hdec' T hT.le) (norm_nonneg _))
      calc exp (T • L) x ⬝ᵥ exp (T • L) x ≤ n * ‖exp (T • L) x‖ ^ 2 :=
            Control.dotProduct_self_le_mul_sq_norm _
        _ ≤ n * (C' * Real.exp (-(α * T)) * ‖x‖) ^ 2 := by gcongr
        _ = n * (C' * Real.exp (-(α * T))) ^ 2 * ‖x‖ ^ 2 := by ring
        _ ≤ 1 / 2 * ‖x‖ ^ 2 := by gcongr
    have h3 := Control.sq_norm_le_dotProduct_self x
    rw [h1]
    linarith

/-- **MLS Theorem 4.6 for a constant linearization, with an exponential conclusion** (p. 184).
Let `ẋ = f(x, t)` on `ℝⁿ` (sup norm) have the uniform linearization `ż = Lz` (4.39) with constant
`L`, and let `exp(tL)` decay: `‖exp(tL)‖ ≤ C e^{−αt}` for `t ≥ 0`, `α > 0`. Then the origin is
exponentially stable (Definition 4.3), hence uniformly asymptotically stable. No continuity of
`f` is assumed; solutions are not assumed to exist. Proof: the Lyapunov function `xᵀPx` of
`exists_posDef_lyapunov_of_norm_exp_le` and the local form of Theorem 4.5. -/
theorem exponentiallyStable_of_isUniformLinearization {f : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {C α : ℝ} (hα : 0 < α)
    (hdec : ∀ t, 0 ≤ t → ‖exp (t • L)‖ ≤ C * Real.exp (-(α * t)))
    (hf : IsUniformLinearization f (fun _ => L)) : ExponentiallyStable f 0 := by
  obtain ⟨P, hP, hlyap⟩ := exists_posDef_lyapunov_of_norm_exp_le L hα hdec
  obtain ⟨K, hK, hbil⟩ := Control.exists_pos_abs_dotProduct_mulVec_le P
  obtain ⟨r, hr, hlin⟩ := hf (1 / (4 * K)) (by positivity)
  obtain ⟨a₁, ha₁, hlow⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hP
  obtain ⟨a₂, ha₂, hup⟩ := QuadraticBounds.exists_dotProduct_mulVec_le_mul_sq_norm P
  have hsymm : P.IsSymm := by
    unfold Matrix.IsSymm
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hP.isHermitian
  refine exponentiallyStable_of_quadratic_lyapunov_local (V := fun _ y => y ⬝ᵥ (P *ᵥ y))
    (Vdot := fun t y => f t y ⬝ᵥ (P *ᵥ y) + y ⬝ᵥ (P *ᵥ f t y)) (a₃ := 1 / 2) ha₁ ha₂
    (by norm_num) hr ?_ (fun t _ y _ => hlow y) (fun t _ y _ => hup y) ?_ ?_
  · exact (continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)).continuousOn
  · intro t₀ _ x hx t ht _
    exact Control.hasDerivAt_dotProduct (hx.2 t ht) (Control.hasDerivAt_mulVec_const P (hx.2 t ht))
  · intro t ht y hy
    have h1 : f t y ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ f t y) := Control.dotProduct_mulVec_comm hsymm _ _
    have h2 : y ⬝ᵥ (P *ᵥ f t y) = y ⬝ᵥ (P *ᵥ L y) + y ⬝ᵥ (P *ᵥ (f t y - L y)) := by
      rw [Matrix.mulVec_sub, dotProduct_sub]
      ring
    have h4 := hlin t ht y hy
    have h6 : |y ⬝ᵥ (P *ᵥ (f t y - L y))| ≤ 1 / 4 * ‖y‖ ^ 2 :=
      calc |y ⬝ᵥ (P *ᵥ (f t y - L y))| ≤ K * ‖y‖ * ‖f t y - L y‖ := hbil _ _
        _ ≤ K * ‖y‖ * (1 / (4 * K) * ‖y‖) := by gcongr
        _ = 1 / 4 * ‖y‖ ^ 2 := by field_simp
    have h7 := hlyap y
    rw [h1, h2]
    linarith [(abs_le.mp h6).2]

/-- **MLS Theorem 4.6 (p. 184) for a constant linearization `A(t) ≡ L`, exponential form.** If
the origin of `ż = Lz` is uniformly asymptotically stable and `ż = Lz` is a uniform linearization
(4.39) of `ẋ = f(x, t)` on `ℝⁿ`, then the origin of `ẋ = f(x, t)` is exponentially stable. A
constant `L` is bounded, as the theorem requires. -/
theorem exponentiallyStable_of_isUniformLinearization_of_uniformlyAsymptoticallyStable
    {f : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} {L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hL : UniformlyAsymptoticallyStable (fun _ z => L z) 0)
    (hf : IsUniformLinearization f (fun _ => L)) : ExponentiallyStable f 0 := by
  obtain ⟨C, α, hα, hd⟩ := exists_norm_exp_smul_le_of_uniformlyAsymptoticallyStable L hL
  exact exponentiallyStable_of_isUniformLinearization hα hd hf

/-- **MLS Theorem 4.6 (p. 184) for a constant linearization `A(t) ≡ L`, as printed:** if `0` is a
uniformly asymptotically stable equilibrium point of `ż = Lz` (4.40) and (4.39) holds, then `0` is
a (locally) uniformly asymptotically stable equilibrium point of `ẋ = f(x, t)` (4.37), on `ℝⁿ`
with the sup norm. The library's uniform asymptotic stability is local (a ball of initial
states). The time-varying `A(t)` case is not formalized (module docstring). -/
theorem uniformlyAsymptoticallyStable_of_isUniformLinearization
    {f : ℝ → (Fin n → ℝ) → (Fin n → ℝ)} {L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hL : UniformlyAsymptoticallyStable (fun _ z => L z) 0)
    (hf : IsUniformLinearization f (fun _ => L)) : UniformlyAsymptoticallyStable f 0 :=
  (exponentiallyStable_of_isUniformLinearization_of_uniformlyAsymptoticallyStable hL hf
    ).uniformlyAsymptoticallyStable

end Lyapunov

end Stability

namespace Control

open Stability

variable {n : ℕ}

/-- **The eigenvalue criterion for linear systems (for MLS p. 185):** if every complex eigenvalue of
the real matrix `A` has negative real part, the origin of `ż = Az` is globally exponentially stable
(Definition 4.3, p. 181). The system is `fun _ z => A *ᵥ z` on `ℝⁿ` with the sup norm. -/
theorem IsHurwitz.globallyExponentiallyStable {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    GloballyExponentiallyStable (fun _ z => A *ᵥ z) 0 := by
  obtain ⟨C, α, hα, h⟩ := hA.exists_norm_exp_smul_le
  simpa using globallyExponentiallyStable_of_norm_exp_le _ hα h

/-- **The eigenvalue condition gives the hypothesis of MLS Theorem 4.6 (p. 184):** if every
complex eigenvalue of `A` has negative real part, the origin of `ż = Az` (4.40) is uniformly
asymptotically stable. -/
theorem IsHurwitz.uniformlyAsymptoticallyStable {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) : UniformlyAsymptoticallyStable (fun _ z => A *ᵥ z) 0 :=
  hA.globallyExponentiallyStable.exponentiallyStable.uniformlyAsymptoticallyStable

/-- **A Lyapunov inequality for a matrix with eigenvalues in the open left half plane** (the
Lyapunov function of the indirect method, MLS §4.3, p. 184): there is a positive definite `P` with
`2 xᵀPAx ≤ −‖x‖²` for all `x ∈ ℝⁿ` (sup norm). MLS does not print it. -/
theorem IsHurwitz.exists_posDef_lyapunov {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧ ∀ x, 2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x))) ≤ -‖x‖ ^ 2 := by
  obtain ⟨C, α, hα, h⟩ := hA.exists_norm_exp_smul_le
  simpa using exists_posDef_lyapunov_of_norm_exp_le _ hα h

/-- **MLS Theorem 4.6 (p. 184) with the eigenvalue condition of p. 185:** if `ż = Az` is a uniform
linearization (4.39) of `ẋ = f(x, t)` on `ℝⁿ` with a constant real matrix `A` all of whose complex
eigenvalues have negative real part, then the origin of `ẋ = f(x, t)` is exponentially stable
(Definition 4.3), in particular uniformly asymptotically stable. `f` may depend on time. -/
theorem IsHurwitz.exponentiallyStable_of_isUniformLinearization {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {f : ℝ → (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : IsUniformLinearization f (fun _ => LinearMap.toContinuousLinearMap (Matrix.toLin' A))) :
    ExponentiallyStable f 0 := by
  obtain ⟨C, α, hα, h⟩ := hA.exists_norm_exp_smul_le
  exact Stability.exponentiallyStable_of_isUniformLinearization hα h hf

/-- **The time-invariant indirect method of MLS p. 185, exponential form:** for `ẋ = F(x)` on `ℝⁿ`
with `F(0) = 0` and Fréchet derivative `x ↦ Ax` at `0`, where every complex eigenvalue of `A` has
negative real part, the origin is exponentially stable (Definition 4.3). MLS states the conclusion
as asymptotic stability (`IsHurwitz.asymptoticallyStableAt_of_hasFDerivAt`). The system is
`fun _ => F`, sup norm. -/
theorem IsHurwitz.exponentiallyStable_of_hasFDerivAt {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF0 : F 0 = 0)
    (hF : HasFDerivAt F (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) 0) :
    ExponentiallyStable (fun _ => F) 0 :=
  hA.exponentiallyStable_of_isUniformLinearization (isUniformLinearization_of_hasFDerivAt hF0 hF)

/-- **The time-invariant indirect method, as printed (MLS p. 185):** "if the eigenvalues of
`A = ∂f(x)/∂x|_{x=0}` are in the open left half complex plane, then the origin is asymptotically
stable", here at every initial time `t₀ ≥ 0` (Definition 4.2, p. 180), for `ẋ = F(x)` on `ℝⁿ` with
`F(0) = 0` and Fréchet derivative `x ↦ Ax` at `0`. -/
theorem IsHurwitz.asymptoticallyStableAt_of_hasFDerivAt {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) {F : (Fin n → ℝ) → (Fin n → ℝ)} (hF0 : F 0 = 0)
    (hF : HasFDerivAt F (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) 0) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) : AsymptoticallyStableAt (fun _ => F) 0 t₀ :=
  (hA.exponentiallyStable_of_hasFDerivAt hF0 hF).asymptoticallyStableAt ht₀

end Control
end RoboLean
