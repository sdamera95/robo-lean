import RoboLean.Control.StateTransition
import RoboLean.Control.Linearization

/-!
# Linear time-varying systems: uniform asymptotic stability and a Gramian Lyapunov function

For MLS Theorem 4.6 (printed p. 184) with a time-varying linearization `ż = A(t)z` (4.40).

**What MLS prints (read this session, pp. 183–185).** Theorem 4.6 assumes that `0` is a uniformly
asymptotically stable equilibrium point of (4.40) and that `A(·)` is bounded; p. 185 adds that
"global uniform asymptotic stability of the linearization implies local uniform asymptotic
stability of the original nonlinear system". Theorem 4.5 (p. 183) characterizes exponential
stability by a function `V(x, t)` with `α₁‖x‖² ≤ V ≤ α₂‖x‖²`, `V̇ ≤ −α₃‖x‖²` and
`‖∂V/∂x‖ ≤ α₄‖x‖`. MLS prints no proof of either theorem.

**Formalized here**, for a state-transition matrix `Φ` of `ż = A(t)z` (`IsStateTransition A Φ`):

* uniform asymptotic stability of `ż = A(t)z` is equivalent to an exponential bound
  `‖Φ(t, s)‖ ≤ C e^{−α(t − s)}` for `0 ≤ s ≤ t`, and to global exponential stability
  (`IsStateTransition.uniformlyAsymptoticallyStable_iff_exists_norm_le`,
  `.uniformlyAsymptoticallyStable_iff_globallyExponentiallyStable`); on any real Banach space;
* on `ℝⁿ`, the Gramian `V(t, x) = ∫_t^{t+T} ‖Φ(s, t)x‖₂² ds` (`gramianForm Φ T t x x`, with the
  Euclidean dot product): its derivative along any differentiable curve
  (`IsStateTransition.hasDerivAt_gramianForm`; along solutions of `ż = A(t)z` it is
  `‖Φ(t + T, t)x‖₂² − ‖x‖₂²`), its bounds `a₁‖x‖² ≤ V ≤ a₂‖x‖²` (`le_gramianForm`,
  `abs_gramianForm_le`, with `A` bounded for the lower one), joint continuity, and the fourth
  bound of Theorem 4.5, `‖∂V/∂x‖ ≤ a₄‖x‖` (`exists_hasFDerivAt_gramianForm`).

**Conventions.** As in `RoboLean.Stability`: time first, solutions `IsSolution`, times `t, s ≥ 0`,
the sup norm on `Fin n → ℝ`, the operator norm on `E →L[ℝ] E`. The bound on `Φ` is written
`‖Φ t s‖ ≤ C * exp (−(α (t − s)))` for `0 ≤ s ≤ t`. `V` uses the Euclidean dot product, compared
with the sup norm through `‖x‖² ≤ x ⬝ x ≤ n‖x‖²`.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean

namespace Control

variable {n : ℕ}

/-- **The dot product is bounded by `n` times the sup norms** on `ℝⁿ`: `|u ⬝ v| ≤ n ‖u‖ ‖v‖`. Used
for the Gramian Lyapunov function of MLS Theorem 4.6 (p. 184) with a time-varying linearization. -/
theorem abs_dotProduct_le (u v : Fin n → ℝ) : |u ⬝ᵥ v| ≤ n * ‖u‖ * ‖v‖ := by
  have h : ∀ i, |u i * v i| ≤ ‖u‖ * ‖v‖ := by
    intro i
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_le_pi_norm u i) (by simpa using norm_le_pi_norm v i)
      (abs_nonneg _) (norm_nonneg _)
  calc |u ⬝ᵥ v| = |∑ i, u i * v i| := rfl
    _ ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖u‖ * ‖v‖ := Finset.sum_le_sum fun i _ => h i
    _ = n * ‖u‖ * ‖v‖ := by simp [mul_assoc]

end Control

namespace Stability

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- If `‖y‖ < δ` implies `‖L y‖ < η`, then `‖L‖ ≤ 2η/δ` (scaling). -/
private theorem norm_le_of_forall_norm_lt {L : E →L[ℝ] E} {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (h : ∀ y, ‖y‖ < δ → ‖L y‖ < η) : ‖L‖ ≤ 2 * η / δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set c := δ / (2 * ‖y‖) with hc
  have hcpos : 0 < c := by positivity
  have hcy : ‖c • y‖ < δ := by
    rw [norm_smul, Real.norm_of_nonneg hcpos.le, hc]
    field_simp
    linarith
  have h1 := h _ hcy
  rw [map_smul, norm_smul, Real.norm_of_nonneg hcpos.le, hc] at h1
  have h2 : δ * ‖L y‖ < η * (2 * ‖y‖) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at h1
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

namespace IsStateTransition

variable {A : ℝ → E →L[ℝ] E} {Φ : ℝ → ℝ → E →L[ℝ] E}

/-- **An exponential bound on the state-transition matrix gives global exponential stability**
of `ż = A(t)z` (MLS eq. (4.40), p. 184, and Definition 4.3, p. 181): if
`‖Φ(t, s)‖ ≤ C e^{−α(t − s)}` for `0 ≤ s ≤ t` with `α > 0`, every solution satisfies
`‖z(t)‖ ≤ max(C, 1) e^{−α(t − t₀)} ‖z(t₀)‖`. -/
theorem globallyExponentiallyStable_of_norm_le [CompleteSpace E] (h : IsStateTransition A Φ)
    {C α : ℝ} (hα : 0 < α)
    (hd : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ C * Real.exp (-(α * (t - s)))) :
    GloballyExponentiallyStable (fun t z => A t z) 0 := by
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), α, hα,
    fun t₀ ht₀ x hx t ht => ?_⟩
  simp only [sub_zero]
  rw [h.eq_of_isSolution ht₀ hx ht]
  have he : Real.exp (-(α * (t - t₀))) = Real.exp (-α * (t - t₀)) := by ring_nf
  calc ‖Φ t t₀ (x t₀)‖ ≤ ‖Φ t t₀‖ * ‖x t₀‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * Real.exp (-(α * (t - t₀))) * ‖x t₀‖ := by gcongr; exact hd t t₀ ht₀ ht
    _ ≤ max C 1 * Real.exp (-α * (t - t₀)) * ‖x t₀‖ := by
        rw [he]
        gcongr
        exact le_max_left _ _

/-- **Uniform asymptotic stability of `ż = A(t)z` gives an exponential bound on `Φ`** (for MLS
Theorem 4.6, p. 184, whose hypothesis is uniform asymptotic stability of (4.40)): there are `C`
and `α > 0` with `‖Φ(t, s)‖ ≤ C e^{−α(t − s)}` for `0 ≤ s ≤ t`. Uniform stability bounds
`‖Φ(t, s)‖` by a constant `K`, uniform attraction of a ball gives `‖Φ(t, s)‖ ≤ 1/2` for
`t ≥ s + T'`, and the composition law gives `‖Φ(t, s)‖ ≤ K 2^{−k}` for `t ≥ s + kT'`; the rate is
`α = (log 2)/T'`. No continuity or boundedness of `A` is used. -/
theorem exists_norm_le_of_uniformlyAsymptoticallyStable [CompleteSpace E]
    (h : IsStateTransition A Φ) (hL : UniformlyAsymptoticallyStable (fun t z => A t z) 0) :
    ∃ C α, 0 < α ∧ ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ C * Real.exp (-(α * (t - s))) := by
  obtain ⟨hUS, δ, hδ, hatt⟩ := hL
  obtain ⟨δ₁, hδ₁, hst⟩ := hUS 1 one_pos
  obtain ⟨T, hT0, hT⟩ := hatt (δ / 4) (by positivity)
  set K := 2 * 1 / δ₁ with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ K := by
    intro t s hs hst'
    refine norm_le_of_forall_norm_lt hδ₁ one_pos fun y hy => ?_
    have := hst s hs (fun τ => Φ τ s y) (h.isSolution hs y)
      (by simpa [h.self_eq_one s hs] using hy) t hst'
    simpa using this
  set T' := T + 1 with hT'def
  have hT' : 0 < T' := by linarith
  have hhalf : ∀ t s, 0 ≤ s → s + T' ≤ t → ‖Φ t s‖ ≤ 1 / 2 := by
    intro t s hs hst'
    have := norm_le_of_forall_norm_lt (L := Φ t s) hδ (by positivity : (0 : ℝ) < δ / 4)
      fun y hy => by
        have := hT s hs (fun τ => Φ τ s y) (h.isSolution hs y)
          (by simpa [h.self_eq_one s hs] using hy) t (by linarith)
        simpa using this
    calc ‖Φ t s‖ ≤ 2 * (δ / 4) / δ := this
      _ = 1 / 2 := by field_simp; ring
  have hpow : ∀ k : ℕ, ∀ t s, 0 ≤ s → s + k * T' ≤ t → ‖Φ t s‖ ≤ K * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero =>
      intro t s hs hst'
      simpa using hK t s hs (by simpa using hst')
    | succ k ih =>
      intro t s hs hst'
      have hs' : 0 ≤ s + T' := by linarith
      push_cast at hst'
      have ht : 0 ≤ t := by nlinarith [(by positivity : (0 : ℝ) ≤ k * T')]
      rw [← h.mul_eq t (s + T') s ht hs' hs]
      calc ‖Φ t (s + T') * Φ (s + T') s‖ ≤ ‖Φ t (s + T')‖ * ‖Φ (s + T') s‖ := norm_mul_le _ _
        _ ≤ K * (1 / 2) ^ k * (1 / 2) := by
          gcongr
          · exact ih t (s + T') hs' (by linarith)
          · exact hhalf (s + T') s hs le_rfl
        _ = K * (1 / 2) ^ (k + 1) := by ring
  refine ⟨2 * K, Real.log 2 / T', div_pos (Real.log_pos one_lt_two) hT',
    fun t s hs hst => ?_⟩
  set k := ⌊(t - s) / T'⌋₊ with hk
  have hk1 : (k : ℝ) * T' ≤ t - s :=
    (le_div_iff₀ hT').1 (Nat.floor_le (div_nonneg (by linarith) hT'.le))
  have hk2 : (t - s) / T' < k + 1 := Nat.lt_floor_add_one _
  have hb := hpow k t s hs (by linarith)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : (1 / 2 : ℝ) ^ k ≤ 2 * Real.exp (-(Real.log 2 / T' * (t - s))) := by
    have h1 : (1 / 2 : ℝ) ^ k = Real.exp (-(k * Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, _root_.one_div_pow, one_div]
    have h2 : 2 * Real.exp (-(Real.log 2 / T' * (t - s))) =
        Real.exp (Real.log 2 + -(Real.log 2 / T' * (t - s))) := by
      rw [Real.exp_add, Real.exp_log two_pos]
    rw [h1, h2]
    refine Real.exp_le_exp.2 ?_
    have h3 : Real.log 2 / T' * (t - s) = Real.log 2 * ((t - s) / T') := by ring
    rw [h3]
    nlinarith
  calc ‖Φ t s‖ ≤ K * (1 / 2) ^ k := hb
    _ ≤ K * (2 * Real.exp (-(Real.log 2 / T' * (t - s)))) := by gcongr
    _ = 2 * K * Real.exp (-(Real.log 2 / T' * (t - s))) := by ring

/-- **Uniform asymptotic stability of `ż = A(t)z` is an exponential bound on `Φ`** (MLS Theorem
4.6's hypothesis on (4.40), p. 184): the origin of `ż = A(t)z` is uniformly asymptotically
stable (MLS p. 180) if and only if `‖Φ(t, s)‖ ≤ C e^{−α(t − s)}` for `0 ≤ s ≤ t`, some `C` and
`α > 0`. The time-varying analogue of E026's
`uniformlyAsymptoticallyStable_iff_globallyExponentiallyStable`; `E` is a real Banach space. -/
theorem uniformlyAsymptoticallyStable_iff_exists_norm_le [CompleteSpace E]
    (h : IsStateTransition A Φ) :
    UniformlyAsymptoticallyStable (fun t z => A t z) 0 ↔
      ∃ C α, 0 < α ∧ ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ C * Real.exp (-(α * (t - s))) :=
  ⟨h.exists_norm_le_of_uniformlyAsymptoticallyStable, fun ⟨_, _, hα, hd⟩ =>
    (h.globallyExponentiallyStable_of_norm_le hα hd).exponentiallyStable
      |>.uniformlyAsymptoticallyStable⟩

/-- **For a linear time-varying system, uniform asymptotic stability is global exponential
stability** (MLS p. 185: "global uniform asymptotic stability of the linearization"; the notions
of pp. 180–181 for `ż = A(t)z`, eq. (4.40)), given a state-transition matrix. -/
theorem uniformlyAsymptoticallyStable_iff_globallyExponentiallyStable [CompleteSpace E]
    (h : IsStateTransition A Φ) :
    UniformlyAsymptoticallyStable (fun t z => A t z) 0 ↔
      GloballyExponentiallyStable (fun t z => A t z) 0 := by
  refine ⟨fun hL => ?_, fun hG => hG.exponentiallyStable.uniformlyAsymptoticallyStable⟩
  obtain ⟨C, α, hα, hd⟩ := h.exists_norm_le_of_uniformlyAsymptoticallyStable hL
  exact h.globallyExponentiallyStable_of_norm_le hα hd

end IsStateTransition

end Banach

/-! ### The Gramian Lyapunov function on `ℝⁿ` -/

section Gramian

variable {n : ℕ}

/-- **The Gramian of the state-transition matrix over `[t, t + T]`** (the Lyapunov function in
the proof of MLS Theorem 4.6, p. 184, with a time-varying linearization; MLS does not print it):
`gramianForm Φ T t u v = ∫_t^{t+T} (Φ(s, t)u) ⬝ (Φ(s, t)v) ds`, with the Euclidean dot product on
`ℝⁿ`. `V(t, x) = gramianForm Φ T t x x = ∫_t^{t+T} ‖Φ(s, t)x‖₂² ds`. -/
def gramianForm (Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (T t : ℝ) (u v : Fin n → ℝ) : ℝ :=
  ∫ s in t..t + T, Φ s t u ⬝ᵥ Φ s t v

/-- **The Gramian form is symmetric** (MLS Theorem 4.6, p. 184, Lyapunov function of the
proof). -/
theorem gramianForm_comm (Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (T t : ℝ)
    (u v : Fin n → ℝ) : gramianForm Φ T t u v = gramianForm Φ T t v u := by
  unfold gramianForm
  congr 1
  funext s
  exact dotProduct_comm _ _

/- The Gram matrix `(K eᵢ) ⬝ (K eⱼ)` of a linear map on `ℝⁿ`. -/
private def gramMat (K : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K (Pi.single i 1) ⬝ᵥ K (Pi.single j 1)

private theorem dotProduct_gramMat_mulVec (K : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (u v : Fin n → ℝ) : u ⬝ᵥ (gramMat K *ᵥ v) = K u ⬝ᵥ K v := by
  have hu : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hv : v = ∑ j, v j • Pi.single j (1 : ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hr : K u ⬝ᵥ K v = ∑ i, ∑ j, u i * v j * gramMat K i j := by
    conv_lhs => rw [hu, hv]
    simp only [map_sum, map_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [gramMat]
    ring
  rw [hr]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- Integration commutes with a bilinear form whose matrix has continuous entries. -/
private theorem integral_dotProduct_mulVec {G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hG : ∀ i j, Continuous fun s => G s i j) (a b : ℝ) (w w' : Fin n → ℝ) :
    ∫ s in a..b, w ⬝ᵥ (G s *ᵥ w') = w ⬝ᵥ ((fun i j => ∫ s in a..b, G s i j) *ᵥ w') := by
  have hsum : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      w ⬝ᵥ (M *ᵥ w') = ∑ i, ∑ j, w i * M i j * w' j := fun M => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum (fun i j => ∫ s in a..b, G s i j)]
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun i s => ∑ j, w i * G s i j * w' j) fun i _ =>
      (continuous_finsetSum _ fun j _ =>
        (continuous_const.mul (hG i j)).mul continuous_const).intervalIntegrable a b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun j s => w i * G s i j * w' j) fun j _ =>
      ((continuous_const.mul (hG i j)).mul continuous_const).intervalIntegrable a b]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

/- The derivative of `τ ↦ ∫_τ^{τ+T} g` for a continuous `g`. -/
private theorem hasDerivAt_integral_add {g : ℝ → ℝ} (hg : Continuous g) (T τ : ℝ) :
    HasDerivAt (fun τ => ∫ s in τ..τ + T, g s) (g (τ + T) - g τ) τ := by
  have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u + T, g s) (g (τ + T)) τ :=
    ((hg.integral_hasStrictDerivAt 0 (τ + T)).hasDerivAt).comp_add_const τ T
  have h2 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g τ) τ :=
    (hg.integral_hasStrictDerivAt 0 τ).hasDerivAt
  refine (h1.sub h2).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
  exact (intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable 0 (u + T))
    (hg.intervalIntegrable 0 u)).symm

variable {A : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}

/- The fundamental matrix `X(s) = Φ(s, 0)`, extended by `Φ(0, 0)` to `s < 0` so that it is
continuous on `ℝ`. -/
private def fundX (Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (s : ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  Φ (max s 0) 0

private theorem continuous_fundX (h : IsStateTransition A Φ) : Continuous (fundX Φ) :=
  (h.continuousOn le_rfl).comp_continuous (continuous_id.max continuous_const)
    fun s => le_max_right s 0

private theorem continuous_gramMat_fundX (h : IsStateTransition A Φ) (i j : Fin n) :
    Continuous fun s => gramMat (fundX Φ s) i j :=
  ((continuous_fundX h).clm_apply continuous_const).dotProduct
    ((continuous_fundX h).clm_apply continuous_const)

/- The Gramian of the fundamental matrix over `[τ, τ + T]`. -/
private def gramianMat (Φ : ℝ → ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (T τ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ s in τ..τ + T, gramMat (fundX Φ s) i j

/- `gramianForm` through the fundamental matrix: for `t ≥ 0`,
`∫_t^{t+T} Φ(s,t)u ⬝ Φ(s,t)v ds = (Φ(0,t)u) ⬝ G(t) (Φ(0,t)v)`. -/
private theorem gramianForm_eq (h : IsStateTransition A Φ) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (u v : Fin n → ℝ) :
    gramianForm Φ T t u v = Φ 0 t u ⬝ᵥ (gramianMat Φ T t *ᵥ Φ 0 t v) := by
  have h1 : gramianForm Φ T t u v =
      ∫ s in t..t + T, Φ 0 t u ⬝ᵥ (gramMat (fundX Φ s) *ᵥ Φ 0 t v) := by
    unfold gramianForm
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by linarith)] at hs
    have hs0 : 0 ≤ s := ht.trans hs.1
    simp only [dotProduct_gramMat_mulVec, fundX, max_eq_left hs0]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, h.mul_eq s 0 t hs0 le_rfl ht]
  rw [h1, integral_dotProduct_mulVec (continuous_gramMat_fundX h)]
  rfl

private theorem hasDerivAt_gramianMat (h : IsStateTransition A Φ) (T t : ℝ) (i j : Fin n) :
    HasDerivAt (fun τ => gramianMat Φ T τ i j)
      ((gramMat (fundX Φ (t + T)) - gramMat (fundX Φ t)) i j) t := by
  rw [Matrix.sub_apply]
  exact hasDerivAt_integral_add (continuous_gramMat_fundX h i j) T t

private theorem continuous_gramianMat (h : IsStateTransition A Φ) (T : ℝ) (i j : Fin n) :
    Continuous fun τ => gramianMat Φ T τ i j :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_gramianMat h T τ i j).continuousAt

/-- **The Gramian is bounded by the bound on `Φ`** (MLS Theorem 4.6, p. 184, time-varying
linearization; the upper bound `V ≤ α₂‖x‖²` of Theorem 4.5, p. 183): if `‖Φ(t, s)‖ ≤ K` for
`0 ≤ s ≤ t`, then `|∫_t^{t+T} Φ(s,t)u ⬝ Φ(s,t)v ds| ≤ T n K² ‖u‖ ‖v‖` for `t ≥ 0`, `T ≥ 0` (sup
norms). -/
theorem abs_gramianForm_le {T K : ℝ} (hT : 0 ≤ T)
    (hK : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ K) {t : ℝ} (ht : 0 ≤ t) (u v : Fin n → ℝ) :
    |gramianForm Φ T t u v| ≤ T * (n * K ^ 2) * ‖u‖ * ‖v‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK t t ht le_rfl)
  have hb : ∀ s ∈ uIoc t (t + T), ‖Φ s t u ⬝ᵥ Φ s t v‖ ≤ n * K ^ 2 * ‖u‖ * ‖v‖ := by
    intro s hs
    rw [uIoc_of_le (by linarith)] at hs
    have h1 : ‖Φ s t u‖ ≤ K * ‖u‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hK s t ht hs.1.le) (norm_nonneg _))
    have h2 : ‖Φ s t v‖ ≤ K * ‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hK s t ht hs.1.le) (norm_nonneg _))
    rw [Real.norm_eq_abs]
    calc |Φ s t u ⬝ᵥ Φ s t v| ≤ n * ‖Φ s t u‖ * ‖Φ s t v‖ := Control.abs_dotProduct_le _ _
      _ ≤ n * (K * ‖u‖) * (K * ‖v‖) := by gcongr
      _ = n * K ^ 2 * ‖u‖ * ‖v‖ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, show t + T - t = T by ring, abs_of_nonneg hT] at this
  unfold gramianForm
  calc _ ≤ n * K ^ 2 * ‖u‖ * ‖v‖ * T := this
    _ = T * (n * K ^ 2) * ‖u‖ * ‖v‖ := by ring

namespace IsStateTransition

/-- **The derivative of the Gramian Lyapunov function along a curve** (MLS Theorem 4.6, p. 184,
time-varying linearization; `V̇` of Theorem 4.5, p. 183): for `V(t, x) = gramianForm Φ T t x x`,
`T ≥ 0`, `t > 0` and a curve `x` with derivative `x'` at `t`,
`d/dτ V(τ, x(τ)) = 2 ∫_t^{t+T} Φ(s,t)(x' − A(t)x) ⬝ Φ(s,t)x ds + ‖Φ(t+T, t)x‖₂² − ‖x‖₂²`
at `τ = t`, with `x = x(t)`. Along a solution of `ż = A(t)z` the first term vanishes. -/
theorem hasDerivAt_gramianForm (h : IsStateTransition A Φ) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin n → ℝ} {x' : Fin n → ℝ} {t : ℝ} (ht : 0 < t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun τ => gramianForm Φ T τ (x τ) (x τ))
      (2 * gramianForm Φ T t (x' - A t (x t)) (x t) +
        (Φ (t + T) t (x t) ⬝ᵥ Φ (t + T) t (x t) - x t ⬝ᵥ x t)) t := by
  have hw : HasDerivAt (fun τ => Φ 0 τ (x τ)) (Φ 0 t (x' - A t (x t))) t := by
    have := (h.hasDerivAt_snd le_rfl ht).clm_apply hx
    convert this using 1
    simp [sub_eq_add_neg, add_comm]
  have hd := Control.hasDerivAt_dotProduct hw
    (Control.hasDerivAt_matrix_mulVec (hasDerivAt_gramianMat h T t) hw)
  refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds ht] with τ hτ
    exact gramianForm_eq h hT hτ.le _ _
  · have hX1 : fundX Φ (t + T) (Φ 0 t (x t)) = Φ (t + T) t (x t) := by
      simp only [fundX, max_eq_left (by linarith : (0 : ℝ) ≤ t + T)]
      rw [← mul_apply_eq_comp, h.mul_eq (t + T) 0 t (by linarith) le_rfl ht.le]
    have hX2 : fundX Φ t (Φ 0 t (x t)) = x t := by
      simp only [fundX, max_eq_left ht.le]
      rw [← mul_apply_eq_comp, h.mul_eq_one ht.le le_rfl, one_apply_eq_self]
    rw [Matrix.sub_mulVec, dotProduct_add, dotProduct_sub, dotProduct_gramMat_mulVec,
      dotProduct_gramMat_mulVec, hX1, hX2, ← gramianForm_eq h hT ht.le,
      ← gramianForm_eq h hT ht.le, gramianForm_comm Φ T t (x t)]
    ring

/-- **The Gramian is bounded below when `A` is bounded** (MLS Theorem 4.6, p. 184, "let `A(·)` be
bounded"; the lower bound `α₁‖x‖² ≤ V` of Theorem 4.5, p. 183): if `‖A(t)‖ ≤ M` for `t ≥ 0`
with `M ≥ 0`, then `T e^{−2MT} ‖x‖² ≤ ∫_t^{t+T} ‖Φ(s, t)x‖₂² ds` for `t ≥ 0`, `T ≥ 0` (sup norm),
by Grönwall's bound on `Φ(t, s)` backward in time. -/
theorem le_gramianForm (h : IsStateTransition A Φ) {M T : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) (hT : 0 ≤ T) {t : ℝ} (ht : 0 ≤ t) (x : Fin n → ℝ) :
    T * Real.exp (-(2 * (M * T))) * ‖x‖ ^ 2 ≤ gramianForm Φ T t x x := by
  have heq : gramianForm Φ T t x x =
      ∫ s in t..t + T, fundX Φ s (Φ 0 t x) ⬝ᵥ fundX Φ s (Φ 0 t x) := by
    unfold gramianForm
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by linarith)] at hs
    have hs0 : 0 ≤ s := ht.trans hs.1
    simp only [fundX, max_eq_left hs0]
    rw [← mul_apply_eq_comp, h.mul_eq s 0 t hs0 le_rfl ht]
  have hc : Continuous fun s => fundX Φ s (Φ 0 t x) ⬝ᵥ fundX Φ s (Φ 0 t x) :=
    ((continuous_fundX h).clm_apply continuous_const).dotProduct
      ((continuous_fundX h).clm_apply continuous_const)
  have hconst : ∫ _s in t..t + T, Real.exp (-(2 * (M * T))) * ‖x‖ ^ 2 =
      T * Real.exp (-(2 * (M * T))) * ‖x‖ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [heq, ← hconst]
  refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    (hc.intervalIntegrable _ _) fun s hs => ?_
  have hs0 : 0 ≤ s := ht.trans hs.1
  have hX : fundX Φ s (Φ 0 t x) = Φ s t x := by
    simp only [fundX, max_eq_left hs0]
    rw [← mul_apply_eq_comp, h.mul_eq s 0 t hs0 le_rfl ht]
  rw [hX]
  have h1 : ‖x‖ ≤ Real.exp (M * T) * ‖Φ s t x‖ := by
    have hxe : x = Φ t s (Φ s t x) := by
      rw [← mul_apply_eq_comp, h.mul_eq_one ht hs0, one_apply_eq_self]
    have hb := h.norm_le_exp_snd hM ht hs.1
    have hb' : Real.exp (M * (s - t)) ≤ Real.exp (M * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM0)
    calc ‖x‖ = ‖Φ t s (Φ s t x)‖ := by rw [← hxe]
      _ ≤ ‖Φ t s‖ * ‖Φ s t x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.exp (M * T) * ‖Φ s t x‖ := by gcongr; exact hb.trans hb'
  have h2 : Real.exp (-(2 * (M * T))) * ‖x‖ ^ 2 ≤ ‖Φ s t x‖ ^ 2 := by
    have he : Real.exp (-(2 * (M * T))) * Real.exp (M * T) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    have h3 : ‖x‖ ^ 2 ≤ Real.exp (M * T) ^ 2 * ‖Φ s t x‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc Real.exp (-(2 * (M * T))) * ‖x‖ ^ 2
        ≤ Real.exp (-(2 * (M * T))) * (Real.exp (M * T) ^ 2 * ‖Φ s t x‖ ^ 2) := by gcongr
      _ = ‖Φ s t x‖ ^ 2 := by rw [← mul_assoc, he, one_mul]
  exact h2.trans (Control.sq_norm_le_dotProduct_self _)

/-- **The Gramian Lyapunov function is continuous** on `[0, ∞) × ℝⁿ` (MLS Theorem 4.6, p. 184,
time-varying linearization; Theorem 4.5 asks `V` continuous), for `T ≥ 0`. -/
theorem continuousOn_gramianForm (h : IsStateTransition A Φ) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) => gramianForm Φ T p.1 p.2 p.2) (Ici 0 ×ˢ univ) := by
  have hY : Continuous fun τ => Φ 0 (max τ 0) :=
    (h.continuousOn_snd le_rfl).comp_continuous (continuous_id.max continuous_const)
      fun s => le_max_right s 0
  have hw : Continuous fun p : ℝ × (Fin n → ℝ) => Φ 0 (max p.1 0) p.2 :=
    (hY.comp continuous_fst).clm_apply continuous_snd
  have hG : Continuous fun p : ℝ × (Fin n → ℝ) => gramianMat Φ T p.1 :=
    (continuous_pi fun i => continuous_pi fun j => continuous_gramianMat h T i j).comp
      continuous_fst
  refine (hw.dotProduct (hG.matrix_mulVec hw)).continuousOn.congr fun p hp => ?_
  have hp0 : 0 ≤ p.1 := hp.1
  simp only [max_eq_left hp0]
  exact gramianForm_eq h hT hp0 _ _

/-- **The fourth bound of MLS Theorem 4.5 (p. 183), `‖∂V/∂x‖ ≤ α₄‖x‖`, for the Gramian Lyapunov
function of a linear time-varying system** (the Lyapunov function of Theorem 4.6, p. 184): if
`‖Φ(t, s)‖ ≤ K` for `0 ≤ s ≤ t`, then for `t ≥ 0`, `T ≥ 0` and every `y`, `x ↦ V(t, x)` has a
Fréchet derivative `D` at `y` with `‖D‖ ≤ 2 T n K² ‖y‖` (operator norm of the sup norm). -/
theorem exists_hasFDerivAt_gramianForm (h : IsStateTransition A Φ) {T K : ℝ} (hT : 0 ≤ T)
    (hK : ∀ t s, 0 ≤ s → s ≤ t → ‖Φ t s‖ ≤ K) {t : ℝ} (ht : 0 ≤ t) (y : Fin n → ℝ) :
    ∃ D : (Fin n → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun z => gramianForm Φ T t z z) D y ∧
      ‖D‖ ≤ 2 * (T * (n * K ^ 2)) * ‖y‖ := by
  set κ := T * (n * K ^ 2) with hκ
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK t t ht le_rfl)
  have hκ0 : 0 ≤ κ := by positivity
  let B₀ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => gramianForm Φ T t u v)
      (fun u u' v => by
        simp only [gramianForm_eq h hT ht, map_add, add_dotProduct])
      (fun c u v => by
        simp only [gramianForm_eq h hT ht, map_smul, smul_dotProduct])
      (fun u v v' => by
        simp only [gramianForm_eq h hT ht, map_add, Matrix.mulVec_add, dotProduct_add])
      (fun c u v => by
        simp only [gramianForm_eq h hT ht, map_smul, Matrix.mulVec_smul, dotProduct_smul])
  have hB₀ : ∀ u v, ‖B₀ u v‖ ≤ κ * ‖u‖ * ‖v‖ := fun u v => by
    rw [Real.norm_eq_abs]
    exact abs_gramianForm_le hT hK ht u v
  set B := B₀.mkContinuous₂ κ hB₀ with hB
  have hBapp : ∀ u v, B u v = gramianForm Φ T t u v := fun u v => rfl
  have hD := B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
  refine ⟨(ContinuousLinearMap.precompR (Fin n → ℝ) B) y (ContinuousLinearMap.id ℝ _) +
    (ContinuousLinearMap.precompL (Fin n → ℝ) B) (ContinuousLinearMap.id ℝ _) y, ?_, ?_⟩
  · simpa only [hBapp, id] using hD
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    simp only [_root_.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_id', id_eq,
      hBapp, Real.norm_eq_abs]
    calc |gramianForm Φ T t y z + gramianForm Φ T t z y|
        ≤ |gramianForm Φ T t y z| + |gramianForm Φ T t z y| := abs_add_le _ _
      _ ≤ κ * ‖y‖ * ‖z‖ + κ * ‖z‖ * ‖y‖ :=
          add_le_add (abs_gramianForm_le hT hK ht y z) (abs_gramianForm_le hT hK ht z y)
      _ = 2 * κ * ‖y‖ * ‖z‖ := by ring

end IsStateTransition

end Gramian

end Stability
end RoboLean
