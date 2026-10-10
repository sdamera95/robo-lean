import RoboLean.Control.LaSalle
import RoboLean.Control.ErrorDynamics

/-!
# The damped harmonic oscillator (MLS Example 4.5, printed pp. 185–187)

**What MLS prints.** The spring–mass–damper of Figure 4.8 obeys `M q̈ + B q̇ + K q = 0` (4.41)
with `M, B, K` all positive, written on the state `x = (q, q̇)` as
`d/dt (q, q̇) = (q̇, −(K/M) q − (B/M) q̇)` (4.42). MLS reads off the eigenvalues of the Jacobian
that "the system is (globally) exponentially stable". It then takes the energy
`V = ½ M q̇² + ½ K q²` (4.43), computes `V̇ = −B q̇²` (4.44), observes that `−V̇` is not locally
positive definite, and remarks: "It is still possible to conclude asymptotic stability using
Lasalle's invariance principle (described in the next section), but this is obviously
conservative since we already know that the system is exponentially stable." It finally skews
the energy to obtain exponential stability from Lyapunov's direct method.

**What is proved here.**

* the field (4.42) as a continuous linear map (`oscillatorMap`), the energy (4.43) and the rate
  (4.44), and that the rate is the derivative of the energy along every solution
  (`hasDerivAlongSolutions_oscillatorEnergy`);
* MLS's Lasalle remark, with the unskewed energy: the largest invariant set inside
  `{V ≤ c, V̇ = 0}` is contained in `{0}` (`oscillator_largestInvariantSubset`), so the origin is
  asymptotically stable (`asymptoticallyStableAt_oscillator`) and every solution converges to it
  (`tendsto_oscillator`), through `Stability.asymptoticallyStableAt_of_lasalle` and
  `Stability.lasalle_isSolution`;
* MLS's "(globally) exponentially stable" (`globallyExponentiallyStable_oscillator`), obtained not
  from the eigenvalues but from the error system of Proposition 4.8 (MLS (4.50), p. 191) at
  `n = 1` with unit inertia, i.e. after division by `M`, with `K_p = K/M` and `K_v = B/M`; that
  theorem uses the skewed energy of this example. The bridge is the coordinate identification
  `oscillatorEmbed`, which preserves the norm.

**Carrier.** The state space is `ℝ × ℝ` with `x = (q, q̇)`, `x.1 = q`, `x.2 = q̇`, and Mathlib's
norm on a product, the maximum of the absolute values of the two components (sup norm). The
system is time-invariant and is written `fun _ => oscillatorMap M B K` (time first, ignored), as
in `RoboLean.Stability`.

These are instances of the general theorems of `RoboLean.Control`, showing that their hypotheses
can be met; they are not claims about a physical spring, mass or damper.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean.Examples

/-- **The linear field of the damped harmonic oscillator, MLS Example 4.5, eq. (4.42),
printed p. 186:** `(q, q̇) ↦ (q̇, −(K/M) q − (B/M) q̇)`, a continuous linear map on the state
space `ℝ × ℝ` with state `(q, q̇)` (sup norm). -/
def oscillatorMap (M B K : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-(K / M)) • ContinuousLinearMap.fst ℝ ℝ ℝ - (B / M) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- **The field (4.42) of MLS Example 4.5 (printed p. 186), pointwise**, on the state
`x = (q, q̇)`: `oscillatorMap M B K x = (q̇, −(K/M) q − (B/M) q̇)`. -/
theorem oscillatorMap_apply (M B K : ℝ) (x : ℝ × ℝ) :
    oscillatorMap M B K x = (x.2, -(K / M) * x.1 - (B / M) * x.2) := by
  simp [oscillatorMap, smul_eq_mul]

/-- **The energy of the oscillator, MLS Example 4.5, eq. (4.43), printed p. 186:**
`V(q, q̇) = ½ M q̇² + ½ K q²` on the state `x = (q, q̇)`, time-invariant. -/
def oscillatorEnergy (M K : ℝ) (x : ℝ × ℝ) : ℝ :=
  (1 / 2) * M * x.2 ^ 2 + (1 / 2) * K * x.1 ^ 2

/-- **The rate of the energy along the oscillator, MLS Example 4.5, eq. (4.44), printed p. 186:**
`V̇(q, q̇) = −B q̇²` on the state `x = (q, q̇)`, time-invariant. -/
def oscillatorEnergyRate (B : ℝ) (x : ℝ × ℝ) : ℝ :=
  -(B * x.2 ^ 2)

/-- **MLS Example 4.5, eq. (4.44), printed p. 186:** along every solution of (4.42), the energy
(4.43) has the derivative `V̇ = M q̇ q̈ + K q q̇ = −B q̇²`, on the whole state space. State
`(q, q̇)`; `M ≠ 0` is needed to cancel the division by `M` in (4.42). -/
theorem hasDerivAlongSolutions_oscillatorEnergy {M B K : ℝ} (hM : M ≠ 0) :
    Stability.HasDerivAlongSolutions (fun _ => oscillatorMap M B K)
      (fun _ => oscillatorEnergy M K) (fun _ => oscillatorEnergyRate B) Set.univ := by
  intro t₀ _ x hx t ht _
  have hd := hx.2 t ht
  have h1 : HasDerivAt (fun s => (x s).1) (oscillatorMap M B K (x t)).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have h2 : HasDerivAt (fun s => (x s).2) (oscillatorMap M B K (x t)).2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  rw [oscillatorMap_apply] at h1 h2
  have h := ((h2.pow 2).const_mul ((1 / 2) * M)).add ((h1.pow 2).const_mul ((1 / 2) * K))
  convert h using 1
  · funext s
    simp only [oscillatorEnergy, Pi.add_apply, Pi.pow_apply]
  · simp only [oscillatorEnergyRate]
    field_simp
    ring

/-- The rate (4.44) vanishes exactly where `q̇ = 0`, for `B ≠ 0`. -/
private lemma oscillatorEnergyRate_eq_zero {B : ℝ} (hB : B ≠ 0) {x : ℝ × ℝ}
    (h : oscillatorEnergyRate B x = 0) : x.2 = 0 := by
  simp only [oscillatorEnergyRate, neg_eq_zero, mul_eq_zero, hB, false_or] at h
  exact pow_eq_zero_iff two_ne_zero |>.mp h

/-- **The invariant-set step of MLS Example 4.5 (printed p. 186, "using Lasalle's invariance
principle"; the same argument as Example 4.7, p. 189):** for positive `M, B, K` and every level
`c`, the largest invariant set (Definition 4.8, p. 188) of the flow `exp(t A)` of (4.42) inside
`S = {V ≤ c, V̇ = 0}` lies in `{0}`. On it `q̇ ≡ 0`, hence `q̈ = −(K/M) q = 0`, so `q = 0` for
`t > 0`, and the starting point is the limit as `t → 0⁺`. State `(q, q̇)`, sup norm. -/
theorem oscillator_largestInvariantSubset {M B K c : ℝ} (hM : 0 < M) (hB : 0 < B) (hK : 0 < K) :
    Stability.largestInvariantSubset (fun t x => NormedSpace.exp (t • oscillatorMap M B K) x)
      {y | oscillatorEnergy M K y ≤ c ∧ oscillatorEnergyRate B y = 0} ⊆ {0} := by
  set A := oscillatorMap M B K
  have hfl := Stability.hasFlow_linear A
  intro y hy
  rw [Stability.mem_largestInvariantSubset_iff hfl] at hy
  set γ : ℝ → ℝ × ℝ := fun t => NormedSpace.exp (t • A) y
  have hv : ∀ t, 0 ≤ t → (γ t).2 = 0 := fun t ht =>
    oscillatorEnergyRate_eq_zero hB.ne' (hy t ht).2
  have hpos : ∀ t, 0 < t → γ t = 0 := by
    intro t ht
    have hd : HasDerivAt γ (A (γ t)) t := (hfl.isSolution y).2 t ht
    have h2 : HasDerivAt (fun s => (γ s).2) (A (γ t)).2 t :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
    have h0 : HasDerivAt (fun s => (γ s).2) 0 t := by
      refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds ht] with s hs
      exact hv s hs.le
    have heq := h2.unique h0
    rw [oscillatorMap_apply, hv t ht.le] at heq
    have hq : (γ t).1 = 0 := by
      have hKM : K / M ≠ 0 := div_ne_zero hK.ne' hM.ne'
      have : -(K / M) * (γ t).1 = 0 := by linarith
      simpa [hKM] using this
    exact Prod.ext hq (hv t ht.le)
  have hc : ContinuousWithinAt γ (Ioi 0) 0 :=
    ((hfl.continuousOn_trajectory y).continuousWithinAt self_mem_Ici).mono Ioi_subset_Ici_self
  have hy0 : γ 0 = y := hfl.map_zero y
  rw [ContinuousWithinAt, hy0] at hc
  have hlim : Tendsto γ (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hpos t ht).symm)
  exact tendsto_nhds_unique hc hlim

private lemma continuous_oscillatorEnergy (M K : ℝ) : Continuous (oscillatorEnergy M K) := by
  unfold oscillatorEnergy
  fun_prop

private lemma continuous_oscillatorEnergyRate (B : ℝ) : Continuous (oscillatorEnergyRate B) := by
  unfold oscillatorEnergyRate
  fun_prop

private lemma oscillatorEnergyRate_nonpos {B : ℝ} (hB : 0 < B) (x : ℝ × ℝ) :
    oscillatorEnergyRate B x ≤ 0 :=
  neg_nonpos.mpr (mul_nonneg hB.le (sq_nonneg _))

/-- The energy (4.43) dominates `(min M K / 2) ‖x‖²` in the sup norm. -/
private lemma mul_sq_norm_le_oscillatorEnergy {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (x : ℝ × ℝ) :
    min M K / 2 * ‖x‖ ^ 2 ≤ oscillatorEnergy M K x := by
  have hn := Control.sq_norm_prod_le x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at hn
  have h1 := min_le_left M K
  have h2 := min_le_right M K
  have hm : 0 ≤ min M K := le_min hM.le hK.le
  unfold oscillatorEnergy
  nlinarith [sq_nonneg x.1, sq_nonneg x.2, mul_le_mul_of_nonneg_left hn hm,
    mul_le_mul_of_nonneg_right h1 (sq_nonneg x.2), mul_le_mul_of_nonneg_right h2 (sq_nonneg x.1)]

private lemma locallyPositiveDefinite_oscillatorEnergy {M K : ℝ} (hM : 0 < M) (hK : 0 < K) :
    Stability.LocallyPositiveDefinite (fun _ => oscillatorEnergy M K) := by
  refine ⟨((continuous_oscillatorEnergy M K).comp continuous_snd).continuousOn, 1, one_pos,
    fun r => min M K / 2 * r ^ 2, Stability.isClassK_mul_sq (by positivity), fun _ _ => ?_⟩
  refine ⟨by simp [oscillatorEnergy], fun x _ => mul_sq_norm_le_oscillatorEnergy hM hK x⟩

private lemma isCompact_oscillatorEnergy_le {M K : ℝ} (hM : 0 < M) (hK : 0 < K) (c : ℝ) :
    IsCompact {x | oscillatorEnergy M K x ≤ c} := by
  have hm : 0 < min M K := lt_min hM hK
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_oscillatorEnergy M K) continuous_const)
    ((Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1 + 2 * c / min M K)).subset ?_)
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hb := (mul_sq_norm_le_oscillatorEnergy hM hK x).trans hx
  have hsq : ‖x‖ ^ 2 ≤ 2 * c / min M K := by
    rw [le_div_iff₀ hm]
    linarith
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- **MLS Example 4.5 (printed p. 186), "It is still possible to conclude asymptotic stability
using Lasalle's invariance principle":** for positive `M, B, K` the origin of (4.42) is
asymptotically stable (Definition 4.2, p. 180) at every initial time `t₀ ≥ 0`. Proved by
Theorem 4.7 (p. 188, `Stability.asymptoticallyStableAt_of_lasalle`) with the energy (4.43), its
rate (4.44), the level `c = 1` and the flow `exp(t A)`. State `(q, q̇)`, sup norm. -/
theorem asymptoticallyStableAt_oscillator {M B K : ℝ} (hM : 0 < M) (hB : 0 < B) (hK : 0 < K)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.AsymptoticallyStableAt (fun _ => oscillatorMap M B K) 0 t₀ :=
  Stability.asymptoticallyStableAt_of_lasalle (Stability.hasFlow_linear (oscillatorMap M B K))
    one_pos (locallyPositiveDefinite_oscillatorEnergy hM hK) (isCompact_oscillatorEnergy_le hM hK 1)
    ((hasDerivAlongSolutions_oscillatorEnergy hM.ne').mono (subset_univ _))
    (continuous_oscillatorEnergyRate B).continuousOn
    (fun y _ => oscillatorEnergyRate_nonpos hB y)
    (oscillator_largestInvariantSubset hM hB hK) ht₀

/-- **Every solution of the oscillator converges to the origin** (MLS Example 4.5, printed
p. 186, by Lasalle's principle, Theorem 4.7, p. 188, in its global form): for positive `M, B, K`,
every solution of (4.42) from `t₀ ≥ 0` tends to `0` as `t → ∞`. Proved by
`Stability.lasalle_isSolution` with the energy (4.43) and the level `c = V(x(t₀)) + 1`. State
`(q, q̇)`, sup norm. -/
theorem tendsto_oscillator {M B K : ℝ} (hM : 0 < M) (hB : 0 < B) (hK : 0 < K) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) {x : ℝ → ℝ × ℝ}
    (hx : Stability.IsSolution (fun _ => oscillatorMap M B K) t₀ x) :
    Filter.Tendsto x Filter.atTop (nhds 0) := by
  refine tendsto_nhds.mpr fun U hU h0U => ?_
  exact Stability.lasalle_isSolution (Stability.hasFlow_linear (oscillatorMap M B K))
    (c := oscillatorEnergy M K (x t₀) + 1) (continuous_oscillatorEnergy M K)
    (isCompact_oscillatorEnergy_le hM hK _)
    ((hasDerivAlongSolutions_oscillatorEnergy hM.ne').mono (subset_univ _))
    (continuous_oscillatorEnergyRate B).continuousOn
    (fun y _ => oscillatorEnergyRate_nonpos hB y) ht₀ hx (lt_add_one _) hU
    ((oscillator_largestInvariantSubset hM hB hK).trans (singleton_subset_iff.mpr h0U))

/-- **The coordinate identification of (4.42) with the error system (4.50) at `n = 1`** (MLS
Example 4.5, p. 186, and the proof of Proposition 4.8, p. 191): the state `(q, q̇) ∈ ℝ × ℝ` as
the pair of one-component vectors `(e, ė) ∈ (Fin 1 → ℝ) × (Fin 1 → ℝ)`, `e = (q)`, `ė = (q̇)`. -/
def oscillatorEmbed : ℝ × ℝ →L[ℝ] (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.snd ℝ ℝ ℝ)

private lemma oscillatorEmbed_apply (z : ℝ × ℝ) :
    oscillatorEmbed z = (fun _ => z.1, fun _ => z.2) := rfl

/-- **`oscillatorEmbed` preserves the norm** (MLS p. 191, at `n = 1`): the sup norm of `(q, q̇)`
on `ℝ × ℝ` equals the norm of `((q), (q̇))` on `(Fin 1 → ℝ) × (Fin 1 → ℝ)`, the maximum of the
two sup norms. -/
theorem norm_oscillatorEmbed (z : ℝ × ℝ) : ‖oscillatorEmbed z‖ = ‖z‖ := by
  rw [oscillatorEmbed_apply, Prod.norm_def, Prod.norm_def, pi_norm_const, pi_norm_const]

/-- **The oscillator (4.42) is the error system (4.50) with `K_p = K/M`, `K_v = B/M` at `n = 1`**
(MLS Example 4.5, p. 186, and the proof of Proposition 4.8, p. 191), i.e. (4.41) divided by `M`:
`errorField !![K/M] !![B/M]` composed with `oscillatorEmbed` is `oscillatorEmbed` composed with
`oscillatorMap M B K`. State `(q, q̇)` and `(e, ė)`, `e` first; the time argument of
`errorField` is ignored. -/
theorem errorField_comp_oscillator (M B K : ℝ) (z : ℝ × ℝ) :
    Control.errorField !![K / M] !![B / M] 0 (oscillatorEmbed z) =
      oscillatorEmbed (oscillatorMap M B K z) := by
  rw [oscillatorEmbed_apply, oscillatorEmbed_apply, oscillatorMap_apply]
  simp only [Control.errorField, Prod.mk.injEq, true_and]
  funext i
  fin_cases i
  simp [dotProduct]
  ring

private lemma posDef_one_by_one {a : ℝ} (ha : 0 < a) :
    (!![a] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  have h : (!![a] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal ![a] := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h]
  exact Matrix.PosDef.diagonal fun i => by fin_cases i; exact ha

/-- **MLS Example 4.5 (printed p. 186): "the system is (globally) exponentially stable".** For
positive `M, B, K` the origin of (4.42) is globally exponentially stable (Definition 4.3, global
form, p. 181) on the state `(q, q̇)` with the sup norm. MLS argues from the eigenvalues; the proof
here transports `Control.globallyExponentiallyStable_errorField` (Proposition 4.8, p. 192, whose
proof uses the skewed energy of this example) at `n = 1`, `K_p = K/M`, `K_v = B/M`, through the
norm-preserving `oscillatorEmbed`. -/
theorem globallyExponentiallyStable_oscillator {M B K : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hK : 0 < K) : Stability.GloballyExponentiallyStable (fun _ => oscillatorMap M B K) 0 := by
  obtain ⟨m, hm, α, hα, h⟩ := Control.globallyExponentiallyStable_errorField
    (posDef_one_by_one (div_pos hK hM)) (posDef_one_by_one (div_pos hB hM))
  refine ⟨m, hm, α, hα, fun t₀ ht₀ x hx t ht => ?_⟩
  have hy : Stability.IsSolution (Control.errorField !![K / M] !![B / M] (n := 1)) t₀
      (fun s => oscillatorEmbed (x s)) := by
    refine ⟨oscillatorEmbed.continuous.comp_continuousOn hx.1, fun s hs => ?_⟩
    have hd := oscillatorEmbed.hasFDerivAt.comp_hasDerivAt s (hx.2 s hs)
    have he := errorField_comp_oscillator M B K (x s)
    exact he ▸ hd
  have hb := h t₀ ht₀ _ hy t ht
  simpa only [sub_zero, norm_oscillatorEmbed] using hb

end RoboLean.Examples
