import RoboLean.Control.LaSalleLocal
import RoboLean.Control.GlobalFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The nonlinear spring–mass system with damper (MLS Examples 4.6 and 4.7, printed pp. 187–189)

**What MLS prints.** Example 4.6 (p. 187): a unit mass on a nonlinear spring with a
velocity-dependent damper, with position `x₁` and velocity `x₂`, obeys
`ẋ₁ = x₂`, `ẋ₂ = −f(x₂) − g(x₁)` (4.45), where `f` and `g` are smooth and passive:
`σ f(σ) ≥ 0` and `σ g(σ) ≥ 0` for `σ ∈ [−σ₀, σ₀]`, "and equality is only achieved when `σ = 0`".
With `V(x) = x₂²/2 + ∫₀^{x₁} g(σ) dσ`, "the passivity of `g` guarantees that `V(x)` is a locally
positive definite function", and "a short calculation verifies that `V̇(x) = −x₂ f(x₂) ≤ 0` when
`|x₂| ≤ σ₀`" (p. 188), which "establishes the stability, but not the asymptotic stability of the
origin". Example 4.7 (p. 189) chooses `c = min(V(−σ₀, 0), V(σ₀, 0))`, states `V̇ ≤ 0` on
`Ω_c = {V ≤ c}`, and finds that the largest invariant set inside `Ω_c ∩ {V̇ = 0}` is the origin:
`x₂ ≡ 0` forces `x₁ ≡ x₁₀` and `0 = −f(0) − g(x₁₀)`, so `g(x₁₀) = 0` and `x₁₀ = 0`; by Lasalle's
principle (Theorem 4.7, p. 188) the origin is locally asymptotically stable.

**What is proved here.**

* the field (4.45) (`springField`), the energy `V` (`springEnergy`, with the potential
  `springPotential`) and its rate `V̇ = −x₂ f(x₂)` (`springEnergyRate`), and that the rate is the
  derivative of the energy along every solution, for continuous `g`
  (`hasDerivAlongSolutions_springEnergy`);
* passivity on `[−σ₀, σ₀]` (`IsPassiveOn`); MLS uses `f(0) = 0` and `g(0) = 0` tacitly on p. 189;
  here they are derived from continuity and passivity (`IsPassiveOn.apply_zero`);
* `V` locally positive definite (`locallyPositiveDefinite_springEnergy`) and Example 4.6's
  stability (`stableAt_spring`, by Theorem 4.4(1); no flow needed);
* Example 4.7's invariant-set step (`spring_largestInvariantSubset`) and asymptotic stability
  (`asymptoticallyStableAt_spring`), under a flow hypothesis `HasFlow`;
* for Lipschitz `f, g` the flow is constructed (`lipschitzWith_springField`,
  `asymptoticallyStableAt_spring_of_lipschitz`), and the damped pendulum `f = id`, `g = sin`,
  `σ₀ = 1` is an instance with every hypothesis discharged
  (`asymptoticallyStableAt_dampedPendulum`).

**Departures from the printed text.**

* A general nonlinear spring field is not globally Lipschitz (for example `g(σ) = σ³`), so the
  existence of a forward flow does not follow from `GlobalFlow`; the flow is a hypothesis
  (`HasFlow`) in general and is constructed only for Lipschitz `f, g`. MLS's "smooth" is replaced by
  continuity, which is all the proofs use.
* MLS's `c = min(V(−σ₀, 0), V(σ₀, 0))` with `Ω_c = {V ≤ c}` is replaced by the local Lasalle
  theorem `Stability.asymptoticallyStableAt_of_lasalle_ball` on the ball of radius `σ₀`. This is an
  inference about the printed text, not something proved here: when passivity holds only on
  `[−σ₀, σ₀]`, `∫₀^{x₁} g` may become negative far from the origin, so `{V ≤ c}` need not be
  bounded (hence not compact), and it can contain points with `|x₂| > σ₀`, where `V̇ ≤ 0` is not
  available.

**Carrier.** The state is `x = (x₁, x₂) ∈ ℝ × ℝ`, `x.1` the position and `x.2` the velocity, with
Mathlib's sup norm `‖x‖ = max |x₁| |x₂|`. The system is time-invariant and is written
`fun _ => springField f g` (time first, ignored), as in `RoboLean.Stability`. These are instances of
the general theorems of `RoboLean.Control`; they are not claims about a physical spring or damper.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean.Examples

variable {f g h : ℝ → ℝ} {σ₀ : ℝ}

/-- **The nonlinear spring–mass–damper field, MLS Example 4.6, eq. (4.45), printed p. 187:**
`(x₁, x₂) ↦ (x₂, −f(x₂) − g(x₁))` on the state `x = (x₁, x₂)` (position, velocity), where `f` is
the damper friction and `g` the spring restoring force. -/
def springField (f g : ℝ → ℝ) : ℝ × ℝ → ℝ × ℝ := fun x => (x.2, -f x.2 - g x.1)

/-- **The spring potential `∫₀^{x₁} g(σ) dσ`** of MLS Example 4.6 (printed p. 188), as an interval
integral in the position `x₁`. -/
def springPotential (g : ℝ → ℝ) (x₁ : ℝ) : ℝ := ∫ σ in (0 : ℝ)..x₁, g σ

/-- **The Lyapunov function of MLS Example 4.6 (printed p. 188):**
`V(x) = x₂²/2 + ∫₀^{x₁} g(σ) dσ` on the state `x = (x₁, x₂)`, time-invariant. -/
def springEnergy (g : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := x.2 ^ 2 / 2 + springPotential g x.1

/-- **The rate of the Lyapunov function of MLS Example 4.6 (printed p. 188):**
`V̇(x) = −x₂ f(x₂)` on the state `x = (x₁, x₂)`, time-invariant. -/
def springEnergyRate (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := -(x.2 * f x.2)

/-- **Passivity on `[−σ₀, σ₀]`, MLS Example 4.6, printed p. 187:** `σ h(σ) ≥ 0` for
`|σ| ≤ σ₀`, with equality there only at `σ = 0`. -/
def IsPassiveOn (h : ℝ → ℝ) (σ₀ : ℝ) : Prop :=
  ∀ σ, |σ| ≤ σ₀ → 0 ≤ σ * h σ ∧ (σ * h σ = 0 → σ = 0)

/-! ### Passivity -/

/-- A passive function is positive on `(0, σ₀]` (MLS p. 187). -/
private lemma IsPassiveOn.pos_of_pos (hp : IsPassiveOn h σ₀) {σ : ℝ} (h0 : 0 < σ)
    (h1 : σ ≤ σ₀) : 0 < h σ := by
  obtain ⟨hn, hz⟩ := hp σ (by rw [abs_of_pos h0]; exact h1)
  have hne : σ * h σ ≠ 0 := fun he => h0.ne' (hz he)
  exact pos_of_mul_pos_right (lt_of_le_of_ne hn (Ne.symm hne)) h0.le

/-- A passive function is negative on `[−σ₀, 0)` (MLS p. 187). -/
private lemma IsPassiveOn.neg_of_neg (hp : IsPassiveOn h σ₀) {σ : ℝ} (h0 : σ < 0)
    (h1 : -σ₀ ≤ σ) : h σ < 0 := by
  obtain ⟨hn, hz⟩ := hp σ (by rw [abs_of_neg h0]; linarith)
  have hne : σ * h σ ≠ 0 := fun he => h0.ne (hz he)
  have hp' : 0 < σ * h σ := lt_of_le_of_ne hn (Ne.symm hne)
  by_contra hc
  push Not at hc
  nlinarith

/-- **A continuous passive function vanishes at `0`** (MLS Example 4.7, printed p. 189, uses
`f(0) = 0` and `g(0) = 0` without comment). From passivity on `[−σ₀, σ₀]` with `σ₀ > 0`, `h > 0`
on `(0, σ₀]` and `h < 0` on `[−σ₀, 0)`; continuity at `0` gives `h(0) = 0`. -/
theorem IsPassiveOn.apply_zero (hc : Continuous h) (hp : IsPassiveOn h σ₀) (hσ₀ : 0 < σ₀) :
    h 0 = 0 := by
  have h1 : 0 ≤ h 0 := by
    refine ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto h (𝓝[>] 0) (𝓝 (h 0))) ?_
    filter_upwards [Ioo_mem_nhdsGT hσ₀] with σ hσ
    exact (hp.pos_of_pos hσ.1 hσ.2.le).le
  have h2 : h 0 ≤ 0 := by
    refine le_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto h (𝓝[<] 0) (𝓝 (h 0))) ?_
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hσ₀)] with σ hσ
    exact (hp.neg_of_neg hσ.2 hσ.1.le).le
  linarith

/-! ### The energy and its rate -/

/-- The fundamental theorem of calculus for the spring potential (MLS p. 188). -/
private lemma hasDerivAt_springPotential (hg : Continuous g) (x : ℝ) :
    HasDerivAt (springPotential g) (g x) x :=
  (hg.integral_hasStrictDerivAt 0 x).hasDerivAt

private lemma continuous_springPotential (hg : Continuous g) : Continuous (springPotential g) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_springPotential hg x).continuousAt

private lemma springPotential_zero : springPotential g 0 = 0 := by
  simp [springPotential]

private lemma continuous_springEnergy (hg : Continuous g) : Continuous (springEnergy g) :=
  ((continuous_snd.pow 2).div_const 2).add ((continuous_springPotential hg).comp continuous_fst)

private lemma continuous_springEnergyRate (hf : Continuous f) :
    Continuous (springEnergyRate f) :=
  (continuous_snd.mul (hf.comp continuous_snd)).neg

/-- **MLS Example 4.6, printed p. 188, "a short calculation verifies that `V̇(x) = −x₂ f(x₂)`":**
for continuous `g`, along every solution of (4.45) the energy `V(x) = x₂²/2 + ∫₀^{x₁} g` has the
derivative `x₂ (−f(x₂) − g(x₁)) + g(x₁) x₂ = −x₂ f(x₂)`, on the whole state space (fundamental
theorem of calculus for the potential). State `(x₁, x₂)`, system `fun _ => springField f g`. -/
theorem hasDerivAlongSolutions_springEnergy (hg : Continuous g) :
    Stability.HasDerivAlongSolutions (fun _ => springField f g) (fun _ => springEnergy g)
      (fun _ => springEnergyRate f) univ := by
  intro t₀ _ x hx t ht _
  have hd := hx.2 t ht
  have h1 : HasDerivAt (fun s => (x s).1) (x t).2 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have h2 : HasDerivAt (fun s => (x s).2) (-f (x t).2 - g (x t).1) t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have h := ((h2.pow 2).div_const 2).add ((hasDerivAt_springPotential hg (x t).1).comp t h1)
  convert h using 1
  · funext s
    simp only [springEnergy, Pi.add_apply, Pi.pow_apply, Function.comp_apply]
  · show -((x t).2 * f (x t).2) = _
    push_cast
    ring

/-! ### Local positive definiteness -/

/-- A function that is continuous, strictly increasing and zero at `0` on `[0, σ₀]`, extended
past `σ₀` by adding `r − σ₀`, is a comparison function (MLS Definition 4.4, p. 182). -/
private lemma isClassK_extend {a : ℝ → ℝ} (hσ₀ : 0 < σ₀) (hc : ContinuousOn a (Icc 0 σ₀))
    (hm : StrictMonoOn a (Icc 0 σ₀)) (h0 : a 0 = 0) :
    Stability.IsClassK fun r => a (min r σ₀) + max (r - σ₀) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.add (hc.comp (continuous_id.min continuous_const).continuousOn ?_)
      ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    intro r hr
    exact ⟨le_min hr hσ₀.le, min_le_right _ _⟩
  · intro r hr s hs hrs
    have hr' : (0 : ℝ) ≤ r := hr
    rcases le_or_gt s σ₀ with hsσ | hsσ
    · have hrσ : r ≤ σ₀ := hrs.le.trans hsσ
      simp only [min_eq_left hsσ, min_eq_left hrσ, max_eq_right (sub_nonpos.mpr hsσ),
        max_eq_right (sub_nonpos.mpr hrσ), add_zero]
      exact hm ⟨hr', hrσ⟩ ⟨hr'.trans hrs.le, hsσ⟩ hrs
    · have h1 : a (min r σ₀) ≤ a (min s σ₀) := by
        rw [min_eq_right hsσ.le]
        exact hm.monotoneOn ⟨le_min hr' hσ₀.le, min_le_right _ _⟩ ⟨hσ₀.le, le_rfl⟩
          (min_le_right _ _)
      have h2 : max (r - σ₀) 0 < max (s - σ₀) 0 := by
        rw [max_eq_left (by linarith : 0 ≤ s - σ₀)]
        exact max_lt (by linarith) (by linarith)
      linarith
  · show a (min 0 σ₀) + max (0 - σ₀) 0 = 0
    rw [min_eq_left hσ₀.le, max_eq_right (by linarith), h0, add_zero]

private lemma strictMonoOn_min {a b : ℝ → ℝ} {D : Set ℝ} (ha : StrictMonoOn a D)
    (hb : StrictMonoOn b D) : StrictMonoOn (fun s => min (a s) (b s)) D :=
  fun _ hx _ hy hxy => min_lt_min (ha hx hy hxy) (hb hx hy hxy)

/-- The potential is strictly increasing on `[0, σ₀]` (its derivative `g` is positive inside). -/
private lemma strictMonoOn_springPotential (hg : Continuous g) (hgp : IsPassiveOn g σ₀) :
    StrictMonoOn (springPotential g) (Icc 0 σ₀) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 σ₀) (continuous_springPotential hg).continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_springPotential hg x).deriv]
  exact hgp.pos_of_pos hx.1 hx.2.le

/-- `r ↦ ∫₀^{−r} g` is strictly increasing on `[0, σ₀]` (its derivative `−g(−r)` is positive). -/
private lemma strictMonoOn_springPotential_neg (hg : Continuous g) (hgp : IsPassiveOn g σ₀) :
    StrictMonoOn (fun s => springPotential g (-s)) (Icc 0 σ₀) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 σ₀)
    ((continuous_springPotential hg).comp continuous_neg).continuousOn fun x hx => ?_
  rw [interior_Icc] at hx
  have hd : HasDerivAt (fun s => springPotential g (-s)) (g (-x) * (-1)) x :=
    (hasDerivAt_springPotential hg (-x)).comp x (hasDerivAt_neg x)
  rw [hd.deriv]
  have := hgp.neg_of_neg (neg_lt_zero.mpr hx.1) (neg_le_neg hx.2.le)
  linarith

/-- **MLS Example 4.6, printed p. 188: "The passivity of `g` guarantees that `V(x)` is a locally
positive definite function"** (Definition 4.4, p. 182). For continuous `g`, passive on
`[−σ₀, σ₀]` with `σ₀ > 0`, the energy `V(x) = x₂²/2 + ∫₀^{x₁} g` satisfies `α(‖x‖) ≤ V(x)` for
`‖x‖ < σ₀` with the comparison function
`α(r) = min(r²/2, ∫₀^{ρ} g, ∫₀^{−ρ} g) + max(r − σ₀, 0)`, `ρ = min(r, σ₀)`. State `(x₁, x₂)`,
sup norm. -/
theorem locallyPositiveDefinite_springEnergy (hg : Continuous g) (hσ₀ : 0 < σ₀)
    (hgp : IsPassiveOn g σ₀) : Stability.LocallyPositiveDefinite (fun _ => springEnergy g) := by
  set G := springPotential g with hGdef
  have hGc : Continuous G := continuous_springPotential hg
  set m : ℝ → ℝ := fun s => min (G s) (G (-s)) with hmdef
  have hmm : StrictMonoOn m (Icc 0 σ₀) :=
    strictMonoOn_min (strictMonoOn_springPotential hg hgp)
      (strictMonoOn_springPotential_neg hg hgp)
  set a : ℝ → ℝ := fun s => min (1 / 2 * s ^ 2) (m s) with hadef
  have hac : ContinuousOn a (Icc 0 σ₀) :=
    (((continuous_const.mul (continuous_pow 2)).min
      (hGc.min (hGc.comp continuous_neg)))).continuousOn
  have ham : StrictMonoOn a (Icc 0 σ₀) :=
    strictMonoOn_min ((Stability.isClassK_mul_sq one_half_pos).2.1.mono Icc_subset_Ici_self) hmm
  have ha0 : a 0 = 0 := by simp [a, m, G, springPotential_zero]
  refine ⟨((continuous_springEnergy hg).comp continuous_snd).continuousOn, σ₀, hσ₀, _,
    isClassK_extend hσ₀ hac ham ha0, fun _ _ => ⟨?_, fun x hx => ?_⟩⟩
  · simp [springEnergy, springPotential_zero]
  · have hxσ : ‖x‖ ≤ σ₀ := hx.le
    show a (min ‖x‖ σ₀) + max (‖x‖ - σ₀) 0 ≤ springEnergy g x
    rw [min_eq_left hxσ, max_eq_right (sub_nonpos.mpr hxσ), add_zero]
    have hn : ‖x‖ = max |x.1| |x.2| := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |x.1| ≤ σ₀ := (le_max_left _ _).trans (hn ▸ hxσ)
    have hGx : m |x.1| ≤ G x.1 := by
      rcases abs_choice x.1 with h | h
      · rw [h]
        exact min_le_left _ _
      · show min (G |x.1|) (G (-|x.1|)) ≤ G x.1
        rw [h, neg_neg]
        exact min_le_right _ _
    have hm0 : 0 ≤ m |x.1| := by
      have := hmm.monotoneOn ⟨le_rfl, hσ₀.le⟩ ⟨abs_nonneg _, h1⟩ (abs_nonneg x.1)
      simpa [m, G, springPotential_zero] using this
    have hE : springEnergy g x = x.2 ^ 2 / 2 + G x.1 := rfl
    rw [hE]
    rcases le_total |x.1| |x.2| with h | h
    · rw [hn, max_eq_right h]
      have : a |x.2| ≤ 1 / 2 * |x.2| ^ 2 := min_le_left _ _
      rw [sq_abs] at this
      linarith
    · rw [hn, max_eq_left h]
      have : a |x.1| ≤ m |x.1| := min_le_right _ _
      nlinarith [sq_nonneg x.2]

/-! ### Example 4.6: stability -/

private lemma springEnergyRate_nonpos (hfp : IsPassiveOn f σ₀) {y : ℝ × ℝ}
    (hy : y ∈ Metric.ball (0 : ℝ × ℝ) σ₀) : springEnergyRate f y ≤ 0 := by
  have h2 := norm_snd_le y
  rw [Real.norm_eq_abs] at h2
  exact neg_nonpos.mpr (hfp y.2 (h2.trans (mem_ball_zero_iff.mp hy).le)).1

/-- **MLS Example 4.6, printed p. 188: "This establishes the stability ... of the origin."** For
continuous `g`, `f` and `g` passive on `[−σ₀, σ₀]` with `σ₀ > 0`, the origin of (4.45) is stable
in the sense of Lyapunov (Definition 4.1, p. 179) at every initial time `t₀ ≥ 0`, by
Theorem 4.4(1) (p. 182) with `V(x) = x₂²/2 + ∫₀^{x₁} g` and `V̇ = −x₂ f(x₂) ≤ 0` on the ball of
radius `σ₀`. No flow is needed. State `(x₁, x₂)`, sup norm, system `fun _ => springField f g`. -/
theorem stableAt_spring (hg : Continuous g) (hσ₀ : 0 < σ₀) (hfp : IsPassiveOn f σ₀)
    (hgp : IsPassiveOn g σ₀) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.StableAt (fun _ => springField f g) 0 t₀ :=
  Stability.stableAt_of_lyapunov (locallyPositiveDefinite_springEnergy hg hσ₀ hgp) hσ₀
    ((hasDerivAlongSolutions_springEnergy hg).mono (subset_univ _))
    (fun _ _ _ hy => springEnergyRate_nonpos hfp hy) ht₀

/-! ### Example 4.7: asymptotic stability by Lasalle's principle -/

/-- **The invariant-set step of MLS Example 4.7 (printed p. 189).** For continuous `f`, with `f`
and `g` passive on `[−σ₀, σ₀]`, `σ₀ > 0`, and a flow `φ` of (4.45), the largest invariant set
(Definition 4.8, p. 188) inside `{x ∈ B(0, σ₀) : V̇(x) = 0}` lies in `{0}`. On such a trajectory
`x₂ ≡ 0`, so `ẋ₂ = 0 = −f(0) − g(x₁)`, `g(x₁) = 0` and `x₁ = 0` for `t > 0`; the starting point is
the limit as `t → 0⁺`. Continuity of `g` is not used here. The ball replaces MLS's `Ω_c` (module
docstring). State `(x₁, x₂)`, sup norm. -/
theorem spring_largestInvariantSubset (hf : Continuous f) (hσ₀ : 0 < σ₀)
    (hfp : IsPassiveOn f σ₀) (hgp : IsPassiveOn g σ₀) {φ : ℝ → ℝ × ℝ → ℝ × ℝ}
    (hφ : Stability.HasFlow (springField f g) φ) :
    Stability.largestInvariantSubset φ
      {y | y ∈ Metric.ball (0 : ℝ × ℝ) σ₀ ∧ springEnergyRate f y = 0} ⊆ {0} := by
  intro y hy
  rw [Stability.mem_largestInvariantSubset_iff hφ] at hy
  set γ : ℝ → ℝ × ℝ := fun t => φ t y with hγdef
  have hf0 : f 0 = 0 := hfp.apply_zero hf hσ₀
  have hin : ∀ t, 0 ≤ t → |(γ t).1| < σ₀ ∧ |(γ t).2| < σ₀ := by
    intro t ht
    have hb := mem_ball_zero_iff.mp (hy t ht).1
    have h1 := norm_fst_le (γ t)
    have h2 := norm_snd_le (γ t)
    rw [Real.norm_eq_abs] at h1 h2
    exact ⟨h1.trans_lt hb, h2.trans_lt hb⟩
  have hv : ∀ t, 0 ≤ t → (γ t).2 = 0 := by
    intro t ht
    have hr : (γ t).2 * f (γ t).2 = 0 := neg_eq_zero.mp (hy t ht).2
    exact (hfp _ (hin t ht).2.le).2 hr
  have hpos : ∀ t, 0 < t → γ t = 0 := by
    intro t ht
    have hd : HasDerivAt γ (springField f g (γ t)) t := (hφ.isSolution y).2 t ht
    have h2 : HasDerivAt (fun s => (γ s).2) (-f (γ t).2 - g (γ t).1) t :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
    have h0 : HasDerivAt (fun s => (γ s).2) 0 t := by
      refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds ht] with s hs
      exact hv s hs.le
    have heq := h2.unique h0
    rw [hv t ht.le, hf0] at heq
    have hgz : (γ t).1 * g (γ t).1 = 0 := by
      rw [show g (γ t).1 = 0 by linarith, mul_zero]
    exact Prod.ext ((hgp _ (hin t ht.le).1.le).2 hgz) (hv t ht.le)
  have hc : ContinuousWithinAt γ (Ioi 0) 0 :=
    ((hφ.continuousOn_trajectory y).continuousWithinAt self_mem_Ici).mono Ioi_subset_Ici_self
  have hy0 : γ 0 = y := hφ.map_zero y
  rw [ContinuousWithinAt, hy0] at hc
  have hlim : Tendsto γ (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hpos t ht).symm)
  exact tendsto_nhds_unique hc hlim

/-- **MLS Example 4.7, printed p. 189: "by Lasalle's principle, the origin is locally
asymptotically stable".** For continuous `f, g`, passive on `[−σ₀, σ₀]` with `σ₀ > 0`, and a flow
`φ` of (4.45) (`HasFlow`, a hypothesis: a general nonlinear spring field need not be globally
Lipschitz), the origin is asymptotically stable (Definition 4.2, p. 180) at every initial time
`t₀ ≥ 0`. Proved by the local form of Theorem 4.7 (p. 188),
`Stability.asymptoticallyStableAt_of_lasalle_ball`, on the ball of radius `σ₀` in place of MLS's
`Ω_c`. State `(x₁, x₂)`, sup norm, system `fun _ => springField f g`. -/
theorem asymptoticallyStableAt_spring (hf : Continuous f) (hg : Continuous g) (hσ₀ : 0 < σ₀)
    (hfp : IsPassiveOn f σ₀) (hgp : IsPassiveOn g σ₀) {φ : ℝ → ℝ × ℝ → ℝ × ℝ}
    (hφ : Stability.HasFlow (springField f g) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.AsymptoticallyStableAt (fun _ => springField f g) 0 t₀ :=
  Stability.asymptoticallyStableAt_of_lasalle_ball hφ hσ₀
    (locallyPositiveDefinite_springEnergy hg hσ₀ hgp)
    ((hasDerivAlongSolutions_springEnergy hg).mono (subset_univ _))
    (continuous_springEnergyRate hf).continuousOn (fun _ hy => springEnergyRate_nonpos hfp hy)
    (spring_largestInvariantSubset hf hσ₀ hfp hgp hφ) ht₀

/-! ### Lipschitz springs and dampers: the flow exists -/

/-- **The field (4.45) of MLS Example 4.6 (printed p. 187) is Lipschitz when `f` and `g` are**:
with constants `K_f`, `K_g`, the constant `max(1, K_f + K_g)` works for the sup norm on the
state `(x₁, x₂)`. -/
theorem lipschitzWith_springField {Kf Kg : NNReal} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (max 1 (Kf + Kg)) (springField f g) := by
  have h2 : LipschitzWith (Kf + Kg) (fun x : ℝ × ℝ => -f x.2 - g x.1) := by
    simpa using (hf.comp LipschitzWith.prod_snd).neg.sub (hg.comp LipschitzWith.prod_fst)
  exact LipschitzWith.prod_snd.prodMk h2

/-- **MLS Example 4.7 (printed p. 189) for Lipschitz `f, g`, with no flow hypothesis.** If `f`
and `g` are Lipschitz and passive on `[−σ₀, σ₀]` with `σ₀ > 0`, the origin of (4.45) is
asymptotically stable (Definition 4.2, p. 180) at every initial time `t₀ ≥ 0`. The flow is
constructed by `Stability.exists_hasFlow_of_lipschitzWith`. State `(x₁, x₂)`, sup norm, system
`fun _ => springField f g`. -/
theorem asymptoticallyStableAt_spring_of_lipschitz {Kf Kg : NNReal} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) (hσ₀ : 0 < σ₀) (hfp : IsPassiveOn f σ₀) (hgp : IsPassiveOn g σ₀)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : Stability.AsymptoticallyStableAt (fun _ => springField f g) 0 t₀ :=
  have ⟨_, hφ⟩ := Stability.exists_hasFlow_of_lipschitzWith (lipschitzWith_springField hf hg)
  asymptoticallyStableAt_spring hf.continuous hg.continuous hσ₀ hfp hgp hφ ht₀

/-! ### The damped pendulum -/

private lemma isPassiveOn_id : IsPassiveOn id 1 :=
  fun σ _ => ⟨mul_self_nonneg σ, fun h => mul_self_eq_zero.mp h⟩

private lemma isPassiveOn_sin : IsPassiveOn Real.sin 1 := by
  intro σ hσ
  have hπ : 1 < Real.pi := by linarith [Real.two_le_pi]
  rcases lt_trichotomy σ 0 with h | h | h
  · have hs : Real.sin σ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h) (by linarith [neg_le_abs σ])
      rw [Real.sin_neg] at this
      linarith
    have hp : 0 < σ * Real.sin σ := mul_pos_of_neg_of_neg h hs
    exact ⟨hp.le, fun he => absurd he hp.ne'⟩
  · subst h
    simp
  · have hp := mul_pos h (Real.sin_pos_of_pos_of_lt_pi h (by linarith [le_abs_self σ]))
    exact ⟨hp.le, fun he => absurd he hp.ne'⟩

/-- **A concrete instance of MLS Example 4.7 (printed p. 189): the damped pendulum**
`ẋ₁ = x₂`, `ẋ₂ = −x₂ − sin x₁`, i.e. (4.45) with linear damping `f = id` and the restoring force
`g = sin`, both passive on `[−1, 1]` and Lipschitz with constant `1`. The origin is
asymptotically stable (Definition 4.2, p. 180) at every initial time `t₀ ≥ 0`; every hypothesis of
`asymptoticallyStableAt_spring_of_lipschitz` is discharged, with `σ₀ = 1`. State `(x₁, x₂)`, sup
norm. -/
theorem asymptoticallyStableAt_dampedPendulum {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.AsymptoticallyStableAt (fun _ => springField id Real.sin) 0 t₀ :=
  asymptoticallyStableAt_spring_of_lipschitz LipschitzWith.id Real.lipschitzWith_sin one_pos
    isPassiveOn_id isPassiveOn_sin ht₀

end RoboLean.Examples
