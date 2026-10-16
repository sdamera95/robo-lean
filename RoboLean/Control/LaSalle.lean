import RoboLean.Control.SolutionFlow
import Mathlib.Dynamics.OmegaLimit

/-!
# Lasalle's invariance principle (MLS Theorem 4.7, Definitions 4.7–4.8, pp. 188–189)

**What MLS prints (p. 188).** For the autonomous system `ẋ = f(x)` (4.46) with
solutions `s(t, x₀, t₀)`:

* Definition 4.7: "The set `S ⊂ ℝⁿ` is the ω limit set of a trajectory `s(·, x₀, t₀)` if for every
  `y ∈ S`, there exists a strictly increasing sequence of times `tₙ` such that
  `s(tₙ, x₀, t₀) → y` as `tₙ → ∞`."
* Definition 4.8: "The set `M ⊂ ℝⁿ` is said to be an (positively) invariant set if for all
  `y ∈ M` and `t₀ ≥ 0`, we have `s(t, y, t₀) ∈ M` for all `t ≥ t₀`."
* Theorem 4.7: "Let `V : ℝⁿ → ℝ` be a locally positive definite function such that on the compact
  set `Ω_c = {x ∈ ℝⁿ : V(x) ≤ c}` we have `V̇(x) ≤ 0`. Define `S = {x ∈ Ω_c : V̇(x) = 0}`. As
  `t → ∞`, the trajectory tends to the largest invariant set inside `S`; i.e., its ω limit set is
  contained inside the largest invariant set in `S`. In particular, if `S` contains no invariant
  sets other than `x = 0`, then `0` is asymptotically stable."

**Formalized, under `HasFlow F φ` (the solution-flow interface of `SolutionFlow`).**

* the ω-limit set of the trajectory from `x₀` is Mathlib's `omegaLimit atTop φ {x₀}`, with MLS's
  sequence characterization (`mem_omegaLimit_iff_exists_seq`); an invariant set is Mathlib's
  `IsForwardInvariant φ M` (`φ t` maps `M` into `M` for `t ≥ 0`), equivalent to MLS's wording
  (`isForwardInvariant_iff`); the largest invariant subset of `S` is
  `largestInvariantSubset φ S`, the union of all invariant subsets of `S`
  (`mem_largestInvariantSubset_iff`);
* the principle for a compact positively invariant set `Ω` (`lasalle`, the form of Khalil's
  Theorem 4.4): the ω-limit set of every trajectory from `Ω` is nonempty and contained in the
  largest invariant subset `M` of `{x ∈ Ω : V̇(x) = 0}`, and the trajectory eventually enters
  every open set containing `M`;
* MLS's sublevel form (`lasalle_sublevel`, `lasalle_isSolution`) for trajectories starting in the
  open sublevel `{V < c}`, and MLS's "in particular" (`asymptoticallyStableAt_of_lasalle`).

**Hypotheses the book does not state.**

* `Ω_c` positively invariant. As printed, with `V̇ ≤ 0` only on `Ω_c`, a trajectory starting on
  the level `{V = c}` can leave `Ω_c` (a derivation not formalized here: on `ℝ` with
  `V = 2x² − x⁴` on `[−1, 1]`, `V = 1` on `[1, 3]`, `V = 1 + (x − 3)²` beyond, and a Lipschitz
  field `f = −x` on `x ≤ 1`, `f > 0` on `(3/2, 4)`, `f(4) = 0`, the trajectory from `x₀ = 2 ∈ Ω₁`
  tends to `4 ∉ Ω₁`, while `S ⊆ Ω₁`). Trajectories from `{V < c}` cannot leave `Ω_c`
  (`le_of_lyapunov_sublevel`), and that is the form proved;
* `V̇` continuous on `Ω_c`. MLS takes `V̇ = (∂V/∂x) f`, continuous when `V` is `C¹`; it is used to
  show that `V̇` vanishes on the ω-limit set;
* the derivative along solutions is `HasDerivAlongSolutions` for the time-invariant `V`,
  as in Theorem 4.4.

The trajectory from `x₀` at time `t₀` is `t ↦ φ (t − t₀) x₀`; its ω-limit set does not depend on
`t₀`, so the trajectory `t ↦ φ t x₀` from time `0` is used. Compactness is the hypothesis
`IsCompact`; in `ℝⁿ` (more generally in a proper space) a closed bounded set is compact.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### ω-limit sets (MLS Definition 4.7, p. 188) -/

/-- **MLS Definition 4.7 (p. 188), sequence form.** A point `y` is in the ω-limit set
`omegaLimit atTop φ {x₀}` of the trajectory `t ↦ φ t x₀` exactly when there is a strictly
increasing sequence of times `tₙ → ∞` with `φ tₙ x₀ → y`. Mathlib's `omegaLimit` is used as the
definition. -/
theorem mem_omegaLimit_iff_exists_seq {X : Type*} [PseudoMetricSpace X] (φ : ℝ → X → X)
    (x₀ y : X) :
    y ∈ omegaLimit atTop φ {x₀} ↔
      ∃ τ : ℕ → ℝ, StrictMono τ ∧ Tendsto τ atTop atTop ∧
        Tendsto (fun n => φ (τ n) x₀) atTop (𝓝 y) := by
  rw [mem_omegaLimit_singleton_iff_mapClusterPt]
  constructor
  · intro h
    have hfr : ∀ n : ℕ, ∀ a : ℝ, ∃ b ≥ a, dist (φ b x₀) y < 1 / ((n : ℝ) + 1) := by
      intro n a
      have hball : Metric.ball y (1 / ((n : ℝ) + 1)) ∈ 𝓝 y :=
        Metric.ball_mem_nhds y (by positivity)
      obtain ⟨b, hb, hbm⟩ := (frequently_atTop.mp (h.frequently hball)) a
      exact ⟨b, hb, hbm⟩
    choose g hg hgd using hfr
    let τ : ℕ → ℝ := fun n => Nat.rec (g 0 0) (fun k r => g (k + 1) (r + 1)) n
    have hτ0 : τ 0 = g 0 0 := rfl
    have hτs : ∀ k, τ (k + 1) = g (k + 1) (τ k + 1) := fun _ => rfl
    have hmono : StrictMono τ := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      rw [hτs]
      linarith [hg (k + 1) (τ k + 1)]
    have hge : ∀ k : ℕ, (k : ℝ) ≤ τ k := by
      intro k
      induction k with
      | zero => rw [hτ0]; simpa using hg 0 0
      | succ k ih =>
        rw [hτs]
        push_cast
        linarith [hg (k + 1) (τ k + 1)]
    have hdist : ∀ k, dist (φ (τ k) x₀) y < 1 / ((k : ℝ) + 1) := by
      intro k
      cases k with
      | zero => rw [hτ0]; exact hgd 0 0
      | succ k => rw [hτs]; exact hgd (k + 1) (τ k + 1)
    refine ⟨τ, hmono, tendsto_atTop_mono hge tendsto_natCast_atTop_atTop, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) (fun k => (hdist k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨τ, -, hτ, hconv⟩
    exact MapClusterPt.of_comp hτ hconv.mapClusterPt

/-! ### Invariant sets (MLS Definition 4.8, p. 188) -/

section InvariantSets

variable {X : Type*}

/-- **MLS Definition 4.8 (p. 188).** Mathlib's `IsForwardInvariant φ M` (`φ t` maps `M` into `M`
for every `t ≥ 0`) is MLS's "for all `y ∈ M` and `t₀ ≥ 0`, `s(t, y, t₀) ∈ M` for all `t ≥ t₀`",
with `s(t, y, t₀) = φ (t − t₀) y`. -/
theorem isForwardInvariant_iff (φ : ℝ → X → X) (M : Set X) :
    IsForwardInvariant φ M ↔ ∀ y ∈ M, ∀ t₀, 0 ≤ t₀ → ∀ t, t₀ ≤ t → φ (t - t₀) y ∈ M := by
  constructor
  · intro h y hy t₀ _ t ht
    exact h (sub_nonneg.mpr ht) hy
  · intro h t ht y hy
    simpa using h y hy 0 le_rfl t ht

/-- **The largest (positively) invariant set inside `S`** (MLS Theorem 4.7, p. 188): the union of
all subsets of `S` that are invariant in the sense of Definition 4.8. -/
def largestInvariantSubset (φ : ℝ → X → X) (S : Set X) : Set X :=
  ⋃₀ {N | N ⊆ S ∧ IsForwardInvariant φ N}

/-- The largest invariant subset of `S` lies in `S` (MLS p. 188). -/
theorem largestInvariantSubset_subset (φ : ℝ → X → X) (S : Set X) :
    largestInvariantSubset φ S ⊆ S :=
  sUnion_subset fun _ hN => hN.1

/-- The largest invariant subset of `S` is invariant (MLS Definition 4.8, p. 188). -/
theorem isForwardInvariant_largestInvariantSubset (φ : ℝ → X → X) (S : Set X) :
    IsForwardInvariant φ (largestInvariantSubset φ S) := by
  intro t ht y ⟨N, hN, hy⟩
  exact ⟨N, hN, hN.2 ht hy⟩

/-- Every invariant subset of `S` lies in the largest one (MLS p. 188). -/
theorem subset_largestInvariantSubset {φ : ℝ → X → X} {S N : Set X} (hNS : N ⊆ S)
    (hN : IsForwardInvariant φ N) : N ⊆ largestInvariantSubset φ S :=
  fun _ hy => ⟨N, ⟨hNS, hN⟩, hy⟩

/-- The largest invariant subset is monotone in the ambient set (MLS p. 188). -/
theorem largestInvariantSubset_mono (φ : ℝ → X → X) {S T : Set X} (hST : S ⊆ T) :
    largestInvariantSubset φ S ⊆ largestInvariantSubset φ T :=
  sUnion_subset fun _ hN => subset_largestInvariantSubset (hN.1.trans hST) hN.2

end InvariantSets

/-- **The largest invariant subset of `S`, pointwise** (MLS p. 188): under a flow, `y` lies in
it exactly when its whole forward trajectory stays in `S`. -/
theorem mem_largestInvariantSubset_iff {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ)
    (S : Set E) (y : E) :
    y ∈ largestInvariantSubset φ S ↔ ∀ t, 0 ≤ t → φ t y ∈ S := by
  constructor
  · rintro ⟨N, hN, hy⟩ t ht
    exact hN.1 (hN.2 ht hy)
  · intro hy
    refine subset_largestInvariantSubset (N := {z | ∀ t, 0 ≤ t → φ t z ∈ S}) ?_ ?_ hy
    · intro z hz
      simpa [h.map_zero] using hz 0 le_rfl
    · intro s hs z hz t ht
      rw [← h.map_add hs ht]
      exact hz _ (add_nonneg ht hs)

/-! ### Supporting lemmas -/

/-- **Trajectories from the open sublevel set stay in it** (the positive invariance used in MLS
Theorem 4.7, p. 188). Let `V` be continuous with `V̇ ≤ 0` along the solutions while they are in
`Ω_c = {V ≤ c}`. A solution from `t₀ ≥ 0` with `V(x(t₀)) < c` satisfies `V(x(t)) ≤ V(x(t₀))` for
all `t ≥ t₀`. For time-invariant `V` and any system `f`. -/
theorem le_of_lyapunov_sublevel {f : ℝ → E → E} {V Vdot : E → ℝ} {c : ℝ} (hV : Continuous V)
    (hVdot : HasDerivAlongSolutions f (fun _ => V) (fun _ => Vdot) {y | V y ≤ c})
    (hneg : ∀ y, V y ≤ c → Vdot y ≤ 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E}
    (hx : IsSolution f t₀ x) (hx₀ : V (x t₀) < c) : ∀ t, t₀ ≤ t → V (x t) ≤ V (x t₀) := by
  have hcont : ContinuousOn (fun p : ℝ × E => (fun _ : ℝ => V) p.1 p.2) (Ici 0 ×ˢ univ) :=
    (hV.comp continuous_snd).continuousOn
  have hneg' : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ {y | V y ≤ c}, Vdot y ≤ 0 := fun _ _ y hy => hneg y hy
  have hVx : ContinuousOn (fun s => V (x s)) (Ici t₀) := hV.comp_continuousOn hx.1
  -- the solution never reaches the level `c`
  have hbelow : ∀ t, t₀ ≤ t → V (x t) < c := by
    intro t ht
    by_contra hcon
    push Not at hcon
    set A := Ici t₀ ∩ (fun s => V (x s)) ⁻¹' Ici c with hA
    have hAc : IsClosed A := hVx.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Ici
    have hAne : A.Nonempty := ⟨t, ht, hcon⟩
    have hAbdd : BddBelow A := ⟨t₀, fun s hs => hs.1⟩
    set T := sInf A with hT
    have hTA : T ∈ A := hAc.csInf_mem hAne hAbdd
    have hT₀ : t₀ < T := by
      rcases lt_or_eq_of_le (show t₀ ≤ T from hTA.1) with h | h
      · exact h
      · exfalso
        have h2 : c ≤ V (x T) := hTA.2
        rw [← h] at h2
        linarith
    have hbefore : ∀ s ∈ Ico t₀ T, V (x s) < c := by
      intro s hs
      by_contra h'
      push Not at h'
      have : T ≤ s := csInf_le hAbdd ⟨hs.1, h'⟩
      linarith [hs.2]
    have hanti := antitoneOn_of_isSolution hcont hVdot hneg' ht₀ hx (convex_Icc t₀ T)
      Icc_subset_Ici_self (by
        intro s hs
        rw [interior_Icc] at hs
        exact ⟨hs.1, (hbefore s ⟨hs.1.le, hs.2⟩).le⟩)
    have h1 : V (x T) ≤ V (x t₀) := hanti ⟨le_rfl, hT₀.le⟩ ⟨hT₀.le, le_rfl⟩ hT₀.le
    have h2 : c ≤ V (x T) := hTA.2
    linarith
  intro t ht
  have hanti := antitoneOn_of_isSolution hcont hVdot hneg' ht₀ hx (convex_Ici t₀) subset_rfl
    (by
      intro s hs
      rw [interior_Ici] at hs
      exact ⟨hs, (hbelow s hs.le).le⟩)
  exact hanti self_mem_Ici ht ht

/-- Along the trajectory of a flow that stays in `Ω`, a continuous `V` with `V̇ ≤ 0` on `Ω` is
antitone on `[0, ∞)` (the monotonicity step of MLS Theorem 4.7, p. 188). -/
theorem antitoneOn_comp_flow {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ) {V Vdot : E → ℝ}
    {Ω : Set E} (hV : Continuous V)
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) Ω)
    (hneg : ∀ y ∈ Ω, Vdot y ≤ 0) {x₀ : E} (hstay : ∀ t, 0 ≤ t → φ t x₀ ∈ Ω) :
    AntitoneOn (fun t => V (φ t x₀)) (Ici 0) :=
  antitoneOn_of_isSolution (V := fun _ => V) (Vdot := fun _ => Vdot)
    (hV.comp continuous_snd).continuousOn hVdot (fun _ _ y hy => hneg y hy) le_rfl
    (h.isSolution x₀) (convex_Ici 0) subset_rfl (by
      intro s hs
      rw [interior_Ici] at hs
      exact ⟨hs, hstay s hs.le⟩)

/-- **The ω-limit set of a flow is positively invariant** (MLS p. 188: "the ω limit set of every
trajectory is closed and invariant"; closedness is Mathlib's `isClosed_omegaLimit`). -/
theorem HasFlow.isForwardInvariant_omegaLimit {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ)
    (x₀ : E) : IsForwardInvariant φ (omegaLimit atTop φ {x₀}) := by
  intro s hs
  have h1 : MapsTo (φ s) (omegaLimit atTop φ {x₀})
      (omegaLimit atTop (fun t x => φ (s + t) x) {x₀}) := by
    refine mapsTo_omegaLimit' {x₀} (ga := id) (fun _ hx => hx) ?_ (h.continuous s hs)
    filter_upwards [eventually_ge_atTop 0] with t ht x _
    simp only [Function.comp_apply, id]
    rw [h.map_add ht hs]
  exact h1.mono_right (omegaLimit_subset_of_tendsto φ {x₀}
    (tendsto_atTop_add_const_left atTop s tendsto_id))

/-! ### Lasalle's principle (MLS Theorem 4.7, p. 188) -/

/-- **MLS Theorem 4.7 (p. 188), for a compact positively invariant set.** Let `φ` be the flow of
`ẋ = F(x)`, `Ω` a compact set that the flow maps into itself, `V` continuous with derivative
`V̇` along the solutions in `Ω`, `V̇` continuous on `Ω` and `V̇ ≤ 0` on `Ω`. For every `x₀ ∈ Ω` the
ω-limit set of the trajectory from `x₀` is nonempty and contained in the largest invariant set
in `S = {x ∈ Ω : V̇(x) = 0}`. -/
theorem lasalle {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ) {V Vdot : E → ℝ} {Ω : Set E}
    (hΩ : IsCompact Ω) (hinv : IsForwardInvariant φ Ω) (hV : Continuous V)
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) Ω)
    (hVdotc : ContinuousOn Vdot Ω) (hneg : ∀ y ∈ Ω, Vdot y ≤ 0) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (omegaLimit atTop φ {x₀}).Nonempty ∧
      omegaLimit atTop φ {x₀} ⊆ largestInvariantSubset φ {y | y ∈ Ω ∧ Vdot y = 0} := by
  set L := omegaLimit atTop φ {x₀} with hL
  have hstay : ∀ t, 0 ≤ t → φ t x₀ ∈ Ω := fun t ht => hinv ht hx₀
  have himage : ∀ T, 0 ≤ T → image2 φ (Ici T) {x₀} ⊆ Ω := by
    rintro T hT _ ⟨t, ht, _, rfl, rfl⟩
    exact hstay t (hT.trans ht)
  have hclos : closure (image2 φ (Ici 0) {x₀}) ⊆ Ω :=
    closure_minimal (himage 0 le_rfl) hΩ.isClosed
  refine ⟨nonempty_omegaLimit_of_isCompact_absorbing atTop φ {x₀} hΩ
    ⟨Ici 0, Ici_mem_atTop 0, hclos⟩ (singleton_nonempty x₀), ?_⟩
  have hLΩ : L ⊆ Ω := (omegaLimit_subset_closure_image2 atTop φ {x₀} (Ici_mem_atTop 0)).trans hclos
  -- `V` along the trajectory decreases to a limit `c`
  have hanti := antitoneOn_comp_flow h hV hVdot hneg hstay
  obtain ⟨m, hm⟩ := hΩ.bddBelow_image hV.continuousOn
  set g : ℝ → ℝ := fun t => V (φ (max t 0) x₀) with hg
  have hganti : Antitone g := by
    intro s t hst
    exact hanti (le_max_right s 0) (le_max_right t 0) (max_le_max hst le_rfl)
  have hgbdd : BddBelow (range g) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hm ⟨φ (max t 0) x₀, hstay _ (le_max_right t 0), rfl⟩
  set c := ⨅ t, g t with hc
  have hgc : Tendsto g atTop (𝓝 c) := tendsto_atTop_ciInf hganti hgbdd
  have hVc : Tendsto (fun t => V (φ t x₀)) atTop (𝓝 c) := by
    refine hgc.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp [hg, max_eq_left ht]
  have hcle : ∀ t, 0 ≤ t → c ≤ V (φ t x₀) := by
    intro t ht
    have := ciInf_le hgbdd t
    simpa [hg, max_eq_left ht] using this
  -- `V = c` on the ω-limit set
  have hVL : ∀ y ∈ L, V y = c := by
    intro y hy
    have hmem : ∀ T, 0 ≤ T → V y ∈ Icc c (V (φ T x₀)) := by
      intro T hT
      have hyT : y ∈ closure (image2 φ (Ici T) {x₀}) :=
        omegaLimit_subset_closure_image2 atTop φ {x₀} (Ici_mem_atTop T) hy
      have hmaps : MapsTo V (image2 φ (Ici T) {x₀}) (Icc c (V (φ T x₀))) := by
        rintro _ ⟨t, ht, _, rfl, rfl⟩
        exact ⟨hcle t (hT.trans ht), hanti (show (0 : ℝ) ≤ T from hT) (hT.trans ht) ht⟩
      have := map_mem_closure hV hyT hmaps
      rwa [isClosed_Icc.closure_eq] at this
    refine le_antisymm ?_ (hmem 0 le_rfl).1
    refine ge_of_tendsto hVc ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact (hmem T hT).2
  -- the ω-limit set is invariant, so `V̇ = 0` on it
  have hLinv := h.isForwardInvariant_omegaLimit x₀
  have hVdotL : ∀ y ∈ L, Vdot y = 0 := by
    intro y hy
    have hzero : ∀ r, 0 < r → Vdot (φ r y) = 0 := by
      intro r hr
      have hd := hVdot 0 le_rfl (fun t => φ t y) (h.isSolution y) r hr (hLΩ (hLinv hr.le hy))
      have hconst : (fun s => V (φ s y)) =ᶠ[𝓝 r] fun _ => c := by
        filter_upwards [Ioi_mem_nhds hr] with s hs
        exact hVL _ (hLinv (le_of_lt hs) hy)
      exact hd.unique ((hasDerivAt_const r c).congr_of_eventuallyEq hconst)
    have htraj : Tendsto (fun r => φ r y) (𝓝[>] 0) (𝓝[Ω] y) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := ((h.continuousOn_trajectory y) 0 self_mem_Ici).mono
          (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
        simpa [h.map_zero] using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact hLΩ (hLinv (le_of_lt hr) hy)
    have hlim := (hVdotc y (hLΩ hy)).tendsto.comp htraj
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hzero r hr).symm
  exact subset_largestInvariantSubset (fun y hy => ⟨hLΩ hy, hVdotL y hy⟩) hLinv

/-- **MLS Theorem 4.7 (p. 188), "the trajectory tends to the largest invariant set inside `S`".**
Under the hypotheses of `lasalle`, the trajectory from `x₀ ∈ Ω` eventually enters every open set
that contains the largest invariant set in `S = {x ∈ Ω : V̇(x) = 0}`. -/
theorem lasalle_eventually_mem {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ) {V Vdot : E → ℝ}
    {Ω : Set E} (hΩ : IsCompact Ω) (hinv : IsForwardInvariant φ Ω) (hV : Continuous V)
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) Ω)
    (hVdotc : ContinuousOn Vdot Ω) (hneg : ∀ y ∈ Ω, Vdot y ≤ 0) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {U : Set E} (hU : IsOpen U)
    (hMU : largestInvariantSubset φ {y | y ∈ Ω ∧ Vdot y = 0} ⊆ U) :
    ∀ᶠ t in atTop, φ t x₀ ∈ U := by
  have hω := (lasalle h hΩ hinv hV hVdot hVdotc hneg hx₀).2
  have hev := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop φ
    {x₀} hΩ (by
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact fun _ hx => by rw [mem_singleton_iff.mp hx]; exact hinv ht hx₀) hU (hω.trans hMU)
  filter_upwards [hev] with t ht
  exact ht (mem_singleton x₀)

/-- **MLS Theorem 4.7 (p. 188), sublevel form.** Let `φ` be the flow of `ẋ = F(x)` and `V`
continuous with `Ω_c = {x : V(x) ≤ c}` compact, derivative `V̇` along the solutions in `Ω_c`,
`V̇` continuous on `Ω_c` and `V̇ ≤ 0` on `Ω_c`, and let `M` be the largest invariant set in
`S = {x ∈ Ω_c : V̇(x) = 0}`. For every `x₀` with `V(x₀) < c`, the ω-limit set of the trajectory
from `x₀` is nonempty and contained in `M`, and the trajectory eventually enters every open set
containing `M`. MLS states this for `x₀ ∈ Ω_c`; trajectories from the level `{V = c}` are excluded
because without positive invariance of `Ω_c` they can leave it (module docstring). -/
theorem lasalle_sublevel {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ) {V Vdot : E → ℝ}
    {c : ℝ} (hV : Continuous V) (hΩ : IsCompact {x | V x ≤ c})
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) {x | V x ≤ c})
    (hVdotc : ContinuousOn Vdot {x | V x ≤ c}) (hneg : ∀ y, V y ≤ c → Vdot y ≤ 0) {x₀ : E}
    (hx₀ : V x₀ < c) :
    (omegaLimit atTop φ {x₀}).Nonempty ∧
      omegaLimit atTop φ {x₀} ⊆ largestInvariantSubset φ {y | V y ≤ c ∧ Vdot y = 0} ∧
      ∀ U, IsOpen U → largestInvariantSubset φ {y | V y ≤ c ∧ Vdot y = 0} ⊆ U →
        ∀ᶠ t in atTop, φ t x₀ ∈ U := by
  set c' := V x₀ with hc'
  have hsub : {x | V x ≤ c'} ⊆ {x | V x ≤ c} := fun x hx => le_trans hx hx₀.le
  have hΩ' : IsCompact {x | V x ≤ c'} :=
    hΩ.of_isClosed_subset (isClosed_le hV continuous_const) hsub
  have hinv : IsForwardInvariant φ {x | V x ≤ c'} := by
    intro t ht y hy
    have hy' : V y < c := lt_of_le_of_lt hy hx₀
    have := le_of_lyapunov_sublevel hV hVdot hneg le_rfl (h.isSolution y) (by
      simpa [h.map_zero] using hy') t ht
    simp only [h.map_zero] at this
    exact le_trans this hy
  have hVdot' := hVdot.mono hsub
  have hneg' : ∀ y ∈ {x | V x ≤ c'}, Vdot y ≤ 0 := fun y hy => hneg y (hsub hy)
  have hM : largestInvariantSubset φ {y | y ∈ {x | V x ≤ c'} ∧ Vdot y = 0} ⊆
      largestInvariantSubset φ {y | V y ≤ c ∧ Vdot y = 0} :=
    largestInvariantSubset_mono φ fun y hy => ⟨hsub hy.1, hy.2⟩
  obtain ⟨hne, hω⟩ := lasalle h hΩ' hinv hV hVdot' (hVdotc.mono hsub) hneg'
    (show V x₀ ≤ c' from le_rfl)
  refine ⟨hne, hω.trans hM, fun U hU hMU => ?_⟩
  exact lasalle_eventually_mem h hΩ' hinv hV hVdot' (hVdotc.mono hsub) hneg'
    (show V x₀ ≤ c' from le_rfl) hU (hM.trans hMU)

/-- **MLS Theorem 4.7 (p. 188) for solutions.** Under the hypotheses of `lasalle_sublevel`,
every solution `x` from `t₀ ≥ 0` with `V(x(t₀)) < c` eventually enters every open set containing
the largest invariant set in `S = {x ∈ Ω_c : V̇(x) = 0}`. -/
theorem lasalle_isSolution {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ) {V Vdot : E → ℝ}
    {c : ℝ} (hV : Continuous V) (hΩ : IsCompact {x | V x ≤ c})
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) {x | V x ≤ c})
    (hVdotc : ContinuousOn Vdot {x | V x ≤ c}) (hneg : ∀ y, V y ≤ c → Vdot y ≤ 0) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution (fun _ => F) t₀ x) (hx₀ : V (x t₀) < c)
    {U : Set E} (hU : IsOpen U)
    (hMU : largestInvariantSubset φ {y | V y ≤ c ∧ Vdot y = 0} ⊆ U) :
    ∀ᶠ t in atTop, x t ∈ U :=
  tendsto_principal.mp (h.tendsto_of_isSolution ht₀ hx (l := 𝓟 U)
    (tendsto_principal.mpr ((lasalle_sublevel h hV hΩ hVdot hVdotc hneg hx₀).2.2 U hU hMU)))

/-- **MLS Theorem 4.7 (p. 188), "in particular".** Let `V` be locally positive definite
(Definition 4.4, time-invariant), `c > 0`, `Ω_c = {V ≤ c}` compact, `V̇` the derivative along the
solutions in `Ω_c`, continuous and `≤ 0` there. If the largest invariant set in
`S = {x ∈ Ω_c : V̇(x) = 0}` is contained in `{0}`, then the origin is asymptotically stable
(Definition 4.2) at every initial time `t₀ ≥ 0`. Stability is Theorem 4.4(1); attractivity holds
for every solution starting in the open set `{V < c}`. -/
theorem asymptoticallyStableAt_of_lasalle {F : E → E} {φ : ℝ → E → E} (h : HasFlow F φ)
    {V Vdot : E → ℝ} {c : ℝ} (hc : 0 < c) (hpd : LocallyPositiveDefinite fun _ => V)
    (hΩ : IsCompact {x | V x ≤ c})
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) {x | V x ≤ c})
    (hVdotc : ContinuousOn Vdot {x | V x ≤ c}) (hneg : ∀ y, V y ≤ c → Vdot y ≤ 0)
    (hM : largestInvariantSubset φ {y | V y ≤ c ∧ Vdot y = 0} ⊆ {0}) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    AsymptoticallyStableAt (fun _ => F) 0 t₀ := by
  have hV : Continuous V := by
    have := hpd.1.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨(le_refl (0 : ℝ)), mem_univ y⟩)
    exact this
  have hV0 : V 0 = 0 := ((hpd.2.choose_spec.2.choose_spec.2) 0 le_rfl).1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt hV continuous_const) 0
    (show V 0 < c by rw [hV0]; exact hc)
  have hballsub : Metric.ball (0 : E) r ⊆ {x | V x ≤ c} := fun y hy =>
    show V y ≤ c from le_of_lt (hball hy)
  refine ⟨stableAt_of_lyapunov hpd hr (hVdot.mono hballsub)
    (fun _ _ y hy => hneg y (hballsub hy)) ht₀, r, hr, fun x hx hx0 => ?_⟩
  rw [sub_zero] at hx0
  have hx0' : V (x t₀) < c := hball (mem_ball_zero_iff.mpr hx0)
  refine tendsto_nhds.mpr fun U hU h0U => ?_
  exact lasalle_isSolution h hV hΩ hVdot hVdotc hneg ht₀ hx hx0' hU
    (hM.trans (singleton_subset_iff.mpr h0U))

end Stability
end RoboLean
