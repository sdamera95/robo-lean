import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lyapunov stability: solutions, stability notions and the direct method

MLS Chapter 4, Section 4 ("Lyapunov Stability Theory"), printed pp. 179–184.

MLS considers `ẋ = f(x, t)`, `x(t₀) = x₀` (eq. (4.31), p. 179), assumes "the standard conditions
for the existence and uniqueness of solutions" and states its definitions for "all solutions
which start near `x*`". Nothing here proves existence or uniqueness. Instead every notion
quantifies over all solutions in the sense of `IsSolution`, so the statements hold whether or not
solutions exist or are unique.

Conventions (recorded for the conventions document):

* the right-hand side is `f : ℝ → E → E` with time first, `f t x` (MLS writes `f(x, t)`); likewise
  a Lyapunov function is `V : ℝ → E → ℝ`, `V t x` for MLS's `V(x, t)`; `E` is any real normed
  space and `‖·‖` its norm (for `Fin n → ℝ` and products, Mathlib's sup norm; every notion here is
  invariant under a change to an equivalent norm, up to the constants);
* a solution from `t₀` (`IsSolution f t₀ x`) is a curve `x : ℝ → E`, continuous on `[t₀, ∞)`,
  with the actual derivative `f t (x t)` at every `t > t₀`. Values before `t₀` are irrelevant;
* times are `t ≥ 0` where MLS writes `ℝ₊` (Definitions 4.4–4.6), and initial times `t₀ ≥ 0`;
* the comparison functions `α`, `β` of Definitions 4.4 and 4.6 ("continuous, strictly increasing
  function `ℝ₊ → ℝ`") are additionally required to vanish at `0` (`IsClassK`). MLS does not state
  `α(0) = 0`. Without it the definition admits `α(r) = r − 1`, `V ≡ 0`, and Theorem 4.4(1) would
  then claim that every system is stable, which is false; the condition is the standard one in
  the references MLS cites (Vidyasagar, Khalil);
* the derivative of `V` "along the trajectories of the system" (p. 182) is a hypothesis
  `HasDerivAlongSolutions f V Vdot U`: along every solution, while it is in `U`, the actual
  derivative of `t ↦ V t (x t)` is `Vdot t (x t)`. For a Fréchet-differentiable `V` this holds with
  MLS's formula `V̇ = ∂V/∂t + ∂V/∂x · f` (`hasDerivAlongSolutions_of_hasFDerivAt`).

Proved here: Theorem 4.4 parts (1) (stability), (2) (uniform stability) and (3) (uniform
asymptotic stability) of the basic theorem of Lyapunov (pp. 182–183), the sufficiency half of
Theorem 4.5 (exponential stability from quadratic bounds, p. 183) in its global form with the rate
bounds printed on p. 184, and the facts that exponential stability implies stability and
asymptotic stability (p. 181). Not formalized:
Theorem 4.4 part (4) (global), the converse half of Theorem 4.5 and its local form, Theorem 4.6
(linearization), Lasalle's principle (Theorem 4.7) and the existence and uniqueness theory.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Solutions and equilibria (MLS eq. (4.31), p. 179) -/

/-- **A solution of `ẋ = f(x, t)` from time `t₀` (MLS eq. (4.31), p. 179).** The curve `x` is
continuous on `[t₀, ∞)` and has the actual derivative `f t (x t)` at every `t > t₀`. Time is the
first argument of `f` (MLS writes `f(x, t)`). No existence or uniqueness is assumed anywhere. -/
def IsSolution (f : ℝ → E → E) (t₀ : ℝ) (x : ℝ → E) : Prop :=
  ContinuousOn x (Ici t₀) ∧ ∀ t, t₀ < t → HasDerivAt x (f t (x t)) t

/-- **An equilibrium point (MLS p. 179):** `x*` with `f(x*, t) ≡ 0`. -/
def IsEquilibrium (f : ℝ → E → E) (xe : E) : Prop :=
  ∀ t, f t xe = 0

/-- At an equilibrium the constant curve is a solution from every initial time (MLS p. 179). -/
theorem IsEquilibrium.isSolution_const {f : ℝ → E → E} {xe : E} (h : IsEquilibrium f xe)
    (t₀ : ℝ) : IsSolution f t₀ (fun _ => xe) :=
  ⟨continuousOn_const, fun t _ => by rw [h t]; exact hasDerivAt_const t xe⟩

/-- A solution from `t₀` is a solution from every later time (MLS eq. (4.31)). -/
theorem IsSolution.mono {f : ℝ → E → E} {t₀ s : ℝ} {x : ℝ → E} (hx : IsSolution f t₀ x)
    (hs : t₀ ≤ s) : IsSolution f s x :=
  ⟨hx.1.mono (Ici_subset_Ici.mpr hs), fun t ht => hx.2 t (hs.trans_lt ht)⟩

/-! ### Stability notions (MLS Definitions 4.1–4.3, pp. 179–181) -/

/-- **MLS Definition 4.1, p. 179: stability in the sense of Lyapunov at `t = t₀`** of the point
`xe` (MLS states it for `x* = 0` after shifting the origin): for every `ε > 0` there is `δ > 0`
such that every solution from `t₀` with `‖x(t₀) − xe‖ < δ` satisfies `‖x(t) − xe‖ < ε` for all
`t ≥ t₀`. -/
def StableAt (f : ℝ → E → E) (xe : E) (t₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ < δ → ∀ t, t₀ ≤ t → ‖x t - xe‖ < ε

/-- **Uniform stability (MLS pp. 179–180):** the `δ` of Definition 4.1 does not depend on the
initial time `t₀ ≥ 0`. -/
def UniformlyStable (f : ℝ → E → E) (xe : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ < δ →
    ∀ t, t₀ ≤ t → ‖x t - xe‖ < ε

/-- **MLS Definition 4.2, p. 180: asymptotic stability at `t = t₀`:** `xe` is stable at `t₀` and
locally attractive, i.e. there is `δ > 0` such that every solution from `t₀` with
`‖x(t₀) − xe‖ < δ` converges to `xe` as `t → ∞` (eq. (4.33)). -/
def AsymptoticallyStableAt (f : ℝ → E → E) (xe : E) (t₀ : ℝ) : Prop :=
  StableAt f xe t₀ ∧
    ∃ δ > 0, ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ < δ → Tendsto x atTop (𝓝 xe)

/-- **Uniform asymptotic stability (MLS p. 180):** `xe` is uniformly stable and uniformly locally
attractive: there is `δ > 0`, independent of the initial time, such that solutions starting within
`δ` converge to `xe` uniformly, i.e. for every `η > 0` there is a time `T`, independent of `t₀ ≥ 0`
and of the solution, after which they stay within `η` of `xe`. MLS states the uniformity of the
convergence in words; this is the standard reading. -/
def UniformlyAsymptoticallyStable (f : ℝ → E → E) (xe : E) : Prop :=
  UniformlyStable f xe ∧ ∃ δ > 0, ∀ η > 0, ∃ T ≥ 0, ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x →
    ‖x t₀ - xe‖ < δ → ∀ t, t₀ + T ≤ t → ‖x t - xe‖ < η

/-- **MLS Definition 4.3, pp. 180–181: exponential stability.** There are constants `m, α > 0` and
`ε > 0` such that every solution with `‖x(t₀) − xe‖ ≤ ε` satisfies
`‖x(t) − xe‖ ≤ m e^{−α(t − t₀)} ‖x(t₀) − xe‖` for `t ≥ t₀` (eq. (4.34)). MLS does not say how `t₀`
is quantified; it adds that exponential stability implies uniform asymptotic stability, so the
constants are taken independent of the initial time `t₀ ≥ 0`. -/
def ExponentiallyStable (f : ℝ → E → E) (xe : E) : Prop :=
  ∃ m > 0, ∃ α > 0, ∃ ε > 0, ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ ≤ ε →
    ∀ t, t₀ ≤ t → ‖x t - xe‖ ≤ m * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖

/-- **Global exponential stability (MLS p. 181):** the bound (4.34) of Definition 4.3 holds for
every initial condition. -/
def GloballyExponentiallyStable (f : ℝ → E → E) (xe : E) : Prop :=
  ∃ m > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x →
    ∀ t, t₀ ≤ t → ‖x t - xe‖ ≤ m * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖

/-- Global exponential stability implies exponential stability (MLS p. 181). -/
theorem GloballyExponentiallyStable.exponentiallyStable {f : ℝ → E → E} {xe : E}
    (h : GloballyExponentiallyStable f xe) : ExponentiallyStable f xe := by
  obtain ⟨m, hm, α, hα, h⟩ := h
  exact ⟨m, hm, α, hα, 1, one_pos, fun t₀ ht₀ x hx _ => h t₀ ht₀ x hx⟩

/-- **MLS p. 181: exponential stability implies stability** at every initial time `t₀ ≥ 0`. -/
theorem ExponentiallyStable.stableAt {f : ℝ → E → E} {xe : E} (h : ExponentiallyStable f xe)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : StableAt f xe t₀ := by
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := h
  intro ε' hε'
  refine ⟨min ε (ε' / m), lt_min hε (div_pos hε' hm), fun x hx hx0 t ht => ?_⟩
  have hb := h t₀ ht₀ x hx (hx0.le.trans (min_le_left _ _)) t ht
  have he : Real.exp (-α * (t - t₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 : ‖x t₀ - xe‖ < ε' / m := hx0.trans_le (min_le_right _ _)
  have h2 : m * ‖x t₀ - xe‖ < ε' := by rwa [lt_div_iff₀ hm, mul_comm] at h1
  calc ‖x t - xe‖ ≤ m * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖ := hb
    _ ≤ m * 1 * ‖x t₀ - xe‖ := by gcongr
    _ < ε' := by rwa [mul_one]

/-- **MLS p. 181: exponential stability implies asymptotic stability** at every initial time
`t₀ ≥ 0`. -/
theorem ExponentiallyStable.asymptoticallyStableAt {f : ℝ → E → E} {xe : E}
    (h : ExponentiallyStable f xe) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : AsymptoticallyStableAt f xe t₀ := by
  refine ⟨h.stableAt ht₀, ?_⟩
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := h
  refine ⟨ε, hε, fun x hx hx0 => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t => m * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -α * (t - t₀)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hα)
        (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul m
    simpa using h2.mul_const ‖x t₀ - xe‖
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact h t₀ ht₀ x hx hx0.le t ht

/-! ### Shifting the equilibrium to the origin (MLS p. 179) -/

/-- **The system with the origin shifted to `xe` (MLS p. 179):** `z' = f(t, z + xe)`, whose
solutions are `x − xe` for the solutions `x` of `f`. -/
def shift (f : ℝ → E → E) (xe : E) : ℝ → E → E :=
  fun t z => f t (z + xe)

/-- Solutions of the shifted system are exactly the shifted solutions (MLS p. 179). -/
theorem isSolution_shift_iff {f : ℝ → E → E} {xe : E} {t₀ : ℝ} {x : ℝ → E} :
    IsSolution (shift f xe) t₀ (fun t => x t - xe) ↔ IsSolution f t₀ x := by
  simp only [IsSolution, shift, sub_add_cancel, hasDerivAt_sub_const_iff]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨(hc.add (continuousOn_const (c := xe))).congr fun t _ => ?_, hd⟩
    simp
  · rintro ⟨hc, hd⟩
    exact ⟨hc.sub continuousOn_const, hd⟩

/-- **Stability of `xe` is stability of the origin of the shifted system** (MLS p. 179). -/
theorem stableAt_shift_iff {f : ℝ → E → E} {xe : E} {t₀ : ℝ} :
    StableAt (shift f xe) 0 t₀ ↔ StableAt f xe t₀ := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hx0 t ht => ?_⟩
    have := h (fun t => x t - xe) (isSolution_shift_iff.mpr hx) (by simpa using hx0) t ht
    simpa using this
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    refine ⟨δ, hδ, fun z hz hz0 t ht => ?_⟩
    have hx : IsSolution f t₀ (fun t => z t + xe) :=
      (isSolution_shift_iff (xe := xe)).mp (by simpa using hz)
    have := h (fun t => z t + xe) hx (by simpa using hz0) t ht
    simpa using this

/-! ### Lyapunov function candidates (MLS Definitions 4.4–4.6, p. 182) -/

/-- **The comparison functions of MLS Definitions 4.4 and 4.6 (p. 182):** continuous and strictly
increasing on `ℝ₊ = [0, ∞)`, and vanishing at `0`. MLS states only "continuous, strictly
increasing"; the condition `α 0 = 0` is added (see the module docstring for why it is needed). -/
def IsClassK (α : ℝ → ℝ) : Prop :=
  ContinuousOn α (Ici 0) ∧ StrictMonoOn α (Ici 0) ∧ α 0 = 0

theorem IsClassK.pos {α : ℝ → ℝ} (hα : IsClassK α) {r : ℝ} (hr : 0 < r) : 0 < α r := by
  have := hα.2.1 (self_mem_Ici : (0 : ℝ) ∈ Ici 0) (le_of_lt hr : (0 : ℝ) ≤ r) hr
  rwa [hα.2.2] at this

theorem IsClassK.le {α : ℝ → ℝ} (hα : IsClassK α) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    α r ≤ α s :=
  hα.2.1.monotoneOn hr (hr.trans hrs) hrs

/-- **MLS Definition 4.4, p. 182: a locally positive definite function (lpdf).** `V` is
continuous on `ℝ₊ × E`, and for some `ε > 0` and some comparison function `α` (`IsClassK`),
`V(t, 0) = 0` and `α(‖x‖) ≤ V(t, x)` for all `‖x‖ < ε` and `t ≥ 0` (eq. (4.35)). Time is the first
argument (MLS writes `V(x, t)`). -/
def LocallyPositiveDefinite (V : ℝ → E → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
    ∃ ε > 0, ∃ α, IsClassK α ∧ ∀ t, 0 ≤ t → V t 0 = 0 ∧ ∀ x : E, ‖x‖ < ε → α ‖x‖ ≤ V t x

/-- **MLS Definition 4.5, p. 182: a positive definite function (pdf).** As Definition 4.4 with
the bound `α(‖x‖) ≤ V(t, x)` for every `x` and `α(p) → ∞` as `p → ∞`. MLS keeps the words "the
conditions of Definition 4.4", whose bound is only on a ball; the global bound is the reading
under which `α(p) → ∞` has content. Not used by the theorems here. -/
def PositiveDefinite (V : ℝ → E → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
    ∃ α, IsClassK α ∧ Tendsto α atTop atTop ∧ ∀ t, 0 ≤ t → V t 0 = 0 ∧ ∀ x : E, α ‖x‖ ≤ V t x

/-- **MLS Definition 4.6, p. 182: a decrescent function.** `V` is continuous on `ℝ₊ × E`, and
for some `ε > 0` and some comparison function `β` (`IsClassK`), `V(t, x) ≤ β(‖x‖)` for all
`‖x‖ < ε` and `t ≥ 0` (eq. (4.36)). -/
def Decrescent (V : ℝ → E → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
    ∃ ε > 0, ∃ β, IsClassK β ∧ ∀ t, 0 ≤ t → ∀ x : E, ‖x‖ < ε → V t x ≤ β ‖x‖

/-- **The derivative of `V` along the trajectories of the system (MLS p. 182), in a region `U`.**
For every initial time `t₀ ≥ 0`, every solution `x` from `t₀` and every `t > t₀` with `x t ∈ U`,
the function `s ↦ V s (x s)` has the actual derivative `Vdot t (x t)` at `t`. MLS writes `V̇` and
computes it as `∂V/∂t + ∂V/∂x · f` (`hasDerivAlongSolutions_of_hasFDerivAt`). -/
def HasDerivAlongSolutions (f : ℝ → E → E) (V Vdot : ℝ → E → ℝ) (U : Set E) : Prop :=
  ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ∀ t, t₀ < t → x t ∈ U →
    HasDerivAt (fun s => V s (x s)) (Vdot t (x t)) t

/-- **MLS p. 182: `V̇ = ∂V/∂t + ∂V/∂x · f`.** If `V` (as a function of `(t, x)`) has the Fréchet
derivative `DV t y` at every `(t, y)` with `t > 0` and `y ∈ U`, then `V̇(t, y) = DV t y (1, f t y)`
is the derivative of `V` along the solutions in `U`. -/
theorem hasDerivAlongSolutions_of_hasFDerivAt {f : ℝ → E → E} {V : ℝ → E → ℝ} {U : Set E}
    {DV : ℝ → E → (ℝ × E →L[ℝ] ℝ)}
    (hV : ∀ t, 0 < t → ∀ y ∈ U, HasFDerivAt (fun p : ℝ × E => V p.1 p.2) (DV t y) (t, y)) :
    HasDerivAlongSolutions f V (fun t y => DV t y (1, f t y)) U := by
  intro t₀ ht₀ x hx t ht hxt
  have hcurve : HasDerivAt (fun s => (s, x s)) ((1 : ℝ), f t (x t)) t :=
    (hasDerivAt_id t).prodMk (hx.2 t ht)
  exact (hV t (by linarith) (x t) hxt).comp_hasDerivAt t hcurve

/-- The derivative along solutions in a region is also the derivative in every smaller region. -/
theorem HasDerivAlongSolutions.mono {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {U U' : Set E}
    (h : HasDerivAlongSolutions f V Vdot U) (hU : U' ⊆ U) : HasDerivAlongSolutions f V Vdot U' :=
  fun t₀ ht₀ x hx t ht hxt => h t₀ ht₀ x hx t ht (hU hxt)

/-! ### The basic theorem of Lyapunov (MLS Theorem 4.4, p. 182) -/

/-- Along a solution, `t ↦ V(t, x(t))` is antitone on every interval `D ⊆ [t₀, ∞)` whose interior
the solution spends in a region `U` where `V̇ ≤ 0` (the monotonicity step of MLS Theorem 4.4,
p. 182). -/
theorem antitoneOn_of_isSolution {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {U : Set E}
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hVdot : HasDerivAlongSolutions f V Vdot U) (hneg : ∀ t, 0 ≤ t → ∀ y ∈ U, Vdot t y ≤ 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution f t₀ x) {D : Set ℝ}
    (hD : Convex ℝ D) (hDsub : D ⊆ Ici t₀) (hin : ∀ s ∈ interior D, t₀ < s ∧ x s ∈ U) :
    AntitoneOn (fun s => V s (x s)) D := by
  have hc : ContinuousOn (fun s => V s (x s)) D := by
    have h1 : ContinuousOn (fun s => (s, x s)) D := continuousOn_id.prodMk (hx.1.mono hDsub)
    exact hcont.comp h1 fun s hs => ⟨ht₀.trans (hDsub hs), mem_univ _⟩
  refine antitoneOn_of_hasDerivWithinAt_nonpos hD hc (f' := fun s => Vdot s (x s)) ?_ ?_
  · intro s hs
    obtain ⟨h1, h2⟩ := hin s hs
    exact (hVdot t₀ ht₀ x hx s h1 h2).hasDerivWithinAt
  · intro s hs
    obtain ⟨h1, h2⟩ := hin s hs
    exact hneg s (by linarith) _ h2

/-- **The trapping step of MLS Theorem 4.4, p. 182.** Let `V` be continuous on `ℝ₊ × E` with
`V̇ ≤ 0` on a region containing the ball of radius `ρ`, and `α(‖y‖) ≤ V(t, y)` for `‖y‖ ≤ ρ`. A
solution from `t₀ ≥ 0` that starts in that ball with `V(t₀, x(t₀)) < α(ρ)` stays in the ball for
all `t ≥ t₀`. -/
theorem norm_lt_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {U : Set E}
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hVdot : HasDerivAlongSolutions f V Vdot U) (hneg : ∀ t, 0 ≤ t → ∀ y ∈ U, Vdot t y ≤ 0)
    {α : ℝ → ℝ} {ρ : ℝ} (hball : Metric.ball (0 : E) ρ ⊆ U)
    (hlow : ∀ t, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ρ → α ‖y‖ ≤ V t y) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → E} (hx : IsSolution f t₀ x) (hx₀ : ‖x t₀‖ < ρ) (hV₀ : V t₀ (x t₀) < α ρ) :
    ∀ t, t₀ ≤ t → ‖x t‖ < ρ := by
  intro t ht
  by_contra hcon
  push Not at hcon
  set A := Ici t₀ ∩ (fun s => ‖x s‖) ⁻¹' Ici ρ with hA
  have hAc : IsClosed A :=
    (continuous_norm.comp_continuousOn hx.1).preimage_isClosed_of_isClosed isClosed_Ici
      isClosed_Ici
  have hAne : A.Nonempty := ⟨t, ht, hcon⟩
  have hAbdd : BddBelow A := ⟨t₀, fun s hs => hs.1⟩
  set T := sInf A with hT
  have hTA : T ∈ A := hAc.csInf_mem hAne hAbdd
  have hT₀ : t₀ < T := by
    rcases lt_or_eq_of_le (show t₀ ≤ T from hTA.1) with h | h
    · exact h
    · exfalso
      have h2 : ρ ≤ ‖x T‖ := hTA.2
      rw [← h] at h2
      linarith
  have hbefore : ∀ s ∈ Ico t₀ T, ‖x s‖ < ρ := by
    intro s hs
    by_contra h'
    push Not at h'
    have : T ≤ s := csInf_le hAbdd ⟨hs.1, h'⟩
    linarith [hs.2]
  have hTle : ‖x T‖ ≤ ρ := by
    have hcw : ContinuousWithinAt x (Ico t₀ T) T := (hx.1 T hTA.1).mono Ico_subset_Ici_self
    have hcl : T ∈ closure (Ico t₀ T) := by
      rw [closure_Ico hT₀.ne]
      exact ⟨hT₀.le, le_rfl⟩
    have hsub : closure (x '' Ico t₀ T) ⊆ Metric.closedBall 0 ρ :=
      closure_minimal (by rintro _ ⟨s, hs, rfl⟩; simpa using (hbefore s hs).le)
        Metric.isClosed_closedBall
    simpa using hsub (hcw.mem_closure_image hcl)
  have hTeq : ‖x T‖ = ρ := le_antisymm hTle hTA.2
  have hanti := antitoneOn_of_isSolution hcont hVdot hneg ht₀ hx (convex_Icc t₀ T)
    Icc_subset_Ici_self (by
      intro s hs
      rw [interior_Icc] at hs
      exact ⟨hs.1, hball (by simpa using hbefore s ⟨hs.1.le, hs.2⟩)⟩)
  have h1 : V T (x T) ≤ V t₀ (x t₀) :=
    hanti ⟨le_rfl, hT₀.le⟩ ⟨hT₀.le, le_rfl⟩ hT₀.le
  have h2 : α ρ ≤ V T (x T) := by
    rw [← hTeq]
    exact hlow T (by linarith) _ hTeq.le
  linarith

/-- **MLS Theorem 4.4(1), p. 182: the basic theorem of Lyapunov, stability.** If `V` is locally
positive definite (Definition 4.4) and its derivative along the solutions satisfies `V̇(t, x) ≤ 0`
for `‖x‖ < r` and all `t ≥ 0`, then the origin is stable in the sense of Lyapunov (Definition 4.1)
at every initial time `t₀ ≥ 0`. MLS also assumes `V` non-negative; that is not needed. -/
theorem stableAt_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {r : ℝ}
    (hV : LocallyPositiveDefinite V) (hr : 0 < r)
    (hVdot : HasDerivAlongSolutions f V Vdot (Metric.ball 0 r))
    (hneg : ∀ t, 0 ≤ t → ∀ y ∈ Metric.ball (0 : E) r, Vdot t y ≤ 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    StableAt f 0 t₀ := by
  obtain ⟨hcont, ε₀, hε₀, α, hα, hb⟩ := hV
  intro ε hε
  set ρ := min ε (min ε₀ r) / 2 with hρdef
  have hm : 0 < min ε (min ε₀ r) := lt_min hε (lt_min hε₀ hr)
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε (min ε₀ r)
    linarith
  have hρε₀ : ρ < ε₀ := by
    have := (min_le_right ε (min ε₀ r)).trans (min_le_left ε₀ r)
    linarith
  have hρr : ρ < r := by
    have := (min_le_right ε (min ε₀ r)).trans (min_le_right ε₀ r)
    linarith
  have hαρ : 0 < α ρ := hα.pos hρ
  have hc0 : ContinuousAt (fun y => V t₀ y) 0 := by
    have hw := hcont (t₀, 0) ⟨ht₀, mem_univ _⟩
    have h2 : ContinuousWithinAt (fun y : E => (t₀, y)) univ 0 :=
      (continuous_const.prodMk continuous_id).continuousWithinAt
    exact (continuousWithinAt_univ _ _).mp (hw.comp h2 fun y _ => ⟨ht₀, mem_univ _⟩)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hc0 (α ρ) hαρ
  refine ⟨min δ₁ ρ, lt_min hδ₁ hρ, fun x hx hx0 t ht => ?_⟩
  rw [sub_zero] at hx0 ⊢
  have hx0ρ : ‖x t₀‖ < ρ := hx0.trans_le (min_le_right _ _)
  have hV0 : V t₀ (x t₀) < α ρ := by
    have h := hδ₁' (x := x t₀) (by rw [dist_zero_right]; exact hx0.trans_le (min_le_left _ _))
    rw [(hb t₀ ht₀).1, Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  have hlow : ∀ s, 0 ≤ s → ∀ y : E, ‖y‖ ≤ ρ → α ‖y‖ ≤ V s y :=
    fun s hs y hy => (hb s hs).2 y (hy.trans_lt hρε₀)
  have hball : Metric.ball (0 : E) ρ ⊆ Metric.ball 0 r := Metric.ball_subset_ball hρr.le
  have := norm_lt_of_lyapunov hcont hVdot hneg hball hlow ht₀ hx hx0ρ hV0 t ht
  linarith

/-- **MLS Theorem 4.4(2), p. 182: uniform stability.** If `V` is locally positive definite and
decrescent (Definitions 4.4 and 4.6) and `V̇(t, x) ≤ 0` for `‖x‖ < r` and all `t ≥ 0`, then the
origin is uniformly stable: the `δ` of Definition 4.1 can be chosen independently of `t₀ ≥ 0`. -/
theorem uniformlyStable_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {r : ℝ}
    (hV : LocallyPositiveDefinite V) (hdec : Decrescent V) (hr : 0 < r)
    (hVdot : HasDerivAlongSolutions f V Vdot (Metric.ball 0 r))
    (hneg : ∀ t, 0 ≤ t → ∀ y ∈ Metric.ball (0 : E) r, Vdot t y ≤ 0) :
    UniformlyStable f 0 := by
  obtain ⟨hcont, ε₀, hε₀, α, hα, hb⟩ := hV
  obtain ⟨-, ε₁, hε₁, β, hβ, hbβ⟩ := hdec
  intro ε hε
  set ρ := min ε (min ε₀ r) / 2 with hρdef
  have hm : 0 < min ε (min ε₀ r) := lt_min hε (lt_min hε₀ hr)
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε (min ε₀ r)
    linarith
  have hρε₀ : ρ < ε₀ := by
    have := (min_le_right ε (min ε₀ r)).trans (min_le_left ε₀ r)
    linarith
  have hρr : ρ < r := by
    have := (min_le_right ε (min ε₀ r)).trans (min_le_right ε₀ r)
    linarith
  have hαρ : 0 < α ρ := hα.pos hρ
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    Metric.continuousWithinAt_iff.mp (hβ.1 0 self_mem_Ici) (α ρ) hαρ
  refine ⟨min δ₁ (min ρ ε₁), lt_min hδ₁ (lt_min hρ hε₁), fun t₀ ht₀ x hx hx0 t ht => ?_⟩
  rw [sub_zero] at hx0 ⊢
  have hx0ρ : ‖x t₀‖ < ρ := hx0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hV0 : V t₀ (x t₀) < α ρ := by
    have h := hδ₁' (x := ‖x t₀‖) (norm_nonneg _)
      (by rw [Real.dist_eq, sub_zero, abs_norm]; exact hx0.trans_le (min_le_left _ _))
    rw [hβ.2.2, Real.dist_eq, sub_zero] at h
    have h2 := hbβ t₀ ht₀ (x t₀) (hx0.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact h2.trans_lt ((le_abs_self _).trans_lt h)
  have hlow : ∀ s, 0 ≤ s → ∀ y : E, ‖y‖ ≤ ρ → α ‖y‖ ≤ V s y :=
    fun s hs y hy => (hb s hs).2 y (hy.trans_lt hρε₀)
  have hball : Metric.ball (0 : E) ρ ⊆ Metric.ball 0 r := Metric.ball_subset_ball hρr.le
  have := norm_lt_of_lyapunov hcont hVdot hneg hball hlow ht₀ hx hx0ρ hV0 t ht
  linarith

/-- Uniform stability implies stability at every initial time `t₀ ≥ 0` (MLS pp. 179–180). -/
theorem UniformlyStable.stableAt {f : ℝ → E → E} {xe : E} (h : UniformlyStable f xe)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : StableAt f xe t₀ := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  exact ⟨δ, hδ, h t₀ ht₀⟩

/-- Uniform asymptotic stability implies asymptotic stability (Definition 4.2) at every initial
time `t₀ ≥ 0` (MLS p. 180). -/
theorem UniformlyAsymptoticallyStable.asymptoticallyStableAt {f : ℝ → E → E} {xe : E}
    (h : UniformlyAsymptoticallyStable f xe) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    AsymptoticallyStableAt f xe t₀ := by
  refine ⟨h.1.stableAt ht₀, ?_⟩
  obtain ⟨δ, hδ, h⟩ := h.2
  refine ⟨δ, hδ, fun x hx hx0 => Metric.tendsto_atTop.mpr fun η hη => ?_⟩
  obtain ⟨T, -, hT⟩ := h η hη
  exact ⟨t₀ + T, fun t ht => by rw [dist_eq_norm]; exact hT t₀ ht₀ x hx hx0 t ht⟩

/-- **MLS Theorem 4.4(3), p. 183: uniform asymptotic stability.** If `V` is locally positive
definite and decrescent (Definitions 4.4 and 4.6), and `−V̇` is locally positive definite, where
`V̇` is the derivative of `V` along the solutions in a ball of radius `r > 0`, then the origin is
uniformly asymptotically stable (`UniformlyAsymptoticallyStable`), hence asymptotically stable
at every `t₀ ≥ 0`. -/
theorem uniformlyAsymptoticallyStable_of_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {r : ℝ}
    (hV : LocallyPositiveDefinite V) (hdec : Decrescent V)
    (hVdot' : LocallyPositiveDefinite fun t y => -Vdot t y) (hr : 0 < r)
    (hVdot : HasDerivAlongSolutions f V Vdot (Metric.ball 0 r)) :
    UniformlyAsymptoticallyStable f 0 := by
  obtain ⟨hcont, ε₀, hε₀, α, hα, hb⟩ := hV
  obtain ⟨-, ε₁, hε₁, β, hβ, hbβ⟩ := hdec
  obtain ⟨-, ε₂, hε₂, γ, hγ, hbγ⟩ := hVdot'
  set r' := min r ε₂ with hr'
  have hr'0 : 0 < r' := lt_min hr hε₂
  have hneg : ∀ t, 0 ≤ t → ∀ y ∈ Metric.ball (0 : E) r', Vdot t y ≤ 0 := by
    intro t ht y hy
    rw [mem_ball_zero_iff] at hy
    have h1 := (hbγ t ht).2 y (hy.trans_le (min_le_right _ _))
    have h2 : 0 ≤ γ ‖y‖ := by
      have := hγ.le le_rfl (norm_nonneg y)
      rwa [hγ.2.2] at this
    linarith
  have hVdotr : HasDerivAlongSolutions f V Vdot (Metric.ball 0 r') :=
    hVdot.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hUS : UniformlyStable f 0 :=
    uniformlyStable_of_lyapunov ⟨hcont, ε₀, hε₀, α, hα, hb⟩ ⟨hcont, ε₁, hε₁, β, hβ, hbβ⟩ hr'0
      hVdotr hneg
  refine ⟨hUS, ?_⟩
  set R := min (min ε₀ ε₁) r' / 2 with hR
  have hm : 0 < min (min ε₀ ε₁) r' := lt_min (lt_min hε₀ hε₁) hr'0
  have hR0 : 0 < R := by positivity
  have hRε₀ : R < ε₀ := by
    have := (min_le_left (min ε₀ ε₁) r').trans (min_le_left ε₀ ε₁)
    linarith
  have hRε₁ : R < ε₁ := by
    have := (min_le_left (min ε₀ ε₁) r').trans (min_le_right ε₀ ε₁)
    linarith
  have hRr' : R < r' := by
    have := min_le_right (min ε₀ ε₁) r'
    linarith
  have hRε₂ : R < ε₂ := hRr'.trans_le (min_le_right _ _)
  obtain ⟨δ₀, hδ₀, hstay⟩ := hUS R hR0
  refine ⟨min δ₀ R, lt_min hδ₀ hR0, fun η hη => ?_⟩
  obtain ⟨δη, hδη, hstayη⟩ := hUS η hη
  set ρ := min δη R with hρ
  have hρ0 : 0 < ρ := lt_min hδη hR0
  set c := γ ρ with hc
  have hc0 : 0 < c := hγ.pos hρ0
  have hβR : 0 ≤ β R := by
    have := hβ.le le_rfl hR0.le
    rwa [hβ.2.2] at this
  refine ⟨β R / c + 1, by positivity, fun t₀ ht₀ x hx hx0 t ht => ?_⟩
  rw [sub_zero] at hx0 ⊢
  have hin : ∀ s, t₀ ≤ s → ‖x s‖ < R := by
    intro s hs
    simpa using hstay t₀ ht₀ x hx (by simpa using hx0.trans_le (min_le_left _ _)) s hs
  -- some time `s ≤ t₀ + T` at which the solution is within `ρ ≤ δη`
  have hexists : ∃ s, t₀ ≤ s ∧ s ≤ t₀ + (β R / c + 1) ∧ ‖x s‖ < ρ := by
    by_contra hne
    push Not at hne
    set T := β R / c + 1 with hT
    have hT0 : 0 < T := by positivity
    set W : ℝ → E → ℝ := fun s y => V s y + c * s with hW
    have hWc : ContinuousOn (fun p : ℝ × E => W p.1 p.2) (Ici 0 ×ˢ univ) :=
      hcont.add (continuous_const.mul continuous_fst).continuousOn
    have hWd : HasDerivAlongSolutions f W (fun s y => Vdot s y + c)
        {y | ρ ≤ ‖y‖ ∧ ‖y‖ < R} := by
      intro s₀ hs₀ z hz s hs hzs
      have h1 := hVdotr s₀ hs₀ z hz s hs
        (by rw [mem_ball_zero_iff]; exact hzs.2.trans hRr')
      have h2 := h1.add ((hasDerivAt_id s).const_mul c)
      rw [mul_one] at h2
      exact h2
    have hWneg : ∀ s, 0 ≤ s → ∀ y ∈ {y : E | ρ ≤ ‖y‖ ∧ ‖y‖ < R}, Vdot s y + c ≤ 0 := by
      intro s hs y hy
      have h1 : γ ‖y‖ ≤ -Vdot s y := (hbγ s hs).2 y (hy.2.trans hRε₂)
      have h2 : γ ρ ≤ γ ‖y‖ := hγ.le hρ0.le hy.1
      linarith [hc]
    have hanti := antitoneOn_of_isSolution hWc hWd hWneg ht₀ hx (convex_Icc t₀ (t₀ + T))
      Icc_subset_Ici_self (by
        intro s hs
        rw [interior_Icc] at hs
        exact ⟨hs.1, hne s hs.1.le hs.2.le, hin s hs.1.le⟩)
    have h1 := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t₀ ≤ t₀ + T)
    simp only [hW] at h1
    have hVT : 0 ≤ V (t₀ + T) (x (t₀ + T)) := by
      have h2 := (hb (t₀ + T) (by linarith)).2 (x (t₀ + T))
        ((hin (t₀ + T) (by linarith)).trans hRε₀)
      have h3 : 0 ≤ α ‖x (t₀ + T)‖ := by
        have := hα.le le_rfl (norm_nonneg (x (t₀ + T)))
        rwa [hα.2.2] at this
      linarith
    have hV0 : V t₀ (x t₀) ≤ β R := by
      have h2 := hbβ t₀ ht₀ (x t₀) ((hin t₀ le_rfl).trans hRε₁)
      exact h2.trans (hβ.le (norm_nonneg _) (hin t₀ le_rfl).le)
    have hcT : c * T = β R + c := by
      rw [hT]
      field_simp
    nlinarith
  obtain ⟨s, hs₀, hsT, hxs⟩ := hexists
  have := hstayη s (ht₀.trans hs₀) x (hx.mono hs₀)
    (by simpa using hxs.trans_le (min_le_left _ _)) t (hsT.trans ht)
  simpa using this

/-! ### Exponential stability from quadratic bounds (MLS Theorem 4.5, pp. 183–184) -/

/-- **MLS Theorem 4.5, sufficiency, global form, with the rate bounds of p. 184.** Suppose
`V` is continuous on `ℝ₊ × E`, `a₁‖x‖² ≤ V(t, x) ≤ a₂‖x‖²` and `V̇(t, x) ≤ −a₃‖x‖²` for all
`x` and `t ≥ 0`, with `a₁, a₂, a₃ > 0`. Then every solution from `t₀ ≥ 0` satisfies
`‖x(t)‖ ≤ √(a₂/a₁) e^{−(a₃/(2a₂))(t − t₀)} ‖x(t₀)‖` for `t ≥ t₀`, i.e. (4.34) with
`m = √(a₂/a₁)` and `α = a₃/(2a₂)` (MLS p. 184). The fourth bound of Theorem 4.5,
`‖∂V/∂x‖ ≤ a₄‖x‖`, is used only by the converse and is not assumed. -/
theorem norm_le_of_quadratic_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ} {a₁ a₂ a₃ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hlow : ∀ t, 0 ≤ t → ∀ y : E, a₁ * ‖y‖ ^ 2 ≤ V t y)
    (hup : ∀ t, 0 ≤ t → ∀ y : E, V t y ≤ a₂ * ‖y‖ ^ 2)
    (hVdot : HasDerivAlongSolutions f V Vdot univ)
    (hdec : ∀ t, 0 ≤ t → ∀ y : E, Vdot t y ≤ -(a₃ * ‖y‖ ^ 2))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution f t₀ x) {t : ℝ} (ht : t₀ ≤ t) :
    ‖x t‖ ≤ Real.sqrt (a₂ / a₁) * Real.exp (-(a₃ / (2 * a₂)) * (t - t₀)) * ‖x t₀‖ := by
  set k := a₃ / a₂ with hk
  have hk0 : 0 < k := div_pos ha₃ ha₂
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
      have hv := hVdot t₀ ht₀ x hx s hs (mem_univ _)
      have := he.mul hv
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      ring
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 ≤ s := ht₀.trans (le_of_lt hs)
      have h1 := hup s hs0 (x s)
      have h2 := hdec s hs0 (x s)
      have hepos := Real.exp_pos (k * (s - t₀))
      have h3 : k * V s (x s) + Vdot s (x s) ≤ 0 := by
        have : k * (a₂ * ‖x s‖ ^ 2) = a₃ * ‖x s‖ ^ 2 := by
          rw [hk]; field_simp
        nlinarith
      nlinarith
  have hgt : g t ≤ g t₀ := hanti (self_mem_Ici) ht ht
  have hg0 : g t₀ = V t₀ (x t₀) := by simp [hg]
  have hVt : V t (x t) ≤ Real.exp (-(k * (t - t₀))) * (a₂ * ‖x t₀‖ ^ 2) := by
    have h1 : Real.exp (k * (t - t₀)) * V t (x t) ≤ a₂ * ‖x t₀‖ ^ 2 := by
      have := hup t₀ ht₀ (x t₀)
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
      (hlow t (ht₀.trans ht) (x t)).trans hVt
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

/-- **MLS Theorem 4.5, sufficiency, global form (pp. 183–184):** under the hypotheses of
`norm_le_of_quadratic_lyapunov` the origin is globally exponentially stable, with
`m = √(a₂/a₁)` and rate `α = a₃/(2a₂)`. -/
theorem globallyExponentiallyStable_of_quadratic_lyapunov {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    {a₁ a₂ a₃ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hlow : ∀ t, 0 ≤ t → ∀ y : E, a₁ * ‖y‖ ^ 2 ≤ V t y)
    (hup : ∀ t, 0 ≤ t → ∀ y : E, V t y ≤ a₂ * ‖y‖ ^ 2)
    (hVdot : HasDerivAlongSolutions f V Vdot univ)
    (hdec : ∀ t, 0 ≤ t → ∀ y : E, Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) :
    GloballyExponentiallyStable f 0 := by
  refine ⟨Real.sqrt (a₂ / a₁), Real.sqrt_pos.mpr (div_pos ha₂ ha₁), a₃ / (2 * a₂),
    div_pos ha₃ (by positivity), fun t₀ ht₀ x hx t ht => ?_⟩
  simpa using
    norm_le_of_quadratic_lyapunov ha₁ ha₂ ha₃ hcont hlow hup hVdot hdec ht₀ hx ht

end Stability
end RoboLean
