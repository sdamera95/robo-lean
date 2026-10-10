import RoboLean.Control.Stability
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Solution flows of autonomous systems (an interface for MLS §4.5, pp. 188–189)

MLS assumes "the standard conditions for the existence and uniqueness of solutions" (p. 179) and,
for Lasalle's principle, writes the solution of the autonomous system `ẋ = f(x)` (eq. (4.46),
p. 188) as `s(t, x₀, t₀)`, the state at time `t` of the solution starting from `x₀` at `t₀`.
The E016 notions quantify over all solutions and prove nothing about their existence. Lasalle's
principle needs more: every solution must exist for all forward time, be unique, and depend
continuously on its initial state. That is packaged here as a hypothesis structure, `HasFlow F φ`,
for the autonomous system written in E016's carrier as `fun _ => F` (time first, ignored):

* `φ t x₀` is MLS's `s(t₀ + t, x₀, t₀)` for every `t₀`; `φ 0 x₀ = x₀`;
* existence: `t ↦ φ t x₀` solves the system from time `0`; hence `t ↦ φ (t − t₀) x₀` solves it
  from every `t₀` (`HasFlow.isSolution_sub`);
* uniqueness: every solution from `t₀ ≥ 0` equals `t ↦ φ (t − t₀) (x(t₀))` on `[t₀, ∞)`;
* continuous dependence: each `φ t` (`t ≥ 0`) is continuous on the whole state space.

The structure presupposes forward completeness (no finite escape time); it is not proved from
Picard–Lindelöf here. What is proved: for a globally Lipschitz field, uniqueness and continuous
dependence follow from Mathlib's Grönwall bounds, so `HasFlow` reduces to forward existence
(`HasFlow.of_lipschitzWith`); and every linear field `ẋ = A x` on a complete space has the flow
`φ t = exp(t A)` (`hasFlow_linear`). Shifting a flow by a constant gives the flow of the shifted
field (`HasFlow.comp_sub_const`).

Relation to Mathlib's `Flow`: a `Flow ℝ E` is a two-sided action of `ℝ`, jointly continuous in
`(t, x)`. Neither two-sidedness nor joint continuity is needed for Lasalle's principle, and many
systems are not backward complete, so a forward version is used.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Autonomous systems: translation in time -/

/-- **Solutions of an autonomous system can be translated in time** (MLS eq. (4.46), p. 188: for
`ẋ = f(x)` the solution `s(t, x₀, t₀)` depends on `t − t₀` only). If `y` solves `ẋ = F(x)` from
`s`, then `t ↦ y(t − c)` solves it from `s + c`. The system is written `fun _ => F`. -/
theorem IsSolution.comp_sub_const {F : E → E} {s : ℝ} {y : ℝ → E}
    (hy : IsSolution (fun _ => F) s y) (c : ℝ) :
    IsSolution (fun _ => F) (s + c) (fun t => y (t - c)) := by
  obtain ⟨hc, hd⟩ := hy
  refine ⟨hc.comp (continuous_id.sub continuous_const).continuousOn fun t ht => ?_, fun t ht => ?_⟩
  · simp only [mem_Ici] at ht ⊢
    linarith
  · exact (hd (t - c) (by linarith)).comp_sub_const t c

/-- **At the initial time a solution of a continuous autonomous system has the right derivative
`F(x(t₀))`** (MLS eq. (4.31), p. 179). `IsSolution` asks only continuity at `t₀`; the right
derivative there follows from the limit of the derivatives `F(x(t)) → F(x(t₀))`. -/
theorem IsSolution.hasDerivWithinAt_Ici {F : E → E} (hF : Continuous F) {t₀ : ℝ} {x : ℝ → E}
    (hx : IsSolution (fun _ => F) t₀ x) : HasDerivWithinAt x (F (x t₀)) (Ici t₀) t₀ := by
  have hcw : ContinuousWithinAt x (Ioi t₀) t₀ := (hx.1 t₀ self_mem_Ici).mono Ioi_subset_Ici_self
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi t₀)
    (fun t ht => (hx.2 t ht).differentiableAt.differentiableWithinAt) hcw self_mem_nhdsWithin ?_
  refine ((hF.tendsto (x t₀)).comp hcw.tendsto).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ((hx.2 t ht).deriv).symm

/-- On `[t₀, b)` a solution of a continuous autonomous system has the right derivative `F(x(t))`
(the hypothesis form of Mathlib's Grönwall and uniqueness theorems). -/
theorem IsSolution.hasDerivWithinAt_Ici_of_mem {F : E → E} (hF : Continuous F) {t₀ : ℝ}
    {x : ℝ → E} (hx : IsSolution (fun _ => F) t₀ x) {t : ℝ} (ht : t₀ ≤ t) :
    HasDerivWithinAt x (F (x t)) (Ici t) t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    exact hx.hasDerivWithinAt_Ici hF
  · exact (hx.2 t h).hasDerivWithinAt

/-! ### Uniqueness and continuous dependence for globally Lipschitz fields -/

/-- **Grönwall's bound for two solutions of a globally Lipschitz autonomous system** (the
continuous-dependence part of MLS's standing assumption, p. 179): if `F` is `K`-Lipschitz and `x`,
`y` solve `ẋ = F(x)` from `t₀`, then `‖x(t) − y(t)‖ ≤ ‖x(t₀) − y(t₀)‖ e^{K(t − t₀)}` for
`t ≥ t₀`, in distance form. -/
theorem IsSolution.dist_le_of_lipschitzWith {F : E → E} {K : NNReal} (hF : LipschitzWith K F)
    {t₀ : ℝ} {x y : ℝ → E} (hx : IsSolution (fun _ => F) t₀ x)
    (hy : IsSolution (fun _ => F) t₀ y) {t : ℝ} (ht : t₀ ≤ t) :
    dist (x t) (y t) ≤ dist (x t₀) (y t₀) * Real.exp (K * (t - t₀)) :=
  dist_le_of_trajectories_ODE (v := fun _ => F) (fun _ => hF) (hx.1.mono Icc_subset_Ici_self)
    (fun _ hs => hx.hasDerivWithinAt_Ici_of_mem hF.continuous hs.1)
    (hy.1.mono Icc_subset_Ici_self) (fun _ hs => hy.hasDerivWithinAt_Ici_of_mem hF.continuous hs.1)
    le_rfl t ⟨ht, le_rfl⟩

/-- **Uniqueness of solutions of a globally Lipschitz autonomous system** (MLS p. 179: "`f(x, t)`
Lipschitz continuous with respect to `x`" is one of the standard conditions MLS assumes): two
solutions from `t₀` with the same initial state agree on `[t₀, ∞)`. -/
theorem IsSolution.eq_of_lipschitzWith {F : E → E} {K : NNReal} (hF : LipschitzWith K F)
    {t₀ : ℝ} {x y : ℝ → E} (hx : IsSolution (fun _ => F) t₀ x)
    (hy : IsSolution (fun _ => F) t₀ y) (h0 : x t₀ = y t₀) {t : ℝ} (ht : t₀ ≤ t) :
    x t = y t := by
  have := hx.dist_le_of_lipschitzWith hF hy ht
  rw [h0, dist_self, zero_mul] at this
  exact dist_le_zero.mp this

/-! ### The flow interface -/

/-- **The solution flow of an autonomous system `ẋ = F(x)` (MLS eq. (4.46) and the standing
assumption of p. 179).** `φ t x₀` is the state at time `t₀ + t` of the solution that starts from
`x₀` at time `t₀` (MLS's `s(t₀ + t, x₀, t₀)`). The fields state: the initial condition; existence
of the solution for all forward time; uniqueness of solutions from every initial time `t₀ ≥ 0`;
and continuous dependence on the initial state at each fixed time `t ≥ 0`. This is a hypothesis
on `F`; it is not derived from Picard–Lindelöf. The system is `fun _ => F` in the carrier of
`IsSolution` (time first, ignored). -/
structure HasFlow (F : E → E) (φ : ℝ → E → E) : Prop where
  /-- The initial condition `s(t₀, x₀, t₀) = x₀`. -/
  map_zero : ∀ x, φ 0 x = x
  /-- Existence: the curve `t ↦ φ t x₀` solves the system from time `0`. -/
  isSolution : ∀ x, IsSolution (fun _ => F) 0 (fun t => φ t x)
  /-- Uniqueness: a solution from `t₀ ≥ 0` is `t ↦ φ (t − t₀) (x t₀)` on `[t₀, ∞)`. -/
  eq_of_isSolution : ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → E, IsSolution (fun _ => F) t₀ x →
    ∀ t, t₀ ≤ t → x t = φ (t - t₀) (x t₀)
  /-- Continuous dependence on the initial state, at each forward time. -/
  continuous : ∀ t, 0 ≤ t → Continuous (φ t)

namespace HasFlow

variable {F : E → E} {φ : ℝ → E → E}

/-- **Existence from every initial time (MLS p. 188):** `t ↦ φ (t − t₀) x₀`, MLS's
`s(t, x₀, t₀)`, solves `ẋ = F(x)` from `t₀` and starts at `x₀`. -/
theorem isSolution_sub (h : HasFlow F φ) (t₀ : ℝ) (x₀ : E) :
    IsSolution (fun _ => F) t₀ (fun t => φ (t - t₀) x₀) := by
  simpa using (h.isSolution x₀).comp_sub_const t₀

/-- **The semigroup property of the flow** (a consequence of uniqueness, MLS p. 179):
`φ (t + s) x = φ t (φ s x)` for `s, t ≥ 0`. -/
theorem map_add (h : HasFlow F φ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    φ (t + s) x = φ t (φ s x) := by
  have := h.eq_of_isSolution s hs (fun r => φ r x) ((h.isSolution x).mono hs) (t + s)
    (by linarith)
  simpa using this

/-- The trajectory `t ↦ φ t x₀` is continuous on `[0, ∞)` (MLS p. 188). -/
theorem continuousOn_trajectory (h : HasFlow F φ) (x₀ : E) :
    ContinuousOn (fun t => φ t x₀) (Ici 0) :=
  (h.isSolution x₀).1

/-- **A solution converges along `atTop` exactly as the flow from its initial state does**
(uniqueness, MLS p. 188): for a solution `x` from `t₀ ≥ 0` and any filter `l`, if
`φ t (x t₀)` tends to `l` then so does `x t`. -/
theorem tendsto_of_isSolution (h : HasFlow F φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E}
    (hx : IsSolution (fun _ => F) t₀ x) {l : Filter E}
    (hl : Tendsto (fun t => φ t (x t₀)) atTop l) : Tendsto x atTop l := by
  have hshift : Tendsto (fun t : ℝ => t - t₀) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-t₀) tendsto_id
  refine (hl.comp hshift).congr' ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact (h.eq_of_isSolution t₀ ht₀ x hx t ht).symm

/-- **For a globally Lipschitz field, a flow is forward existence** (MLS p. 179): if `F` is
Lipschitz, `φ 0 x = x` and every `t ↦ φ t x` solves `ẋ = F(x)` from `0`, then uniqueness and
continuous dependence hold (Grönwall), so `HasFlow F φ`. -/
theorem of_lipschitzWith {K : NNReal} (hF : LipschitzWith K F) (h0 : ∀ x, φ 0 x = x)
    (hsol : ∀ x, IsSolution (fun _ => F) 0 (fun t => φ t x)) : HasFlow F φ where
  map_zero := h0
  isSolution := hsol
  eq_of_isSolution := by
    intro t₀ _ x hx t ht
    have hy : IsSolution (fun _ => F) t₀ (fun s => φ (s - t₀) (x t₀)) := by
      simpa using (hsol (x t₀)).comp_sub_const t₀
    exact hx.eq_of_lipschitzWith hF hy (by simp [h0]) ht
  continuous := by
    intro t ht
    refine (LipschitzWith.of_dist_le_mul fun x y => ?_ :
      LipschitzWith (Real.toNNReal (Real.exp (K * t))) (φ t)).continuous
    have := (hsol x).dist_le_of_lipschitzWith hF (hsol y) ht
    rw [h0, h0, sub_zero] at this
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm]
    exact this

/-- **Shifting the state by a constant** (MLS p. 179, "by shifting the origin"): if `φ` is a flow
of `F`, then `t x ↦ φ t (x − c) + c` is a flow of `x ↦ F(x − c)`, whose rest points are those of
`F` moved by `c`. -/
theorem comp_sub_const (h : HasFlow F φ) (c : E) :
    HasFlow (fun x => F (x - c)) (fun t x => φ t (x - c) + c) := by
  have hs : shift (fun _ => fun x => F (x - c)) c = fun _ => F := by
    funext t z
    simp [shift]
  refine ⟨fun x => by simp [h.map_zero], fun x => ?_, fun t₀ ht₀ x hx t ht => ?_, fun t ht =>
    ((h.continuous t ht).comp (continuous_id.sub continuous_const)).add continuous_const⟩
  · apply (isSolution_shift_iff (f := fun _ => fun x => F (x - c)) (xe := c) (t₀ := 0)
      (x := fun t => φ t (x - c) + c)).mp
    rw [hs]
    simpa using h.isSolution (x - c)
  · have hx' : IsSolution (fun _ => F) t₀ (fun s => x s - c) := by
      have := (isSolution_shift_iff (f := fun _ => fun x => F (x - c)) (xe := c)).mpr hx
      rwa [hs] at this
    have := h.eq_of_isSolution t₀ ht₀ _ hx' t ht
    rw [← this, sub_add_cancel]

end HasFlow

/-- **The flow of a linear system `ẋ = A x` is `φ t = exp(t A)`** (MLS Example 4.5, eq. (4.42),
p. 186, is such a system). For a continuous linear map `A` on a complete space, `t ↦ exp(t A) x₀`
solves the system and starts at `x₀` (Mathlib's `hasDerivAt_exp_smul_const'`), and `A` is
Lipschitz, so all fields of `HasFlow` hold. The exponential is Mathlib's `NormedSpace.exp` in the
Banach algebra `E →L[ℝ] E`. -/
theorem hasFlow_linear [CompleteSpace E] (A : E →L[ℝ] E) :
    HasFlow (fun x => A x) (fun t x => NormedSpace.exp (t • A) x) := by
  have hd : ∀ x t, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) x)
      (A (NormedSpace.exp (t • A) x)) t := by
    intro x t
    have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
    have h2 := h1.clm_apply (hasDerivAt_const t x)
    simpa using h2
  refine HasFlow.of_lipschitzWith A.lipschitzWith (fun x => by simp) fun x => ⟨?_, ?_⟩
  · exact fun t _ => (hd x t).continuousAt.continuousWithinAt
  · exact fun t _ => hd x t

end Stability
end RoboLean
