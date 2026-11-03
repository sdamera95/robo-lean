import RoboLean.Nonholonomic.Filtration
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Drift-free control systems, reachable sets and Chow's theorem as a statement

MLS Chapter 7, printed pp. 329–331: the drift-free system (7.10) `Σ : q̇ = g₁(q) u₁ + ⋯ + g_m(q) u_m`,
`u ∈ U ⊂ ℝ^m`; controllability; the reachable sets `R^V(q₀, T)` and `R^V(q₀, ≤ T)`; small-time
local controllability; Theorem 7.5 (Chow, p. 329); the reversal step of Proposition 7.7 (p. 331);
and Exercise 4 (p. 349).

**Conventions.** Controls are piecewise constant (`IsPiecewiseConstant U T u`: values in `U` on
`[0, T]`, locally constant on `(0, T)` away from finitely many switching times); MLS names no
control class in (7.10), and the proof of Proposition 7.7 chooses "a piecewise constant `u`"
(p. 331). A trajectory on `[0, T]` (`IsTrajectory g u T x`) is continuous on `[0, T]` and satisfies
`ẋ(t) = Σ uⱼ(t) gⱼ(x(t))` at every `t ∈ (0, T)` away from finitely many times. `R^V(q₀, T)` is the
set of endpoints `x(T)` of trajectories from `x(0) = q₀` that stay in `V` on `[0, T]` (p. 329 writes
"steers `Σ` from `q(0) = q₀` to `q(T) = q_f`" for the point `q` of the set). Local controllability at
`q₀`: `R^V(q₀, ≤ T)` is a neighborhood of `q₀` for every neighborhood `V` of `q₀` and every `T > 0`.

**Corrected printing.** Exercise 4(a) prints `ũ(t) = u(t/T)`; the input that steers in one unit of
time along `t ↦ q(T t)` is `ũ(t) = T u(T t)`, used here. The reversal `ū(t) = −ũ(1 − t)` of 4(b) and
`u′(t) = −u(T/2 − t)` of Proposition 7.7 need `−u` to be admissible: `U = −U`, a hypothesis the book
does not state.

**Chow's theorem** is recorded as the named proposition `ChowStatement E` (smooth generators, the
controllability rank condition at `q`, unconstrained controls `U = ℝ^m`) and proved for
finite-dimensional `E` in `Nonholonomic/Chow` (`chowStatement`) by the maximal-rank argument on
composed flows of the generators; MLS sketches a proof (Propositions 7.6–7.7) that flows along
brackets.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS eq. (7.10), p. 329: the drift-free right-hand side `Σⱼ uⱼ gⱼ(q)`.** -/
def driftFree (g : Fin m → E → E) (q : E) (u : Fin m → ℝ) : E := ∑ j, u j • g j q

/-- **MLS p. 329: a trajectory of (7.10) on `[0, T]` for the input `u`:** continuous on `[0, T]`,
with derivative `Σⱼ uⱼ(t) gⱼ(x(t))` at every `t ∈ (0, T)` outside a finite set (the switching
times of a piecewise constant input). -/
def IsTrajectory (g : Fin m → E → E) (u : ℝ → Fin m → ℝ) (T : ℝ) (x : ℝ → E) : Prop :=
  ContinuousOn x (Icc 0 T) ∧
    ∃ S : Finset ℝ, ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivAt x (driftFree g (x t) (u t)) t

/-- **MLS pp. 329 and 331: a piecewise constant input with values in `U` on `[0, T]`:** locally
constant at every `t ∈ (0, T)` outside a finite set of switching times. -/
def IsPiecewiseConstant (U : Set (Fin m → ℝ)) (T : ℝ) (u : ℝ → Fin m → ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, u t ∈ U) ∧ ∃ S : Finset ℝ, ∀ t ∈ Ioo 0 T, t ∉ S → ∀ᶠ s in 𝓝 t, u s = u t

/-- **MLS p. 329: the reachable set `R^V(q₀, T)`:** the endpoints `x(T)` of trajectories of (7.10)
on `[0, T]` with piecewise constant inputs in `U`, starting at `q₀` and staying in `V`. -/
def reachableSet (g : Fin m → E → E) (U : Set (Fin m → ℝ)) (V : Set E) (q₀ : E) (T : ℝ) :
    Set E :=
  {q | ∃ u x, IsPiecewiseConstant U T u ∧ IsTrajectory g u T x ∧ x 0 = q₀ ∧ x T = q ∧
    ∀ t ∈ Icc 0 T, x t ∈ V}

/-- **MLS p. 329: `R^V(q₀, ≤ T) = ⋃_{0 < τ ≤ T} R^V(q₀, τ)`.** -/
def reachableSetLE (g : Fin m → E → E) (U : Set (Fin m → ℝ)) (V : Set E) (q₀ : E) (T : ℝ) :
    Set E :=
  ⋃ τ ∈ Ioc 0 T, reachableSet g U V q₀ τ

/-- **MLS p. 329: small-time local controllability at `q₀`:** `R^V(q₀, ≤ T)` contains a
neighborhood of `q₀` for every neighborhood `V` of `q₀` and every `T > 0`. -/
def IsLocallyControllableAt (g : Fin m → E → E) (U : Set (Fin m → ℝ)) (q₀ : E) : Prop :=
  ∀ V ∈ 𝓝 q₀, ∀ T : ℝ, 0 < T → reachableSetLE g U V q₀ T ∈ 𝓝 q₀

/-- **MLS p. 329: controllability:** every `q_f` is reachable from every `q₀` in some time
`T > 0`. -/
def IsControllable (g : Fin m → E → E) (U : Set (Fin m → ℝ)) : Prop :=
  ∀ q₀ qf : E, ∃ T : ℝ, 0 < T ∧ qf ∈ reachableSet g U Set.univ q₀ T

/-- **MLS Theorem 7.5 (Chow), p. 329, as a named statement, proved for finite-dimensional `E` in
`Nonholonomic/Chow` (`chowStatement`):** for smooth generators,
if the controllability Lie algebra `L(g₁, …, g_m)` has full rank at `q`, the system (7.10) with
unconstrained inputs is locally controllable at `q`. -/
def ChowStatement (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ (m : ℕ) (g : Fin m → E → E), (∀ j, ContDiff ℝ ∞ (g j)) → ∀ q : E,
    lieAlgebraAt g q = ⊤ → IsLocallyControllableAt g Set.univ q

/-- **MLS eq. (7.10), p. 329:** the drift-free right-hand side is linear in the input; in
particular `Σ (−uⱼ) gⱼ = −Σ uⱼ gⱼ`. -/
theorem driftFree_neg (g : Fin m → E → E) (q : E) (u : Fin m → ℝ) :
    driftFree g q (-u) = -driftFree g q u := by
  simp [driftFree, Finset.sum_neg_distrib, neg_smul]

/-- **MLS eq. (7.10), p. 329:** `Σ (c uⱼ) gⱼ = c Σ uⱼ gⱼ`. -/
theorem driftFree_smul (g : Fin m → E → E) (q : E) (c : ℝ) (u : Fin m → ℝ) :
    driftFree g q (c • u) = c • driftFree g q u := by
  simp [driftFree, Finset.smul_sum, smul_smul]

/-- **MLS Exercise 4(b), p. 349, and Proposition 7.7, p. 331: reversal.** If `x` is a trajectory
on `[0, T]` for the input `u`, then `t ↦ x(T − t)` is a trajectory on `[0, T]` for the input
`t ↦ −u(T − t)`: the system is drift-free, so it can "flow backwards". -/
theorem IsTrajectory.reverse {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {T : ℝ} {x : ℝ → E}
    (hx : IsTrajectory g u T x) :
    IsTrajectory g (fun t => -u (T - t)) T (fun t => x (T - t)) := by
  obtain ⟨hc, S, hS⟩ := hx
  refine ⟨hc.comp (continuous_const.sub continuous_id).continuousOn fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩, S.image (fun s => T - s), fun t ht htS => ?_⟩
  have h1 : T - t ∈ Ioo 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h2 : T - t ∉ S := fun h => htS (Finset.mem_image.2 ⟨T - t, h, by ring⟩)
  have hd' : HasDerivAt (fun s => T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  simpa [Function.comp_def, driftFree_neg] using (hS (T - t) h1 h2).scomp t hd'

/-- **MLS Exercise 4(a), p. 349, corrected printing: rescaling to unit time.** If `x` is a
trajectory on `[0, T]`, `T > 0`, for the input `u`, then `t ↦ x(T t)` is a trajectory on `[0, 1]`
for the input `t ↦ T u(T t)` (MLS prints `u(t/T)`). -/
theorem IsTrajectory.rescale {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {T : ℝ} {x : ℝ → E}
    (hT : 0 < T) (hx : IsTrajectory g u T x) :
    IsTrajectory g (fun t => T • u (T * t)) 1 (fun t => x (T * t)) := by
  obtain ⟨hc, S, hS⟩ := hx
  refine ⟨hc.comp (continuous_const.mul continuous_id).continuousOn fun t ht =>
    ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩, S.image (fun s => s / T), fun t ht htS => ?_⟩
  have h1 : T * t ∈ Ioo 0 T := ⟨mul_pos hT ht.1, by nlinarith [ht.2]⟩
  have h2 : T * t ∉ S := fun h => htS (Finset.mem_image.2 ⟨T * t, h, by field_simp⟩)
  have hd' : HasDerivAt (fun s => T * s) T t := by
    simpa using (hasDerivAt_id t).const_mul T
  simpa [Function.comp_def, driftFree_smul] using (hS (T * t) h1 h2).scomp t hd'

/-- **MLS Proposition 7.7, p. 331:** the reversed input `t ↦ −u(T − t)` of a piecewise constant
input with values in a symmetric set `U = −U` is piecewise constant with values in `U`. -/
theorem IsPiecewiseConstant.reverse {U : Set (Fin m → ℝ)} {T : ℝ} {u : ℝ → Fin m → ℝ}
    (hU : ∀ v ∈ U, -v ∈ U) (hu : IsPiecewiseConstant U T u) :
    IsPiecewiseConstant U T (fun t => -u (T - t)) := by
  obtain ⟨hv, S, hS⟩ := hu
  refine ⟨fun t ht => hU _ (hv _ ⟨by linarith [ht.2], by linarith [ht.1]⟩),
    S.image (fun s => T - s), fun t ht htS => ?_⟩
  have h1 : T - t ∈ Ioo 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h2 : T - t ∉ S := fun h => htS (Finset.mem_image.2 ⟨T - t, h, by ring⟩)
  have hlim : Tendsto (fun s => T - s) (𝓝 t) (𝓝 (T - t)) :=
    (continuous_const.sub continuous_id).tendsto t
  filter_upwards [hlim.eventually (hS (T - t) h1 h2)] with s hs
  rw [hs]

/-- **MLS Exercise 4(a), p. 349:** the rescaled input `t ↦ T u(T t)`, `T > 0`, of a piecewise
constant input is piecewise constant on `[0, 1]`, with values in `U` when `U` is closed under
multiplication by `T`. -/
theorem IsPiecewiseConstant.rescale {U : Set (Fin m → ℝ)} {T : ℝ} {u : ℝ → Fin m → ℝ}
    (hT : 0 < T) (hU : ∀ v ∈ U, T • v ∈ U) (hu : IsPiecewiseConstant U T u) :
    IsPiecewiseConstant U 1 (fun t => T • u (T * t)) := by
  obtain ⟨hv, S, hS⟩ := hu
  refine ⟨fun t ht => hU _ (hv _ ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩),
    S.image (fun s => s / T), fun t ht htS => ?_⟩
  have h1 : T * t ∈ Ioo 0 T := ⟨mul_pos hT ht.1, by nlinarith [ht.2]⟩
  have h2 : T * t ∉ S := fun h => htS (Finset.mem_image.2 ⟨T * t, h, by field_simp⟩)
  have hlim : Tendsto (fun s => T * s) (𝓝 t) (𝓝 (T * t)) :=
    (continuous_const.mul continuous_id).tendsto t
  filter_upwards [hlim.eventually (hS (T * t) h1 h2)] with s hs
  rw [hs]

/-- **MLS Proposition 7.7, p. 331, the reversal step:** for a symmetric input set `U = −U`, if `q`
is reachable from `q₀` in time `T` inside `V`, then `q₀` is reachable from `q` in time `T` inside
`V`. -/
theorem mem_reachableSet_reverse {g : Fin m → E → E} {U : Set (Fin m → ℝ)} {V : Set E}
    {q₀ q : E} {T : ℝ} (hU : ∀ v ∈ U, -v ∈ U) (h : q ∈ reachableSet g U V q₀ T) :
    q₀ ∈ reachableSet g U V q T := by
  obtain ⟨u, x, hu, hx, h0, hxT, hV⟩ := h
  exact ⟨fun t => -u (T - t), fun t => x (T - t), hu.reverse hU, hx.reverse,
    by simpa using hxT, by simpa using h0,
    fun t ht => hV _ ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

/-- **MLS Exercise 4(a), p. 349, corrected printing:** a point reachable in time `T > 0` is
reachable in unit time, when `U` is closed under multiplication by `T`. -/
theorem mem_reachableSet_one {g : Fin m → E → E} {U : Set (Fin m → ℝ)} {V : Set E} {q₀ q : E}
    {T : ℝ} (hT : 0 < T) (hU : ∀ v ∈ U, T • v ∈ U) (h : q ∈ reachableSet g U V q₀ T) :
    q ∈ reachableSet g U V q₀ 1 := by
  obtain ⟨u, x, hu, hx, h0, hxT, hV⟩ := h
  exact ⟨fun t => T • u (T * t), fun t => x (T * t), hu.rescale hT hU, hx.rescale hT,
    by simpa using h0, by simpa using hxT,
    fun t ht => hV _ ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩⟩

/-- **MLS Exercise 4, p. 349:** with unconstrained inputs, if an input steers `q₀` to `q_f` in time
`T > 0`, an input steers `q_f` back to `q₀` in unit time. -/
theorem mem_reachableSet_one_reverse {g : Fin m → E → E} {V : Set E} {q₀ qf : E} {T : ℝ}
    (hT : 0 < T) (h : qf ∈ reachableSet g Set.univ V q₀ T) :
    q₀ ∈ reachableSet g Set.univ V qf 1 := by
  exact mem_reachableSet_reverse (fun v _ => Set.mem_univ _)
    (mem_reachableSet_one hT (fun v _ => Set.mem_univ _) h)

/-- **MLS p. 329:** a point of `V` is reachable from itself in any time `T` with the zero input,
when `0 ∈ U`. -/
theorem self_mem_reachableSet {g : Fin m → E → E} {U : Set (Fin m → ℝ)} {V : Set E} {q₀ : E}
    {T : ℝ} (hU : (0 : Fin m → ℝ) ∈ U) (hV : q₀ ∈ V) :
    q₀ ∈ reachableSet g U V q₀ T := by
  refine ⟨fun _ => 0, fun _ => q₀,
    ⟨fun _ _ => hU, ∅, fun _ _ _ => Filter.Eventually.of_forall fun _ => rfl⟩,
    ⟨continuousOn_const, ∅, fun t _ _ => ?_⟩, rfl, rfl, fun _ _ => hV⟩
  simpa [driftFree] using hasDerivAt_const t q₀

end Nonholonomic
end RoboLean
