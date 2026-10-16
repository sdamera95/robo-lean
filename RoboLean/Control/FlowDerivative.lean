import RoboLean.Control.StateTransition

/-!
# Solution flows differentiable in the initial state (for MLS Theorem 4.5, p. 183)

**What MLS states.** Theorem 4.5 (p. 183): "`x* = 0` is an exponentially stable equilibrium point of
`ẋ = f(x, t)` if and only if there exists an `ε > 0` and a function `V(x, t)` which satisfies
`α₁‖x‖² ≤ V(x, t) ≤ α₂‖x‖²`, `V̇|_{ẋ = f(x, t)} ≤ −α₃‖x‖²`, `‖∂V/∂x (x, t)‖ ≤ α₄‖x‖` for some
positive constants `α₁, α₂, α₃, α₄`, and `‖x‖ ≤ ε`." MLS gives no proof (it cites its reference
[102]). The standing assumption of p. 179 is that `f(x, t)` satisfies "the standard conditions for
the existence and uniqueness of solutions", for instance Lipschitz continuity in `x`, uniformly in
`t`. The fourth bound concerns `∂V/∂x`; for the usual converse function
`V(x, t) = ∫_t^{t+T} ‖s(τ, x, t)‖² dτ` it needs the derivative of the solution `s(τ, x, t)` in its
initial state `x`.

**The obstruction at the pinned Mathlib.** `Mathlib/Analysis/ODE` proves local existence
(Picard–Lindelöf), uniqueness, Grönwall bounds and Lipschitz dependence on the initial state, but no
differentiability of a flow in the initial state: none of its files mentions `fderiv` or
`HasFDerivAt`. The missing theorem is differentiable dependence on initial conditions: for `f`
continuous in `t` and `C¹` in `x` with bounded derivative, the solution `s(t, x, s₀)` is
differentiable in `x`, and its derivative `D(t, s₀, x)` solves the variational equation
`∂D/∂t = ∂f/∂x(t, s(t, x, s₀)) D`, `D(s₀, s₀, x) = I`.

**Formalized here.** That conclusion as a hypothesis structure, `IsDifferentiableFlow f Df φ D`
(like `HasFlow` and `IsStateTransition`), for a time-varying field `f(t, x)` (time first) on a real
normed space, with `Df t y = ∂f/∂x (t, y)`, `φ t s x = s(t, x, s)` (the state at time `t` of the
solution starting from `x` at time `s`, for `0 ≤ s ≤ t`) and `D t s x = ∂φ(t, s, x)/∂x`.
Consequences: the composition law of the flow (`eq_comp`), the Grönwall bound on `D`
(`norm_fderiv_le_exp`) and the backward Grönwall bound on the flow (`norm_le_exp_mul_norm`). The
linear time-varying case is a discharged instance: a state-transition matrix gives a differentiable
flow with `D = Φ` (`IsStateTransition.isDifferentiableFlow`). The converse of Theorem 4.5 with all
four bounds under this hypothesis is in `Control/ConverseLyapunovGeneral`.

**Conventions.** As in `RoboLean.Stability`: time first, solutions `IsSolution` (continuous on
`[s, ∞)`, an actual derivative at every `t > s`), initial times `s ≥ 0`; derivatives in the state
are Fréchet derivatives (`HasFDerivAt`), continuous linear maps `E →L[ℝ] E` multiplied by
composition.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A solution flow of `ẋ = f(x, t)` differentiable in the initial state, with the variational
equation (MLS Theorem 4.5, p. 183, the fourth bound; MLS's standing assumption, p. 179).** The
fields state: `f(t, ·)` has the Fréchet derivative `Df t y` at every `y` for `t ≥ 0`; `φ s s x = x`;
existence (`t ↦ φ t s x` solves the system from `s`) and uniqueness (every solution from `s ≥ 0` is
`t ↦ φ t s (x s)` on `[s, ∞)`); continuity of `(t, s, x) ↦ φ t s x` on `0 ≤ s ≤ t`; `φ t s` has the
Fréchet derivative `D t s x` at every `x` for `0 ≤ s ≤ t`; `D s s x = 1`; and the variational
equation `∂D(t, s, x)/∂t = Df(t, φ t s x) D(t, s, x)` as a derivative within `[s, ∞)`. A hypothesis
on `f`: differentiable dependence on initial conditions is not in the pinned Mathlib. Time first;
`φ t s x` is MLS's `s(t, x, s)`. -/
structure IsDifferentiableFlow (f : ℝ → E → E) (Df : ℝ → E → E →L[ℝ] E) (φ : ℝ → ℝ → E → E)
    (D : ℝ → ℝ → E → E →L[ℝ] E) : Prop where
  /-- `f(t, ·)` has the Fréchet derivative `Df t y` at `y`, for `t ≥ 0`. -/
  hasFDerivAt_field : ∀ t, 0 ≤ t → ∀ y, HasFDerivAt (f t) (Df t y) y
  /-- The initial condition `s(s, x, s) = x`. -/
  self_eq : ∀ s, 0 ≤ s → ∀ x, φ s s x = x
  /-- Existence: `t ↦ φ t s x` solves the system from `s`. -/
  isSolution : ∀ s, 0 ≤ s → ∀ x, IsSolution f s (fun t => φ t s x)
  /-- Uniqueness: a solution from `s ≥ 0` is `t ↦ φ t s (x s)` on `[s, ∞)`. -/
  eq_of_isSolution : ∀ s, 0 ≤ s → ∀ x : ℝ → E, IsSolution f s x → ∀ t, s ≤ t → x t = φ t s (x s)
  /-- Continuity of `(t, s, x) ↦ φ t s x` on `0 ≤ s ≤ t`. -/
  continuousOn : ContinuousOn (fun p : ℝ × ℝ × E => φ p.1 p.2.1 p.2.2) {p | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1}
  /-- Differentiability in the initial state: `φ t s` has the derivative `D t s x` at `x`. -/
  hasFDerivAt : ∀ t s, 0 ≤ s → s ≤ t → ∀ x, HasFDerivAt (φ t s) (D t s x) x
  /-- `D(s, s, x) = 1`. -/
  fderiv_self : ∀ s, 0 ≤ s → ∀ x, D s s x = 1
  /-- The variational equation `∂D/∂t = Df(t, φ t s x) D`, within `[s, ∞)`. -/
  variational : ∀ t s, 0 ≤ s → s ≤ t → ∀ x,
    HasDerivWithinAt (fun τ => D τ s x) (Df t (φ t s x) * D t s x) (Ici s) t

namespace IsDifferentiableFlow

variable {f : ℝ → E → E} {Df : ℝ → E → E →L[ℝ] E} {φ : ℝ → ℝ → E → E}
  {D : ℝ → ℝ → E → E →L[ℝ] E}

/-- **The composition law of the flow (MLS p. 179, uniqueness of solutions):** for `0 ≤ r ≤ s ≤ t`,
`φ t s (φ s r x) = φ t r x`. -/
theorem eq_comp (h : IsDifferentiableFlow f Df φ D) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) (x : E) : φ t s (φ s r x) = φ t r x :=
  (h.eq_of_isSolution s (hr.trans hrs) _ ((h.isSolution r hr x).mono hrs) t hst).symm

/-- **The trajectory `τ ↦ φ τ s x` is continuous on `[s, ∞)`** (MLS eq. (4.31), p. 179). -/
theorem continuousOn_trajectory (h : IsDifferentiableFlow f Df φ D) {s : ℝ} (hs : 0 ≤ s) (x : E) :
    ContinuousOn (fun τ => φ τ s x) (Ici s) :=
  (h.isSolution s hs x).1

/-- **`τ ↦ D(τ, s, x)` is continuous on `[s, ∞)`** (the variational equation of the derivative in
the initial state, for MLS Theorem 4.5, p. 183). -/
theorem continuousOn_fderiv (h : IsDifferentiableFlow f Df φ D) {s : ℝ} (hs : 0 ≤ s) (x : E) :
    ContinuousOn (fun τ => D τ s x) (Ici s) :=
  fun τ hτ => (h.variational τ s hs hτ x).continuousWithinAt

/-- **Grönwall's bound on the derivative in the initial state (for the fourth bound of MLS Theorem
4.5, p. 183):** if `f(t, ·)` is `K`-Lipschitz for `t ≥ 0`, then `‖D(t, s, x)‖ ≤ e^{K(t − s)}` for
`0 ≤ s ≤ t` (operator norm). -/
theorem norm_fderiv_le_exp (h : IsDifferentiableFlow f Df φ D) {K : NNReal}
    (hf : ∀ t, 0 ≤ t → LipschitzWith K (f t)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : E) :
    ‖D t s x‖ ≤ Real.exp (K * (t - s)) := by
  have hDf : ∀ τ, 0 ≤ τ → ∀ y, ‖Df τ y‖ ≤ K := fun τ hτ y =>
    (h.hasFDerivAt_field τ hτ y).le_of_lipschitz (hf τ hτ)
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun τ => D τ s x)
    (f' := fun τ => Df τ (φ τ s x) * D τ s x) (δ := 1) (K := K) (ε := 0) (a := s) (b := t)
    ((h.continuousOn_fderiv hs x).mono Icc_subset_Ici_self)
    (fun τ hτ => (h.variational τ s hs hτ.1 x).mono (Ici_subset_Ici.2 hτ.1))
    (by simp only [h.fderiv_self s hs x]; exact ContinuousLinearMap.norm_id_le)
    (fun τ hτ => by
      rw [add_zero]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hDf τ (hs.trans hτ.1) _) (norm_nonneg _)))
    t ⟨hst, le_rfl⟩
  simpa [gronwallBound_ε0] using this

/-- **Grönwall's inequality backwards in time along the flow** (the lower bound in the converse of
MLS Theorem 4.5, p. 183): if `‖f(τ, y)‖ ≤ K‖y‖` for `τ > 0`, then `‖x‖ ≤ e^{K(t − s)} ‖φ t s x‖` for
`0 ≤ s ≤ t`. -/
theorem norm_le_exp_mul_norm (h : IsDifferentiableFlow f Df φ D) {K : ℝ}
    (hf : ∀ τ, 0 < τ → ∀ y, ‖f τ y‖ ≤ K * ‖y‖) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : E) :
    ‖x‖ ≤ Real.exp (K * (t - s)) * ‖φ t s x‖ := by
  have hcont : ContinuousOn (fun r => φ (t - r) s x) (Icc 0 (t - s)) := by
    refine (h.continuousOn_trajectory hs x).comp
      (continuous_const.sub continuous_id).continuousOn ?_
    intro r hr
    simp only [mem_Ici]
    linarith [hr.2]
  have hder : ∀ r ∈ Ico 0 (t - s),
      HasDerivWithinAt (fun r => φ (t - r) s x) (-f (t - r) (φ (t - r) s x)) (Ici r) r := by
    intro r hr
    have hpos : s < t - r := by linarith [hr.2]
    have h1 := (h.isSolution s hs x).2 (t - r) hpos
    have h2 : HasDerivAt (fun r => t - r) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub t
    have h3 := h1.scomp r h2
    simpa [Function.comp_def] using h3.hasDerivWithinAt
  have hbound : ∀ r ∈ Ico 0 (t - s),
      ‖-f (t - r) (φ (t - r) s x)‖ ≤ K * ‖φ (t - r) s x‖ + 0 := by
    intro r hr
    rw [norm_neg, add_zero]
    exact hf _ (by linarith [hr.2]) _
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder (le_refl _) hbound (t - s)
    ⟨by linarith, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero, sub_sub_cancel, h.self_eq s hs, sub_zero] at key
  linarith [mul_comm (‖φ t s x‖) (Real.exp (K * (t - s)))]

end IsDifferentiableFlow

/-- **The linear time-varying case is a discharged instance (MLS eq. (4.40), p. 184):** a
state-transition matrix `Φ` of `ż = A(t)z` gives a differentiable flow `φ t s x = Φ(t, s) x` with
`Df t y = A(t)` and `D t s x = Φ(t, s)`; the variational equation is `∂Φ(t, s)/∂t = A(t) Φ(t, s)`.
On a real Banach space. -/
theorem IsStateTransition.isDifferentiableFlow [CompleteSpace E] {A : ℝ → E →L[ℝ] E}
    {Φ : ℝ → ℝ → E →L[ℝ] E} (h : IsStateTransition A Φ) :
    IsDifferentiableFlow (fun t z => A t z) (fun t _ => A t) (fun t s x => Φ t s x)
      (fun t s _ => Φ t s) := by
  refine ⟨fun t _ y => (A t).hasFDerivAt, fun s hs x => by simp [h.self_eq_one s hs],
    fun s hs x => h.isSolution hs x, fun s hs x hx t hst => h.eq_of_isSolution hs hx hst, ?_,
    fun t s _ _ x => (Φ t s).hasFDerivAt, fun s hs _ => h.self_eq_one s hs,
    fun t s hs hst _ => (h.hasDerivWithinAt t s (hs.trans hst) hs).mono (Ici_subset_Ici.2 hs)⟩
  have hX : ContinuousOn (fun p : ℝ × ℝ × E => Φ p.1 0) {p | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1} :=
    (h.continuousOn le_rfl).comp continuous_fst.continuousOn fun p hp =>
      (mem_Ici.2 (hp.1.trans hp.2))
  have hY : ContinuousOn (fun p : ℝ × ℝ × E => Φ 0 p.2.1) {p | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1} :=
    (h.continuousOn_snd le_rfl).comp (continuous_fst.comp continuous_snd).continuousOn
      fun p hp => mem_Ici.2 hp.1
  refine ((hX.mul hY).clm_apply (continuous_snd.comp continuous_snd).continuousOn).congr ?_
  intro p hp
  change Φ p.1 p.2.1 p.2.2 = (Φ p.1 0 * Φ 0 p.2.1) p.2.2
  rw [h.mul_eq p.1 0 p.2.1 (hp.1.trans hp.2) le_rfl hp.1]

end Stability
end RoboLean
