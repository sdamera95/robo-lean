import RoboLean.Control.StateTransition

/-!
# State-transition matrices and piecewise continuous `A(t)` (MLS pp. 179, 184)

**What MLS states.** Theorem 4.6 (p. 184) assumes the uniform linearization (4.39), `A(·)` bounded
and `0` uniformly asymptotically stable for `ż = A(t)z` (4.40); the standing conditions of p. 179
are "for instance, that `f(x, t)` is Lipschitz continuous with respect to `x`, uniformly in `t`, and
piecewise continuous in `t`". The library's Theorem 4.6 with a time-varying `A(t)` constructs a
state-transition matrix (`IsStateTransition A Φ`) from `A` continuous on `[0, ∞)`, a hypothesis MLS
does not state; the versions that take `IsStateTransition A Φ` as a hypothesis
(`IsStateTransition.exponentiallyStable_of_isUniformLinearization` and
`IsStateTransition.exponentiallyStable_of_isUniformLinearization_of_norm_le`) assume no continuity
of `A` beyond what `Φ` carries.

**Formalized here: what `Φ` carries.** `IsStateTransition A Φ` asks `∂Φ(t, s)/∂t = A(t) Φ(t, s)` at
every `t ≥ 0` (a derivative within `[0, ∞)`, so a two-sided derivative at every `t > 0`), as the
library's solutions (`IsSolution`) ask a derivative at every time. Then `A` agrees with each of its
one-sided limits: if `A(τ) → L` as `τ → t⁻` (`t > 0`) or as `τ → t⁺` (`t ≥ 0`), then `L = A(t)`
(`IsStateTransition.eq_of_tendsto_nhdsWithin_Iio`,
`IsStateTransition.eq_of_tendsto_nhdsWithin_Ioi`). Consequently, for `A` with one-sided limits at
every point (in particular for `A` continuous except at finitely many points of every bounded
interval, with one-sided limits there), a state-transition matrix exists only if `A` is continuous
on `[0, ∞)` (`IsStateTransition.continuousOn_of_forall_tendsto`): within the library's notion of
solution, the continuity hypothesis of Theorem 4.6 costs nothing for such `A`, and a
state-transition matrix for an `A` with a jump does not exist (an instance is in
`Examples/ConverseLyapunovGeneral`). Theorem 4.6 for `A` with jumps needs solutions with derivatives
off the jump times (Carathéodory solutions), which is a change of the library's notion of solution,
not formalized.

**Conventions.** As in `StateTransition`: time first, `A : ℝ → (E →L[ℝ] E)`, `Φ(t, s) : E →L[ℝ] E`,
times `t, s ≥ 0`; one-sided limits are Mathlib's `𝓝[<] t` and `𝓝[>] t` in the operator norm.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : ℝ → E →L[ℝ] E}
  {Φ : ℝ → ℝ → E →L[ℝ] E}

namespace IsStateTransition

/-- **A state-transition matrix forces `A` to agree with its left limits (MLS eq. (4.40), p. 184,
with the piecewise continuity allowed on p. 179).** If `IsStateTransition A Φ`, `t > 0` and
`A(τ) → L` as `τ → t⁻`, then `L = A(t)`: the derivative of `τ ↦ Φ(τ, t)` at `t` is `A(t)` and also
the left limit `L Φ(t, t) = L` of its derivatives. -/
theorem eq_of_tendsto_nhdsWithin_Iio (h : IsStateTransition A Φ) {t : ℝ} (ht : 0 < t)
    {L : E →L[ℝ] E} (hL : Tendsto A (𝓝[<] t) (𝓝 L)) : L = A t := by
  set g : ℝ → E →L[ℝ] E := fun τ => Φ τ t with hg
  have hcont : ContinuousAt g t := (h.continuousOn ht.le).continuousAt (Ici_mem_nhds ht)
  have hdiff : DifferentiableOn ℝ g (Ioo 0 t) := fun τ hτ =>
    (h.hasDerivAt hτ.1 ht.le).differentiableAt.differentiableWithinAt
  have hlim : Tendsto (fun τ => deriv g τ) (𝓝[<] t) (𝓝 L) := by
    have h1 : Tendsto (fun τ => A τ * Φ τ t) (𝓝[<] t) (𝓝 (L * Φ t t)) :=
      hL.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    rw [h.self_eq_one t ht.le, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht] with τ hτ
    exact ((h.hasDerivAt hτ.1 ht.le).deriv).symm
  have hL' := hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcont.continuousWithinAt
    (Ioo_mem_nhdsLT ht) hlim
  have hA : HasDerivWithinAt g (A t * Φ t t) (Iic t) t := (h.hasDerivAt ht ht.le).hasDerivWithinAt
  rw [h.self_eq_one t ht.le, mul_one] at hA
  exact (uniqueDiffWithinAt_Iic t).eq_deriv _ hL' hA

/-- **A state-transition matrix forces `A` to agree with its right limits (MLS eq. (4.40), p. 184,
with p. 179).** If `IsStateTransition A Φ`, `t ≥ 0` and `A(τ) → L` as `τ → t⁺`, then `L = A(t)`. -/
theorem eq_of_tendsto_nhdsWithin_Ioi (h : IsStateTransition A Φ) {t : ℝ} (ht : 0 ≤ t)
    {L : E →L[ℝ] E} (hL : Tendsto A (𝓝[>] t) (𝓝 L)) : L = A t := by
  set g : ℝ → E →L[ℝ] E := fun τ => Φ τ t with hg
  have hcont : ContinuousWithinAt g (Ici t) t :=
    (h.hasDerivWithinAt t t ht ht).continuousWithinAt.mono (Ici_subset_Ici.2 ht)
  have hdiff : DifferentiableOn ℝ g (Ioo t (t + 1)) := fun τ hτ =>
    (h.hasDerivAt (ht.trans_lt hτ.1) ht).differentiableAt.differentiableWithinAt
  have hlim : Tendsto (fun τ => deriv g τ) (𝓝[>] t) (𝓝 L) := by
    have h1 : Tendsto (fun τ => A τ * Φ τ t) (𝓝[>] t) (𝓝 (L * Φ t t)) :=
      hL.mul ((continuousWithinAt_Ioi_iff_Ici.2 hcont).tendsto)
    rw [h.self_eq_one t ht, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith : t < t + 1)] with τ hτ
    exact ((h.hasDerivAt (ht.trans_lt hτ.1) ht).deriv).symm
  have hL' := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
    (hcont.mono (Ioo_subset_Ioi_self.trans Ioi_subset_Ici_self))
    (Ioo_mem_nhdsGT (by linarith : t < t + 1)) hlim
  have hA : HasDerivWithinAt g (A t * Φ t t) (Ici t) t :=
    (h.hasDerivWithinAt t t ht ht).mono (Ici_subset_Ici.2 ht)
  rw [h.self_eq_one t ht, mul_one] at hA
  exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hL' hA

/-- **For `A` with one-sided limits, a state-transition matrix exists only for `A` continuous on
`[0, ∞)` (MLS Theorem 4.6, p. 184, and the piecewise continuity of p. 179).** If
`IsStateTransition A Φ`, `A` has a left limit at every `t > 0` and a right limit at every `t ≥ 0`,
then `A` is continuous on `[0, ∞)`. -/
theorem continuousOn_of_forall_tendsto (h : IsStateTransition A Φ)
    (hl : ∀ t, 0 < t → ∃ L, Tendsto A (𝓝[<] t) (𝓝 L))
    (hr : ∀ t, 0 ≤ t → ∃ L, Tendsto A (𝓝[>] t) (𝓝 L)) : ContinuousOn A (Ici 0) := by
  intro t ht
  obtain ⟨R, hR⟩ := hr t ht
  have hRt := h.eq_of_tendsto_nhdsWithin_Ioi ht hR
  rw [hRt] at hR
  have hright : ContinuousWithinAt A (Ici t) t := continuousWithinAt_Ioi_iff_Ici.1 hR
  rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0 | hpos
  · subst h0
    exact hright
  · obtain ⟨L, hL⟩ := hl t hpos
    have hLt := h.eq_of_tendsto_nhdsWithin_Iio hpos hL
    rw [hLt] at hL
    exact (continuousAt_iff_continuous_left_right.2
      ⟨continuousWithinAt_Iio_iff_Iic.1 hL, hright⟩).continuousWithinAt

end IsStateTransition

end Stability
end RoboLean
