import RoboLean.Control.LaSalle

/-!
# Lasalle's principle on a ball (MLS Theorem 4.7, "in particular", local form, p. 188)

**What MLS prints (p. 188).** Theorem 4.7 asks for a locally positive definite `V` such that on
the compact set `Ω_c = {x : V(x) ≤ c}` we have `V̇(x) ≤ 0`, and concludes: "In particular, if `S`
contains no invariant sets other than `x = 0`, then `0` is asymptotically stable", where
`S = {x ∈ Ω_c : V̇(x) = 0}`. Example 4.7 (p. 189) applies it to the nonlinear spring.

**What is proved here.** `asymptoticallyStableAt_of_lasalle_ball` replaces the sublevel set by a
ball: if `V̇ ≤ 0` and `V̇` is continuous on an open ball `B(0, r)`, and the largest invariant set
inside `{x ∈ B(0, r) : V̇(x) = 0}` lies in `{0}`, then the origin is asymptotically stable. No
sublevel set of `V` is asked to be compact, and nothing is assumed outside the ball. The proof
builds a small compact positively invariant set `Ω = {‖y‖ ≤ ρ, V(y) ≤ c}` inside the ball from
the comparison function of `V` and applies `lasalle_eventually_mem` to it.

The state space is a real normed space `E` that is proper (closed balls are compact, as in
`ℝⁿ`); the system is the autonomous `fun _ => F` with flow hypothesis `HasFlow F φ`, as in
`RoboLean.Control.LaSalle`.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS Theorem 4.7 (p. 188), "in particular", local form on a ball.** Let `φ` be the flow of
`ẋ = F(x)` (`HasFlow`, as in `asymptoticallyStableAt_of_lasalle`), `V` locally positive definite
(Definition 4.4, time-invariant) with derivative `V̇` along the solutions in the open ball
`B(0, r)`, `r > 0`, `V̇` continuous and `≤ 0` on that ball. If the largest invariant set
(Definition 4.8) inside `{x ∈ B(0, r) : V̇(x) = 0}` is contained in `{0}`, then the origin is
asymptotically stable (Definition 4.2) at every initial time `t₀ ≥ 0`.

Differences from the printed theorem: no sublevel set `{V ≤ c}` is assumed compact, and `V̇ ≤ 0`
and the continuity of `V̇` are asked only on the ball `B(0, r)`, with `S` taken inside that ball;
the flow hypothesis `HasFlow` is the one of `RoboLean.Control.LaSalle`. The space `E` is proper
(closed balls compact, as in `ℝⁿ`). The system is written `fun _ => F` (time first, ignored). -/
theorem asymptoticallyStableAt_of_lasalle_ball [ProperSpace E] {F : E → E} {φ : ℝ → E → E}
    (h : HasFlow F φ) {V Vdot : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hpd : LocallyPositiveDefinite fun _ => V)
    (hVdot : HasDerivAlongSolutions (fun _ => F) (fun _ => V) (fun _ => Vdot) (Metric.ball 0 r))
    (hVdotc : ContinuousOn Vdot (Metric.ball 0 r))
    (hneg : ∀ y ∈ Metric.ball (0 : E) r, Vdot y ≤ 0)
    (hM : largestInvariantSubset φ {y | y ∈ Metric.ball (0 : E) r ∧ Vdot y = 0} ⊆ {0})
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) : AsymptoticallyStableAt (fun _ => F) 0 t₀ := by
  have hV : Continuous V :=
    hpd.1.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨(le_refl (0 : ℝ)), mem_univ y⟩)
  refine ⟨stableAt_of_lyapunov hpd hr hVdot (fun _ _ y hy => hneg y hy) ht₀, ?_⟩
  obtain ⟨hcont, ε₀, hε₀, α, hα, hb⟩ := hpd
  have hV0 : V 0 = 0 := (hb 0 le_rfl).1
  set ρ := min ε₀ r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε₀ : ρ < ε₀ := by
    have := min_le_left ε₀ r
    linarith
  have hρr : ρ < r := by
    have := min_le_right ε₀ r
    linarith
  have hαρ : 0 < α ρ := hα.pos hρ
  set c := α ρ / 2 with hcdef
  have hc : 0 < c := by positivity
  have hlow : ∀ t : ℝ, 0 ≤ t → ∀ y : E, ‖y‖ ≤ ρ → α ‖y‖ ≤ (fun _ => V) t y :=
    fun t ht y hy => (hb t ht).2 y (hy.trans_lt hρε₀)
  set Ω : Set E := {y | ‖y‖ ≤ ρ ∧ V y ≤ c} with hΩdef
  have hΩc : IsCompact Ω :=
    (isCompact_closedBall (0 : E) ρ).of_isClosed_subset
      ((isClosed_le continuous_norm continuous_const).inter (isClosed_le hV continuous_const))
      (fun y hy => mem_closedBall_zero_iff.mpr hy.1)
  have hΩr : Ω ⊆ Metric.ball 0 r := fun y hy => mem_ball_zero_iff.mpr (hy.1.trans_lt hρr)
  -- on `Ω` the bound `α ‖y‖ ≤ V y ≤ α ρ / 2` keeps `y` off the sphere of radius `ρ`
  have hΩlt : ∀ y ∈ Ω, ‖y‖ < ρ := by
    intro y hy
    rcases lt_or_eq_of_le hy.1 with h1 | h1
    · exact h1
    · have := hlow 0 le_rfl y hy.1
      rw [h1] at this
      have := hy.2
      linarith
  have hinv : IsForwardInvariant φ Ω := by
    intro t ht y hy
    have hstay : ∀ s, 0 ≤ s → ‖φ s y‖ < ρ :=
      norm_lt_of_lyapunov (f := fun _ => F) (V := fun _ => V) (Vdot := fun _ => Vdot) hcont
        hVdot (fun _ _ z hz => hneg z hz) (Metric.ball_subset_ball hρr.le) hlow le_rfl
        (h.isSolution y) (by simpa [h.map_zero] using hΩlt y hy)
        (by simp only [h.map_zero]; linarith [hy.2])
    have hanti := antitoneOn_comp_flow h hV hVdot hneg
      (fun s hs => mem_ball_zero_iff.mpr ((hstay s hs).trans hρr))
    have hle : V (φ t y) ≤ V (φ 0 y) := hanti self_mem_Ici ht ht
    rw [h.map_zero] at hle
    exact ⟨(hstay t ht).le, hle.trans hy.2⟩
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hV.continuousAt c hc
  refine ⟨min δ₁ ρ, lt_min hδ₁ hρ, fun x hx hx0 => ?_⟩
  rw [sub_zero] at hx0
  have hxΩ : x t₀ ∈ Ω := by
    refine ⟨(hx0.trans_le (min_le_right _ _)).le, ?_⟩
    have h1 := hδ₁' (x := x t₀) (by rw [dist_zero_right]; exact hx0.trans_le (min_le_left _ _))
    rw [hV0, Real.dist_eq, sub_zero] at h1
    exact ((le_abs_self _).trans_lt h1).le
  refine h.tendsto_of_isSolution ht₀ hx (tendsto_nhds.mpr fun U hU h0U => ?_)
  have hMΩ : largestInvariantSubset φ {y | y ∈ Ω ∧ Vdot y = 0} ⊆ U :=
    (largestInvariantSubset_mono φ (T := {y | y ∈ Metric.ball (0 : E) r ∧ Vdot y = 0})
      fun y hy => ⟨hΩr hy.1, hy.2⟩).trans
      (hM.trans (singleton_subset_iff.mpr h0U))
  exact lasalle_eventually_mem h hΩc hinv hV (hVdot.mono hΩr) (hVdotc.mono hΩr)
    (fun y hy => hneg y (hΩr hy)) hxΩ hU hMΩ

end Stability
end RoboLean
