import RoboLean.Nonholonomic.RankMaximality
import RoboLean.Nonholonomic.Concatenation
import RoboLean.Nonholonomic.FlowBox
import RoboLean.Control.FlowDifferentiable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Chow's theorem (MLS Theorem 7.5, p. 329)

**What MLS prints.** Theorem 7.5 (Chow), p. 329: "The control system (7.10) is locally
controllable at `q ∈ ℝⁿ` if `Δ_q = T_q ℝⁿ`", where `Δ = L(g₁, …, g_m)` is the controllability Lie
algebra and (7.10) is `q̇ = g₁(q)u₁ + ⋯ + g_m(q)u_m`, `u ∈ U ⊂ ℝᵐ`, with smooth, linearly
independent and complete `gⱼ` (p. 329). The proof is the pair of implications of p. 330,
Proposition 7.6 (the rank condition near `q₀` gives `int R^V(q₀, ≤ T) ≠ ∅`) and Proposition 7.7
(p. 331: that interior is non-empty for all `V` and `T` iff the system is locally controllable).

**Proved here.** On a finite-dimensional real normed space, for smooth generators and unconstrained
inputs (`U = ℝᵐ`), the rank condition at `q` gives local controllability at `q`
(`isLocallyControllableAt_of_lieAlgebraAt_eq_top`), which discharges the library's named statement
`ChowStatement E` (`chowStatement`). Neither linear independence nor completeness of the `gⱼ` is
used: the fields are cut off by a smooth bump outside a ball about `q`, which changes nothing
inside the ball, where the trajectories stay. Proposition 7.6's conclusion follows under the rank
condition at `q₀` alone (`self_mem_interior_reachableSetLE`). The route: the rank condition is
open (`Nonholonomic/ChowJacobi`); the two-sided flows of the cut-off fields form a flow family
(`isFlowFamily_twoSidedFlow`); a composed flow of the generators with total time `Σ |sᵢ|` small is
reached in any time `T > 0` by a piecewise constant input, inside `V`
(`flowSeq_mem_reachableSet`); the maximal-rank step and the reversal step of
`Nonholonomic/RankMaximality` give a map of the times onto a neighbourhood of `q`.

**Conventions.** Those of `Nonholonomic/Controllability` (piecewise constant inputs, trajectories
on `[0, T]`, `R^V(q, ≤ T)`, `IsLocallyControllableAt`) and `Nonholonomic/RankMaximality`
(`flowSeq`, `IsFlowFamily`); flows are the library's `IsDifferentiableFlow` from time `0` and
`twoSidedFlow` (Chapter 7, `FlowsTwoSided`); `C^∞` is `ContDiff ℝ ∞`.
-/

noncomputable section

open Set Filter Topology VectorField Metric
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS pp. 322–323: the two-sided flows are a flow family.** If `φⱼ` and `φ′ⱼ` are flows of `Xⱼ`
and `−Xⱼ` differentiable in the initial state (`IsDifferentiableFlow`, time first) and `DXⱼ` is
continuous and bounded by `K`, the maps `twoSidedFlow φⱼ φ′ⱼ` have the properties of
`IsFlowFamily`. -/
theorem isFlowFamily_twoSidedFlow {X : Fin m → E → E} {DX DX' : Fin m → E → E →L[ℝ] E}
    {φ φ' : Fin m → ℝ → ℝ → E → E} {D D' : Fin m → ℝ → ℝ → E → E →L[ℝ] E} {K : NNReal}
    (hX : ∀ j, Stability.IsDifferentiableFlow (fun _ => X j) (fun _ => DX j) (φ j) (D j))
    (hX' : ∀ j, Stability.IsDifferentiableFlow (fun _ => -X j) (fun _ => DX' j) (φ' j) (D' j))
    (hDX : ∀ j, Continuous (DX j)) (hK : ∀ j y, ‖DX j y‖ ≤ K) :
    IsFlowFamily X fun j => twoSidedFlow (φ j) (φ' j) := by
  refine ⟨fun j => contDiff_twoSidedFlow (hX j) (hX' j) (hDX j) (hK j),
    fun j x => twoSidedFlow_zero (hX j) x, fun j t x => ?_, fun j t x => ?_, fun j y => ?_⟩
  · rw [twoSidedFlow_add (hX j) (hX' j), neg_add_cancel, twoSidedFlow_zero (hX j)]
  · exact isIntegralCurve_twoSidedFlow (hX j) (hX' j) x t
  · have hvar := (hX j).variational 0 0 le_rfl le_rfl y
    rw [(hX j).self_eq 0 le_rfl, (hX j).fderiv_self 0 le_rfl, mul_one] at hvar
    rw [← ((hX j).hasFDerivAt_field 0 le_rfl y).fderiv] at hvar
    refine hvar.congr (fun σ hσ => ?_) ?_
    · simp only [twoSidedFlow, mem_Ici.1 hσ, ↓reduceIte]
      exact ((hX j).hasFDerivAt σ 0 le_rfl hσ y).fderiv
    · simp only [twoSidedFlow, le_refl, ↓reduceIte]
      exact ((hX j).hasFDerivAt 0 0 le_rfl le_rfl y).fderiv

/-- **MLS p. 330 (Proposition 7.6, "`N_k ⊂ R^V(q₀, ≤ ε₁ + ⋯ + ε_k)`") with p. 331 (concatenation):
a composed flow is reachable.** Let `t ↦ Φⱼ(t, x)` be integral curves of fields `Xⱼ` bounded by
`M ≥ 0` with `Φⱼ(0) = id`, and let `Xⱼ = gⱼ` on the ball `B(q, ρ) ⊂ V`. If `x₀ ∈ R^V(q, T₀)`,
`T₀ ≥ 0`, `‖x₀ − q‖ ≤ a` and `a + M Σ |sᵢ| < ρ`, then for every `c > 0`,
`flowSeq Φ x₀ r w s ∈ R^V(q, T₀ + r c)` (each factor in time `c` with the constant input
`(sᵢ / c) e_{wᵢ}`) and `‖flowSeq Φ x₀ r w s − q‖ ≤ a + M Σ |sᵢ|`. -/
theorem flowSeq_mem_reachableSet {g X : Fin m → E → E} {Φ : Fin m → ℝ → E → E} {V : Set E}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j y, ‖X j y‖ ≤ M)
    (hd : ∀ j t x, HasDerivAt (fun s => Φ j s x) (X j (Φ j t x)) t) (hz : ∀ j x, Φ j 0 x = x)
    {q x₀ : E} {ρ : ℝ} (hXg : ∀ j, EqOn (X j) (g j) (ball q ρ)) (hV : ball q ρ ⊆ V) {T₀ a : ℝ}
    (hT₀ : 0 ≤ T₀) (hx₀ : x₀ ∈ reachableSet g univ V q T₀) (ha : ‖x₀ - q‖ ≤ a) {c : ℝ}
    (hc : 0 < c) (r : ℕ) (w : Fin r → Fin m) (s : Fin r → ℝ) (hrs : a + M * ∑ i, |s i| < ρ) :
    flowSeq Φ x₀ r w s ∈ reachableSet g univ V q (T₀ + r * c) ∧
      ‖flowSeq Φ x₀ r w s - q‖ ≤ a + M * ∑ i, |s i| := by
  have hseg : ∀ j τ y, ‖Φ j τ y - y‖ ≤ M * |τ| := fun j τ y => by
    simpa [flowSeq] using norm_flowSeq_sub_le hM hd hz y 1 (fun _ => j) (fun _ => τ)
  induction r with
  | zero => simpa [flowSeq] using ⟨hx₀, ha⟩
  | succ r ih =>
    have hsplit : ∑ i, |s i| = ∑ i, |Fin.init s i| + |s (Fin.last r)| := by
      rw [Fin.sum_univ_castSucc]
      rfl
    have hlast := abs_nonneg (s (Fin.last r))
    obtain ⟨hreach, hnorm⟩ := ih (Fin.init w) (Fin.init s) (by
      rw [hsplit] at hrs
      nlinarith)
    set x₁ := flowSeq Φ x₀ r (Fin.init w) (Fin.init s) with hx₁
    set j := w (Fin.last r)
    set σ := s (Fin.last r)
    have hball : ∀ τ ∈ uIcc 0 σ, ‖Φ j τ x₁ - q‖ ≤ a + M * ∑ i, |s i| := by
      intro τ hτ
      have hτσ : |τ| ≤ |σ| := by simpa using abs_sub_left_of_mem_uIcc hτ
      calc ‖Φ j τ x₁ - q‖ ≤ ‖Φ j τ x₁ - x₁‖ + ‖x₁ - q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ M * |σ| + (a + M * ∑ i, |Fin.init s i|) :=
            add_le_add ((hseg j τ x₁).trans (mul_le_mul_of_nonneg_left hτσ hM0)) hnorm
        _ = a + M * ∑ i, |s i| := by rw [hsplit]; ring
    have hmem : ∀ τ ∈ uIcc 0 σ, Φ j τ x₁ ∈ ball q ρ := fun τ hτ => by
      rw [mem_ball, dist_eq_norm]
      exact (hball τ hτ).trans_lt hrs
    have hseg' := mem_reachableSet_of_integralCurve (g := g) (U := univ) (V := V) j hc (mem_univ _)
      (γ := fun τ => Φ j τ x₁) (fun τ => hd j τ x₁) (fun τ hτ => hXg j (hmem τ hτ))
      (fun τ hτ => hV (hmem τ hτ))
    simp only [hz] at hseg'
    refine ⟨?_, hball σ (by simp)⟩
    have h := mem_reachableSet_trans hreach hseg' (by positivity) hc.le
    rw [show T₀ + ↑(r + 1) * c = T₀ + ↑r * c + c by push_cast; ring]
    exact h

/-- **MLS Theorem 7.5 (Chow), p. 329, on a finite-dimensional space with unconstrained inputs:**
if the generators `g₁, …, g_m` are smooth and the controllability Lie algebra has full rank at `q`
(`lieAlgebraAt g q = ⊤`, "`Δ_q = T_q ℝⁿ`"), the system (7.10) with `U = ℝᵐ` is (small-time)
locally controllable at `q`. MLS also assumes the `gⱼ` linearly independent and complete; neither
is used. -/
theorem isLocallyControllableAt_of_lieAlgebraAt_eq_top [FiniteDimensional ℝ E]
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j)) {q : E} (hq : lieAlgebraAt g q = ⊤) :
    IsLocallyControllableAt g univ q := by
  intro V hV T hT
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- the rank condition near `q`
  have hsp0 : spanAt (leftNormedFields g) q = ⊤ := by
    rw [← lieAlgebraAt_eq_spanAt_leftNormedFields hg]
    exact hq
  have hcont : ∀ f ∈ leftNormedFields g, Continuous f := fun f hf => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hf
    exact (contDiff_of_mem_filtrationFields hg hi).continuous
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (eventually_spanAt_eq_top hcont hsp0))
  -- the cut-off fields
  set χ : ContDiffBump q := ⟨ρ / 2, ρ, by positivity, by linarith⟩ with hχ
  set X : Fin m → E → E := fun j y => χ y • g j y with hXdef
  have hXc : ∀ j, ContDiff ℝ ∞ (X j) := fun j => χ.contDiff.smul (hg j)
  have hXcs : ∀ j, HasCompactSupport (X j) := fun j => by
    have h : X j = (fun y => χ y) • g j := rfl
    rw [h]
    exact χ.hasCompactSupport.smul_right
  have hXg : ∀ j, EqOn (X j) (g j) (ball q (ρ / 2)) := fun j y hy => by
    simp [hXdef, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hDXc : ∀ j, Continuous (fderiv ℝ (X j)) := fun j => (hXc j).continuous_fderiv (by simp)
  have hDX : ∀ j y, HasFDerivAt (X j) (fderiv ℝ (X j) y) y := fun j y =>
    ((hXc j).differentiable (by simp) y).hasFDerivAt
  -- bounds
  choose C hC using fun j => (hXc j).continuous.bounded_above_of_compact_support (hXcs j)
  choose C' hC' using fun j => (hDXc j).bounded_above_of_compact_support ((hXcs j).fderiv (𝕜 := ℝ))
  set M : ℝ := ∑ j, |C j| + 1 with hMdef
  have hMpos : 0 < M := by positivity
  have hM : ∀ j y, ‖X j y‖ ≤ M := fun j y =>
    (hC j y).trans ((le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (C i))
      (Finset.mem_univ j)).trans (by linarith)))
  set K : NNReal := Real.toNNReal (∑ j, |C' j|) with hKdef
  have hK : ∀ j y, ‖fderiv ℝ (X j) y‖ ≤ K := fun j y =>
    (hC' j y).trans ((le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (C' i))
      (Finset.mem_univ j)).trans (Real.le_coe_toNNReal _)))
  -- the flows
  choose φ D hφ using fun j => Stability.exists_isDifferentiableFlow_autonomous (hDX j) (hDXc j)
    (hK j)
  choose φ' D' hφ' using fun j => Stability.exists_isDifferentiableFlow_autonomous
    (F := -X j) (DF := fun y => -fderiv ℝ (X j) y) (fun y => (hDX j y).neg) (hDXc j).neg
    (fun y => by rw [norm_neg]; exact hK j y)
  set Φ : Fin m → ℝ → E → E := fun j => twoSidedFlow (φ j) (φ' j) with hΦdef
  have hΦ : IsFlowFamily X Φ := isFlowFamily_twoSidedFlow hφ hφ' hDXc hK
  -- the maximal-rank step
  set δ : ℝ := ρ / (4 * M) with hδdef
  have hδ : 0 < δ := by positivity
  have hMδ : M * δ = ρ / 4 := by rw [hδdef]; field_simp
  have hsmall : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ), ∑ i, |s i| < δ →
      flowSeq Φ q r w s ∈ ball q (ρ / 2) := by
    intro r w s hs
    rw [mem_ball, dist_eq_norm]
    have h := norm_flowSeq_sub_le hM hΦ.hasDerivAt hΦ.zero q r w s
    have h2 : M * ∑ i, |s i| < M * δ := mul_lt_mul_of_pos_left hs hMpos
    linarith
  have hW : ∀ r (w : Fin r → Fin m) (s : Fin r → ℝ), ∑ i, |s i| < δ →
      flowSeq Φ q r w s ∈ {p | spanAt (leftNormedFields X) p = ⊤} := by
    intro r w s hs
    have hp := hsmall r w s hs
    have hp' : flowSeq Φ q r w s ∈ ball q ρ := ball_subset_ball (by linarith) hp
    refine eq_top_iff.2 ?_
    rw [← (hρsub hp').2]
    exact spanAt_leftNormedFields_le isOpen_ball hXg hp
  obtain ⟨r, w, s, hs, htop⟩ := exists_range_fderiv_flowSeq_eq_top hΦ hXc hδ hW (fun p hp => hp)
  obtain ⟨w', s', hs'eq, hundo⟩ := exists_flowSeq_undo hΦ.neg_comp r w s
  have hmap := map_nhds_flowSeq_undo hΦ.contDiff htop hundo
  have hO : {s₁ : Fin r → ℝ | ∑ i, |s₁ i| < δ} ∈ 𝓝 s :=
    (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).abs)
      continuous_const).mem_nhds hs
  have himg := image_mem_map (m := fun s₁ => flowSeq Φ (flowSeq Φ q r w s₁) r w' s') hO
  rw [hmap] at himg
  refine mem_of_superset himg ?_
  rintro _ ⟨s₁, hs₁, rfl⟩
  have hVρ : ball q (ρ / 2) ⊆ V := fun p hp =>
    (hρsub (ball_subset_ball (by linarith) hp)).1
  have hqV : q ∈ V := hVρ (mem_ball_self (by positivity))
  refine mem_iUnion₂.2 ⟨T, ⟨hT, le_rfl⟩, ?_⟩
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact self_mem_reachableSet (mem_univ _) hqV
  · set c : ℝ := T / (2 * r) with hcdef
    have hc : 0 < c := by positivity
    have h1 := flowSeq_mem_reachableSet hMpos.le hM hΦ.hasDerivAt hΦ.zero hXg hVρ le_rfl
      (self_mem_reachableSet (T := 0) (mem_univ _) hqV) (by simp : ‖q - q‖ ≤ 0) hc r w s₁
      (by have := mul_lt_mul_of_pos_left (show ∑ i, |s₁ i| < δ from hs₁) hMpos; linarith)
    have h2 := flowSeq_mem_reachableSet hMpos.le hM hΦ.hasDerivAt hΦ.zero hXg hVρ
      (by positivity) h1.1 h1.2 hc r w' s' (by
        have e1 := mul_lt_mul_of_pos_left (show ∑ i, |s₁ i| < δ from hs₁) hMpos
        have e2 := mul_lt_mul_of_pos_left (hs'eq ▸ hs : ∑ i, |s' i| < δ) hMpos
        linarith)
    have hTc : 0 + ↑r * c + ↑r * c = T := by
      rw [hcdef]
      field_simp
      ring
    rw [hTc] at h2
    exact h2.1

/-- **MLS Theorem 7.5 (Chow), p. 329: the named statement `ChowStatement` holds on every
finite-dimensional real normed space.** -/
theorem chowStatement [FiniteDimensional ℝ E] : ChowStatement E :=
  fun _ _ hg _ hq => isLocallyControllableAt_of_lieAlgebraAt_eq_top hg hq

/-- **MLS Proposition 7.6, p. 330, under the rank condition at `q₀` only (MLS asks it on a
neighbourhood of `q₀`):** on a finite-dimensional space, for smooth generators with `Δ_{q₀} = T_{q₀}ℝⁿ`
and unconstrained inputs, `int R^V(q₀, ≤ T)` is non-empty (it contains `q₀`) for every
neighbourhood `V` of `q₀` and every `T > 0`. -/
theorem self_mem_interior_reachableSetLE [FiniteDimensional ℝ E] {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {q₀ : E} (hq : lieAlgebraAt g q₀ = ⊤) {V : Set E}
    (hV : V ∈ 𝓝 q₀) {T : ℝ} (hT : 0 < T) :
    q₀ ∈ interior (reachableSetLE g univ V q₀ T) := by
  exact mem_interior_iff_mem_nhds.2
    (isLocallyControllableAt_of_lieAlgebraAt_eq_top hg hq V hV T hT)

end Nonholonomic
end RoboLean
