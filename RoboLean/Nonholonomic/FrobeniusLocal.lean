import RoboLean.Nonholonomic.Frobenius
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Frobenius' theorem for fields commuting near a point (MLS Theorem 7.2, p. 326, "if")

**What MLS prints.** Theorem 7.2 (Frobenius, p. 326), stated without proof; fields with vanishing
bracket commute (p. 324). The classical proof needs the brackets to vanish only near the point.

**Proved here.**

* Flows commute where the bracket vanishes along the trajectories involved
  (`fderiv_flow_apply_of_lieBracket_eq_zero_on`, `flow_comm_of_lieBracket_eq_zero_on`), for
  forward flows and for two-sided flows (`twoSidedFlow_comm_of_lieBracket_eq_zero_on`).
* A flow of a field bounded by `M` moves points by at most `M |t|` (`norm_twoSidedFlow_sub_le`).
* **Frobenius for a frame commuting near `q`**
  (`isIntegrableAtOfClass_one_of_lieBracket_eq_zero_nhds`): on a finite-dimensional space, if
  `X₁, …, X_k` are bounded with continuous bounded derivatives, their brackets vanish on a
  neighbourhood of `q`, and `X₁(q), …, X_k(q)` are linearly independent, then
  `span{X₁, …, X_k}` is integrable at `q` with a `C¹` defining map.

**Conventions.** As in `Nonholonomic/Frobenius`: Mathlib's bracket (the book's sign), flows
`IsDifferentiableFlow` from time `0`, two-sided flows `twoSidedFlow`, `composedFlow Φ t x` with
`Φ_k` applied first.
-/

noncomputable section

open Set Filter Topology VectorField Metric

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The derivative of the flow of `X` along `Y` where `[X, Y]` vanishes along the trajectory
(MLS p. 324):** if `φ` is a flow of `X` (`IsDifferentiableFlow`, time first) with `‖DX y‖ ≤ K`,
`Y` has the Fréchet derivative `DY y` at every `y`, and `[X, Y](φ(τ, 0, p)) = 0` for
`τ ∈ [0, t]`, then `D(t, 0, p) Y(p) = Y(φ(t, 0, p))`. -/
theorem fderiv_flow_apply_of_lieBracket_eq_zero_on {X Y : E → E} {DX DY : E → E →L[ℝ] E}
    {φ : ℝ → ℝ → E → E} {D : ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hDY : ∀ y, HasFDerivAt Y (DY y) y) {t : ℝ} (ht : 0 ≤ t) {p : E}
    (hXY : ∀ τ ∈ Icc 0 t, lieBracket ℝ X Y (φ τ 0 p) = 0) :
    D t 0 p (Y p) = Y (φ t 0 p) := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt_field 0 le_rfl y).continuousAt
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun y => (hDY y).continuousAt
  have hYX : ∀ τ ∈ Icc 0 t, DY (φ τ 0 p) (X (φ τ 0 p)) = DX (φ τ 0 p) (Y (φ τ 0 p)) :=
    fun τ hτ => by
      have h := hXY τ hτ
      rw [lieBracket, (hDY _).fderiv, (hX.hasFDerivAt_field 0 le_rfl _).fderiv, sub_eq_zero] at h
      exact h
  have hsol := hX.isSolution 0 le_rfl p
  have hcont : ContinuousOn (fun τ => D τ 0 p (Y p) - Y (φ τ 0 p)) (Icc 0 t) :=
    (((hX.continuousOn_fderiv le_rfl p).clm_apply continuousOn_const).sub
      (hYc.comp_continuousOn (hX.continuousOn_trajectory le_rfl p))).mono Icc_subset_Ici_self
  have hder : ∀ τ ∈ Ico 0 t, HasDerivWithinAt (fun τ => D τ 0 p (Y p) - Y (φ τ 0 p))
      (DX (φ τ 0 p) (D τ 0 p (Y p) - Y (φ τ 0 p))) (Ici τ) τ := by
    intro τ hτ
    have h1 := ((hX.variational τ 0 le_rfl hτ.1 p).mono (Ici_subset_Ici.2 hτ.1)).clm_apply
      (hasDerivWithinAt_const τ _ (Y p))
    have h2 := (hDY (φ τ 0 p)).comp_hasDerivWithinAt τ
      (Stability.IsSolution.hasDerivWithinAt_Ici_of_mem hXc hsol hτ.1)
    convert h1.sub h2 using 1
    · rfl
    · rw [mul_apply_eq_comp, map_zero, add_zero, hYX τ ⟨hτ.1, hτ.2.le⟩,
        map_sub]
  have hzero : D 0 0 p (Y p) - Y (φ 0 0 p) = 0 := by
    rw [hX.fderiv_self 0 le_rfl p, hX.self_eq 0 le_rfl p, one_apply_eq_self,
      sub_self]
  have hbound : ∀ τ ∈ Ico 0 t, ‖DX (φ τ 0 p) (D τ 0 p (Y p) - Y (φ τ 0 p))‖ ≤
      K * ‖D τ 0 p (Y p) - Y (φ τ 0 p)‖ := fun τ _ =>
    ((DX (φ τ 0 p)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hXK _) (norm_nonneg _))
  have hw := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hder hzero hbound t
    ⟨ht, le_rfl⟩
  exact sub_eq_zero.1 hw

/-- **Flows commute where the bracket vanishes (MLS p. 324):** if `φ` and `ψ` are flows of `X`
and `Y` (`IsDifferentiableFlow`, time first) with `‖DX y‖ ≤ K` and `‖DY y‖ ≤ K'`, and
`[X, Y](φ(τ, 0, ψ(σ, 0, q))) = 0` for `σ ∈ [0, s]` and `τ ∈ [0, t]`, then
`φ(t, 0, ψ(s, 0, q)) = ψ(s, 0, φ(t, 0, q))`. -/
theorem flow_comm_of_lieBracket_eq_zero_on {X Y : E → E} {DX DY : E → E →L[ℝ] E}
    {φ ψ : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ} {K' : NNReal}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hY : Stability.IsDifferentiableFlow (fun _ => Y) (fun _ => DY) ψ D')
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hYK : ∀ y, ‖DY y‖ ≤ K') {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    {q : E} (hXY : ∀ σ ∈ Icc 0 s, ∀ τ ∈ Icc 0 t, lieBracket ℝ X Y (φ τ 0 (ψ σ 0 q)) = 0) :
    φ t 0 (ψ s 0 q) = ψ s 0 (φ t 0 q) := by
  have hDY : ∀ y, HasFDerivAt Y (DY y) y := hY.hasFDerivAt_field 0 le_rfl
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun y => (hDY y).continuousAt
  have hlip : LipschitzWith K' Y :=
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hDY y).differentiableAt) fun y => by
      rw [(hDY y).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hYK y
  have hφc : Continuous (φ t 0) := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt t 0 le_rfl ht y).continuousAt
  have hsolq := hY.isSolution 0 le_rfl q
  have hsolp := hY.isSolution 0 le_rfl (φ t 0 q)
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => Y) (s := fun _ => univ)
    (K := K') (f := fun σ => φ t 0 (ψ σ 0 q)) (g := fun σ => ψ σ 0 (φ t 0 q)) (a := 0) (b := s)
    (fun _ _ => hlip.lipschitzOnWith)
    (hφc.comp_continuousOn ((hY.continuousOn_trajectory le_rfl q).mono Icc_subset_Ici_self))
    (fun σ hσ => by
      have h1 := (hX.hasFDerivAt t 0 le_rfl ht (ψ σ 0 q)).comp_hasDerivWithinAt σ
        (Stability.IsSolution.hasDerivWithinAt_Ici_of_mem hYc hsolq hσ.1)
      rw [fderiv_flow_apply_of_lieBracket_eq_zero_on hX hXK hDY ht
        (hXY σ ⟨hσ.1, hσ.2.le⟩)] at h1
      exact h1)
    (fun _ _ => mem_univ _)
    ((hY.continuousOn_trajectory le_rfl _).mono Icc_subset_Ici_self)
    (fun σ hσ => Stability.IsSolution.hasDerivWithinAt_Ici_of_mem hYc hsolp hσ.1)
    (fun _ _ => mem_univ _)
    (by simp only [hY.self_eq 0 le_rfl])
  exact heq ⟨hs, le_rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **The two-sided flow at a nonnegative time is the forward flow (MLS pp. 322–323).** -/
theorem twoSidedFlow_of_nonneg {φ φ' : ℝ → ℝ → E → E} {τ : ℝ} (hτ : 0 ≤ τ) (x : E) :
    twoSidedFlow φ φ' τ x = φ τ 0 x := by
  simp [twoSidedFlow, hτ]

/-- **The two-sided flow at a nonpositive time is the reversed flow (MLS pp. 322–323):** with a
flow `φ` of `X` (`IsDifferentiableFlow`, time first) and any `φ'` with `φ'(0, 0, x) = x`,
`twoSidedFlow φ φ' (−τ) x = φ'(τ, 0, x)` for `τ ≥ 0`. -/
theorem twoSidedFlow_neg_of_nonneg {X : E → E} {DX DX' : E → E →L[ℝ] E}
    {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') {τ : ℝ}
    (hτ : 0 ≤ τ) (x : E) : twoSidedFlow φ φ' (-τ) x = φ' τ 0 x := by
  rcases eq_or_lt_of_le hτ with h | h
  · subst h
    simp [twoSidedFlow, hX.self_eq 0 le_rfl, hX'.self_eq 0 le_rfl]
  · simp [twoSidedFlow, not_le.2 (neg_neg_of_pos h)]

/-- The bracket of `−X` and `Y` at a point (MLS Proposition 7.1, p. 325, with bilinearity). -/
private theorem lieBracket_neg_left_apply (X Y : E → E) (y : E) :
    lieBracket ℝ (-X) Y y = -lieBracket ℝ X Y y := by
  have h := congrFun (lieBracket_neg_right Y X) y
  rw [lieBracket_swap, h, Pi.neg_apply, neg_neg, lieBracket_swap]

/-- The derivative of the flow of `−X` is `−DX` (MLS pp. 322–323, the reversed flow). -/
private theorem fderiv_neg_eq'' {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') (y : E) :
    DX' y = -DX y :=
  (hX'.hasFDerivAt_field 0 le_rfl y).unique (hX.hasFDerivAt_field 0 le_rfl y).neg

/-- **Two-sided flows commute where the bracket vanishes (MLS p. 324):** with flows `φ, φ'` of
`X, −X` and `ψ, ψ'` of `Y, −Y` (`IsDifferentiableFlow`, time first), `‖DX y‖ ≤ K`,
`‖DY y‖ ≤ K'`, and `[X, Y] = 0` on a set `W` that contains `φ^X_τ(φ^Y_σ(x))` for all
`|τ| ≤ |t|`, `|σ| ≤ |s|`, the flows satisfy `φ^X_t(φ^Y_s(x)) = φ^Y_s(φ^X_t(x))`. -/
theorem twoSidedFlow_comm_of_lieBracket_eq_zero_on {X Y : E → E}
    {DX DX' DY DY' : E → E →L[ℝ] E} {φ φ' ψ ψ' : ℝ → ℝ → E → E}
    {D₁ D₂ D₃ D₄ : ℝ → ℝ → E → E →L[ℝ] E} {K K' : NNReal}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D₁)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D₂)
    (hY : Stability.IsDifferentiableFlow (fun _ => Y) (fun _ => DY) ψ D₃)
    (hY' : Stability.IsDifferentiableFlow (fun _ => -Y) (fun _ => DY') ψ' D₄)
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hYK : ∀ y, ‖DY y‖ ≤ K') {W : Set E}
    (hW : ∀ y ∈ W, lieBracket ℝ X Y y = 0) {t s : ℝ} {x : E}
    (hsub : ∀ σ τ : ℝ, |σ| ≤ |s| → |τ| ≤ |t| →
      twoSidedFlow φ φ' τ (twoSidedFlow ψ ψ' σ x) ∈ W) :
    twoSidedFlow φ φ' t (twoSidedFlow ψ ψ' s x) = twoSidedFlow ψ ψ' s (twoSidedFlow φ φ' t x) := by
  have hXK' : ∀ y, ‖DX' y‖ ≤ (K : ℝ) := fun y => by
    rw [fderiv_neg_eq'' hX hX', norm_neg]; exact hXK y
  have hYK' : ∀ y, ‖DY' y‖ ≤ K' := fun y => by
    rw [fderiv_neg_eq'' hY hY', norm_neg]; exact hYK y
  have hW1 : ∀ y ∈ W, lieBracket ℝ (-X) Y y = 0 := fun y hy => by
    rw [lieBracket_neg_left_apply, hW y hy, neg_zero]
  have hW2 : ∀ y ∈ W, lieBracket ℝ X (-Y) y = 0 := fun y hy => by
    rw [lieBracket_neg_right, Pi.neg_apply, hW y hy, neg_zero]
  have hW3 : ∀ y ∈ W, lieBracket ℝ (-X) (-Y) y = 0 := fun y hy => by
    rw [lieBracket_neg_right, Pi.neg_apply, lieBracket_neg_left_apply, neg_neg, hW y hy]
  have hpos : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → b ≤ a → |b| ≤ |a| := fun ha hb hba => by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact hba
  have hneg : ∀ {a b : ℝ}, ¬ 0 ≤ a → 0 ≤ b → b ≤ -a → |-b| ≤ |a| := fun ha hb hba => by
    rw [abs_neg, abs_of_nonneg hb, abs_of_neg (not_le.1 ha)]; exact hba
  by_cases ht : 0 ≤ t <;> by_cases hs : 0 ≤ s
  · rw [twoSidedFlow_of_nonneg ht, twoSidedFlow_of_nonneg hs, twoSidedFlow_of_nonneg ht,
      twoSidedFlow_of_nonneg hs]
    refine flow_comm_of_lieBracket_eq_zero_on hX hY hXK hYK ht hs fun σ hσ τ hτ => hW _ ?_
    have h := hsub σ τ (hpos hs hσ.1 hσ.2) (hpos ht hτ.1 hτ.2)
    rwa [twoSidedFlow_of_nonneg hτ.1, twoSidedFlow_of_nonneg hσ.1] at h
  · have hs' : 0 ≤ -s := by linarith
    rw [twoSidedFlow_of_nonneg ht, twoSidedFlow_of_nonneg ht, ← neg_neg s,
      twoSidedFlow_neg_of_nonneg hY hY' hs', twoSidedFlow_neg_of_nonneg hY hY' hs']
    refine flow_comm_of_lieBracket_eq_zero_on hX hY' hXK hYK' ht hs' fun σ hσ τ hτ => hW2 _ ?_
    have h := hsub (-σ) τ (hneg hs hσ.1 hσ.2) (hpos ht hτ.1 hτ.2)
    rwa [twoSidedFlow_of_nonneg hτ.1, twoSidedFlow_neg_of_nonneg hY hY' hσ.1] at h
  · have ht' : 0 ≤ -t := by linarith
    rw [twoSidedFlow_of_nonneg hs, twoSidedFlow_of_nonneg hs, ← neg_neg t,
      twoSidedFlow_neg_of_nonneg hX hX' ht', twoSidedFlow_neg_of_nonneg hX hX' ht']
    refine flow_comm_of_lieBracket_eq_zero_on hX' hY hXK' hYK ht' hs fun σ hσ τ hτ => hW1 _ ?_
    have h := hsub σ (-τ) (hpos hs hσ.1 hσ.2) (hneg ht hτ.1 hτ.2)
    rwa [twoSidedFlow_neg_of_nonneg hX hX' hτ.1, twoSidedFlow_of_nonneg hσ.1] at h
  · have ht' : 0 ≤ -t := by linarith
    have hs' : 0 ≤ -s := by linarith
    rw [← neg_neg t, ← neg_neg s, twoSidedFlow_neg_of_nonneg hX hX' ht',
      twoSidedFlow_neg_of_nonneg hY hY' hs', twoSidedFlow_neg_of_nonneg hX hX' ht',
      twoSidedFlow_neg_of_nonneg hY hY' hs']
    refine flow_comm_of_lieBracket_eq_zero_on hX' hY' hXK' hYK' ht' hs' fun σ hσ τ hτ =>
      hW3 _ ?_
    have h := hsub (-σ) (-τ) (hneg hs hσ.1 hσ.2) (hneg ht hτ.1 hτ.2)
    rwa [twoSidedFlow_neg_of_nonneg hX hX' hτ.1, twoSidedFlow_neg_of_nonneg hY hY' hσ.1] at h

/-- **A flow of a field bounded by `M` moves points by at most `M |t|` (MLS eq. (7.7),
p. 322):** with flows `φ` of `X` and `φ'` of `−X` (`IsDifferentiableFlow`, time first) and
`‖X y‖ ≤ M`, `‖φ^X_t(x) − x‖ ≤ M |t|` for all real `t`. -/
theorem norm_twoSidedFlow_sub_le {X : E → E} {DX DX' : E → E →L[ℝ] E}
    {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E} {M : NNReal}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    (hM : ∀ y, ‖X y‖ ≤ M) (t : ℝ) (x : E) :
    ‖twoSidedFlow φ φ' t x - x‖ ≤ M * |t| := by
  have hc := isIntegralCurve_twoSidedFlow hX hX' x
  have hlip : LipschitzWith M fun τ => twoSidedFlow φ φ' τ x :=
    lipschitzWith_of_nnnorm_deriv_le (fun τ => (hc τ).differentiableAt) fun τ => by
      rw [(hc τ).deriv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hM _
  have h := hlip.dist_le_mul t 0
  rwa [twoSidedFlow_zero hX, dist_eq_norm, Real.dist_eq, sub_zero] at h

variable {k : ℕ}

omit [NormedSpace ℝ E] in
/-- Points along a composition of maps that move points by at most `M δ` (for MLS
pp. 330–331). -/
private theorem norm_foldr_sub_le {Φ : Fin k → ℝ → E → E} {M δ : ℝ}
    (hdisp : ∀ a τ y, ‖Φ a τ y - y‖ ≤ M * |τ|) (hM : 0 ≤ M) {t : Fin k → ℝ}
    (ht : ∀ i, |t i| ≤ δ) (l : List (Fin k)) (x : E) :
    ‖l.foldr (fun i y => Φ i (t i) y) x - x‖ ≤ l.length * (M * δ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc ‖Φ a (t a) (l.foldr (fun i y => Φ i (t i) y) x) - x‖
        ≤ ‖Φ a (t a) (l.foldr (fun i y => Φ i (t i) y) x) - l.foldr (fun i y => Φ i (t i) y) x‖ +
          ‖l.foldr (fun i y => Φ i (t i) y) x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M * δ + l.length * (M * δ) :=
          add_le_add ((hdisp _ _ _).trans (mul_le_mul_of_nonneg_left (ht a) hM)) ih
      _ = (l.length + 1) * (M * δ) := by ring

omit [NormedSpace ℝ E] in
/-- Moving one time out of a composition of maps that commute near the base point (for MLS
p. 324 and pp. 330–331). -/
private theorem foldr_add_single_on {Φ : Fin k → ℝ → E → E} {j : Fin k} {s M δ : ℝ} {x : E}
    (hdisp : ∀ a τ y, ‖Φ a τ y - y‖ ≤ M * |τ|) (hM : 0 ≤ M)
    (hcomm : ∀ a τ y, |τ| ≤ δ → ‖y - x‖ ≤ k * (M * δ) → Φ j s (Φ a τ y) = Φ a τ (Φ j s y))
    (hadd : ∀ τ y, Φ j (τ + s) y = Φ j s (Φ j τ y)) {t : Fin k → ℝ} (ht : ∀ i, |t i| ≤ δ)
    (l : List (Fin k)) (hl : l.Nodup) (hlen : l.length ≤ k) :
    l.foldr (fun i y => Φ i ((t + Pi.single j s : Fin k → ℝ) i) y) x =
      if j ∈ l then Φ j s (l.foldr (fun i y => Φ i (t i) y) x)
        else l.foldr (fun i y => Φ i (t i) y) x := by
  have hMδ : 0 ≤ M * δ := mul_nonneg hM ((abs_nonneg _).trans (ht j))
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hlen' : l.length ≤ k := by simp at hlen; omega
    have hF : ‖l.foldr (fun i y => Φ i (t i) y) x - x‖ ≤ k * (M * δ) :=
      (norm_foldr_sub_le hdisp hM ht l x).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen') hMδ)
    simp only [List.foldr_cons, List.mem_cons]
    rw [ih hl.2 hlen']
    by_cases haj : a = j
    · subst haj
      simp only [hl.1, ↓reduceIte, true_or, Pi.add_apply, Pi.single_eq_same]
      exact hadd _ _
    · have hja : ¬ j = a := fun h => haj h.symm
      simp only [hja, false_or, Pi.add_apply, Pi.single_eq_of_ne haj, add_zero]
      split_ifs with hj
      · exact (hcomm a (t a) _ (ht a) hF).symm
      · rfl

/-- **Frobenius for a frame commuting near `q` (MLS Theorem 7.2, p. 326, "if", with p. 324), with a
`C¹` defining map:** on a finite-dimensional real space, let `X₁, …, X_k` be bounded by `M` with
Fréchet derivatives `DXᵢ` continuous and bounded by `K`, let `[Xᵢ, Xⱼ] = 0` on a neighbourhood of
`q` (Mathlib's bracket, the book's sign), and let `X₁(q), …, X_k(q)` be linearly independent.
Then `Δ = span{X₁, …, X_k}` is integrable at `q` with a defining map of class `C¹`
(`IsIntegrableAtOfClass 1`; MLS asks smooth functions). -/
theorem isIntegrableAtOfClass_one_of_lieBracket_eq_zero_nhds [FiniteDimensional ℝ E]
    {X : Fin k → E → E} {DX : Fin k → E → E →L[ℝ] E} {K M : NNReal}
    (hDX : ∀ i y, HasFDerivAt (X i) (DX i y) y) (hDXc : ∀ i, Continuous (DX i))
    (hK : ∀ i y, ‖DX i y‖ ≤ K) (hM : ∀ i y, ‖X i y‖ ≤ M) {q : E}
    (hbr : ∀ᶠ y in 𝓝 q, ∀ i j, lieBracket ℝ (X i) (X j) y = 0)
    (hli : LinearIndependent ℝ fun i => X i q) :
    IsIntegrableAtOfClass 1 (spanAt (Set.range X)) q := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  choose φ D hφ using fun i => Stability.exists_isDifferentiableFlow_autonomous (hDX i) (hDXc i)
    (hK i)
  choose φ' D' hφ' using fun i => Stability.exists_isDifferentiableFlow_autonomous
    (F := -X i) (DF := fun y => -DX i y) (fun y => (hDX i y).neg) (hDXc i).neg
    (fun y => by rw [norm_neg]; exact hK i y)
  set Φ : Fin k → ℝ → E → E := fun i => twoSidedFlow (φ i) (φ' i) with hΦdef
  have hΦc : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2 := fun i =>
    contDiff_twoSidedFlow (hφ i) (hφ' i) (hDXc i) (hK i)
  have h0 : ∀ i x, Φ i 0 x = x := fun i x => twoSidedFlow_zero (hφ i) x
  have hX0 : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0 := fun i x => by
    have h : HasDerivAt (fun t => Φ i t x) (X i (Φ i 0 x)) 0 :=
      isIntegralCurve_twoSidedFlow (hφ i) (hφ' i) x 0
    rwa [h0 i x] at h
  have hdisp : ∀ a τ y, ‖Φ a τ y - y‖ ≤ (M : ℝ) * |τ| := fun a τ y =>
    norm_twoSidedFlow_sub_le (hφ a) (hφ' a) (hM a) τ y
  have hadd : ∀ j s τ y, Φ j (τ + s) y = Φ j s (Φ j τ y) := fun j s τ y => by
    rw [add_comm]; exact (twoSidedFlow_add (hφ j) (hφ' j) s τ y).symm
  -- the radius where the brackets vanish, and the small times
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hbr
  set δ : ℝ := ρ / (4 * ((k : ℝ) + 2) * ((M : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hMδ : ((k : ℝ) + 2) * ((M : ℝ) * δ) ≤ ρ / 4 := by
    rw [hδdef]
    have hM0 : (0 : ℝ) ≤ M := M.coe_nonneg
    have hk0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [show ((k : ℝ) + 2) * ((M : ℝ) * (ρ / (4 * ((k : ℝ) + 2) * ((M : ℝ) + 1)))) =
      ρ / 4 * ((M : ℝ) / ((M : ℝ) + 1)) by field_simp]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  -- local commutation of the two-sided flows
  have hcomm : ∀ x : E, ‖x - q‖ < ρ / 2 → ∀ j a : Fin k, ∀ s τ y, |s| ≤ δ → |τ| ≤ δ →
      ‖y - x‖ ≤ k * (M * δ) → Φ j s (Φ a τ y) = Φ a τ (Φ j s y) := by
    intro x hx j a s τ y hs hτ hy
    refine twoSidedFlow_comm_of_lieBracket_eq_zero_on (hφ j) (hφ' j) (hφ a) (hφ' a) (hK j) (hK a)
      (W := ball q ρ) (fun z hz => hball z hz j a) fun σ τ' hσ hτ' => ?_
    rw [mem_ball, dist_eq_norm]
    have h1 := hdisp j τ' (Φ a σ y)
    have h2 := hdisp a σ y
    have hM0 : (0 : ℝ) ≤ M := M.coe_nonneg
    have e1 : (M : ℝ) * |τ'| ≤ M * δ := mul_le_mul_of_nonneg_left (hτ'.trans hs) hM0
    have e2 : (M : ℝ) * |σ| ≤ M * δ := mul_le_mul_of_nonneg_left (hσ.trans hτ) hM0
    calc ‖Φ j τ' (Φ a σ y) - q‖
        ≤ ‖Φ j τ' (Φ a σ y) - Φ a σ y‖ + ‖Φ a σ y - y‖ + ‖y - x‖ + ‖x - q‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (Φ j τ' (Φ a σ y)) (Φ a σ y) q
          have := norm_sub_le_norm_sub_add_norm_sub (Φ a σ y) y q
          have := norm_sub_le_norm_sub_add_norm_sub y x q
          linarith
      _ < ρ := by nlinarith [hMδ]
  -- the flow box and its coordinate lines near `(0, 0)`
  obtain ⟨C, -, A, -, hA⟩ := exists_flowBox_fderiv hΦc h0 hX0 hli
  set Ψ : (Fin k → ℝ) × C → E := fun p => composedFlow Φ p.1 (q + (p.2 : E)) with hΨ
  have hin : ContDiff ℝ 1 fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E)) :=
    contDiff_fst.prodMk (contDiff_const.add (C.subtypeL.contDiff.comp contDiff_snd))
  have hΨc : ContDiff ℝ 1 Ψ := (contDiff_composedFlow hΦc).comp hin
  have hmove : ∀ z : (Fin k → ℝ) × C, ‖z‖ < min (δ / 2) (ρ / 2) → ∀ i, ∀ s, |s| ≤ δ →
      composedFlow Φ (z.1 + Pi.single i s) (q + (z.2 : E)) =
        Φ i s (composedFlow Φ z.1 (q + (z.2 : E))) := by
    intro z hz i s hs
    have hz1 : ∀ a, |z.1 a| ≤ δ := fun a =>
      ((norm_le_pi_norm z.1 a).trans ((norm_fst_le z).trans (hz.le.trans
        ((min_le_left _ _).trans (by linarith))))).trans' (le_of_eq (Real.norm_eq_abs _).symm)
    have hx : ‖q + (z.2 : E) - q‖ < ρ / 2 := by
      rw [add_sub_cancel_left]
      calc ‖(z.2 : E)‖ = ‖z.2‖ := rfl
        _ ≤ ‖z‖ := norm_snd_le z
        _ < ρ / 2 := hz.trans_le (min_le_right _ _)
    have h := foldr_add_single_on (hdisp) M.coe_nonneg
      (fun a τ y hτ hy => hcomm _ hx i a s τ y hs hτ hy) (hadd i s) hz1 (List.finRange k)
      (List.nodup_finRange k) (by simp)
    simp only [List.mem_finRange, ↓reduceIte] at h
    exact h
  have htan : ∀ᶠ z in 𝓝 ((0 : Fin k → ℝ), (0 : C)), ∀ i,
      fderiv ℝ Ψ z ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i (Ψ z) := by
    filter_upwards [ball_mem_nhds _ (lt_min (half_pos hδ) (half_pos hρ))] with z hz i
    rw [mem_ball, Prod.mk_zero_zero, dist_zero_right] at hz
    have hline : HasDerivAt (fun s : ℝ => z + s • ((Pi.single i 1 : Fin k → ℝ), (0 : C)))
        ((Pi.single i 1 : Fin k → ℝ), (0 : C)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        ((Pi.single i 1 : Fin k → ℝ), (0 : C))).const_add z
    have hcomp := ((hΨc.differentiable one_ne_zero) z).hasFDerivAt.comp_hasDerivAt_of_eq
      (0 : ℝ) hline (by simp)
    have hfun : (Ψ ∘ fun s : ℝ => z + s • ((Pi.single i 1 : Fin k → ℝ), (0 : C))) =
        fun s => composedFlow Φ (z.1 + Pi.single i s) (q + (z.2 : E)) := by
      funext s
      simp only [Function.comp_apply, hΨ, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
        Prod.smul_snd, smul_zero, add_zero]
      congr 2
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hfun] at hcomp
    have hloc : (fun s => composedFlow Φ (z.1 + Pi.single i s) (q + (z.2 : E))) =ᶠ[𝓝 0]
        fun s => Φ i s (composedFlow Φ z.1 (q + (z.2 : E))) := by
      filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with s hs
      exact hmove z hz i s (abs_le.2 ⟨hs.1.le, hs.2.le⟩)
    have hd : HasDerivAt (fun s => Φ i s (composedFlow Φ z.1 (q + (z.2 : E))))
        (X i (composedFlow Φ z.1 (q + (z.2 : E)))) 0 := hX0 i _
    exact hcomp.unique (hd.congr_of_eventuallyEq hloc)
  have hres := isIntegrableAtOfClass_one_of_chart hΨc ⟨A, hA⟩ htan
  have hΨ0 : Ψ ((0 : Fin k → ℝ), (0 : C)) = q := by
    simp only [hΨ, ZeroMemClass.coe_zero, add_zero]
    exact composedFlow_zero h0 q
  rwa [hΨ0] at hres

end Nonholonomic
end RoboLean
