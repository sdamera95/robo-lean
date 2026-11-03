import RoboLean.Nonholonomic.FlowsTwoSided
import RoboLean.Control.FlowJointC1
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Composed flows and the flow box (MLS pp. 322–323, for Theorem 7.2, p. 326, and Propositions
7.6–7.7, pp. 330–331)

**What MLS prints.** `φ^f_t(q)` is the state at time `t` of the integral curve of `f` from `q`; for
each fixed `t` it is a local diffeomorphism, with the group property for all `t` and `s`
(pp. 322–323). The construction behind Frobenius' theorem (Theorem 7.2, p. 326, stated without
proof) and behind Propositions 7.6–7.7 (pp. 330–331) composes flows of several fields,
`φ^{g₁}_{t₁} ∘ ⋯ ∘ φ^{g_k}_{t_k}(q)`, and differentiates the composition in the times and the
initial point together.

**Proved here.**

* The two-sided flow `(t, x) ↦ φ^X_t(x)` (`twoSidedFlow`, from flows of `X` and `−X`) of a field
  with a continuous bounded derivative is strictly differentiable at every point of `ℝ × E`, with
  derivative `(s, v) ↦ s X(φ^X_t(x)) + D_x φ^X_t(x) v`, and is of class `C¹`
  (`hasStrictFDerivAt_twoSidedFlow`, `contDiff_twoSidedFlow`).
* For maps `Φ₁, …, Φ_k : ℝ × E → E` of class `C¹` with `Φᵢ(0, x) = x` and `∂Φᵢ/∂t(0, x) = Xᵢ(x)`
  (the two-sided flows are such maps), the composed map
  `(t, x) ↦ Φ₁(t₁, Φ₂(t₂, ⋯ Φ_k(t_k, x)))` (`composedFlow`) is `C¹` with derivative
  `(τ, v) ↦ Σᵢ τᵢ Xᵢ(x) + v` at `(0, x)` (`contDiff_composedFlow`,
  `hasFDerivAt_composedFlow_zero`); in the times alone its derivative at `0` is injective exactly
  when `X₁(q), …, X_k(q)` are linearly independent (`injective_fderiv_composedFlow_time_iff`).
* The flow box: on a finite-dimensional space, if `X₁(q), …, X_k(q)` are linearly independent and
  `C` is a complement of their span, then `(t, c) ↦ Φ₁(t₁, ⋯ Φ_k(t_k, q + c))` restricts to a
  homeomorphism from an open neighbourhood of `(0, 0)` onto an open set, with an inverse of class
  `C¹` at `q`, by the inverse function theorem (`exists_flowBox`); its derivative at `(0, 0)` is
  the linear isomorphism `(τ, c) ↦ Σᵢ τᵢ Xᵢ(q) + c` (`exists_flowBox_fderiv`).

**Conventions.** Time first; flows are the library's `IsDifferentiableFlow` from time `0`, the
two-sided flow is `twoSidedFlow` (Chapter 7, `FlowsTwoSided`); derivatives are Fréchet
derivatives; `composedFlow Φ t x` applies `Φ_k` first and `Φ₁` last, as in
`φ^{g₁}_{t₁} ∘ ⋯ ∘ φ^{g_k}_{t_k}(q)`; indices run over `Fin k`.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The two-sided flow is `C¹` in the time and the state -/

/-- **The derivative in the state of the two-sided flow (MLS pp. 322–323):** `D(t, 0, x)` for
`t ≥ 0` and `D'(−t, 0, x)` for `t < 0`, from the derivatives `D` and `D'` of flows of `X` and
`−X`. -/
def twoSidedFlowFDeriv (D D' : ℝ → ℝ → E → E →L[ℝ] E) (t : ℝ) (x : E) : E →L[ℝ] E :=
  if 0 ≤ t then D t 0 x else D' (-t) 0 x

/-- **The two-sided flow is jointly continuous in the time and the state (MLS pp. 322–323):**
with flows `φ` of `X` and `φ'` of `−X` (`IsDifferentiableFlow`, time first),
`(t, x) ↦ twoSidedFlow φ φ' t x` is continuous on `ℝ × E`. -/
theorem continuous_twoSidedFlow {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') :
    Continuous fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2 := by
  have h1 : ContinuousOn (fun p : ℝ × E => φ p.1 0 p.2) {p | (0 : ℝ) ≤ p.1} :=
    hX.continuousOn.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      fun p hp => ⟨le_rfl, hp⟩
  have h2 : ContinuousOn (fun p : ℝ × E => φ' (-p.1) 0 p.2) {p | p.1 ≤ (0 : ℝ)} :=
    hX'.continuousOn.comp
      (continuous_fst.neg.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      fun p hp => ⟨le_rfl, neg_nonneg.2 hp⟩
  have h := continuous_if_le continuous_const continuous_fst h1 h2 fun p hp => by
    rw [← hp, neg_zero, hX.self_eq 0 le_rfl, hX'.self_eq 0 le_rfl]
  refine h.congr fun p => ?_
  simp only [twoSidedFlow]
  split_ifs <;> rfl

/-- The derivative of the flow of `−X` is `−DX` (MLS pp. 322–323, the reversed flow). -/
private theorem fderiv_neg_eq {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') (y : E) :
    DX' y = -DX y :=
  (hX'.hasFDerivAt_field 0 le_rfl y).unique (hX.hasFDerivAt_field 0 le_rfl y).neg

/-- **The derivative in the state of the two-sided flow is jointly continuous (MLS pp. 322–323,
for Propositions 7.6–7.7, pp. 330–331):** with flows `φ` of `X` and `φ'` of `−X`
(`IsDifferentiableFlow`, time first), `DX` continuous and `‖DX y‖ ≤ K`, the map
`(t, x) ↦ twoSidedFlowFDeriv D D' t x` is continuous on `ℝ × E`. -/
theorem continuous_twoSidedFlowFDeriv {X : E → E} {DX DX' : E → E →L[ℝ] E}
    {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E} {K : NNReal}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    (hDX : Continuous DX) (hK : ∀ y, ‖DX y‖ ≤ K) :
    Continuous fun p : ℝ × E => twoSidedFlowFDeriv D D' p.1 p.2 := by
  have hDX' : DX' = fun y => -DX y := funext (fderiv_neg_eq hX hX')
  have hc1 := hX.continuousOn_fderiv_prod (K := K) (hDX.comp continuous_snd).continuousOn
    (fun _ _ y => hK y) le_rfl
  have hc2 := hX'.continuousOn_fderiv_prod (K := K)
    (by rw [hDX']; exact (hDX.comp continuous_snd).neg.continuousOn)
    (fun _ _ y => by rw [hDX', norm_neg]; exact hK y) le_rfl
  have h1 : ContinuousOn (fun p : ℝ × E => D p.1 0 p.2) {p | (0 : ℝ) ≤ p.1} :=
    hc1.mono fun p hp => ⟨hp, mem_univ _⟩
  have h2 : ContinuousOn (fun p : ℝ × E => D' (-p.1) 0 p.2) {p | p.1 ≤ (0 : ℝ)} :=
    hc2.comp (continuous_fst.neg.prodMk continuous_snd).continuousOn
      fun p hp => ⟨show (0 : ℝ) ≤ -p.1 from neg_nonneg.2 hp, mem_univ _⟩
  have h := continuous_if_le continuous_const continuous_fst h1 h2 fun p hp => by
    rw [← hp, neg_zero, hX.fderiv_self 0 le_rfl, hX'.fderiv_self 0 le_rfl]
  exact h.congr fun p => rfl

/-- **The two-sided flow is strictly differentiable in the time and the state together (MLS
pp. 322–323, for Propositions 7.6–7.7, pp. 330–331):** with flows `φ` of `X` and `φ'` of `−X`
(`IsDifferentiableFlow`, time first), `DX` continuous and `‖DX y‖ ≤ K`, the map
`(t, x) ↦ φ^X_t(x)` has at every `(t, x)` the strict derivative
`(s, v) ↦ s X(φ^X_t(x)) + D_x φ^X_t(x) v`. -/
theorem hasStrictFDerivAt_twoSidedFlow {X : E → E} {DX DX' : E → E →L[ℝ] E}
    {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E} {K : NNReal}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    (hDX : Continuous DX) (hK : ∀ y, ‖DX y‖ ≤ K) (u : ℝ × E) :
    HasStrictFDerivAt (fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (X (twoSidedFlow φ φ' u.1 u.2))).coprod
        (twoSidedFlowFDeriv D D' u.1 u.2)) u := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt_field 0 le_rfl y).continuousAt
  have hcf := continuous_twoSidedFlow hX hX'
  refine hasStrictFDerivAt_uncurry_coprod (f := twoSidedFlow φ φ')
    (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (X (twoSidedFlow φ φ' t x)))
    (f₂ := twoSidedFlowFDeriv D D') ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun v => (isIntegralCurve_twoSidedFlow hX hX' v.2 v.1).hasFDerivAt
  · refine Eventually.of_forall fun v => ?_
    show HasFDerivAt (twoSidedFlow φ φ' v.1) (twoSidedFlowFDeriv D D' v.1 v.2) v.2
    by_cases ht : 0 ≤ v.1
    · simp only [twoSidedFlow, twoSidedFlowFDeriv, ht, ↓reduceIte]
      exact hX.hasFDerivAt v.1 0 le_rfl ht v.2
    · simp only [twoSidedFlow, twoSidedFlowFDeriv, ht, ↓reduceIte]
      exact hX'.hasFDerivAt (-v.1) 0 le_rfl (by linarith) v.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp
      (hXc.comp hcf)).continuousAt
  · exact (continuous_twoSidedFlowFDeriv hX hX' hDX hK).continuousAt

/-- **The two-sided flow is of class `C¹` in the time and the state together (MLS pp. 322–323,
for Propositions 7.6–7.7, pp. 330–331):** with flows `φ` of `X` and `φ'` of `−X`
(`IsDifferentiableFlow`, time first), `DX` continuous and `‖DX y‖ ≤ K`, the map
`(t, x) ↦ φ^X_t(x)` is `C¹` on `ℝ × E`. -/
theorem contDiff_twoSidedFlow {X : E → E} {DX DX' : E → E →L[ℝ] E}
    {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E} {K : NNReal}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    (hDX : Continuous DX) (hK : ∀ y, ‖DX y‖ ≤ K) :
    ContDiff ℝ 1 fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2 := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt_field 0 le_rfl y).continuousAt
  have hcf := continuous_twoSidedFlow hX hX'
  refine contDiff_one_iff_hasFDerivAt.2 ⟨fun u =>
    (ContinuousLinearMap.toSpanSingleton ℝ (X (twoSidedFlow φ φ' u.1 u.2))).coprod
      (twoSidedFlowFDeriv D D' u.1 u.2), ?_, fun u =>
    (hasStrictFDerivAt_twoSidedFlow hX hX' hDX hK u).hasFDerivAt⟩
  have h1 : Continuous fun u : ℝ × E =>
      ContinuousLinearMap.toSpanSingleton ℝ (X (twoSidedFlow φ φ' u.1 u.2)) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp (hXc.comp hcf)
  have h2 := continuous_twoSidedFlowFDeriv hX hX' hDX hK
  have h3 : Continuous fun u : ℝ × E =>
      (ContinuousLinearMap.toSpanSingleton ℝ (X (twoSidedFlow φ φ' u.1 u.2))).comp
          (ContinuousLinearMap.fst ℝ ℝ E) +
        (twoSidedFlowFDeriv D D' u.1 u.2).comp (ContinuousLinearMap.snd ℝ ℝ E) :=
    (h1.clm_comp continuous_const).add (h2.clm_comp continuous_const)
  refine h3.congr fun u => ?_
  ext p <;> simp

/-! ### Composed flows -/

variable {k : ℕ}

/-- **The composed flow `φ^{g₁}_{t₁} ∘ ⋯ ∘ φ^{g_k}_{t_k}(x)` (MLS pp. 330–331, Propositions
7.6–7.7; the construction behind Theorem 7.2, p. 326):** for maps `Φᵢ : ℝ → E → E` (in use, the
two-sided flows of fields `gᵢ`), `composedFlow Φ t x = Φ₁(t₁, Φ₂(t₂, ⋯ Φ_k(t_k, x)))`; `Φ_k` acts
first. -/
def composedFlow (Φ : Fin k → ℝ → E → E) (t : Fin k → ℝ) (x : E) : E :=
  (List.finRange k).foldr (fun i y => Φ i (t i) y) x

/-- The composition along a list of indices is `C¹` (for MLS pp. 330–331). -/
private theorem contDiff_foldr {Φ : Fin k → ℝ → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) (l : List (Fin k)) :
    ContDiff ℝ 1 fun p : (Fin k → ℝ) × E => l.foldr (fun i y => Φ i (p.1 i) y) p.2 := by
  induction l with
  | nil => simpa using contDiff_snd
  | cons i l ih =>
    simp only [List.foldr_cons]
    exact (hΦ i).comp (((contDiff_apply ℝ ℝ i).comp contDiff_fst).prodMk ih)

/-- **The composed flow is `C¹` in the times and the initial point (MLS pp. 330–331, for
Propositions 7.6–7.7):** if every `(t, x) ↦ Φᵢ(t, x)` is `C¹` on `ℝ × E`, so is
`(t, x) ↦ composedFlow Φ t x` on `ℝᵏ × E`. -/
theorem contDiff_composedFlow {Φ : Fin k → ℝ → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) :
    ContDiff ℝ 1 fun p : (Fin k → ℝ) × E => composedFlow Φ p.1 p.2 :=
  contDiff_foldr hΦ _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The composition at zero times is the identity (MLS p. 322, `φ^f_0 = id`). -/
private theorem foldr_zero {Φ : Fin k → ℝ → E → E} (h0 : ∀ i x, Φ i 0 x = x)
    (l : List (Fin k)) (x : E) :
    l.foldr (fun i y => Φ i 0 y) x = x := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih]; exact h0 i x

/-- The derivative of one map at time `0` (MLS eq. (7.7), p. 322, at `t = 0`). -/
private theorem hasFDerivAt_zero_of {Φ : ℝ → E → E} {X : E → E}
    (hΦ : ContDiff ℝ 1 fun p : ℝ × E => Φ p.1 p.2) (h0 : ∀ x, Φ 0 x = x)
    (hX : ∀ x, HasDerivAt (fun t => Φ t x) (X x) 0) (x : E) :
    HasFDerivAt (fun p : ℝ × E => Φ p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (X x)).coprod
        (ContinuousLinearMap.id ℝ E)) (0, x) := by
  have hL := ((hΦ.differentiable one_ne_zero) (0, x)).hasFDerivAt
  set L := fderiv ℝ (fun p : ℝ × E => Φ p.1 p.2) (0, x)
  have h1 : L.comp (ContinuousLinearMap.inl ℝ ℝ E) =
      ContinuousLinearMap.toSpanSingleton ℝ (X x) := by
    have hc := hL.comp (0 : ℝ) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) x)
    have hc' : HasFDerivAt (fun t : ℝ => Φ t x) (L.comp (ContinuousLinearMap.inl ℝ ℝ E)) 0 := hc
    exact hc'.unique (hX x).hasFDerivAt
  have h2 : L.comp (ContinuousLinearMap.inr ℝ ℝ E) = ContinuousLinearMap.id ℝ E := by
    have h := hL.comp x (hasFDerivAt_prodMk_right (0 : ℝ) x)
    have he : ((fun p : ℝ × E => Φ p.1 p.2) ∘ fun y : E => ((0 : ℝ), y)) = id :=
      funext fun y => h0 y
    rw [he] at h
    exact h.unique (hasFDerivAt_id x)
  refine hL.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
  have hp : p = ContinuousLinearMap.inl ℝ ℝ E p.1 + ContinuousLinearMap.inr ℝ ℝ E p.2 := by simp
  have e1 := congrArg (fun A : ℝ →L[ℝ] E => A p.1) h1
  have e2 := congrArg (fun A : E →L[ℝ] E => A p.2) h2
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at e1 e2
  rw [hp, map_add, e1, e2]
  simp

/-- The derivative at zero times along a list of indices (for MLS pp. 330–331). -/
private def foldrFDeriv (X : Fin k → E → E) (x : E) (l : List (Fin k)) :
    (Fin k → ℝ) × E →L[ℝ] E :=
  l.foldr (fun i L =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (X i x)).comp
    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) E) + L) (ContinuousLinearMap.snd ℝ (Fin k → ℝ) E)

private theorem foldrFDeriv_apply (X : Fin k → E → E) (x : E) (l : List (Fin k))
    (p : (Fin k → ℝ) × E) :
    foldrFDeriv X x l p = (l.map fun i => p.1 i • X i x).sum + p.2 := by
  induction l with
  | nil => simp [foldrFDeriv]
  | cons i l ih =>
    simp only [foldrFDeriv, List.foldr_cons] at ih ⊢
    simp [ih, add_assoc]

private theorem hasFDerivAt_foldr_zero {Φ : Fin k → ℝ → E → E} {X : Fin k → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) (h0 : ∀ i x, Φ i 0 x = x)
    (hX : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0) (x : E) (l : List (Fin k)) :
    HasFDerivAt (fun p : (Fin k → ℝ) × E => l.foldr (fun i y => Φ i (p.1 i) y) p.2)
      (foldrFDeriv X x l) (0, x) := by
  induction l with
  | nil =>
    simpa [foldrFDeriv] using hasFDerivAt_snd (p := ((0 : Fin k → ℝ), x))
  | cons i l ih =>
    have hin : HasFDerivAt (fun p : (Fin k → ℝ) × E =>
        (p.1 i, l.foldr (fun j y => Φ j (p.1 j) y) p.2))
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (Fin k → ℝ) E)).prod
          (foldrFDeriv X x l)) (0, x) :=
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).comp
        (ContinuousLinearMap.fst ℝ (Fin k → ℝ) E)).hasFDerivAt).prodMk ih
    have hval : ((fun p : (Fin k → ℝ) × E => (p.1 i, l.foldr (fun j y => Φ j (p.1 j) y) p.2))
        ((0 : Fin k → ℝ), x)) = ((0 : ℝ), x) := by
      simp only [Pi.zero_apply, foldr_zero h0]
    have hout := hasFDerivAt_zero_of (hΦ i) (h0 i) (hX i) x
    rw [← hval] at hout
    have h := hout.comp ((0 : Fin k → ℝ), x) hin
    refine h.congr_fderiv ?_
    ext p
    · simp [foldrFDeriv]
    · simp [foldrFDeriv]

/-- **The derivative of the composed flow at zero times (MLS pp. 330–331, Propositions 7.6–7.7;
MLS eq. (7.7), p. 322):** the linear map `(τ, v) ↦ Σᵢ τᵢ Xᵢ(x) + v` on `ℝᵏ × E`. -/
def composedFlowFDerivZero (X : Fin k → E → E) (x : E) : (Fin k → ℝ) × E →L[ℝ] E :=
  (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (X i x)).comp
      (ContinuousLinearMap.fst ℝ (Fin k → ℝ) E) +
    ContinuousLinearMap.snd ℝ (Fin k → ℝ) E

/-- **MLS pp. 330–331:** `composedFlowFDerivZero X x (τ, v) = Σᵢ τᵢ Xᵢ(x) + v`. -/
theorem composedFlowFDerivZero_apply (X : Fin k → E → E) (x : E) (p : (Fin k → ℝ) × E) :
    composedFlowFDerivZero X x p = ∑ i, p.1 i • X i x + p.2 := by
  simp [composedFlowFDerivZero]

/-- **The derivative of the composed flow at zero times (MLS pp. 330–331, Propositions 7.6–7.7,
with MLS eq. (7.7), p. 322):** if every `(t, x) ↦ Φᵢ(t, x)` is `C¹` on `ℝ × E` with
`Φᵢ(0, x) = x` and `∂Φᵢ/∂t(0, x) = Xᵢ(x)`, then `(t, y) ↦ composedFlow Φ t y` has at `(0, x)` the
derivative `(τ, v) ↦ Σᵢ τᵢ Xᵢ(x) + v`. -/
theorem hasFDerivAt_composedFlow_zero {Φ : Fin k → ℝ → E → E} {X : Fin k → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) (h0 : ∀ i x, Φ i 0 x = x)
    (hX : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0) (x : E) :
    HasFDerivAt (fun p : (Fin k → ℝ) × E => composedFlow Φ p.1 p.2)
      (composedFlowFDerivZero X x) (0, x) := by
  refine (hasFDerivAt_foldr_zero hΦ h0 hX x (List.finRange k)).congr_fderiv ?_
  ext p
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, foldrFDeriv_apply,
      composedFlowFDerivZero_apply, ← Fin.sum_univ_def]
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, foldrFDeriv_apply,
      composedFlowFDerivZero_apply, ← Fin.sum_univ_def]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **The composed flow at zero times is the identity (MLS p. 322, `φ^f_0 = id`):** if
`Φᵢ(0, x) = x` for all `i` and `x`, then `composedFlow Φ 0 x = x`. -/
theorem composedFlow_zero {Φ : Fin k → ℝ → E → E} (h0 : ∀ i x, Φ i 0 x = x) (x : E) :
    composedFlow Φ 0 x = x :=
  foldr_zero h0 _ x

/-- **The composed flow in the times alone (MLS pp. 330–331, Propositions 7.6–7.7):** under the
hypotheses of `hasFDerivAt_composedFlow_zero`, `t ↦ composedFlow Φ t q` has at `0` the derivative
`τ ↦ Σᵢ τᵢ Xᵢ(q)`. -/
theorem hasFDerivAt_composedFlow_time {Φ : Fin k → ℝ → E → E} {X : Fin k → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) (h0 : ∀ i x, Φ i 0 x = x)
    (hX : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0) (q : E) :
    HasFDerivAt (fun t : Fin k → ℝ => composedFlow Φ t q)
      (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight
        (X i q)) 0 := by
  have h := (hasFDerivAt_composedFlow_zero hΦ h0 hX q).comp (0 : Fin k → ℝ)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : Fin k → ℝ) q)
  refine h.congr_fderiv ?_
  ext τ
  simp [composedFlowFDerivZero]

/-- **The composed flow is an immersion at zero times exactly for independent fields (MLS
pp. 330–331, the rank of the composed flows in Propositions 7.6–7.7):** under the hypotheses of
`hasFDerivAt_composedFlow_zero`, the derivative `τ ↦ Σᵢ τᵢ Xᵢ(q)` of `t ↦ composedFlow Φ t q` at
`0` is injective if and only if `X₁(q), …, X_k(q)` are linearly independent. -/
theorem injective_fderiv_composedFlow_time_iff (X : Fin k → E → E) (q : E) :
    Function.Injective
      (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (X i q) :
      (Fin k → ℝ) →L[ℝ] E) ↔ LinearIndependent ℝ fun i => X i q := by
  have hap : ∀ τ : Fin k → ℝ,
      (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (X i q) :
        (Fin k → ℝ) →L[ℝ] E) τ =
        ∑ i, τ i • X i q := fun τ => by simp
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hinj τ hτ
    have := hinj (a₁ := τ) (a₂ := 0) (by rw [hap, hap, hτ]; simp)
    exact fun i => congrFun this i
  · intro hli τ₁ τ₂ hτ
    rw [hap, hap] at hτ
    have h0 : ∑ i, (τ₁ - τ₂) i • X i q = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hτ, sub_self]
    funext i
    exact sub_eq_zero.1 (hli _ h0 i)

/-! ### The flow box -/

/-- **The derivative of the flow box (MLS pp. 322–323 and pp. 330–331; the chart behind Theorem
7.2, p. 326):** on a finite-dimensional real space, let `Φ₁, …, Φ_k : ℝ → E → E` be `C¹` in
`(t, x)` with `Φᵢ(0, x) = x` and `∂Φᵢ/∂t(0, x) = Xᵢ(x)`. If `X₁(q), …, X_k(q)` are linearly
independent, then for some complement `C` of their span the map
`(t, c) ↦ Φ₁(t₁, ⋯ Φ_k(t_k, q + c))` on `ℝᵏ × C` has at `(0, 0)` the derivative
`(τ, c) ↦ Σᵢ τᵢ Xᵢ(q) + c`, a linear isomorphism onto `E`. -/
theorem exists_flowBox_fderiv [FiniteDimensional ℝ E] {Φ : Fin k → ℝ → E → E}
    {X : Fin k → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) (h0 : ∀ i x, Φ i 0 x = x)
    (hX : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0) {q : E}
    (hli : LinearIndependent ℝ fun i => X i q) :
    ∃ C : Submodule ℝ E, IsCompl (Submodule.span ℝ (Set.range fun i => X i q)) C ∧
      ∃ A : ((Fin k → ℝ) × C) ≃L[ℝ] E, (∀ p, A p = ∑ i, p.1 i • X i q + (p.2 : E)) ∧
        HasFDerivAt (fun p : (Fin k → ℝ) × C => composedFlow Φ p.1 (q + (p.2 : E)))
          (A : (Fin k → ℝ) × C →L[ℝ] E) ((0 : Fin k → ℝ), (0 : C)) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span ℝ (Set.range fun i => X i q))
  set Ψ : (Fin k → ℝ) × C → E := fun p => composedFlow Φ p.1 (q + (p.2 : E)) with hΨ
  -- the map and its derivative at `(0, 0)`
  have hin : ContDiff ℝ 1 fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E)) :=
    contDiff_fst.prodMk (contDiff_const.add (C.subtypeL.contDiff.comp contDiff_snd))
  have hΨc : ContDiff ℝ 1 Ψ := (contDiff_composedFlow hΦ).comp hin
  set B : (Fin k → ℝ) × C →L[ℝ] E :=
    (composedFlowFDerivZero X q).comp ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) C).prod
      (C.subtypeL.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) C))) with hB
  have hBap : ∀ p : (Fin k → ℝ) × C, B p = ∑ i, p.1 i • X i q + (p.2 : E) := fun p => by
    simp [hB, composedFlowFDerivZero_apply]
  have hΨd : HasFDerivAt Ψ B ((0 : Fin k → ℝ), (0 : C)) := by
    have h1 : HasFDerivAt (fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E)))
        ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) C).prod
          (C.subtypeL.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) C))) ((0 : Fin k → ℝ), (0 : C)) :=
      hasFDerivAt_fst.prodMk ((C.subtypeL.comp
        (ContinuousLinearMap.snd ℝ (Fin k → ℝ) C)).hasFDerivAt.const_add q)
    have h2 := hasFDerivAt_composedFlow_zero hΦ h0 hX q
    have hval : (fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E))) ((0 : Fin k → ℝ), (0 : C)) =
        ((0 : Fin k → ℝ), q) := by simp
    rw [← hval] at h2
    exact h2.comp ((0 : Fin k → ℝ), (0 : C)) h1
  -- the derivative is a bijection
  have hbij : Function.Bijective B := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro p hp
      rw [hBap] at hp
      have hs : ∑ i, p.1 i • X i q ∈ Submodule.span ℝ (Set.range fun i => X i q) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hneg : ∑ i, p.1 i • X i q = -(p.2 : E) := eq_neg_of_add_eq_zero_left hp
      have hc : ∑ i, p.1 i • X i q ∈ C := by rw [hneg]; exact C.neg_mem p.2.2
      have h0' : ∑ i, p.1 i • X i q = 0 := by
        have := hC.disjoint
        rw [Submodule.disjoint_def] at this
        exact this _ hs hc
      have hτ : p.1 = 0 := funext fun i => Fintype.linearIndependent_iff.1 hli _ h0' i
      have hv : (p.2 : E) = 0 := by rw [h0'] at hneg; exact neg_eq_zero.1 hneg.symm
      exact Prod.ext hτ (Subtype.ext hv)
    · intro y
      have hy : y ∈ Submodule.span ℝ (Set.range fun i => X i q) ⊔ C := by
        rw [hC.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨τ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ha
      exact ⟨(τ, ⟨c, hc⟩), by rw [hBap]⟩
  set eB : ((Fin k → ℝ) × C) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (B : (Fin k → ℝ) × C →ₗ[ℝ] E) hbij).toContinuousLinearEquiv with heB
  have hΨd' : HasFDerivAt Ψ (eB : (Fin k → ℝ) × C →L[ℝ] E) ((0 : Fin k → ℝ), (0 : C)) :=
    hΨd.congr_fderiv (ContinuousLinearMap.ext fun p => rfl)
  exact ⟨C, hC, eB, hBap, hΨd'⟩

/-- **The flow box (MLS pp. 322–323 and pp. 330–331; the chart behind Theorem 7.2, p. 326):** on
a finite-dimensional real space, let `Φ₁, …, Φ_k : ℝ → E → E` be `C¹` in `(t, x)` with
`Φᵢ(0, x) = x` and `∂Φᵢ/∂t(0, x) = Xᵢ(x)` (for instance the two-sided flows of fields `Xᵢ` with a
continuous bounded derivative, `contDiff_twoSidedFlow`). If `X₁(q), …, X_k(q)` are linearly
independent, then for some complement `C` of their span the map
`(t, c) ↦ Φ₁(t₁, ⋯ Φ_k(t_k, q + c))` on `ℝᵏ × C` restricts to a homeomorphism `e` from an open
neighbourhood of `(0, 0)` onto an open subset of `E`, whose inverse is `C¹` at `q`. -/
theorem exists_flowBox [FiniteDimensional ℝ E] {Φ : Fin k → ℝ → E → E} {X : Fin k → E → E}
    (hΦ : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2) (h0 : ∀ i x, Φ i 0 x = x)
    (hX : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0) {q : E}
    (hli : LinearIndependent ℝ fun i => X i q) :
    ∃ C : Submodule ℝ E, IsCompl (Submodule.span ℝ (Set.range fun i => X i q)) C ∧
      ∃ e : OpenPartialHomeomorph ((Fin k → ℝ) × C) E, ((0 : Fin k → ℝ), (0 : C)) ∈ e.source ∧
        (∀ p, e p = composedFlow Φ p.1 (q + (p.2 : E))) ∧ e ((0 : Fin k → ℝ), (0 : C)) = q ∧
          ContDiffAt ℝ 1 e.symm q := by
  obtain ⟨C, hC, A, -, hA⟩ := exists_flowBox_fderiv hΦ h0 hX hli
  set Ψ : (Fin k → ℝ) × C → E := fun p => composedFlow Φ p.1 (q + (p.2 : E)) with hΨ
  have hin : ContDiff ℝ 1 fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E)) :=
    contDiff_fst.prodMk (contDiff_const.add (C.subtypeL.contDiff.comp contDiff_snd))
  have hΨc : ContDiff ℝ 1 Ψ := (contDiff_composedFlow hΦ).comp hin
  have hΨ0 : Ψ ((0 : Fin k → ℝ), (0 : C)) = q := by
    simp only [hΨ, ZeroMemClass.coe_zero, add_zero]
    exact composedFlow_zero h0 q
  have hca : ContDiffAt ℝ 1 Ψ ((0 : Fin k → ℝ), (0 : C)) := hΨc.contDiffAt
  refine ⟨C, hC, hca.toOpenPartialHomeomorph Ψ hA one_ne_zero,
    hca.mem_toOpenPartialHomeomorph_source hA one_ne_zero, fun p => rfl, hΨ0, ?_⟩
  have h := hca.to_localInverse hA one_ne_zero
  rw [hΨ0] at h
  exact h

end Nonholonomic
end RoboLean
