import RoboLean.Control.FlowCk

/-!
# The second variational equation (MLS pp. 322–323, with p. 179)

**What MLS prints.** "For each fixed `t`, `φ^f_t` is a local diffeomorphism" (pp. 322–323) for
smooth fields; Chapter 4 differentiates solutions in their initial state (Theorem 4.5, p. 183)
under the standing assumption of p. 179. No variational equation is printed.

**Proved here.** On a finite-dimensional real space, for `F` of class `C²` with bounded first and
second derivatives and a flow `φ` with derivative `D` in the initial state
(`IsDifferentiableFlow`, time first), the second derivative `x ↦ ∂D(τ, s, x)/∂x` exists
(`IsDifferentiableFlow.contDiff_fderiv_flow`), vanishes at `τ = s`
(`IsDifferentiableFlow.fderiv_fderiv_flow_self`), and solves the second variational equation
`∂/∂t [D²(t) h] = D²F(φ(t)) (D(t) h) ∘ D(t) + DF(φ(t)) ∘ D²(t) h` for every direction `h`
(`IsDifferentiableFlow.hasDerivWithinAt_fderiv_fderiv_flow`), with `D²(t) = ∂D(t, s, x)/∂x`.

**Route.** The cut-off augmented flow of `Control/FlowCk` (`IsDifferentiableFlow.exists_augmentedFlow`)
carries `(x, 1)` to `(φ(τ, s, x), D(τ, s, x))` on a window `[s, t + 1]`, so the derivative of
`x ↦ D(τ, s, x)` is the second component of the derivative of the augmented flow in the direction
`(h, 0)`; its variational equation, with the derivative of the augmented field
`(y, M) ↦ (F(y), DF(y) M)` near the trajectory, is the second variational equation.

**Conventions.** As in `Control/FlowDerivative`: time first, `φ t s x` the state at time `t` of the
solution from `x` at time `s`; derivatives are Fréchet derivatives, `D²F(y) u ∈ E →L[ℝ] E` is
`fderiv ℝ (fderiv ℝ F) y u`, and composition of continuous linear maps is `∘L`.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsDifferentiableFlow

variable {F : E → E} {DF : E → E →L[ℝ] E} {φ : ℝ → ℝ → E → E} {D : ℝ → ℝ → E → E →L[ℝ] E}

/-- **The second derivative of the flow vanishes at the initial time (MLS pp. 322–323):** for a
flow with derivative `D` in the initial state (`IsDifferentiableFlow`, time first) and `s ≥ 0`,
`∂D(s, s, x)/∂x = 0`, since `D(s, s, ·) = 1`. -/
theorem fderiv_fderiv_flow_self (h : IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D)
    {s : ℝ} (hs : 0 ≤ s) (x : E) : fderiv ℝ (D s s) x = 0 := by
  have hD : D s s = fun _ => 1 := funext fun y => h.fderiv_self s hs y
  rw [hD]
  simp

/-- **The second variational equation (MLS pp. 322–323, the second derivative of the flow in the
initial state):** on a finite-dimensional real space, let `F` be of class `C²` with bounded first
and second derivatives and `φ` a flow of `ẋ = F(x)` with derivative `D` in the initial state
(`IsDifferentiableFlow`, time first). For `0 ≤ s ≤ t`, `x` and every direction `h`, the map
`τ ↦ ∂D(τ, s, x)/∂x h` has, within `[s, ∞)` at `t`, the derivative
`D²F(φ(t, s, x)) (D(t, s, x) h) ∘ D(t, s, x) + DF(φ(t, s, x)) ∘ (∂D(t, s, x)/∂x h)`. -/
theorem hasDerivWithinAt_fderiv_fderiv_flow [FiniteDimensional ℝ E] (hF : ContDiff ℝ 2 F)
    (hb : HasBoundedIteratedFDeriv 1 2 F)
    (h : IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (x v : E) :
    HasDerivWithinAt (fun τ => fderiv ℝ (D τ s) x v)
      ((fderiv ℝ (fderiv ℝ F) (φ t s x) (D t s x v)).comp (D t s x) +
        (fderiv ℝ F (φ t s x)).comp (fderiv ℝ (D t s) x v)) (Ici s) t := by
  obtain ⟨G, φG, DG, -, -, hGflow, hloc, hid⟩ :=
    h.exists_augmentedFlow (m := 0) (by simpa using hF) hb hs (t + 1)
  have hιd : ∀ y : E, HasFDerivAt (fun y : E => (y, (1 : E →L[ℝ] E)))
      (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E)) y := fun y =>
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const (1 : E →L[ℝ] E) y)
  -- on the window `[s, t + 1]` the derivatives of `φ(τ, s, ·)` and `D(τ, s, ·)` are components of
  -- the derivative of the augmented flow
  have hDf : ∀ τ ∈ Icc s (t + 1), fderiv ℝ (D τ s) x =
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
        ((DG τ s (x, 1)).comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))) := by
    intro τ hτ
    have heq : D τ s = fun y => (φG τ s (y, 1)).2 := funext fun y => by rw [hid τ hτ y]
    rw [heq]
    exact ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp x
      ((hGflow.hasFDerivAt τ s hs hτ.1 (x, 1)).comp x (hιd x))).fderiv
  have hφf : fderiv ℝ (φ t s) x =
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).comp
        ((DG t s (x, 1)).comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))) := by
    have heq : φ t s = fun y => (φG t s (y, 1)).1 :=
      funext fun y => by rw [hid t ⟨hst, by linarith⟩ y]
    rw [heq]
    exact ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp x
      ((hGflow.hasFDerivAt t s hs hst (x, 1)).comp x (hιd x))).fderiv
  -- the variational equation of the augmented flow in the direction `(v, 0)`
  set L : (E × (E →L[ℝ] E) →L[ℝ] E × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).comp
      (ContinuousLinearMap.apply ℝ (E × (E →L[ℝ] E)) ((v, 0) : E × (E →L[ℝ] E))) with hL
  have hvar := L.hasFDerivAt.comp_hasDerivWithinAt t (hGflow.variational t s hs hst (x, 1))
  have hev : (fun τ => fderiv ℝ (D τ s) x v) =ᶠ[𝓝[Ici s] t] (L ∘ fun τ => DG τ s (x, 1)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one t))]
      with τ hτ hτ'
    rw [hDf τ ⟨hτ, le_of_lt hτ'⟩]
    rfl
  have hval : fderiv ℝ (D t s) x v = (L ∘ fun τ => DG τ s (x, 1)) t := by
    rw [hDf t ⟨hst, by linarith⟩]
    rfl
  refine (hvar.congr_of_eventuallyEq hev hval).congr_deriv ?_
  -- the derivative of the augmented field near `(φ(t, s, x), D(t, s, x))`
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  set a := φ t s x with ha
  set M := D t s x with hM
  have h1 : HasFDerivAt (fun q : E × (E →L[ℝ] E) => F q.1)
      ((fderiv ℝ F a).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))) (a, M) :=
    ((hF.differentiable (by norm_num)) a).hasFDerivAt.comp (a, M) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : E × (E →L[ℝ] E) => fderiv ℝ F q.1)
      ((fderiv ℝ (fderiv ℝ F) a).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))) (a, M) :=
    ((hF1.differentiable (by norm_num)) a).hasFDerivAt.comp (a, M) hasFDerivAt_fst
  have h3 := h2.clm_comp (hasFDerivAt_snd (p := (a, M)))
  have hGeq : G =ᶠ[𝓝 (a, M)] fun q => (F q.1, (fderiv ℝ F q.1).comp q.2) := by
    filter_upwards [hloc t ⟨hst, by linarith⟩ x] with q hq
    rw [hq]
    simp
  have hfG := hGeq.fderiv_eq.trans (h1.prodMk h3).fderiv
  have hpt : φG t s (x, 1) = (a, M) := hid t ⟨hst, by linarith⟩ x
  have hw1 : (DG t s (x, 1) (v, 0)).1 = M v := by
    have e := congrArg (fun T : E →L[ℝ] E => T v) hφf
    simp only [(h.hasFDerivAt t s hs hst x).fderiv] at e
    rw [e]
    rfl
  have hw2 : (DG t s (x, 1) (v, 0)).2 = fderiv ℝ (D t s) x v := by
    rw [hDf t ⟨hst, by linarith⟩]
    rfl
  rw [hpt, hfG, ContinuousLinearMap.mul_def]
  simp only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    hw1, hw2]
  abel

end IsDifferentiableFlow

end Stability
end RoboLean
