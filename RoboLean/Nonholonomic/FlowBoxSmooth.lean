import RoboLean.Control.FlowCk
import RoboLean.Nonholonomic.FlowsTwoSided

/-!
# Two-sided flows of class `C^k` in the time and the state together (MLS pp. 322–323)

**What MLS prints.** For a smooth complete field `f` on `ℝⁿ`, `φ^f_t(q)` solves
`d/dt φ^f_t(q) = f(φ^f_t(q))` with `φ^f_0(q) = q`, "for each fixed `t`, `φ^f_t` is a local
diffeomorphism of `ℝⁿ` onto itself", with `φ^f_t ∘ φ^f_s = φ^f_{t+s}` for all `t` and `s`
(pp. 322–323). The flow-box constructions behind Theorem 7.2 (p. 326) and Theorem 5.9 (p. 244)
differentiate `(t, q) ↦ φ^f_t(q)` in the time and the point together.

**Proved here.** On a finite-dimensional real space, for a field `X` of class `C^k`, `k ≥ 1`,
bounded together with its derivatives of orders `1` to `k` (`HasBoundedIteratedFDeriv 0 k X`), the
two-sided flow `(t, x) ↦ φ^X_t(x)` (`twoSidedFlow`, from flows of `X` and `−X`) is of class `C^k`
on `ℝ × E` (`contDiff_twoSidedFlow_of_bounded`); for a smooth field with every derivative bounded,
in particular a smooth field with compact support, it is smooth
(`contDiff_twoSidedFlow_infty`, `contDiff_twoSidedFlow_of_hasCompactSupport`).

**Route.** Time is turned into a state variable: on `ℝ × E` the field `H(λ, x) = (0, χ(λ) X(x))`,
with `χ(λ) = λ` for `|λ| ≤ T` and `χ` smooth with compact support, has bounded derivatives of
orders `1` to `k` (Leibniz's bound for the scalar multiplication), so its flow is `C^k` in the
initial state (`IsDifferentiableFlow.contDiff_flow`). For `|λ| ≤ T` the curve
`τ ↦ (λ, φ^X_{λτ}(x))` solves `H` from `(λ, x)`, so by uniqueness its value at `τ = 1`,
`(λ, φ^X_λ(x))`, is the time-one flow of `H` at `(λ, x)`.

**Hypotheses against MLS.** MLS's fields are smooth and complete. Here the field is bounded with
bounded derivatives (a smooth field cut off outside a ball qualifies), which gives completeness;
the boundedness of `X` itself is used for the time variable.

**Conventions.** As in `Nonholonomic/FlowsTwoSided` and `Nonholonomic/FlowBox`: time first, flows
`IsDifferentiableFlow` from time `0`, the two-sided flow `twoSidedFlow φ φ' t x` from flows `φ` of
`X` and `φ'` of `−X`; derivatives are Fréchet derivatives on `ℝ × E`.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

open Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The two-sided flow is of class `C^k` in the time and the state (MLS pp. 322–323):** on a
finite-dimensional real space, let `X` be of class `C^k`, `k ≥ 1`, bounded with bounded derivatives
of orders `1` to `k`, and let `φ`, `φ'` be flows of `X` and `−X` differentiable in the initial
state (`IsDifferentiableFlow`, time first). Then `(t, x) ↦ φ^X_t(x)` (`twoSidedFlow φ φ'`) is of
class `C^k` on `ℝ × E`. -/
theorem contDiff_twoSidedFlow_of_bounded [FiniteDimensional ℝ E] {k : ℕ} (hk : 1 ≤ k)
    {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    (hXc : ContDiff ℝ k X) (hb : HasBoundedIteratedFDeriv 0 k X) :
    ContDiff ℝ k fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2 := by
  refine contDiff_iff_contDiffAt.2 fun p₀ => ?_
  set T := |p₀.1| + 1 with hT
  have hT0 : 0 < T := by positivity
  -- the cut-off of the time variable
  let ρ : ContDiffBump (0 : ℝ) := ⟨T, T + 1, hT0, by linarith⟩
  set χ : ℝ → ℝ := fun l => ρ l • l with hχ
  have hχc : ContDiff ℝ ∞ χ := ρ.contDiff.smul contDiff_id
  have hχs : HasCompactSupport χ := ρ.hasCompactSupport.smul_right (f' := id)
  have hχid : ∀ l : ℝ, |l| ≤ T → χ l = l := fun l hl => by
    have hmem : l ∈ Metric.closedBall (0 : ℝ) ρ.rIn := by
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
      exact hl
    simp only [hχ, ρ.one_of_mem_closedBall hmem, one_smul]
  -- time as a state variable
  set H : ℝ × E → ℝ × E := fun q => (0, ContinuousLinearMap.lsmul ℝ ℝ (χ q.1) (X q.2)) with hH
  have hχ' : ContDiff ℝ k fun q : ℝ × E => χ q.1 := (hχc.of_le (mod_cast le_top)).comp contDiff_fst
  have hX₂ : ContDiff ℝ k fun q : ℝ × E => X q.2 := hXc.comp contDiff_snd
  have hS : ContDiff ℝ k fun q : ℝ × E => ContinuousLinearMap.lsmul ℝ ℝ (χ q.1) (X q.2) :=
    (contDiff_const.clm_apply hχ').clm_apply hX₂
  have hHc : ContDiff ℝ k H := contDiff_const.prodMk hS
  have hHb : HasBoundedIteratedFDeriv 1 k H := by
    intro j _ hj2
    have hjN : (j : ℕ∞ω) ≤ k := by exact_mod_cast hj2
    obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_bilinear (ContinuousLinearMap.lsmul ℝ ℝ) hχ' hX₂
      hjN
      (fun i _ => by
        obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_of_hasCompactSupport hχc hχs i
        exact ⟨C, fun q => (norm_iteratedFDeriv_comp_clm_le hχc (ContinuousLinearMap.fst ℝ ℝ E)
          (ContinuousLinearMap.norm_fst_le ℝ ℝ E) q (mod_cast le_top)).trans (hC _)⟩)
      (fun i hi => by
        obtain ⟨C, hC⟩ := hb i (Nat.zero_le i) (hi.trans hj2)
        exact ⟨C, fun q => (norm_iteratedFDeriv_comp_clm_le hXc (ContinuousLinearMap.snd ℝ ℝ E)
          (ContinuousLinearMap.norm_snd_le ℝ ℝ E) q (by exact_mod_cast hi.trans hj2)).trans
          (hC _)⟩)
    refine ⟨0 + C, fun q => (norm_iteratedFDeriv_prodMk_le contDiff_const hS hjN q).trans
      (add_le_add ?_ (hC q))⟩
    simp
  -- its flow, of class `C^k` in the initial state
  obtain ⟨K₂, hK₂⟩ := hHb 1 le_rfl hk
  have hHd : ∀ q, HasFDerivAt H (fderiv ℝ H q) q := fun q =>
    ((hHc.differentiable (by norm_cast; omega)) q).hasFDerivAt
  have hHfc : Continuous (fderiv ℝ H) := hHc.continuous_fderiv (by norm_cast; omega)
  have hHK : ∀ q, ‖fderiv ℝ H q‖ ≤ K₂.toNNReal := fun q => by
    rw [norm_fderiv_eq_norm_iteratedFDeriv_one]
    exact (hK₂ q).trans (Real.le_coe_toNNReal _)
  obtain ⟨φH, DH, hHf⟩ := exists_isDifferentiableFlow_autonomous hHd hHfc hHK
  have hφH : ContDiff ℝ k (φH 1 0) := hHf.contDiff_flow hk hHc hHb le_rfl zero_le_one
  -- for `|λ| ≤ T` the time-one flow of `H` at `(λ, x)` is `(λ, φ^X_λ(x))`
  have hid : ∀ q : ℝ × E, |q.1| ≤ T → twoSidedFlow φ φ' q.1 q.2 = (φH 1 0 q).2 := by
    rintro ⟨l, x⟩ hl
    set c : ℝ → ℝ × E := fun τ => (l, twoSidedFlow φ φ' (l * τ) x) with hc
    have hcd : ∀ τ, HasDerivAt c (H (c τ)) τ := by
      intro τ
      have h1 : HasDerivAt (fun τ => twoSidedFlow φ φ' (l * τ) x)
          (l • X (twoSidedFlow φ φ' (l * τ) x)) τ := by
        have := (isIntegralCurve_twoSidedFlow hX hX' x (l * τ)).scomp τ
          ((hasDerivAt_id τ).const_mul l)
        simpa [Function.comp_def] using this
      have e : H (c τ) = (0, l • X (twoSidedFlow φ φ' (l * τ) x)) := by
        simp only [hH, hc, ContinuousLinearMap.lsmul_apply, hχid l hl]
      rw [e]
      exact (hasDerivAt_const τ l).prodMk h1
    have hsol : IsSolution (fun _ => H) 0 c :=
      ⟨fun τ _ => (hcd τ).continuousAt.continuousWithinAt, fun τ _ => hcd τ⟩
    have h2 := hHf.eq_of_isSolution 0 le_rfl c hsol 1 zero_le_one
    have hc0 : c 0 = (l, x) := by simp [hc, twoSidedFlow_zero hX]
    rw [hc0] at h2
    have h3 := congrArg Prod.snd h2
    simpa [hc] using h3
  have hev : (fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2) =ᶠ[𝓝 p₀] fun p => (φH 1 0 p).2 := by
    have hlt : ∀ᶠ p in 𝓝 p₀, |p.1| < T :=
      (continuous_abs.comp continuous_fst).continuousAt.eventually_lt continuousAt_const
        (by simp [hT])
    filter_upwards [hlt] with p hp
    exact hid p hp.le
  exact (contDiff_snd.comp hφH).contDiffAt.congr_of_eventuallyEq hev

/-- **The two-sided flow of a smooth field with bounded derivatives is smooth in the time and the
state (MLS pp. 322–323):** on a finite-dimensional real space, if `X` is smooth and bounded with
every derivative bounded, and `φ`, `φ'` are flows of `X` and `−X` (`IsDifferentiableFlow`, time
first), then `(t, x) ↦ φ^X_t(x)` is smooth on `ℝ × E`. -/
theorem contDiff_twoSidedFlow_infty [FiniteDimensional ℝ E] {X : E → E}
    {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    (hXc : ContDiff ℝ ∞ X) (hb : ∀ k, HasBoundedIteratedFDeriv 0 k X) :
    ContDiff ℝ ∞ fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2 := by
  refine contDiff_infty.2 fun n => ?_
  have h1 := contDiff_twoSidedFlow_of_bounded (k := n + 1) (by omega) hX hX'
    (hXc.of_le (mod_cast le_top)) (hb (n + 1))
  exact h1.of_le (by exact_mod_cast Nat.le_succ n)

/-- **A smooth field with compact support has a two-sided flow smooth in the time and the state
(MLS pp. 322–323, for fields cut off outside a ball):** on a finite-dimensional real space, a
smooth `X` with compact support has flows `φ` of `X` and `φ'` of `−X` (`IsDifferentiableFlow`,
time first, with the derivatives `fderiv ℝ X` and `fderiv ℝ (−X)`), and `(t, x) ↦ φ^X_t(x)` is
smooth on `ℝ × E`. -/
theorem contDiff_twoSidedFlow_of_hasCompactSupport [FiniteDimensional ℝ E] {X : E → E}
    (hXc : ContDiff ℝ ∞ X) (hs : HasCompactSupport X) :
    ∃ (φ φ' : ℝ → ℝ → E → E) (D D' : ℝ → ℝ → E → E →L[ℝ] E),
      IsDifferentiableFlow (fun _ => X) (fun _ => fderiv ℝ X) φ D ∧
      IsDifferentiableFlow (fun _ => -X) (fun _ => fderiv ℝ (-X)) φ' D' ∧
      ContDiff ℝ ∞ fun p : ℝ × E => twoSidedFlow φ φ' p.1 p.2 := by
  have hb := hasBoundedIteratedFDeriv_of_hasCompactSupport hXc hs
  have hb' := hasBoundedIteratedFDeriv_of_hasCompactSupport hXc.neg hs.neg
  obtain ⟨K, hK⟩ := hb 1 1 1 le_rfl le_rfl
  obtain ⟨K', hK'⟩ := hb' 1 1 1 le_rfl le_rfl
  obtain ⟨φ, D, h⟩ := exists_isDifferentiableFlow_autonomous (K := K.toNNReal)
    (fun y => ((hXc.differentiable (by simp)) y).hasFDerivAt) (hXc.continuous_fderiv (by simp))
    fun y => by
      rw [norm_fderiv_eq_norm_iteratedFDeriv_one]
      exact (hK y).trans (Real.le_coe_toNNReal _)
  obtain ⟨φ', D', h'⟩ := exists_isDifferentiableFlow_autonomous (K := K'.toNNReal)
    (fun y => ((hXc.neg.differentiable (by simp)) y).hasFDerivAt)
    (hXc.neg.continuous_fderiv (by simp))
    fun y => by
      rw [norm_fderiv_eq_norm_iteratedFDeriv_one]
      exact (hK' y).trans (Real.le_coe_toNNReal _)
  exact ⟨φ, φ', D, D', h, h', contDiff_twoSidedFlow_infty h h' hXc fun k => hb 0 k⟩

end Nonholonomic
end RoboLean
