import RoboLean.Nonholonomic.FlowsReverse
import Mathlib.Analysis.Calculus.VectorField

/-!
# Vector fields with vanishing Lie bracket have commuting flows (MLS p. 324, eq. (7.8))

**What MLS prints.** The flow `φ^f_t(q)` of a vector field is the solution of `q̇ = f(q)` from `q`
at time `0` (pp. 322–323). The composition of flows `φ^{g₁}_t ∘ φ^{g₂}_s` "in general" differs from
`φ^{g₂}_s ∘ φ^{g₁}_t` (p. 323); around the square of (7.8),
`φ^{−g₂}_ε ∘ φ^{−g₁}_ε ∘ φ^{g₂}_ε ∘ φ^{g₁}_ε (q₀) = q₀ + ε² [g₁, g₂](q₀) + O(ε³)`, and "if
`[f, g] = 0` then it can be shown that the right hand side of equation (7.8) is identically equal
to `q₀` and `f` and `g` are said to commute" (p. 324). MLS gives no proof of the last claim.

**Proved here**, for autonomous fields on a real normed space with flows differentiable in the
initial state (`IsDifferentiableFlow`, constructed for fields with a bounded continuous derivative
by `exists_isDifferentiableFlow_autonomous`) and `[X, Y] = 0` with Mathlib's bracket (the book's
sign, `lieBracket ℝ X Y = DY · X − DX · Y`):

* the derivative of the flow of `X` carries `Y` to `Y`: `Dφ^X_t(p) Y(p) = Y(φ^X_t(p))`
  (`fderiv_flow_apply_of_lieBracket_eq_zero`), since `w(t) = Dφ^X_t(p) Y(p) − Y(φ^X_t(p))` solves
  `ẇ = DX(φ^X_t(p)) w` with `w(0) = 0`;
* the flows commute: `φ^X_t ∘ φ^Y_s = φ^Y_s ∘ φ^X_t` for `t, s ≥ 0`
  (`flow_comm_of_lieBracket_eq_zero`), since `σ ↦ φ^X_t(φ^Y_σ(q))` solves `q̇ = Y(q)`;
* the square (7.8) closes exactly: `φ^{−Y}_ε ∘ φ^{−X}_ε ∘ φ^Y_ε ∘ φ^X_ε (q₀) = q₀` for `ε ≥ 0`
  (`flow_square_eq_of_lieBracket_eq_zero`), with `flow_neg_comp_flow`.

**Hypotheses against MLS.** MLS works with smooth complete fields on `ℝⁿ`; here the fields are
those of differentiable flows, `X` has a derivative bounded by `K` (for Grönwall's uniqueness
argument), and times are nonnegative (the flows of `−X` and `−Y` give the backward motions).

**Conventions.** Time first; `φ t 0 q` is MLS's `φ^X_t(q)` for `t ≥ 0`; solutions in the sense of
`IsSolution`; `lieBracket ℝ X Y` is Mathlib's bracket, equal to the book's `[X, Y]`.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The field of a differentiable flow is continuous (MLS pp. 322–323: the flow of a vector
field). -/
private theorem continuous_of_isDifferentiableFlow {X : E → E} {DX : E → E →L[ℝ] E}
    {φ : ℝ → ℝ → E → E} {D : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D) : Continuous X :=
  continuous_iff_continuousAt.2 fun y => (hX.hasFDerivAt_field 0 le_rfl y).continuousAt

/-- **The derivative of the flow of `X` along a field `Y` with `[X, Y] = 0` (MLS p. 324, the
commuting fields of (7.8)):** if `φ` is a flow of `ẋ = X(x)` differentiable in the initial state
with derivative `D` (`IsDifferentiableFlow`, time first), `‖DX y‖ ≤ K`, `Y` has the Fréchet
derivative `DY y` at every `y`, and `lieBracket ℝ X Y = 0` (Mathlib's bracket, the book's sign),
then `D(t, 0, p) Y(p) = Y(φ(t, 0, p))` for `t ≥ 0`: the flow carries `Y` to itself. -/
theorem fderiv_flow_apply_of_lieBracket_eq_zero {X Y : E → E} {DX DY : E → E →L[ℝ] E}
    {φ : ℝ → ℝ → E → E} {D : ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hDY : ∀ y, HasFDerivAt Y (DY y) y)
    (hXY : ∀ q, lieBracket ℝ X Y q = 0) {t : ℝ} (ht : 0 ≤ t) (p : E) :
    D t 0 p (Y p) = Y (φ t 0 p) := by
  have hXc := continuous_of_isDifferentiableFlow hX
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun y => (hDY y).continuousAt
  have hYX : ∀ q, DY q (X q) = DX q (Y q) := fun q => by
    have h := hXY q
    rw [lieBracket, (hDY q).fderiv, (hX.hasFDerivAt_field 0 le_rfl q).fderiv, sub_eq_zero] at h
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
    · rw [mul_apply_eq_comp, map_zero, add_zero, hYX, map_sub]
  have hzero : D 0 0 p (Y p) - Y (φ 0 0 p) = 0 := by
    rw [hX.fderiv_self 0 le_rfl p, hX.self_eq 0 le_rfl p, one_apply_eq_self,
      sub_self]
  have hbound : ∀ τ ∈ Ico 0 t, ‖DX (φ τ 0 p) (D τ 0 p (Y p) - Y (φ τ 0 p))‖ ≤
      K * ‖D τ 0 p (Y p) - Y (φ τ 0 p)‖ := fun τ _ =>
    ((DX (φ τ 0 p)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hXK _) (norm_nonneg _))
  have hw := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hder hzero hbound t
    ⟨ht, le_rfl⟩
  exact sub_eq_zero.1 hw

/-- **Fields with vanishing Lie bracket have commuting flows (MLS p. 324: "if `[f, g] = 0` ...
`f` and `g` are said to commute").** If `φ` and `ψ` are flows of `ẋ = X(x)` and `ẋ = Y(x)`
differentiable in the initial state (`IsDifferentiableFlow`, time first), `‖DX y‖ ≤ K` and
`lieBracket ℝ X Y = 0` (Mathlib's bracket, the book's sign), then
`φ(t, 0, ψ(s, 0, q)) = ψ(s, 0, φ(t, 0, q))` for `t, s ≥ 0`, i.e. `φ^X_t ∘ φ^Y_s = φ^Y_s ∘ φ^X_t`. -/
theorem flow_comm_of_lieBracket_eq_zero {X Y : E → E} {DX DY : E → E →L[ℝ] E}
    {φ ψ : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hY : Stability.IsDifferentiableFlow (fun _ => Y) (fun _ => DY) ψ D')
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hXY : ∀ q, lieBracket ℝ X Y q = 0)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (q : E) :
    φ t 0 (ψ s 0 q) = ψ s 0 (φ t 0 q) := by
  have hDY : ∀ y, HasFDerivAt Y (DY y) y := hY.hasFDerivAt_field 0 le_rfl
  have hφc : Continuous (φ t 0) := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt t 0 le_rfl ht y).continuousAt
  have hc : Stability.IsSolution (fun _ => Y) 0 (fun σ => φ t 0 (ψ σ 0 q)) := by
    refine ⟨hφc.comp_continuousOn (hY.continuousOn_trajectory le_rfl q), fun σ hσ => ?_⟩
    have h1 : HasDerivAt (fun σ => φ t 0 (ψ σ 0 q)) (D t 0 (ψ σ 0 q) (Y (ψ σ 0 q))) σ :=
      (hX.hasFDerivAt t 0 le_rfl ht (ψ σ 0 q)).comp_hasDerivAt σ
        ((hY.isSolution 0 le_rfl q).2 σ hσ)
    rw [fderiv_flow_apply_of_lieBracket_eq_zero hX hXK hDY hXY ht] at h1
    exact h1
  have h := hY.eq_of_isSolution 0 le_rfl _ hc s hs
  simpa [hY.self_eq 0 le_rfl] using h

/-- **The square of flows (7.8) closes exactly when `[X, Y] = 0` (MLS p. 324: "the right hand side
of equation (7.8) is identically equal to `q₀`").** With flows `φ, ψ, φ', ψ'` of `X, Y, −X, −Y`
differentiable in the initial state (`IsDifferentiableFlow`, time first), `‖DX y‖ ≤ K` and
`lieBracket ℝ X Y = 0` (Mathlib's bracket, the book's sign), for every `ε ≥ 0`:
`φ^{−Y}_ε ∘ φ^{−X}_ε ∘ φ^Y_ε ∘ φ^X_ε (q₀) = q₀`. -/
theorem flow_square_eq_of_lieBracket_eq_zero {X Y : E → E} {DX DY DX' DY' : E → E →L[ℝ] E}
    {φ ψ φ' ψ' : ℝ → ℝ → E → E} {D₁ D₂ D₃ D₄ : ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D₁)
    (hY : Stability.IsDifferentiableFlow (fun _ => Y) (fun _ => DY) ψ D₂)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D₃)
    (hY' : Stability.IsDifferentiableFlow (fun _ => -Y) (fun _ => DY') ψ' D₄)
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hXY : ∀ q, lieBracket ℝ X Y q = 0) {ε : ℝ} (hε : 0 ≤ ε)
    (q₀ : E) : ψ' ε 0 (φ' ε 0 (ψ ε 0 (φ ε 0 q₀))) = q₀ := by
  rw [← flow_comm_of_lieBracket_eq_zero hX hY hXK hXY hε hε q₀, flow_neg_comp_flow hX hX' hε,
    flow_neg_comp_flow hY hY' hε]

end Nonholonomic
end RoboLean
