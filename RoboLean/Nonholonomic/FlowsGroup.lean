import RoboLean.Nonholonomic.FlowsReverse

/-!
# The group property of flows and flows as diffeomorphisms (MLS pp. 322–323)

**What MLS prints.** "By the existence and uniqueness theorem of ordinary differential equations,
for each fixed `t`, `φ^f_t` is a local diffeomorphism of `ℝⁿ` onto itself. Further, it satisfies
the following group property: `φ^f_t ∘ φ^f_s = φ^f_{t+s}`, for all `t` and `s`" (pp. 322–323).

**Proved here**, for an autonomous field `X` with a flow `φ` differentiable in the initial state
(`IsDifferentiableFlow` for the system `fun _ => X`; constructed for fields with a bounded
continuous derivative by `exists_isDifferentiableFlow_autonomous`):

* the group property `φ^X_t ∘ φ^X_s = φ^X_{t+s}` for `t, s ≥ 0` (`flow_add`);
* with a flow `φ'` of `−X`, `φ^X_t ∘ φ^{−X}_t = id` (`flow_comp_flow_neg`; the other order is
  `flow_neg_comp_flow`), so for every `t ≥ 0` the map `φ^X_t` is a bijection of the whole space
  that is differentiable at every point, with the differentiable inverse `φ^{−X}_t`
  (`flow_isDiffeomorph`): a global diffeomorphism of class `C¹` in this sense, which is stronger
  than MLS's "local diffeomorphism".

**Hypotheses against MLS.** MLS states the group property "for all `t` and `s`"; here `t, s ≥ 0`,
negative times being represented by the flow of `−X`. Differentiability of the inverse is that of
the flow of `−X`; continuity of the derivative in the initial state is not part of the statement.

**Conventions.** Time first; `φ t 0 q` is MLS's `φ^X_t(q)` for `t ≥ 0`; solutions in the sense of
`IsSolution`.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The group property of flows (MLS p. 323, `φ^f_t ∘ φ^f_s = φ^f_{t+s}`):** if `φ` is a flow of
`ẋ = X(x)` (`IsDifferentiableFlow`, time first), then `φ(t, 0, φ(s, 0, x)) = φ(t + s, 0, x)` for
`t, s ≥ 0`. -/
theorem flow_add {X : E → E} {DX : E → E →L[ℝ] E} {φ : ℝ → ℝ → E → E}
    {D : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (x : E) : φ t 0 (φ s 0 x) = φ (t + s) 0 x := by
  have hsol := hX.isSolution 0 le_rfl x
  have hc : Stability.IsSolution (fun _ => X) 0 (fun σ => φ (σ + s) 0 x) := by
    refine ⟨?_, fun σ hσ => ?_⟩
    · refine (hX.continuousOn_trajectory le_rfl x).comp
        (continuous_id.add continuous_const).continuousOn fun σ hσ => ?_
      simp only [mem_Ici] at hσ ⊢
      linarith
    · exact HasDerivAt.comp_add_const σ s (hsol.2 (σ + s) (by linarith))
  have h := hX.eq_of_isSolution 0 le_rfl _ hc t ht
  simp only [zero_add] at h
  exact h.symm

/-- **The flow of `X` undoes the flow of `−X` (MLS pp. 322–323):** if `φ` is a flow of
`ẋ = X(x)` and `φ'` a flow of `ẋ = −X(x)` (`IsDifferentiableFlow`, time first), then
`φ(t, 0, φ'(t, 0, q)) = q` for `t ≥ 0`, i.e. `φ^X_t ∘ φ^{−X}_t = id`. -/
theorem flow_comp_flow_neg {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    {t : ℝ} (ht : 0 ≤ t) (q : E) : φ t 0 (φ' t 0 q) = q := by
  have hX2 : Stability.IsDifferentiableFlow (fun _ => -(-X)) (fun _ => DX) φ D := by
    simpa only [neg_neg] using hX
  exact flow_neg_comp_flow hX' hX2 ht q

/-- **For each fixed `t ≥ 0` the flow is a diffeomorphism (MLS pp. 322–323: "for each fixed `t`,
`φ^f_t` is a local diffeomorphism of `ℝⁿ` onto itself"):** if `φ` and `φ'` are flows of `X` and
`−X` differentiable in the initial state (`IsDifferentiableFlow`, time first), then `φ^X_t` and
`φ^{−X}_t` are inverse to each other on the whole space and both have the Fréchet derivatives
`D(t, 0, x)` and `D'(t, 0, x)` at every point `x`. -/
theorem flow_isDiffeomorph {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    {t : ℝ} (ht : 0 ≤ t) :
    Function.LeftInverse (φ' t 0) (φ t 0) ∧ Function.RightInverse (φ' t 0) (φ t 0) ∧
      (∀ x, HasFDerivAt (φ t 0) (D t 0 x) x) ∧ ∀ x, HasFDerivAt (φ' t 0) (D' t 0 x) x :=
  ⟨fun q => flow_neg_comp_flow hX hX' ht q, fun q => flow_comp_flow_neg hX hX' ht q,
    fun x => hX.hasFDerivAt t 0 le_rfl ht x, fun x => hX'.hasFDerivAt t 0 le_rfl ht x⟩

end Nonholonomic
end RoboLean
