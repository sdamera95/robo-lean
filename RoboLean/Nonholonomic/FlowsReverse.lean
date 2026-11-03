import RoboLean.Control.FlowDerivative

/-!
# The flow of `−X` undoes the flow of `X` (MLS pp. 322–324)

**What MLS prints.** The flow `φ^f_t(q)` of a vector field `f` is "the state of the differential
equation at time `t` starting from `q` at time 0" (p. 322); it satisfies the group property
`φ^f_t ∘ φ^f_s = φ^f_{t+s}` (p. 323), and the square of flows (7.8) on p. 324 runs the flows of
`−g₁` and `−g₂` after those of `g₁` and `g₂`, using that the flow of `−g` for `ε` seconds retraces
the flow of `g` for `ε` seconds.

**Proved here.** For an autonomous field `X` with a flow `φ` and the field `−X` with a flow `φ'`
(each a flow in the sense of `IsDifferentiableFlow`, written for the systems `fun _ => X` and
`fun _ => -X`), `φ'(t, 0, φ(t, 0, q)) = q` for `t ≥ 0` (`flow_neg_comp_flow`): the curve that
runs the solution of `X` backwards from time `t` and then continues along `−X` solves `−X`, so by
uniqueness it is the flow of `−X` from `φ(t, 0, q)`.

**Conventions.** Time first; `φ t 0 q` is MLS's `φ^X_t(q)` for `t ≥ 0` (the flow from initial
time `0`); solutions in the sense of `IsSolution`. Only the existence, uniqueness and
initial-condition fields of `IsDifferentiableFlow` are used.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The flow of `−X` undoes the flow of `X` (MLS pp. 322–324, the flows of `−g` in the square
(7.8)):** if `φ` is a flow of `ẋ = X(x)` and `φ'` a flow of `ẋ = −X(x)` (each in the sense of
`IsDifferentiableFlow`, time first), then `φ'(t, 0, φ(t, 0, q)) = q` for every `t ≥ 0`, i.e.
`φ^{−X}_t ∘ φ^X_t = id`. -/
theorem flow_neg_comp_flow {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D')
    {t : ℝ} (ht : 0 ≤ t) (q : E) : φ' t 0 (φ t 0 q) = q := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    rw [hX.self_eq 0 le_rfl, hX'.self_eq 0 le_rfl]
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt_field 0 le_rfl y).continuousAt
  have hy := hX.isSolution 0 le_rfl q
  have hz := hX'.isSolution 0 le_rfl q
  have hy0 : φ 0 0 q = q := hX.self_eq 0 le_rfl q
  have hz0 : φ' 0 0 q = q := hX'.self_eq 0 le_rfl q
  set c : ℝ → E := fun τ => if τ ≤ t then φ (t - τ) 0 q else φ' (τ - t) 0 q with hc_def
  have hneg : HasDerivAt (fun τ : ℝ => t - τ) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub t
  -- the backward piece at a time `τ < t`
  have hback : ∀ τ, τ < t →
      HasDerivAt (fun τ => φ (t - τ) 0 q) (-(X (φ (t - τ) 0 q))) τ := by
    intro τ hτ
    have h1 := hy.2 (t - τ) (by linarith)
    have h2 : HasDerivAt (fun r : ℝ => t - r) (-1) τ := by
      simpa using (hasDerivAt_id τ).const_sub t
    simpa [Function.comp_def] using h1.scomp τ h2
  have hd : ∀ τ, HasDerivAt c (-(X (c τ))) τ := by
    intro τ
    rcases lt_trichotomy τ t with hlt | heq | hgt
    · have hev : c =ᶠ[𝓝 τ] fun τ => φ (t - τ) 0 q := by
        filter_upwards [Iio_mem_nhds hlt] with r hr
        simp [hc_def, (mem_Iio.1 hr).le]
      have hcτ : c τ = φ (t - τ) 0 q := by simp [hc_def, hlt.le]
      rw [hcτ]
      exact (hback τ hlt).congr_of_eventuallyEq hev
    · subst heq
      have hct : c τ = q := by simp [hc_def, hy0]
      rw [hct, ← hasDerivWithinAt_univ, ← Iic_union_Ici]
      refine HasDerivWithinAt.union ?_ ?_
      · have h1 := hy.hasDerivWithinAt_Ici hXc
        have h2 := h1.scomp_of_eq τ (hneg.hasDerivWithinAt (s := Iic τ))
          (fun r hr => by simp only [mem_Ici, mem_Iic] at hr ⊢; linarith) (by simp)
        rw [hy0] at h2
        refine (by simpa [Function.comp_def] using h2 :
          HasDerivWithinAt (fun r => φ (τ - r) 0 q) (-(X q)) (Iic τ) τ).congr ?_ ?_
        · intro r hr
          simp [hc_def, mem_Iic.1 hr]
        · simp [hc_def]
      · have h1 := hz.hasDerivWithinAt_Ici hXc.neg
        have h3 : HasDerivWithinAt (fun r => φ' (r - τ) 0 q) (-(X q)) (Ici τ) τ := by
          have h4 := (h1.scomp_of_eq τ
            (((hasDerivAt_id τ).sub_const τ).hasDerivWithinAt (s := Ici τ))
            (fun r hr => by simp only [mem_Ici, id] at hr ⊢; linarith) (by simp))
          rw [hz0] at h4
          simpa [Function.comp_def] using h4
        refine h3.congr ?_ ?_
        · intro r hr
          rcases eq_or_lt_of_le (mem_Ici.1 hr) with h | h
          · subst h
            simp [hc_def, hy0, hz0]
          · simp [hc_def, not_le.2 h]
        · simp [hc_def, hy0, hz0]
    · have hev : c =ᶠ[𝓝 τ] fun τ => φ' (τ - t) 0 q := by
        filter_upwards [Ioi_mem_nhds hgt] with r hr
        simp [hc_def, not_le.2 (mem_Ioi.1 hr)]
      have hcτ : c τ = φ' (τ - t) 0 q := by simp [hc_def, not_le.2 hgt]
      rw [hcτ]
      have h1 := hz.2 (τ - t) (by linarith)
      exact (by simpa using h1.comp_sub_const τ t :
        HasDerivAt (fun τ => φ' (τ - t) 0 q) (-(X (φ' (τ - t) 0 q))) τ).congr_of_eventuallyEq hev
  have hc : Stability.IsSolution (fun _ => -X) 0 c :=
    ⟨fun τ _ => (hd τ).continuousAt.continuousWithinAt, fun τ _ => by simpa using hd τ⟩
  have key := hX'.eq_of_isSolution 0 le_rfl c hc t ht
  simpa [hc_def, hy0, ht] using key.symm

end Nonholonomic
end RoboLean
