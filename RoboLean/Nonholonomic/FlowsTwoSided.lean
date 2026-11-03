import RoboLean.Nonholonomic.FlowsGroup
import Mathlib.Analysis.ODE.Basic

/-!
# Flows for all real times and the group property "for all `t` and `s`" (MLS pp. 322–323)

**What MLS prints.** `φ^f_t(q)` is the state at time `t` of the solution from `q` at time `0`,
and "it satisfies the following group property: `φ^f_t ∘ φ^f_s = φ^f_{t+s}`, for all `t` and `s`"
(pp. 322–323).

**Proved here.** For an autonomous field `X` with flows `φ` of `X` and `φ'` of `−X`
(`IsDifferentiableFlow`, from time `0`), the two-sided flow `twoSidedFlow φ φ' t` is `φ^X_t` for
`t ≥ 0` and `φ^{−X}_{−t}` for `t < 0`. It is the identity at `t = 0` (`twoSidedFlow_zero`), has
the group property for all real `t` and `s` (`twoSidedFlow_add`), and `t ↦ twoSidedFlow φ φ' t x`
is an integral curve of `X` on the whole real line in Mathlib's sense
(`isIntegralCurve_twoSidedFlow`).

**Conventions.** Time first; Mathlib's `IsIntegralCurve γ v` asks `HasDerivAt γ (v t (γ t)) t` for
every real `t`, with the time-dependent field `v = fun _ => X`.
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The flow of `X` for all real times (MLS pp. 322–323):** `φ^X_t = φ(t, 0, ·)` for `t ≥ 0` and
`φ^{−X}_{−t} = φ'(−t, 0, ·)` for `t < 0`, from a flow `φ` of `X` and a flow `φ'` of `−X`. -/
def twoSidedFlow (φ φ' : ℝ → ℝ → E → E) (t : ℝ) : E → E :=
  if 0 ≤ t then φ t 0 else φ' (-t) 0

/-- **The two-sided flow at time `0` is the identity (MLS p. 322: the solution "starting from `q`
at time 0").** -/
theorem twoSidedFlow_zero {X : E → E} {DX : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D) (x : E) :
    twoSidedFlow φ φ' 0 x = x := by
  simp only [twoSidedFlow, le_refl, ↓reduceIte]
  exact hX.self_eq 0 le_rfl x

/-- **The group property for all real times (MLS p. 323: `φ^f_t ∘ φ^f_s = φ^f_{t+s}`, "for all `t`
and `s`"):** with flows `φ` of `X` and `φ'` of `−X` (`IsDifferentiableFlow`, time first),
`twoSidedFlow φ φ' t (twoSidedFlow φ φ' s x) = twoSidedFlow φ φ' (t + s) x` for all real `t`,
`s`. -/
theorem twoSidedFlow_add {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') (t s : ℝ) (x : E) :
    twoSidedFlow φ φ' t (twoSidedFlow φ φ' s x) = twoSidedFlow φ φ' (t + s) x := by
  have hA : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → ∀ y, φ a 0 (φ b 0 y) = φ (a + b) 0 y :=
    fun ha hb y => flow_add hX ha hb y
  have hB : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → ∀ y, φ' a 0 (φ' b 0 y) = φ' (a + b) 0 y :=
    fun ha hb y => flow_add hX' ha hb y
  have hC : ∀ {a : ℝ}, 0 ≤ a → ∀ y, φ a 0 (φ' a 0 y) = y :=
    fun ha y => flow_comp_flow_neg hX hX' ha y
  have hD : ∀ {a : ℝ}, 0 ≤ a → ∀ y, φ' a 0 (φ a 0 y) = y :=
    fun ha y => flow_neg_comp_flow hX hX' ha y
  simp only [twoSidedFlow]
  by_cases ht : 0 ≤ t <;> by_cases hs : 0 ≤ s <;> by_cases hts : 0 ≤ t + s
  · simp only [ht, hs, hts, ↓reduceIte]
    rw [hA ht hs]
  · exact absurd (add_nonneg ht hs) hts
  · simp only [ht, hs, hts, ↓reduceIte]
    have h := hA hts (by linarith : 0 ≤ -s) (φ' (-s) 0 x)
    rw [show t + s + -s = t by ring, hC (by linarith)] at h
    exact h.symm
  · simp only [ht, hs, hts, ↓reduceIte]
    have h := hB ht (by linarith : 0 ≤ -(t + s)) x
    rw [show t + -(t + s) = -s by ring] at h
    rw [← h, hC ht]
  · simp only [ht, hs, hts, ↓reduceIte]
    have h := hA (by linarith : 0 ≤ -t) hts x
    rw [show -t + (t + s) = s by ring] at h
    rw [← h, hD (by linarith)]
  · simp only [ht, hs, hts, ↓reduceIte]
    have h := hB (by linarith : 0 ≤ -(t + s)) hs (φ s 0 x)
    rw [show -(t + s) + s = -t by ring, hD hs] at h
    exact h.symm
  · exact absurd hts (by linarith)
  · simp only [ht, hs, hts, ↓reduceIte]
    rw [hB (by linarith) (by linarith)]
    congr 1
    ring

/-- **The two-sided flow is an integral curve of `X` on the whole real line (MLS eq. (7.7),
p. 322, `d/dt φ^f_t(q) = f(φ^f_t(q))`):** with flows `φ` of `X` and `φ'` of `−X`
(`IsDifferentiableFlow`, time first), `t ↦ twoSidedFlow φ φ' t x` has the derivative
`X(twoSidedFlow φ φ' t x)` at every real `t` (Mathlib's `IsIntegralCurve` for `fun _ => X`). -/
theorem isIntegralCurve_twoSidedFlow {X : E → E} {DX DX' : E → E →L[ℝ] E}
    {φ φ' : ℝ → ℝ → E → E} {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') (x : E) :
    IsIntegralCurve (fun t => twoSidedFlow φ φ' t x) (fun _ => X) := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun y =>
    (hX.hasFDerivAt_field 0 le_rfl y).continuousAt
  have hy := hX.isSolution 0 le_rfl x
  have hz := hX'.isSolution 0 le_rfl x
  have hy0 : φ 0 0 x = x := hX.self_eq 0 le_rfl x
  have hz0 : φ' 0 0 x = x := hX'.self_eq 0 le_rfl x
  have hneg : ∀ r, r < 0 → HasDerivAt (fun r => φ' (-r) 0 x) (X (φ' (-r) 0 x)) r := by
    intro r hr
    have h1 := hz.2 (-r) (by linarith)
    have h2 := h1.scomp r (hasDerivAt_neg r)
    simpa [Function.comp_def] using h2
  intro t
  show HasDerivAt _ (X (twoSidedFlow φ φ' t x)) t
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · have hev : (fun t => twoSidedFlow φ φ' t x) =ᶠ[𝓝 t] fun r => φ' (-r) 0 x := by
      filter_upwards [Iio_mem_nhds hlt] with r hr
      simp [twoSidedFlow, not_le.2 (mem_Iio.1 hr)]
    have hγ : twoSidedFlow φ φ' t x = φ' (-t) 0 x := by simp [twoSidedFlow, not_le.2 hlt]
    rw [hγ]
    exact (hneg t hlt).congr_of_eventuallyEq hev
  · subst heq
    have hγ : twoSidedFlow φ φ' 0 x = x := twoSidedFlow_zero hX x
    rw [hγ, ← hasDerivWithinAt_univ, ← Iic_union_Ici]
    refine HasDerivWithinAt.union ?_ ?_
    · have h1 := hz.hasDerivWithinAt_Ici hXc.neg
      have h2 := h1.scomp_of_eq (0 : ℝ) ((hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt (s := Iic 0))
        (fun r hr => by simp only [mem_Ici, mem_Iic] at hr ⊢; linarith) (by simp)
      rw [hz0] at h2
      refine (by simpa [Function.comp_def] using h2 :
        HasDerivWithinAt (fun r => φ' (-r) 0 x) (X x) (Iic 0) 0).congr ?_ ?_
      · intro r hr
        rcases eq_or_lt_of_le (mem_Iic.1 hr) with h | h
        · subst h
          simp [twoSidedFlow, hy0, hz0]
        · simp [twoSidedFlow, not_le.2 h]
      · simp [twoSidedFlow, hy0, hz0]
    · have h1 := hy.hasDerivWithinAt_Ici hXc
      rw [hy0] at h1
      refine h1.congr ?_ ?_
      · intro r hr
        simp [twoSidedFlow, mem_Ici.1 hr]
      · simp [twoSidedFlow, hy0]
  · have hev : (fun t => twoSidedFlow φ φ' t x) =ᶠ[𝓝 t] fun r => φ r 0 x := by
      filter_upwards [Ioi_mem_nhds hgt] with r hr
      simp [twoSidedFlow, (mem_Ioi.1 hr).le]
    have hγ : twoSidedFlow φ φ' t x = φ t 0 x := by simp [twoSidedFlow, hgt.le]
    rw [hγ]
    exact (hy.2 t hgt).congr_of_eventuallyEq hev

end Nonholonomic
end RoboLean
