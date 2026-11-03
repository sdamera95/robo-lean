import RoboLean.Nonholonomic.ChainedConversion

/-!
# The named chained-conversion statement needs the dimension `n` (MLS p. 370)

**What MLS prints.** On p. 370 the system `q̇ = g₁(q)u₁ + g₂(q)u₂` has `q ∈ ℝⁿ` (§3.2, from
p. 369) and the distributions `Δ₀, Δ₁, Δ₂` are built with that `n`; the existence of `h₂`
independent of `h₁` with `dh₂ · Δ₂ = 0` is "guaranteed by Frobenius' theorem". The library's
named statement `ChainedConversionStatement E` quantifies over every `n`, with no relation
between `n` and the dimension of `E`.

**Proved here.** `ChainedConversionStatement (Fin 3 → ℝ)` is false
(`not_chainedConversionStatement`): on `ℝ³` with `n = 4`, the fields `g₁ = ∂/∂x`,
`g₂ = ∂/∂y + x ∂/∂z` and the function `h₁ = x` satisfy the printed conditions on the whole space
(`counter_conditions`), with `[g₁, g₂] = ∂/∂z`, `ad²_{g₁}g₂ = 0` and
`Δ₁ = Δ₂ = span{∂/∂y, ∂/∂z}` at every point, `Δ₀ = ℝ³`; every `h₂` with `dh₂ · Δ₂ = 0` at a point
has `dh₂` a multiple of `dh₁` there. With `dim E = n` the existence holds with a `C¹` function
(`exists_chainedConversion_classOne`, `Nonholonomic/ChainedConversionProof`).

**Conventions.** Those of `Nonholonomic/ChainedConversion`; coordinates `x, y, z` are the entries
`0, 1, 2` of `Fin 3 → ℝ`, and `Pi.single i 1` is the `i`-th basis vector.
-/

noncomputable section

open Set VectorField
open RoboLean.Nonholonomic
open scoped ContDiff

namespace RoboLean
namespace Examples

/-- **The counterexample for MLS p. 370: `g₁ = ∂/∂x` on `ℝ³`.** -/
def counterG1 : (Fin 3 → ℝ) → Fin 3 → ℝ := fun _ => Pi.single 0 1

/-- **The counterexample for MLS p. 370: `g₂ = ∂/∂y + x ∂/∂z` on `ℝ³`.** -/
def counterG2 : (Fin 3 → ℝ) → Fin 3 → ℝ := fun q => Pi.single 1 1 + q 0 • Pi.single 2 1

/-- **The counterexample for MLS p. 370: `h₁ = x`.** -/
def counterH1 : (Fin 3 → ℝ) → ℝ := fun q => q 0

/-- **The counterexample for MLS p. 370: the plane `x = 0` of directions,** `span{∂/∂y, ∂/∂z}`. -/
def counterPlane : Submodule ℝ (Fin 3 → ℝ) :=
  LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0)

/-- **MLS p. 370 for the counterexample:** membership of the plane `x = 0`. -/
theorem counter_mem_plane (v : Fin 3 → ℝ) : v ∈ counterPlane ↔ v 0 = 0 := by
  simp [counterPlane]

private theorem counter_hasFDerivAt_G2 (q : Fin 3 → ℝ) :
    HasFDerivAt counterG2 ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).smulRight
      (Pi.single 2 1 : Fin 3 → ℝ)) q :=
  ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) q).smul_const (Pi.single 2 1 : Fin 3 → ℝ)).const_add _

private theorem counter_fderiv_G1 (q : Fin 3 → ℝ) : fderiv ℝ counterG1 q = 0 :=
  (hasFDerivAt_const (Pi.single 0 1 : Fin 3 → ℝ) q).fderiv

private theorem counter_fderiv_H1 (q : Fin 3 → ℝ) :
    fderiv ℝ counterH1 q = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 :=
  (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) q).fderiv

private theorem counter_adIter_zero : adIter counterG1 0 counterG2 = counterG2 := rfl

private theorem counter_adIter_one : adIter counterG1 1 counterG2 = fun _ => Pi.single 2 1 := by
  funext q
  rw [adIter_succ, counter_adIter_zero, lieBracket_eq]
  simp [(counter_hasFDerivAt_G2 q).fderiv, counter_fderiv_G1, counterG1]

private theorem counter_adIter_two : adIter counterG1 2 counterG2 = 0 := by
  funext q
  rw [adIter_succ, counter_adIter_one, lieBracket_eq]
  simp [counter_fderiv_G1]

private theorem counter_isInvolutiveOn_plane {D : (Fin 3 → ℝ) → Submodule ℝ (Fin 3 → ℝ)}
    (hD : ∀ q, D q = counterPlane) : IsInvolutiveOn D univ := by
  intro f g hf hg hfm hgm q _
  have key : ∀ h : (Fin 3 → ℝ) → Fin 3 → ℝ, (∀ x ∈ univ, DifferentiableAt ℝ h x) →
      (∀ x ∈ univ, h x ∈ D x) → ∀ x w, fderiv ℝ h x w 0 = 0 := by
    intro h hd hm x w
    have h0 : (fun y => h y 0) = fun _ => (0 : ℝ) := by
      funext y
      have := hm y (mem_univ y)
      rw [hD y, counter_mem_plane] at this
      exact this
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) (h x)).comp x (hd x (mem_univ x)).hasFDerivAt
    have h3 : HasFDerivAt (fun y => h y 0) (0 : (Fin 3 → ℝ) →L[ℝ] ℝ) x := by
      rw [h0]
      exact hasFDerivAt_const _ _
    have := congrArg (fun T : (Fin 3 → ℝ) →L[ℝ] ℝ => T w) (h1.unique h3)
    simpa using this
  rw [hD q, counter_mem_plane, lieBracket_eq]
  simp only [Pi.sub_apply]
  rw [key g hg hgm, key f hf hfm, sub_zero]

/-- **MLS p. 370 for the counterexample:** `Δ₁ = span{g₂, ad_{g₁}g₂, ad²_{g₁}g₂}` is the plane
`x = 0` at every point (`n = 4`). -/
theorem counter_delta1 (q : Fin 3 → ℝ) :
    spanAt (conversionDelta1 counterG1 counterG2 4) q = counterPlane := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, ⟨k, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, counter_mem_plane]
    fin_cases k <;> simp [counter_adIter_zero, counter_adIter_one, counter_adIter_two, counterG2]
  · intro v hv
    rw [counter_mem_plane] at hv
    have key : v = v 1 • adIter counterG1 0 counterG2 q +
        (v 2 - v 1 * q 0) • adIter counterG1 1 counterG2 q := by
      rw [counter_adIter_zero, counter_adIter_one]
      ext i
      fin_cases i <;> simp [counterG2, hv]
    rw [key]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨⟨0, by norm_num⟩, rfl⟩, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨⟨1, by norm_num⟩, rfl⟩, rfl⟩))

/-- **MLS p. 370 for the counterexample:** `Δ₂ = span{g₂, ad_{g₁}g₂}` is the plane `x = 0` at
every point (`n = 4`). -/
theorem counter_delta2 (q : Fin 3 → ℝ) :
    spanAt (conversionDelta2 counterG1 counterG2 4) q = counterPlane := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, ⟨k, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, counter_mem_plane]
    fin_cases k <;> simp [counter_adIter_zero, counter_adIter_one, counterG2]
  · intro v hv
    rw [counter_mem_plane] at hv
    have key : v = v 1 • adIter counterG1 0 counterG2 q +
        (v 2 - v 1 * q 0) • adIter counterG1 1 counterG2 q := by
      rw [counter_adIter_zero, counter_adIter_one]
      ext i
      fin_cases i <;> simp [counterG2, hv]
    rw [key]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨⟨0, by norm_num⟩, rfl⟩, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨⟨1, by norm_num⟩, rfl⟩, rfl⟩))

/-- **MLS p. 370 for the counterexample:** `Δ₀ = Δ₁ + span{g₁}` is all of `ℝ³` (`n = 4`). -/
theorem counter_delta0 (q : Fin 3 → ℝ) :
    spanAt (conversionDelta0 counterG1 counterG2 4) q = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hsplit : v = v 0 • counterG1 q + (v - v 0 • counterG1 q) := by abel
  have hplane : v - v 0 • counterG1 q ∈ counterPlane := by
    rw [counter_mem_plane]
    simp [counterG1]
  rw [hsplit]
  refine add_mem (Submodule.smul_mem _ _ (mem_spanAt (mem_insert _ _) q)) ?_
  rw [← counter_delta1 q] at hplane
  exact spanAt_mono (subset_insert _ _) q hplane

/-- **MLS p. 370: the printed conditions hold for the counterexample** on all of `ℝ³` with
`n = 4`. -/
theorem counter_conditions : ChainedConversionConditions counterG1 counterG2 4 counterH1 univ := by
  refine ⟨fun q _ => ?_, ⟨Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)), fun q _ => by
      rw [counter_delta0]⟩, fun f g _ _ _ _ q _ => by rw [counter_delta0]; exact Submodule.mem_top,
    ⟨Module.finrank ℝ counterPlane, fun q _ => by rw [counter_delta1]⟩,
    counter_isInvolutiveOn_plane counter_delta1,
    ⟨Module.finrank ℝ counterPlane, fun q _ => by rw [counter_delta2]⟩,
    counter_isInvolutiveOn_plane counter_delta2, fun q _ f hf => ?_, fun q _ => ?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨fun h => ?_, fun a h => ?_⟩
    · have := congrFun h 1
      simp [counterG2] at this
    · have := congrFun h 0
      simp [counterG1, counterG2] at this
  · have hfq : f q ∈ counterPlane := counter_delta1 q ▸ mem_spanAt hf q
    rw [counter_mem_plane] at hfq
    rw [lieDerivative_apply, counter_fderiv_H1]
    simpa using hfq
  · rw [lieDerivative_apply, counter_fderiv_H1]
    simp [counterG1]

/-- **MLS p. 370: the library's named statement `ChainedConversionStatement` is false on `ℝ³`**
(it allows `n = 4 ≠ 3`): the counterexample satisfies the printed conditions and has no `h₂` with
`dh₂ · Δ₂ = 0` independent of `h₁` at any point. -/
theorem not_chainedConversionStatement : ¬ ChainedConversionStatement (Fin 3 → ℝ) := by
  intro hS
  have hg1 : ContDiff ℝ ∞ counterG1 := contDiff_const
  have hg2 : ContDiff ℝ ∞ counterG2 :=
    contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin 3)).smul contDiff_const)
  have hh1 : ContDiff ℝ ∞ counterH1 := contDiff_apply ℝ ℝ (0 : Fin 3)
  obtain ⟨V, -, hq₀V, -, h₂, -, hΔ, hli⟩ :=
    hS counterG1 counterG2 4 counterH1 univ hg1 hg2 hh1 isOpen_univ counter_conditions 0 (mem_univ 0)
  have h0 := hli 0 hq₀V
  have hL1 : fderiv ℝ h₂ 0 (Pi.single 1 1) = 0 := by
    have h := hΔ 0 hq₀V counterG2 ⟨⟨0, by norm_num⟩, rfl⟩
    simpa [lieDerivative_apply, counterG2] using h
  have hL2 : fderiv ℝ h₂ 0 (Pi.single 2 1) = 0 := by
    have h := hΔ 0 hq₀V (adIter counterG1 1 counterG2) ⟨⟨1, by norm_num⟩, rfl⟩
    rw [counter_adIter_one] at h
    simpa [lieDerivative_apply] using h
  have hdh₁ := counter_fderiv_H1 0
  have hL : fderiv ℝ h₂ 0 = fderiv ℝ h₂ 0 (Pi.single 0 1) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hv]
    simp [hL1, hL2, mul_comm]
  rw [linearIndependent_fin2] at h0
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h0
  obtain ⟨hne, hnot⟩ := h0
  generalize fderiv ℝ h₂ 0 (Pi.single 0 1) = c at hL
  by_cases hc : c = 0
  · apply hne
    rw [hL, hc, zero_smul]
  · apply hnot c⁻¹
    rw [hdh₁, hL, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Examples
end RoboLean
