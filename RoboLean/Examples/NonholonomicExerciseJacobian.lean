import RoboLean.Nonholonomic.Steering
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The endpoint map of a three-state chain under sinusoidal inputs and its Jacobian: MLS Chapter 8,
# Exercise 12

MLS Chapter 8, Exercise 12, printed p. 394 (rendered): the system `q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₂u₁`
with `q(0) = 0` and inputs `u₁ = α₁,₀ α₁,₁ cos 2πt + α₁,₂ sin 2πt`,
`u₂ = α₂,₀ + α₂,₁ cos 2πt + α₂,₂ sin 2πt`; (a) integrate from `t = 0` to `t = 1` to obtain `q(1)` as
a function of `α` and compute the Jacobian `A = ∂q(1)/∂α ∈ ℝ^{3×6}`; (b) prove that if `A` is full
rank then the system is controllable with inputs of this form.

**What is formalized.** Corrected printing: the first input is read as
`u₁ = α₁,₀ + α₁,₁ cos 2πt + α₁,₂ sin 2πt` (the `+` is missing on p. 394; the second input shows the
pattern). The system is the one-chain system (8.7) with `n = 3`. The coefficient vector is
`α = (α₁,₀, α₁,₁, α₁,₂, α₂,₀, α₂,₁, α₂,₂)`, indices `0, …, 5`.
* (a) Every trajectory on `[0, 1]` from `0` ends at
  `q(1) = (α₁,₀, α₂,₀, α₁,₀α₂,₀/2 + α₁,₀α₂,₂/(2π) − α₁,₁α₂,₂/(4π) − α₁,₂α₂,₀/(2π) + α₁,₂α₂,₁/(4π))`,
  and trajectories exist; the endpoint map has derivative the printed `3 × 6` Jacobian `A(α)`.
* (b) If `A(α)` has rank `3` (its linear map is onto), the endpoints at time `1` of the inputs of
  this form contain a neighbourhood of `q(1)` (local controllability with these inputs, by the
  surjective-derivative theorem); `A(α)` has rank `3` at `α = e₁`; and in fact every state is the
  endpoint of an input of this form.
-/

noncomputable section

open Set Filter Topology Real

namespace RoboLean
namespace Examples

open RoboLean.Nonholonomic

/-- **MLS Chapter 8, Exercise 12, p. 394, corrected printing: the inputs**
`u₁ = α₁,₀ + α₁,₁ cos 2πt + α₁,₂ sin 2πt`, `u₂ = α₂,₀ + α₂,₁ cos 2πt + α₂,₂ sin 2πt`. -/
def jacInput (α : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![α 0 + α 1 * cos (2 * π * t) + α 2 * sin (2 * π * t),
    α 3 + α 4 * cos (2 * π * t) + α 5 * sin (2 * π * t)]

/-- **MLS Chapter 8, Exercise 12(a), p. 394: the endpoint `q(1)` as a function of `α`.** -/
def jacEndpoint (α : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![α 0, α 3, α 0 * α 3 / 2 + α 0 * α 5 / (2 * π) - α 1 * α 5 / (4 * π) - α 2 * α 3 / (2 * π) +
    α 2 * α 4 / (4 * π)]

/-- **MLS Chapter 8, Exercise 12(a), p. 394: the Jacobian `A = ∂q(1)/∂α ∈ ℝ^{3×6}`.** -/
def jacMatrix (α : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     α 3 / 2 + α 5 / (2 * π), -(α 5 / (4 * π)), -(α 3 / (2 * π)) + α 4 / (4 * π),
       α 0 / 2 - α 2 / (2 * π), α 2 / (4 * π), α 0 / (2 * π) - α 1 / (4 * π)]

/-- **MLS Chapter 8, Exercise 12, p. 394:** the inputs are continuous in time. -/
theorem continuous_jacInput (α : Fin 6 → ℝ) : Continuous (jacInput α) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [jacInput] <;> fun_prop

/-- The closed form of `q₂(t) = ∫₀ᵗ u₂` (supporting definition for MLS p. 394). -/
private def jacQ2 (α : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  α 3 * t + α 4 * sin (2 * π * t) / (2 * π) + α 5 * (1 - cos (2 * π * t)) / (2 * π)

/-- An antiderivative of `q₂(t)u₁(t)` (supporting definition for MLS p. 394). -/
private def jacF (α : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  let w := 2 * π
  let s := sin (w * t)
  let c := cos (w * t)
  α 3 * α 0 * (t ^ 2 / 2) + α 3 * α 1 * (t * s / w + c / w ^ 2) +
    α 3 * α 2 * (-(t * c) / w + s / w ^ 2) + α 4 * α 0 / w * (-c / w) +
    α 4 * α 1 / w * (s ^ 2 / (2 * w)) + α 4 * α 2 / w * (t / 2 - s * c / (2 * w)) +
    α 5 * α 0 / w * (t - s / w) + α 5 * α 1 / w * (s / w - (t / 2 + s * c / (2 * w))) +
    α 5 * α 2 / w * (-c / w - s ^ 2 / (2 * w))

private theorem jacF_hasDerivAt (α : Fin 6 → ℝ) (t : ℝ) :
    HasDerivAt (jacF α) (jacQ2 α t * jacInput α t 0) t := by
  have hw : (2 * π : ℝ) ≠ 0 := by positivity
  have hl : HasDerivAt (fun x => 2 * π * x) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have hs := hl.sin
  have hc := hl.cos
  have ht := hasDerivAt_id t
  have h := ((((((((((ht.pow 2).div_const 2).const_mul (α 3 * α 0)).add
    ((((ht.mul hs).div_const (2 * π)).add (hc.div_const ((2 * π) ^ 2))).const_mul (α 3 * α 1))).add
    ((((ht.mul hc).neg.div_const (2 * π)).add (hs.div_const ((2 * π) ^ 2))).const_mul
      (α 3 * α 2))).add
    ((hc.neg.div_const (2 * π)).const_mul (α 4 * α 0 / (2 * π)))).add
    (((hs.pow 2).div_const (2 * (2 * π))).const_mul (α 4 * α 1 / (2 * π)))).add
    (((ht.div_const 2).sub ((hs.mul hc).div_const (2 * (2 * π)))).const_mul
      (α 4 * α 2 / (2 * π)))).add
    ((ht.sub (hs.div_const (2 * π))).const_mul (α 5 * α 0 / (2 * π)))).add
    (((hs.div_const (2 * π)).sub ((ht.div_const 2).add ((hs.mul hc).div_const (2 * (2 * π))))).const_mul
      (α 5 * α 1 / (2 * π)))).add
    (((hc.neg.div_const (2 * π)).sub ((hs.pow 2).div_const (2 * (2 * π)))).const_mul
      (α 5 * α 2 / (2 * π)))
  convert h using 1
  · funext x
    simp only [jacF, id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
  · simp only [jacQ2, jacInput, Matrix.cons_val_zero, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
    have hsc := sin_sq_add_cos_sq (t * 2 * π)
    linear_combination (α 4 * α 2 - α 5 * α 1) * hsc

/-- **MLS Chapter 8, Exercise 12(a), p. 394: the endpoint.** Every trajectory of the system on
`[0, 1]` with the inputs `jacInput α` from `q(0) = 0` ends at `q(1) = jacEndpoint α`. -/
theorem IsTrajectory.jac_endpoint {α : Fin 6 → ℝ} {x : ℝ → Fin 3 → ℝ}
    (hx : IsTrajectory (chainFields 3) (jacInput α) 1 x) (hx0 : x 0 = 0) :
    x 1 = jacEndpoint α := by
  have hu := continuous_jacInput α
  have hw : (2 * π : ℝ) ≠ 0 := by positivity
  have hl : ∀ t, HasDerivAt (fun x => 2 * π * x) (2 * π) t := fun t => by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  -- the first two coordinates
  have hq : ∀ (i₀ : Fin 3) (a b c : ℝ), (∀ s, jacInput α s (if i₀.val = 0 then 0 else 1) =
      a + b * cos (2 * π * s) + c * sin (2 * π * s)) → (i₀.val = 0 ∨ i₀.val = 1) →
      ∀ t ∈ Icc (0 : ℝ) 1, x t i₀ = a * t + b * sin (2 * π * t) / (2 * π) +
        c * (1 - cos (2 * π * t)) / (2 * π) := by
    intro i₀ a b c hab hi t ht
    obtain ⟨hc, S, hS⟩ := hx
    have hP : ∀ s, HasDerivAt (fun s => a * s + b * sin (2 * π * s) / (2 * π) +
        c * (1 - cos (2 * π * s)) / (2 * π)) (a + b * cos (2 * π * s) + c * sin (2 * π * s)) s := by
      intro s
      convert (((hasDerivAt_id s).const_mul a).add (((hl s).sin.const_mul b).div_const (2 * π))).add
        ((((hl s).cos.const_sub 1).const_mul c).div_const (2 * π)) using 1
      · funext s
        simp only [Pi.add_apply, id]
      · field_simp
    have hint : IntervalIntegrable (fun s => a + b * cos (2 * π * s) + c * sin (2 * π * s))
        MeasureTheory.volume 0 t := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h1 := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => x s i₀)
      (fun s => a + b * cos (2 * π * s) + c * sin (2 * π * s)) ht.1 S.countable_toSet
      (((continuous_apply i₀).comp_continuousOn hc).mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => by
        have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.1, lt_of_lt_of_le hs.1.2 ht.2⟩
        have h := hasDerivAt_pi.1 (hS s hs1 hs.2) i₀
        rcases hi with hi | hi
        · rw [chain_driftFree_of_val_eq_zero _ _ hi] at h
          rw [← hab s]
          simpa [hi] using h
        · rw [chain_driftFree_of_val_eq_one _ _ hi] at h
          rw [← hab s]
          simpa [hi] using h) hint
    have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hP s) hint
    have h0 : x 0 i₀ = 0 := by rw [hx0]; rfl
    rw [h2, h0] at h1
    simp only [mul_zero, sin_zero, cos_zero, sub_self, zero_div, add_zero] at h1
    linarith
  have hq1 := hq 0 (α 0) (α 1) (α 2) (fun s => rfl) (Or.inl rfl)
  have hq2 := hq 1 (α 3) (α 4) (α 5) (fun s => rfl) (Or.inr rfl)
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hs1 : sin (2 * π * 1) = 0 := by rw [mul_one]; exact sin_two_pi
  have hc1 : cos (2 * π * 1) = 1 := by rw [mul_one]; exact cos_two_pi
  -- the third coordinate
  have h3 : x 1 2 = ∫ s in (0 : ℝ)..1, jacQ2 α s * jacInput α s 0 := by
    obtain ⟨hc, S, hS⟩ := hx
    have hint : IntervalIntegrable (fun s => jacQ2 α s * jacInput α s 0) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      simp only [jacQ2, jacInput, Matrix.cons_val_zero]
      fun_prop
    have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => x s 2)
      (fun s => jacQ2 α s * jacInput α s 0) zero_le_one S.countable_toSet
      ((continuous_apply 2).comp_continuousOn hc)
      (fun s hs => by
        have h := hasDerivAt_pi.1 (hS s hs.1 hs.2) 2
        rw [chain_driftFree_of_val_eq_succ (x s) _ (j := 1) rfl le_rfl] at h
        convert h using 1
        rw [hq2 s (Ioo_subset_Icc_self hs.1)]
        simp only [jacQ2]
        ring) hint
    have h0 : x 0 2 = 0 := by rw [hx0]; rfl
    rw [h0, sub_zero] at h
    exact h.symm
  have hI : ∫ s in (0 : ℝ)..1, jacQ2 α s * jacInput α s 0 = jacF α 1 - jacF α 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => jacF_hasDerivAt α s)
      (by
        apply Continuous.intervalIntegrable
        simp only [jacQ2, jacInput, Matrix.cons_val_zero]
        fun_prop)
  ext i
  fin_cases i
  · show x 1 0 = jacEndpoint α 0
    rw [hq1 1 hone, hs1, hc1]
    simp [jacEndpoint]
  · show x 1 1 = jacEndpoint α 1
    rw [hq2 1 hone, hs1, hc1]
    simp [jacEndpoint]
  · show x 1 2 = jacEndpoint α 2
    rw [h3, hI]
    simp only [jacF, mul_one, mul_zero, sin_zero, cos_zero, sin_two_pi, cos_two_pi]
    simp only [jacEndpoint, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    ring

/-- **MLS Chapter 8, Exercise 12, p. 394: trajectories exist** for the inputs `jacInput α` from
every initial state. -/
theorem jac_exists_trajectory (α : Fin 6 → ℝ) (q₀ : Fin 3 → ℝ) :
    ∃ x, IsTrajectory (chainFields 3) (jacInput α) 1 x ∧ x 0 = q₀ := by
  obtain ⟨x, hx0, hx⟩ := chain_exists_solution 3 (continuous_jacInput α) q₀
  exact ⟨x, IsTrajectory.of_hasDerivAt 1 hx, hx0⟩

/-- **MLS Chapter 8, Exercise 12(a), p. 394: the Jacobian.** The endpoint map has derivative
`A(α)` (`jacMatrix`), the printed `3 × 6` matrix `∂q(1)/∂α`. -/
theorem hasFDerivAt_jacEndpoint (α : Fin 6 → ℝ) :
    HasFDerivAt jacEndpoint (Matrix.toLin' (jacMatrix α)).toContinuousLinearMap α := by
  have hP : ∀ k : Fin 6, HasFDerivAt (fun β : Fin 6 → ℝ => β k)
      (ContinuousLinearMap.proj k : (Fin 6 → ℝ) →L[ℝ] ℝ) α := fun k => hasFDerivAt_apply k α
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine (hP 0).congr_fderiv ?_
    ext v
    simp [jacMatrix, dotProduct, Fin.sum_univ_succ]
  · refine (hP 3).congr_fderiv ?_
    ext v
    simp [jacMatrix, dotProduct, Fin.sum_univ_succ]
  · have h := HasFDerivAt.add (HasFDerivAt.sub (HasFDerivAt.sub (HasFDerivAt.add
      (HasFDerivAt.const_mul (HasFDerivAt.mul (hP 0) (hP 3)) (1 / 2))
      (HasFDerivAt.const_mul (HasFDerivAt.mul (hP 0) (hP 5)) (1 / (2 * π))))
      (HasFDerivAt.const_mul (HasFDerivAt.mul (hP 1) (hP 5)) (1 / (4 * π))))
      (HasFDerivAt.const_mul (HasFDerivAt.mul (hP 2) (hP 3)) (1 / (2 * π))))
      (HasFDerivAt.const_mul (HasFDerivAt.mul (hP 2) (hP 4)) (1 / (4 * π)))
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun β => ?_)).congr_fderiv ?_
    · simp [jacEndpoint]
      ring
    · ext v
      simp [jacMatrix, dotProduct, Fin.sum_univ_succ]
      ring

/-- **MLS Chapter 8, Exercise 12(b), p. 394: full rank gives local controllability with these
inputs.** If the linear map of `A(α)` is onto (`A(α)` has rank `3`), the endpoints `q(1)` of the
trajectories from `0` with inputs of this form contain a neighbourhood of the endpoint for `α`. -/
theorem jac_endpoints_mem_nhds {α : Fin 6 → ℝ}
    (hA : Function.Surjective (Matrix.toLin' (jacMatrix α))) :
    {q : Fin 3 → ℝ | ∃ β x, IsTrajectory (chainFields 3) (jacInput β) 1 x ∧ x 0 = 0 ∧ x 1 = q} ∈
      𝓝 (jacEndpoint α) := by
  have hcd : ContDiff ℝ 1 jacEndpoint := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [jacEndpoint] <;> fun_prop
  have hs : HasStrictFDerivAt jacEndpoint (Matrix.toLin' (jacMatrix α)).toContinuousLinearMap α :=
    hcd.contDiffAt.hasStrictFDerivAt' (hasFDerivAt_jacEndpoint α) one_ne_zero
  have hmap := hs.map_nhds_eq_of_surj (by
    rw [LinearMap.range_eq_top]
    exact hA)
  rw [← hmap]
  refine Filter.mem_map.2 (Filter.Eventually.of_forall fun β => ?_)
  obtain ⟨x, hx, hx0⟩ := jac_exists_trajectory β 0
  exact ⟨β, x, hx, hx0, IsTrajectory.jac_endpoint hx hx0⟩

/-- **MLS Chapter 8, Exercise 12(b), p. 394: `A(α)` has rank `3` at `α = e₁`**
(`α₁,₀ = 1`, the other coefficients zero), so the hypothesis of `jac_endpoints_mem_nhds` holds. -/
theorem jacMatrix_surjective_single :
    Function.Surjective (Matrix.toLin' (jacMatrix (Pi.single 0 1))) := by
  intro y
  refine ⟨![y 0, 0, 0, y 1, 0, 2 * π * (y 2 - y 1 / 2)], ?_⟩
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  ext i
  fin_cases i
  · simp [jacMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [jacMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [jacMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp
    ring

/-- **MLS Chapter 8, Exercise 12(b), p. 394: every state is reached with inputs of this form.**
For every `q_f` there is a coefficient vector whose trajectories from `0` end at `q_f` at
time `1`. -/
theorem jac_endpoint_surjective (qf : Fin 3 → ℝ) :
    ∃ β, ∀ x, IsTrajectory (chainFields 3) (jacInput β) 1 x → x 0 = 0 → x 1 = qf := by
  refine ⟨![qf 0, 0, 1, qf 1, 4 * π * (qf 2 - qf 0 * qf 1 / 2 + qf 1 / (2 * π)), 0],
    fun x hx hx0 => ?_⟩
  rw [IsTrajectory.jac_endpoint hx hx0]
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  ext i
  fin_cases i <;> simp [jacEndpoint]

end Examples
end RoboLean
