import RoboLean.Nonholonomic.Steering

/-!
# Steering a second-order model system with sinusoids: MLS p. 363

MLS Chapter 8, §2.2, printed pp. 361–363: for `m = 2` the second-order model system (8.6) becomes
`q̇₁ = u₁, q̇₂ = u₂, q̇₁₂ = q₁ u₂, q̇₁₂₁ = q₁₂ u₁, q̇₁₂₂ = q₁₂ u₂` (p. 363). "To steer `q₁₂₁`
independently of the other states, choose `u₁ = a sin 2πt`, `u₂ = b cos 4πt` to obtain
`q₁₂₁(1) = q₁₂₁(0) − a²b/(16π²)`. Similarly, choosing `u₁ = b cos 4πt`, `u₂ = a sin 2πt` gives
`q₁₂₂(1) = q₁₂₂(0) + a²b/(32π²)` and all the other states return to their original values."

**Conventions.** The state is `Fin 5 → ℝ` with `q 0 = q₁`, `q 1 = q₂`, `q 2 = q₁₂`, `q 3 = q₁₂₁`,
`q 4 = q₁₂₂`. Trajectories are those of `IsTrajectory` on `[0, 1]`, from any initial state; the
inputs are sinusoids (continuous, not piecewise constant).
-/

noncomputable section

open Set Filter Topology Real intervalIntegral

namespace RoboLean
namespace Nonholonomic

/-- **MLS p. 363: the input field `g₁ = (1, 0, 0, q₁₂, 0)`** of the second-order system with two
inputs. -/
def secondOrderG1 (q : Fin 5 → ℝ) : Fin 5 → ℝ := ![1, 0, 0, q 2, 0]

/-- **MLS p. 363: the input field `g₂ = (0, 1, q₁, 0, q₁₂)`** of the second-order system with two
inputs. -/
def secondOrderG2 (q : Fin 5 → ℝ) : Fin 5 → ℝ := ![0, 1, q 0, 0, q 2]

/-- **MLS eq. (8.6), p. 361, for `m = 2` (p. 363): the input fields `(g₁, g₂)`.** -/
def secondOrderFields : Fin 2 → (Fin 5 → ℝ) → Fin 5 → ℝ := ![secondOrderG1, secondOrderG2]

/-- **MLS p. 363: `q̇ = (u₁, u₂, q₁ u₂, q₁₂ u₁, q₁₂ u₂)`.** -/
theorem secondOrder_driftFree (q : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    driftFree secondOrderFields q u = ![u 0, u 1, q 0 * u 1, q 2 * u 0, q 2 * u 1] := by
  ext i
  fin_cases i <;> simp [driftFree, Fin.sum_univ_two, secondOrderFields, secondOrderG1,
    secondOrderG2] <;> ring

/-- Continuous integrands are interval integrable on `[0, 1]` (supporting lemma for MLS p. 363). -/
private theorem ii {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable f MeasureTheory.volume 0 1 :=
  hf.intervalIntegrable 0 1

/-- `∫₀¹ sin 4πt cos 4πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_sin4_cos4 : ∫ t in (0 : ℝ)..1, sin (4 * π * t) * cos (4 * π * t) = 0 := by
  have h : ∀ t : ℝ, sin (4 * π * t) * cos (4 * π * t) = (1 / 2) * sin (2 * π * (4 : ℕ) * t) := by
    intro t
    rw [show 2 * π * ((4 : ℕ) : ℝ) * t = 2 * (4 * π * t) by push_cast; ring, sin_two_mul]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_sin_two_pi_mul, mul_zero]

/-- `∫₀¹ sin 4πt cos 4πt cos 2πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_sin4_cos4_cos2 :
    ∫ t in (0 : ℝ)..1, sin (4 * π * t) * cos (4 * π * t) * cos (2 * π * t) = 0 := by
  have h : ∀ t : ℝ, sin (4 * π * t) * cos (4 * π * t) * cos (2 * π * t) =
      (1 / 4) * sin (2 * π * (5 : ℕ) * t) + (1 / 4) * sin (2 * π * (3 : ℕ) * t) := by
    intro t
    have h5 : sin (2 * π * ((5 : ℕ) : ℝ) * t) = sin (8 * π * t + 2 * π * t) := by
      push_cast; ring_nf
    have h3 : sin (2 * π * ((3 : ℕ) : ℝ) * t) = sin (8 * π * t - 2 * π * t) := by
      push_cast; ring_nf
    have h8 : sin (8 * π * t) = 2 * sin (4 * π * t) * cos (4 * π * t) := by
      rw [show 8 * π * t = 2 * (4 * π * t) by ring, sin_two_mul]
    rw [h5, h3, sin_add, sin_sub, h8]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_two_pi_mul, integral_sin_two_pi_mul]
  ring

/-- `∫₀¹ sin 4πt sin 2πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_sin4_sin2 : ∫ t in (0 : ℝ)..1, sin (4 * π * t) * sin (2 * π * t) = 0 := by
  have h : ∀ t : ℝ, sin (4 * π * t) * sin (2 * π * t) =
      (1 / 2) * cos (2 * π * (1 : ℕ) * t) - (1 / 2) * cos (2 * π * (3 : ℕ) * t) := by
    intro t
    have h1 : cos (2 * π * ((1 : ℕ) : ℝ) * t) = cos (4 * π * t - 2 * π * t) := by
      push_cast; ring_nf
    have h3 : cos (2 * π * ((3 : ℕ) : ℝ) * t) = cos (4 * π * t + 2 * π * t) := by
      push_cast; ring_nf
    rw [h1, h3, cos_add, cos_sub]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (ii (by fun_prop)) (ii (by fun_prop)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_two_pi_mul le_rfl, integral_cos_two_pi_mul (by norm_num)]
  ring

/-- `∫₀¹ sin² 4πt sin 2πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_sin4sq_sin2 :
    ∫ t in (0 : ℝ)..1, sin (4 * π * t) ^ 2 * sin (2 * π * t) = 0 := by
  have h : ∀ t : ℝ, sin (4 * π * t) ^ 2 * sin (2 * π * t) =
      (1 / 2) * sin (2 * π * (1 : ℕ) * t) - (1 / 4) * sin (2 * π * (5 : ℕ) * t) +
        (1 / 4) * sin (2 * π * (3 : ℕ) * t) := by
    intro t
    have h1 : sin (2 * π * ((1 : ℕ) : ℝ) * t) = sin (2 * π * t) := by push_cast; ring_nf
    have h5 : sin (2 * π * ((5 : ℕ) : ℝ) * t) = sin (8 * π * t + 2 * π * t) := by
      push_cast; ring_nf
    have h3 : sin (2 * π * ((3 : ℕ) : ℝ) * t) = sin (8 * π * t - 2 * π * t) := by
      push_cast; ring_nf
    have h8 : cos (8 * π * t) = 1 - 2 * sin (4 * π * t) ^ 2 := by
      rw [show 8 * π * t = 2 * (4 * π * t) by ring, cos_two_mul, cos_sq']
      ring
    rw [h1, h5, h3, sin_add, sin_sub, h8]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_add ((ii (by fun_prop)).sub (ii (by fun_prop))) (ii (by fun_prop)),
    intervalIntegral.integral_sub (ii (by fun_prop)) (ii (by fun_prop)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin_two_pi_mul, integral_sin_two_pi_mul,
    integral_sin_two_pi_mul]
  ring

/-- `∫₀¹ (1 − cos 2πt) sin 2πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_omc_sin2 : ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) * sin (2 * π * t) = 0 := by
  have h : ∀ t : ℝ, (1 - cos (2 * π * t)) * sin (2 * π * t) =
      sin (2 * π * (1 : ℕ) * t) - (1 / 2) * sin (2 * π * (2 : ℕ) * t) := by
    intro t
    have h1 : sin (2 * π * ((1 : ℕ) : ℝ) * t) = sin (2 * π * t) := by push_cast; ring_nf
    have h2 : sin (2 * π * ((2 : ℕ) : ℝ) * t) = sin (2 * (2 * π * t)) := by push_cast; ring_nf
    rw [h1, h2, sin_two_mul]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (ii (by fun_prop)) (ii (by fun_prop)),
    intervalIntegral.integral_const_mul, integral_sin_two_pi_mul, integral_sin_two_pi_mul]
  ring

/-- `∫₀¹ cos 2πt sin 2πt sin 4πt dt = 1/4` (supporting lemma for MLS p. 363). -/
private theorem int_cos2_sin2_sin4 :
    ∫ t in (0 : ℝ)..1, cos (2 * π * t) * sin (2 * π * t) * sin (4 * π * t) = 1 / 4 := by
  have h : ∀ t : ℝ, cos (2 * π * t) * sin (2 * π * t) * sin (4 * π * t) =
      1 / 4 - (1 / 4) * cos (2 * π * (4 : ℕ) * t) := by
    intro t
    have h4 : sin (4 * π * t) = 2 * sin (2 * π * t) * cos (2 * π * t) := by
      rw [show 4 * π * t = 2 * (2 * π * t) by ring, sin_two_mul]
    have h8 : cos (2 * π * ((4 : ℕ) : ℝ) * t) = 1 - 2 * sin (4 * π * t) ^ 2 := by
      rw [show 2 * π * ((4 : ℕ) : ℝ) * t = 2 * (4 * π * t) by push_cast; ring, cos_two_mul,
        cos_sq']
      ring
    rw [h8, h4]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (ii (by fun_prop)) (ii (by fun_prop)),
    intervalIntegral.integral_const_mul, integral_cos_two_pi_mul (by norm_num)]
  simp

/-- `∫₀¹ cos 4πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_cos4 : ∫ t in (0 : ℝ)..1, cos (4 * π * t) = 0 := by
  have e : ∀ t : ℝ, cos (2 * π * ((2 : ℕ) : ℝ) * t) = cos (4 * π * t) := fun t => by
    congr 1
    push_cast
    ring
  have h := integral_cos_two_pi_mul (k := 2) (by norm_num)
  simp_rw [e] at h
  exact h

/-- `∫₀¹ sin 2πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_sin2 : ∫ t in (0 : ℝ)..1, sin (2 * π * t) = 0 := by
  have e : ∀ t : ℝ, sin (2 * π * ((1 : ℕ) : ℝ) * t) = sin (2 * π * t) := fun t => by
    congr 1
    push_cast
    ring
  have h := integral_sin_two_pi_mul 1
  simp_rw [e] at h
  exact h

/-- `∫₀¹ (1 − cos 2πt) cos 4πt dt = 0` (supporting lemma for MLS p. 363). -/
private theorem int_I12 : ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) * cos (4 * π * t) = 0 := by
  have e : ∀ t : ℝ, cos (2 * π * ((2 : ℕ) : ℝ) * t) = cos (4 * π * t) := fun t => by
    congr 1
    push_cast
    ring
  have h := integral_one_sub_cos_pow_mul_cos_of_lt (i := 1) (k := 2) (by norm_num)
  simp_rw [e, pow_one] at h
  exact h

/-- `∫₀¹ (1 − cos 2πt)² cos 4πt dt = 1/4` (supporting lemma for MLS p. 363). -/
private theorem int_I22 :
    ∫ t in (0 : ℝ)..1, (1 - cos (2 * π * t)) ^ 2 * cos (4 * π * t) = 1 / 4 := by
  have e : ∀ t : ℝ, cos (2 * π * ((2 : ℕ) : ℝ) * t) = cos (4 * π * t) := fun t => by
    congr 1
    push_cast
    ring
  have h := integral_one_sub_cos_pow_mul_cos_self 2
  simp_rw [e] at h
  rw [h]
  norm_num

/-- The fundamental theorem of calculus on `[0, t] ⊆ [0, 1]` away from finitely many times
(supporting lemma for MLS p. 363). -/
private theorem sub_eq_integral {y f : ℝ → ℝ} {S : Finset ℝ} (hy : ContinuousOn y (Icc 0 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ S → HasDerivAt y (f s) s) (hf : ContinuousOn f (Icc 0 1)) :
    y 1 - y 0 = ∫ s in (0 : ℝ)..1, f s :=
  (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le y f zero_le_one S.countable_toSet hy
    (fun s hs => hd s hs.1 hs.2) (hf.intervalIntegrable_of_Icc zero_le_one)).symm

/-- The general computation behind MLS p. 363: along a trajectory of the second-order system on
`[0, 1]` with continuous inputs, if `σ̇ = u₁`, `τ̇ = u₂` with `σ, τ` zero at `0` and `1`, then
`q₁, q₂` return, `Δq₁₂ = ∫ q₁ u₂`, `Δq₁₂₁ = −∫ σ q₁ u₂` and `Δq₁₂₂ = −∫ τ q₁ u₂` with
`q₁ = q₁(0) + σ`. -/
private theorem secondOrder_core {u : ℝ → Fin 2 → ℝ} (hu : Continuous u) {x : ℝ → Fin 5 → ℝ}
    (hx : IsTrajectory secondOrderFields u 1 x) {σ τ : ℝ → ℝ} (hσ : ∀ t, HasDerivAt σ (u t 0) t)
    (hτ : ∀ t, HasDerivAt τ (u t 1) t) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 0) (hτ0 : τ 0 = 0)
    (hτ1 : τ 1 = 0) :
    x 1 0 = x 0 0 ∧ x 1 1 = x 0 1 ∧
      x 1 2 - x 0 2 = ∫ t in (0 : ℝ)..1, (x 0 0 + σ t) * u t 1 ∧
      x 1 3 - x 0 3 = -∫ t in (0 : ℝ)..1, σ t * (x 0 0 + σ t) * u t 1 ∧
      x 1 4 - x 0 4 = -∫ t in (0 : ℝ)..1, τ t * (x 0 0 + σ t) * u t 1 := by
  obtain ⟨hc, S, hS⟩ := hx
  have hu0 : Continuous fun t => u t 0 := (continuous_apply 0).comp hu
  have hu1 : Continuous fun t => u t 1 := (continuous_apply 1).comp hu
  have hcomp : ∀ i, ContinuousOn (fun t => x t i) (Icc 0 1) := fun i =>
    (continuous_apply i).comp_continuousOn hc
  have hd : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ S → ∀ i, HasDerivAt (fun t => x t i)
      (![u s 0, u s 1, x s 0 * u s 1, x s 2 * u s 0, x s 2 * u s 1] i) s := by
    intro s hs hsS i
    have h := hasDerivAt_pi.1 (hS s hs hsS) i
    rwa [secondOrder_driftFree] at h
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
  have hτc : Continuous τ := continuous_iff_continuousAt.2 fun t => (hτ t).continuousAt
  have hx0 : ∀ t ∈ Icc (0 : ℝ) 1, x t 0 = x 0 0 + σ t := by
    intro t ht
    have h1 := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => x s 0)
      (fun s => u s 0) ht.1 S.countable_toSet ((hcomp 0).mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => by simpa using hd s ⟨hs.1.1, lt_of_lt_of_le hs.1.2 ht.2⟩ hs.2 0)
      (hu0.intervalIntegrable 0 t)
    have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hσ s)
      (hu0.intervalIntegrable 0 t)
    linarith
  have hx1 : ∀ t ∈ Icc (0 : ℝ) 1, x t 1 = x 0 1 + τ t := by
    intro t ht
    have h1 := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => x s 1)
      (fun s => u s 1) ht.1 S.countable_toSet ((hcomp 1).mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => by simpa using hd s ⟨hs.1.1, lt_of_lt_of_le hs.1.2 ht.2⟩ hs.2 1)
      (hu1.intervalIntegrable 0 t)
    have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hτ s)
      (hu1.intervalIntegrable 0 t)
    linarith
  have hI : Icc (0 : ℝ) 1 = uIcc 0 1 := (uIcc_of_le zero_le_one).symm
  refine ⟨by simpa [hσ1] using hx0 1 ⟨zero_le_one, le_rfl⟩,
    by simpa [hτ1] using hx1 1 ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩
  · rw [sub_eq_integral (f := fun t => x t 0 * u t 1) (hcomp 2)
      (fun s hs hsS => by simpa using hd s hs hsS 2) ((hcomp 0).mul hu1.continuousOn)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [← hI] at ht
    rw [hx0 t ht]
  · have hF := sub_eq_integral (y := fun t => x t 3 - σ t * x t 2)
      (f := fun t => -(σ t * x t 0 * u t 1)) (S := S)
      ((hcomp 3).sub (hσc.continuousOn.mul (hcomp 2)))
      (fun s hs hsS => by
        have h := (hd s hs hsS 3).sub ((hσ s).mul (hd s hs hsS 2))
        convert h using 1
        simp
        ring)
      ((hσc.continuousOn.mul (hcomp 0)).mul hu1.continuousOn).neg
    simp only [hσ0, hσ1, zero_mul, sub_zero] at hF
    rw [hF, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [← hI] at ht
    rw [hx0 t ht]
  · have hG := sub_eq_integral (y := fun t => x t 4 - τ t * x t 2)
      (f := fun t => -(τ t * x t 0 * u t 1)) (S := S)
      ((hcomp 4).sub (hτc.continuousOn.mul (hcomp 2)))
      (fun s hs hsS => by
        have h := (hd s hs hsS 4).sub ((hτ s).mul (hd s hs hsS 2))
        convert h using 1
        simp
        ring)
      ((hτc.continuousOn.mul (hcomp 0)).mul hu1.continuousOn).neg
    simp only [hτ0, hτ1, zero_mul, sub_zero] at hG
    rw [hG, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [← hI] at ht
    rw [hx0 t ht]

/-- **MLS p. 363: the inputs `u₁ = a sin 2πt`, `u₂ = b cos 4πt`.** -/
def secondOrderInput (a b : ℝ) (t : ℝ) : Fin 2 → ℝ := ![a * sin (2 * π * t), b * cos (4 * π * t)]

/-- **MLS p. 363: the inputs `u₁ = b cos 4πt`, `u₂ = a sin 2πt`.** -/
def secondOrderInputSwap (a b : ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![b * cos (4 * π * t), a * sin (2 * π * t)]

/-- **MLS p. 363: steering `q₁₂₁`.** Every trajectory on `[0, 1]` with `u₁ = a sin 2πt`,
`u₂ = b cos 4πt`, from any initial state, ends at `q(1) = q(0) − (a²b/(16π²)) e₁₂₁`: the other
states return. -/
theorem IsTrajectory.secondOrder_steering {a b : ℝ} {x : ℝ → Fin 5 → ℝ}
    (hx : IsTrajectory secondOrderFields (secondOrderInput a b) 1 x) :
    x 1 = x 0 + ![0, 0, 0, -(a ^ 2 * b / (16 * π ^ 2)), 0] := by
  have hu : Continuous (secondOrderInput a b) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [secondOrderInput] <;> fun_prop
  have hπ : π ≠ 0 := pi_ne_zero
  have hσ : ∀ t, HasDerivAt (fun t => a / (2 * π) * (1 - cos (2 * π * t)))
      (secondOrderInput a b t 0) t := by
    intro t
    show HasDerivAt _ (a * sin (2 * π * t)) t
    have h := (((hasDerivAt_id t).const_mul (2 * π)).cos.const_sub 1).const_mul (a / (2 * π))
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hτ : ∀ t, HasDerivAt (fun t => b / (4 * π) * sin (4 * π * t))
      (secondOrderInput a b t 1) t := by
    intro t
    show HasDerivAt _ (b * cos (4 * π * t)) t
    have h := (((hasDerivAt_id t).const_mul (4 * π)).sin).const_mul (b / (4 * π))
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hs4 : b / (4 * π) * sin (4 * π * 1) = 0 := by
    rw [mul_one, show (4 : ℝ) * π = ((4 : ℕ) : ℝ) * π by norm_num, sin_nat_mul_pi, mul_zero]
  obtain ⟨h0, h1, h2, h3, h4⟩ := secondOrder_core hu hx hσ hτ (by simp) (by simp)
    (by simp) hs4
  simp only [secondOrderInput, Matrix.cons_val_one, Matrix.cons_val_zero] at h2 h3 h4
  have i2 : ∫ t in (0 : ℝ)..1, (x 0 0 + a / (2 * π) * (1 - cos (2 * π * t))) * (b * cos (4 * π * t))
      = 0 := by
    have e : ∀ t : ℝ, (x 0 0 + a / (2 * π) * (1 - cos (2 * π * t))) * (b * cos (4 * π * t)) =
        (x 0 0 * b) * cos (4 * π * t) +
          (a * b / (2 * π)) * ((1 - cos (2 * π * t)) * cos (4 * π * t)) := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_cos4, int_I12]
    ring
  have i3 : ∫ t in (0 : ℝ)..1, a / (2 * π) * (1 - cos (2 * π * t)) *
      (x 0 0 + a / (2 * π) * (1 - cos (2 * π * t))) * (b * cos (4 * π * t)) =
        a ^ 2 * b / (16 * π ^ 2) := by
    have e : ∀ t : ℝ, a / (2 * π) * (1 - cos (2 * π * t)) *
        (x 0 0 + a / (2 * π) * (1 - cos (2 * π * t))) * (b * cos (4 * π * t)) =
        (x 0 0 * a * b / (2 * π)) * ((1 - cos (2 * π * t)) * cos (4 * π * t)) +
          (a ^ 2 * b / (4 * π ^ 2)) * ((1 - cos (2 * π * t)) ^ 2 * cos (4 * π * t)) := fun t => by
      field_simp
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_I12, int_I22]
    field_simp
    ring
  have i4 : ∫ t in (0 : ℝ)..1, b / (4 * π) * sin (4 * π * t) *
      (x 0 0 + a / (2 * π) * (1 - cos (2 * π * t))) * (b * cos (4 * π * t)) = 0 := by
    have e : ∀ t : ℝ, b / (4 * π) * sin (4 * π * t) *
        (x 0 0 + a / (2 * π) * (1 - cos (2 * π * t))) * (b * cos (4 * π * t)) =
        (b ^ 2 * (x 0 0 + a / (2 * π)) / (4 * π)) * (sin (4 * π * t) * cos (4 * π * t)) -
          (a * b ^ 2 / (8 * π ^ 2)) *
            (sin (4 * π * t) * cos (4 * π * t) * cos (2 * π * t)) := fun t => by
      field_simp
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (ii (by fun_prop)) (ii (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_sin4_cos4,
      int_sin4_cos4_cos2]
    ring
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simp
    linarith
  · simp
    linarith
  · simp
    linarith

/-- **MLS p. 363: steering `q₁₂₂`.** Every trajectory on `[0, 1]` with `u₁ = b cos 4πt`,
`u₂ = a sin 2πt`, from any initial state, ends at `q(1) = q(0) + (a²b/(32π²)) e₁₂₂`: the other
states return. -/
theorem IsTrajectory.secondOrder_steering_swap {a b : ℝ} {x : ℝ → Fin 5 → ℝ}
    (hx : IsTrajectory secondOrderFields (secondOrderInputSwap a b) 1 x) :
    x 1 = x 0 + ![0, 0, 0, 0, a ^ 2 * b / (32 * π ^ 2)] := by
  have hu : Continuous (secondOrderInputSwap a b) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [secondOrderInputSwap] <;> fun_prop
  have hπ : π ≠ 0 := pi_ne_zero
  have hσ : ∀ t, HasDerivAt (fun t => b / (4 * π) * sin (4 * π * t))
      (secondOrderInputSwap a b t 0) t := by
    intro t
    show HasDerivAt _ (b * cos (4 * π * t)) t
    have h := (((hasDerivAt_id t).const_mul (4 * π)).sin).const_mul (b / (4 * π))
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hτ : ∀ t, HasDerivAt (fun t => a / (2 * π) * (1 - cos (2 * π * t)))
      (secondOrderInputSwap a b t 1) t := by
    intro t
    show HasDerivAt _ (a * sin (2 * π * t)) t
    have h := (((hasDerivAt_id t).const_mul (2 * π)).cos.const_sub 1).const_mul (a / (2 * π))
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
  have hs4 : b / (4 * π) * sin (4 * π * 1) = 0 := by
    rw [mul_one, show (4 : ℝ) * π = ((4 : ℕ) : ℝ) * π by norm_num, sin_nat_mul_pi, mul_zero]
  obtain ⟨h0, h1, h2, h3, h4⟩ := secondOrder_core hu hx hσ hτ (by simp) hs4 (by simp) (by simp)
  simp only [secondOrderInputSwap, Matrix.cons_val_one, Matrix.cons_val_zero] at h2 h3 h4
  have i2 : ∫ t in (0 : ℝ)..1, (x 0 0 + b / (4 * π) * sin (4 * π * t)) * (a * sin (2 * π * t))
      = 0 := by
    have e : ∀ t : ℝ, (x 0 0 + b / (4 * π) * sin (4 * π * t)) * (a * sin (2 * π * t)) =
        (x 0 0 * a) * sin (2 * π * t) +
          (a * b / (4 * π)) * (sin (4 * π * t) * sin (2 * π * t)) := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_sin2,
      int_sin4_sin2]
    ring
  have i3 : ∫ t in (0 : ℝ)..1, b / (4 * π) * sin (4 * π * t) *
      (x 0 0 + b / (4 * π) * sin (4 * π * t)) * (a * sin (2 * π * t)) = 0 := by
    have e : ∀ t : ℝ, b / (4 * π) * sin (4 * π * t) *
        (x 0 0 + b / (4 * π) * sin (4 * π * t)) * (a * sin (2 * π * t)) =
        (x 0 0 * a * b / (4 * π)) * (sin (4 * π * t) * sin (2 * π * t)) +
          (a * b ^ 2 / (16 * π ^ 2)) * (sin (4 * π * t) ^ 2 * sin (2 * π * t)) := fun t => by
      field_simp
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_sin4_sin2,
      int_sin4sq_sin2]
    ring
  have i4 : ∫ t in (0 : ℝ)..1, a / (2 * π) * (1 - cos (2 * π * t)) *
      (x 0 0 + b / (4 * π) * sin (4 * π * t)) * (a * sin (2 * π * t)) =
        -(a ^ 2 * b / (32 * π ^ 2)) := by
    have e : ∀ t : ℝ, a / (2 * π) * (1 - cos (2 * π * t)) *
        (x 0 0 + b / (4 * π) * sin (4 * π * t)) * (a * sin (2 * π * t)) =
        (a ^ 2 * x 0 0 / (2 * π)) * ((1 - cos (2 * π * t)) * sin (2 * π * t)) +
          (a ^ 2 * b / (8 * π ^ 2)) * (sin (4 * π * t) * sin (2 * π * t)) -
          (a ^ 2 * b / (8 * π ^ 2)) *
            (cos (2 * π * t) * sin (2 * π * t) * sin (4 * π * t)) := fun t => by
      field_simp
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub ((ii (by fun_prop)).add (ii (by fun_prop)))
        (ii (by fun_prop)),
      intervalIntegral.integral_add (ii (by fun_prop)) (ii (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, int_omc_sin2, int_sin4_sin2, int_cos2_sin2_sin4]
    field_simp
    ring
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simp
    linarith
  · simp
    linarith
  · simp
    linarith

/-- **MLS p. 363, existence:** for continuous inputs and every initial state the second-order system
has a solution defined for all times (iterated integrals); in particular trajectories on `[0, 1]`
exist for the inputs of p. 363. -/
theorem secondOrder_exists_solution {u : ℝ → Fin 2 → ℝ} (hu : Continuous u) (q₀ : Fin 5 → ℝ) :
    ∃ x : ℝ → Fin 5 → ℝ, x 0 = q₀ ∧
      ∀ t, HasDerivAt x (driftFree secondOrderFields (x t) (u t)) t := by
  have hu0 : Continuous fun t => u t 0 := (continuous_apply 0).comp hu
  have hu1 : Continuous fun t => u t 1 := (continuous_apply 1).comp hu
  have hprim : ∀ {f : ℝ → ℝ}, Continuous f → ∀ (c t : ℝ),
      HasDerivAt (fun t => c + ∫ s in (0 : ℝ)..t, f s) (f t) t := fun hf c t =>
    ((hf.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add c
  have hcont : ∀ {f : ℝ → ℝ}, Continuous f → ∀ c : ℝ,
      Continuous fun t => c + ∫ s in (0 : ℝ)..t, f s := fun hf c =>
    continuous_iff_continuousAt.2 fun t => (hprim hf c t).continuousAt
  set y0 : ℝ → ℝ := fun t => q₀ 0 + ∫ s in (0 : ℝ)..t, u s 0
  set y1 : ℝ → ℝ := fun t => q₀ 1 + ∫ s in (0 : ℝ)..t, u s 1
  set y2 : ℝ → ℝ := fun t => q₀ 2 + ∫ s in (0 : ℝ)..t, y0 s * u s 1
  set y3 : ℝ → ℝ := fun t => q₀ 3 + ∫ s in (0 : ℝ)..t, y2 s * u s 0
  set y4 : ℝ → ℝ := fun t => q₀ 4 + ∫ s in (0 : ℝ)..t, y2 s * u s 1
  have c0 : Continuous y0 := hcont hu0 _
  have c2 : Continuous y2 := hcont (c0.mul hu1) _
  refine ⟨fun t => ![y0 t, y1 t, y2 t, y3 t, y4 t], ?_, fun t => ?_⟩
  · ext i
    fin_cases i <;> simp [y0, y1, y2, y3, y4]
  · rw [secondOrder_driftFree, hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hprim hu0 _ t
    · exact hprim hu1 _ t
    · exact hprim (c0.mul hu1) _ t
    · exact hprim (c2.mul hu0) _ t
    · exact hprim (c2.mul hu1) _ t

end Nonholonomic
end RoboLean
