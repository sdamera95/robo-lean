import RoboLean.Nonholonomic.SteeringSecondOrder
import RoboLean.Nonholonomic.SteeringIntegrals

/-!
# Chapter 8, Exercise 4: the polynomial equations of the four-term sinusoids (MLS p. 392)

MLS Chapter 8, Exercise 4, printed p. 392: for the system `q̇₁ = u₁`, `q̇₂ = u₂`, `q̇₁₂ = q₁ u₂`,
`q̇₁₂₁ = q₁₂ u₁`, `q̇₁₂₂ = q₁₂ u₂` (the second-order model system of p. 363), "apply the inputs
`u₁ = a₁ sin 2πt + a₂ cos 2πt + a₃ sin 4πt + a₄ cos 4πt`,
`u₂ = b₁ sin 2πt + b₂ cos 2πt + b₃ sin 4πt + b₄ cos 4πt` to this system and integrate `q̇₁₂₁` and
`q̇₁₂₂` from `t = 0` to `t = 1` to obtain a system of polynomial equations in `(aᵢ, bᵢ)`."

The module proves two things.

* `IsTrajectory.secondOrder_endpoint_zeroMean`: for any continuous inputs with zero mean over
  `[0, 1]`, written through antiderivatives `σ, τ` vanishing at `0` and `1`, every trajectory
  satisfies `Δq₁ = Δq₂ = 0`, `Δq₁₂ = ∫ σ u₂`, `Δq₁₂₁ = −q₁(0) ∫ σ u₂ − ∫ σ² u₂` and
  `Δq₁₂₂ = ½ ∫ τ² u₁` (integration by parts against the endpoint values).
* `IsTrajectory.exercise4_polynomial`: for the four-term sinusoids the three integrals are the
  explicit polynomials `exercise4P12`, `exercise4P121`, `exercise4P122` in `(aᵢ, bᵢ)`, of degree
  two and three, so that the endpoint equations are polynomial in the coefficients with
  coefficients depending on `q₁(0)` only.

The exercise's second request, "propose a method for solving for the coefficients", asks for a
procedure and is not a theorem; it is not formalized here.

**Conventions.** The state is `Fin 5 → ℝ` with `q 0 = q₁`, `q 1 = q₂`, `q 2 = q₁₂`, `q 3 = q₁₂₁`,
`q 4 = q₁₂₂`, the fields are `secondOrderFields` of p. 363, trajectories are those of
`IsTrajectory` on `[0, 1]` from any initial state; the inputs are indexed `u t 0 = u₁`,
`u t 1 = u₂`; integrals are interval integrals over `[0, 1]`.
-/

noncomputable section

open Set Real intervalIntegral

namespace RoboLean
namespace Nonholonomic

/-- The fundamental theorem of calculus on `[0, 1]` away from finitely many times (supporting
lemma for MLS p. 392, Exercise 4). -/
private theorem sub_eq_integral' {y f : ℝ → ℝ} {S : Finset ℝ} (hy : ContinuousOn y (Icc 0 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, s ∉ S → HasDerivAt y (f s) s) (hf : ContinuousOn f (Icc 0 1)) :
    y 1 - y 0 = ∫ s in (0 : ℝ)..1, f s :=
  (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le y f zero_le_one S.countable_toSet hy
    (fun s hs => hd s hs.1 hs.2) (hf.intervalIntegrable_of_Icc zero_le_one)).symm

/-- **MLS Chapter 8, Exercise 4 (p. 392): the endpoint equations for zero-mean inputs.** Along a
trajectory on `[0, 1]` of the system of p. 363 with continuous inputs, if `σ̇ = u₁` and `τ̇ = u₂`
with `σ` and `τ` zero at `0` and `1` (the inputs have zero mean), then `q₁` and `q₂` return,
`Δq₁₂ = ∫₀¹ σ u₂`, `Δq₁₂₁ = −q₁(0) ∫₀¹ σ u₂ − ∫₀¹ σ² u₂` and `Δq₁₂₂ = ½ ∫₀¹ τ² u₁`. Convention:
the state order `(q₁, q₂, q₁₂, q₁₂₁, q₁₂₂)` and the trajectories of `IsTrajectory`. -/
theorem IsTrajectory.secondOrder_endpoint_zeroMean {u : ℝ → Fin 2 → ℝ} (hu : Continuous u)
    {x : ℝ → Fin 5 → ℝ} (hx : IsTrajectory secondOrderFields u 1 x) {σ τ : ℝ → ℝ}
    (hσ : ∀ t, HasDerivAt σ (u t 0) t) (hτ : ∀ t, HasDerivAt τ (u t 1) t) (hσ0 : σ 0 = 0)
    (hσ1 : σ 1 = 0) (hτ0 : τ 0 = 0) (hτ1 : τ 1 = 0) :
    x 1 0 = x 0 0 ∧ x 1 1 = x 0 1 ∧
      x 1 2 - x 0 2 = ∫ t in (0 : ℝ)..1, σ t * u t 1 ∧
      x 1 3 - x 0 3 = -(x 0 0 * ∫ t in (0 : ℝ)..1, σ t * u t 1) -
        ∫ t in (0 : ℝ)..1, σ t ^ 2 * u t 1 ∧
      x 1 4 - x 0 4 = (1 / 2) * ∫ t in (0 : ℝ)..1, τ t ^ 2 * u t 0 := by
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
  have hio : ∀ s ∈ Ioo (0 : ℝ) 1, s ∈ Icc (0 : ℝ) 1 := fun s hs => Ioo_subset_Icc_self hs
  have i1 : IntervalIntegrable (fun t => σ t * u t 1) MeasureTheory.volume 0 1 :=
    (hσc.mul hu1).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun t => σ t ^ 2 * u t 1) MeasureTheory.volume 0 1 :=
    ((hσc.pow 2).mul hu1).intervalIntegrable 0 1
  refine ⟨by simpa [hσ1] using hx0 1 ⟨zero_le_one, le_rfl⟩,
    by simpa [hτ1] using hx1 1 ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩
  · have h := sub_eq_integral' (y := fun t => x t 2 - x 0 0 * τ t) (f := fun t => σ t * u t 1)
      (S := S) ((hcomp 2).sub (continuousOn_const.mul hτc.continuousOn))
      (fun s hs hsS => by
        have h := (hd s hs hsS 2).sub ((hτ s).const_mul (x 0 0))
        convert h using 1
        simp [hx0 s (hio s hs)]
        ring)
      (hσc.mul hu1).continuousOn
    simp only [hτ0, hτ1, mul_zero, sub_zero] at h
    exact h
  · have h := sub_eq_integral' (y := fun t => x t 3 - σ t * x t 2)
      (f := fun t => -(x 0 0 * (σ t * u t 1)) - σ t ^ 2 * u t 1) (S := S)
      ((hcomp 3).sub (hσc.continuousOn.mul (hcomp 2)))
      (fun s hs hsS => by
        have h := (hd s hs hsS 3).sub ((hσ s).mul (hd s hs hsS 2))
        convert h using 1
        simp [hx0 s (hio s hs)]
        ring)
      ((continuousOn_const.mul (hσc.mul hu1).continuousOn).neg.sub
        ((hσc.pow 2).mul hu1).continuousOn)
    simp only [hσ0, hσ1, zero_mul, sub_zero] at h
    have i3 : IntervalIntegrable (fun t => -(x 0 0 * (σ t * u t 1))) MeasureTheory.volume 0 1 :=
      (i1.const_mul _).neg
    rw [h, intervalIntegral.integral_sub i3 i2, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
  · have h := sub_eq_integral'
      (y := fun t => x t 4 - τ t * x t 2 + (1 / 2) * x 0 0 * τ t ^ 2 + (1 / 2) * σ t * τ t ^ 2)
      (f := fun t => (1 / 2) * (τ t ^ 2 * u t 0)) (S := S)
      ((((hcomp 4).sub (hτc.continuousOn.mul (hcomp 2))).add
        (continuousOn_const.mul (hτc.pow 2).continuousOn)).add
        ((continuousOn_const.mul hσc.continuousOn).mul (hτc.pow 2).continuousOn))
      (fun s hs hsS => by
        have h := (((hd s hs hsS 4).sub ((hτ s).mul (hd s hs hsS 2))).add
          (((hτ s).pow 2).const_mul ((1 / 2) * x 0 0))).add
          (((hσ s).const_mul (1 / 2)).mul ((hτ s).pow 2))
        convert h using 1
        simp [hx0 s (hio s hs)]
        ring)
      (continuousOn_const.mul ((hτc.pow 2).mul hu0).continuousOn)
    simp only [hσ0, hσ1, hτ0, hτ1, zero_mul, mul_zero, sub_zero, add_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    rw [h, intervalIntegral.integral_const_mul]

/-- **MLS Chapter 8, Exercise 4 (p. 392): a four-term sinusoid**
`a₁ sin 2πt + a₂ cos 2πt + a₃ sin 4πt + a₄ cos 4πt`, with the coefficients indexed from `0`
(`a 0 = a₁`, …, `a 3 = a₄`). -/
def fourTerm (a : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  a 0 * sin (2 * π * t) + a 1 * cos (2 * π * t) + a 2 * sin (4 * π * t) + a 3 * cos (4 * π * t)

/-- **MLS Chapter 8, Exercise 4 (p. 392): the inputs `(u₁, u₂)`** with `u₁` the four-term sinusoid
of coefficients `a` and `u₂` that of coefficients `b`. -/
def exercise4Input (a b : Fin 4 → ℝ) (t : ℝ) : Fin 2 → ℝ := ![fourTerm a t, fourTerm b t]

/-- **MLS Chapter 8, Exercise 4 (p. 392):** `2π` times the primitive of a four-term sinusoid
vanishing at `t = 0` (a supporting definition free of `π`). -/
def fourTermP (a : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  a 0 * (1 - cos (2 * π * t)) + a 1 * sin (2 * π * t) + a 2 / 2 * (1 - cos (4 * π * t)) +
    a 3 / 2 * sin (4 * π * t)

/-- **MLS Chapter 8, Exercise 4 (p. 392): the primitive `∫₀ᵗ` of a four-term sinusoid**, which
vanishes at `t = 0` and at `t = 1` (the sinusoids have zero mean over a period). -/
def fourTermPrimitive (a : Fin 4 → ℝ) (t : ℝ) : ℝ := fourTermP a t / (2 * π)

/-- **MLS Chapter 8, Exercise 4 (p. 392): the quadratic coefficient**
`∫₀¹ (∫₀ᵗ u₁) u₂ dt = −(2a₁b₂ − 2a₂b₁ + a₃b₄ − a₄b₃)/(8π)` (book indices), which is `Δq₁₂`. -/
def exercise4I1 (a b : Fin 4 → ℝ) : ℝ :=
  -(2 * a 0 * b 1 - 2 * a 1 * b 0 + a 2 * b 3 - a 3 * b 2) / (8 * π)

/-- **MLS Chapter 8, Exercise 4 (p. 392): the cubic integral** `∫₀¹ (∫₀ᵗ u₁)² u₂ dt`, a cubic
polynomial in `(aᵢ, bᵢ)` over `16π²`; `Δq₁₂₁ = −q₁(0) Δq₁₂ − exercise4I2 a b`. -/
def exercise4I2 (a b : Fin 4 → ℝ) : ℝ :=
  (-4 * a 0 ^ 2 * b 1 + a 0 ^ 2 * b 3 + 4 * a 0 * a 1 * b 0 - 2 * a 0 * a 1 * b 2 - a 0 * a 2 * b 1 -
    2 * a 0 * a 2 * b 3 - a 0 * a 3 * b 0 + 2 * a 0 * a 3 * b 2 - a 1 ^ 2 * b 3 + 3 * a 1 * a 2 * b 0 +
    a 1 * a 3 * b 1 - a 2 ^ 2 * b 3 + a 2 * a 3 * b 2) / (16 * π ^ 2)

/-- **MLS Chapter 8, Exercise 4 (p. 392): the cubic integral** `½ ∫₀¹ (∫₀ᵗ u₂)² u₁ dt`, a cubic
polynomial in `(aᵢ, bᵢ)` over `32π²`, which is `Δq₁₂₂`. -/
def exercise4I3 (a b : Fin 4 → ℝ) : ℝ :=
  (4 * a 0 * b 0 * b 1 - a 0 * b 0 * b 3 + 3 * a 0 * b 1 * b 2 - 4 * a 1 * b 0 ^ 2 - a 1 * b 0 * b 2 +
    a 1 * b 1 * b 3 - 2 * a 2 * b 0 * b 1 + 2 * a 2 * b 0 * b 3 + a 2 * b 2 * b 3 + a 3 * b 0 ^ 2 -
    2 * a 3 * b 0 * b 2 - a 3 * b 1 ^ 2 - a 3 * b 2 ^ 2) / (32 * π ^ 2)

/-- The multiple-angle expansions up to `6θ` in de Moivre form, `θ = 2πt` (supporting lemma for
MLS p. 392, Exercise 4). -/
private theorem trig_expand (t : ℝ) :
    cos (2 * π * (0 + 1) * t) = cos (2 * π * t) ∧ sin (2 * π * (0 + 1) * t) = sin (2 * π * t) ∧
    cos (2 * π * (1 + 1) * t) = cos (2 * π * t) ^ 2 - sin (2 * π * t) ^ 2 ∧
    sin (2 * π * (1 + 1) * t) = 2 * sin (2 * π * t) * cos (2 * π * t) ∧
    cos (2 * π * (2 + 1) * t) = cos (2 * π * t) ^ 3 - 3 * cos (2 * π * t) * sin (2 * π * t) ^ 2 ∧
    sin (2 * π * (2 + 1) * t) = 3 * cos (2 * π * t) ^ 2 * sin (2 * π * t) - sin (2 * π * t) ^ 3 ∧
    cos (2 * π * (3 + 1) * t) = cos (2 * π * t) ^ 4 -
      6 * cos (2 * π * t) ^ 2 * sin (2 * π * t) ^ 2 + sin (2 * π * t) ^ 4 ∧
    sin (2 * π * (3 + 1) * t) = 4 * cos (2 * π * t) ^ 3 * sin (2 * π * t) -
      4 * cos (2 * π * t) * sin (2 * π * t) ^ 3 ∧
    cos (2 * π * (4 + 1) * t) = cos (2 * π * t) ^ 5 -
      10 * cos (2 * π * t) ^ 3 * sin (2 * π * t) ^ 2 + 5 * cos (2 * π * t) * sin (2 * π * t) ^ 4 ∧
    sin (2 * π * (4 + 1) * t) = 5 * cos (2 * π * t) ^ 4 * sin (2 * π * t) -
      10 * cos (2 * π * t) ^ 2 * sin (2 * π * t) ^ 3 + sin (2 * π * t) ^ 5 ∧
    cos (2 * π * (5 + 1) * t) = cos (2 * π * t) ^ 6 -
      15 * cos (2 * π * t) ^ 4 * sin (2 * π * t) ^ 2 +
      15 * cos (2 * π * t) ^ 2 * sin (2 * π * t) ^ 4 - sin (2 * π * t) ^ 6 ∧
    sin (2 * π * (5 + 1) * t) = 6 * cos (2 * π * t) ^ 5 * sin (2 * π * t) -
      20 * cos (2 * π * t) ^ 3 * sin (2 * π * t) ^ 3 + 6 * cos (2 * π * t) * sin (2 * π * t) ^ 5 ∧
    sin (4 * π * t) = 2 * sin (2 * π * t) * cos (2 * π * t) ∧
    cos (4 * π * t) = cos (2 * π * t) ^ 2 - sin (2 * π * t) ^ 2 := by
  have step : ∀ n : ℝ, cos (2 * π * (n + 1) * t) =
      cos (2 * π * n * t) * cos (2 * π * t) - sin (2 * π * n * t) * sin (2 * π * t) ∧
      sin (2 * π * (n + 1) * t) =
      sin (2 * π * n * t) * cos (2 * π * t) + cos (2 * π * n * t) * sin (2 * π * t) := by
    intro n
    rw [show 2 * π * (n + 1) * t = 2 * π * n * t + 2 * π * t by ring, cos_add, sin_add]
    exact ⟨rfl, by ring⟩
  obtain ⟨c1, s1⟩ := step 0
  obtain ⟨c2, s2⟩ := step 1
  obtain ⟨c3, s3⟩ := step 2
  obtain ⟨c4, s4⟩ := step 3
  obtain ⟨c5, s5⟩ := step 4
  obtain ⟨c6, s6⟩ := step 5
  have e1 : (2 * π * 1 * t) = 2 * π * (0 + 1) * t := by ring
  have e2 : (2 * π * 2 * t) = 2 * π * (1 + 1) * t := by ring
  have e3 : (2 * π * 3 * t) = 2 * π * (2 + 1) * t := by ring
  have e4 : (2 * π * 4 * t) = 2 * π * (3 + 1) * t := by ring
  have e5 : (2 * π * 5 * t) = 2 * π * (4 + 1) * t := by ring
  simp only [mul_zero, zero_mul, cos_zero, sin_zero, one_mul, zero_add, sub_zero] at c1 s1
  have c1' : cos (2 * π * (0 + 1) * t) = cos (2 * π * t) := by rw [zero_add, mul_one]
  have s1' : sin (2 * π * (0 + 1) * t) = sin (2 * π * t) := by rw [zero_add, mul_one]
  rw [e1, c1', s1'] at c2 s2
  rw [e2, c2, s2] at c3 s3
  rw [e3, c3, s3] at c4 s4
  rw [e4, c4, s4] at c5 s5
  rw [e5, c5, s5] at c6 s6
  have h4 : 4 * π * t = 2 * π * (1 + 1) * t := by ring
  refine ⟨c1', s1', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c2]; ring
  · rw [s2]; ring
  · rw [c3]; ring
  · rw [s3]; ring
  · rw [c4]; ring
  · rw [s4]; ring
  · rw [c5]; ring
  · rw [s5]; ring
  · rw [c6]; ring
  · rw [s6]; ring
  · rw [h4, s2]; ring
  · rw [h4, c2]; ring

/-- A trigonometric polynomial of period one integrates over `[0, 1]` to its constant term
(supporting lemma for MLS p. 392, Exercise 4). -/
private theorem integral_trigPoly (c0 : ℝ) (al be : List ℝ) (N : ℕ) :
    ∫ t in (0 : ℝ)..1, (c0 + ∑ k ∈ Finset.range N,
      (al.getD k 0 * cos (2 * π * ((k + 1 : ℕ) : ℝ) * t) +
        be.getD k 0 * sin (2 * π * ((k + 1 : ℕ) : ℝ) * t))) = c0 := by
  have hc : ∀ k : ℕ, Continuous fun t : ℝ => al.getD k 0 * cos (2 * π * ((k + 1 : ℕ) : ℝ) * t) +
      be.getD k 0 * sin (2 * π * ((k + 1 : ℕ) : ℝ) * t) := fun k => by fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_finsetSum _ fun k _ => hc k).intervalIntegrable 0 1),
    intervalIntegral.integral_finsetSum fun k _ => (hc k).intervalIntegrable 0 1]
  rw [Finset.sum_eq_zero]
  · simp
  intro k _
  have h1 : IntervalIntegrable (fun t : ℝ => al.getD k 0 * cos (2 * π * ((k + 1 : ℕ) : ℝ) * t))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h2 : IntervalIntegrable (fun t : ℝ => be.getD k 0 * sin (2 * π * ((k + 1 : ℕ) : ℝ) * t))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_cos_two_pi_mul (by omega), integral_sin_two_pi_mul]
  ring

/-- The Fourier expansion of the integrand behind `exercise4I1` (supporting lemma for MLS p. 392,
Exercise 4). -/
private theorem exercise4I1_fourier (a b : Fin 4 → ℝ) (t : ℝ) :
    fourTermP a t * fourTerm b t =
      (-a 0*b 1/2 + a 1*b 0/2 - a 2*b 3/4 + a 3*b 2/4) + ∑ k ∈ Finset.range 6,
        ([(a 0*b 1 - a 0*b 3/2 + a 1*b 2/2 + a 2*b 1/4 + a 3*b 0/4), (-a 0*b 1/2 + a 0*b 3 - a 1*b 0/2 + a 2*b 3/2), (-a 0*b 3/2 - a 1*b 2/2 - a 2*b 1/4 - a 3*b 0/4), (-a 2*b 3/4 - a 3*b 2/4), (0), (0)].getD k 0 * cos (2 * π * ((k + 1 : ℕ) : ℝ) * t) +
          [(a 0*b 0 - a 0*b 2/2 - a 1*b 3/2 + 3*a 2*b 0/4 + a 3*b 1/4), (-a 0*b 0/2 + a 0*b 2 + a 1*b 1/2 + a 2*b 2/2), (-a 0*b 2/2 + a 1*b 3/2 - a 2*b 0/4 + a 3*b 1/4), (-a 2*b 2/4 + a 3*b 3/4), (0), (0)].getD k 0 * sin (2 * π * ((k + 1 : ℕ) : ℝ) * t)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := trig_expand t
  have hp := sin_sq_add_cos_sq (2 * π * t)
  simp only [fourTerm, fourTermP, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
    List.getD_cons_succ, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14]
  generalize sin (2 * π * t) = s at hp ⊢
  generalize cos (2 * π * t) = c at hp ⊢
  linear_combination (-a 0*b 1/2 - a 0*b 2*s/2 - a 0*b 3*c/2 + a 1*b 0/2 + a 1*b 2*c/2 - a 1*b 3*s/2 + a 2*b 0*s/4 - a 2*b 1*c/4 - a 2*b 3*c^2/4 - a 2*b 3*s^2/4 - a 2*b 3/4 + a 3*b 0*c/4 + a 3*b 1*s/4 + a 3*b 2*c^2/4 + a 3*b 2*s^2/4 + a 3*b 2/4) * hp

/-- The Fourier expansion of the integrand behind `exercise4I2` (supporting lemma for MLS p. 392,
Exercise 4). -/
private theorem exercise4I2_fourier (a b : Fin 4 → ℝ) (t : ℝ) :
    fourTermP a t ^ 2 * fourTerm b t =
      (-a 0^2*b 1 + a 0^2*b 3/4 + a 0*a 1*b 0 - a 0*a 1*b 2/2 - a 0*a 2*b 1/4 - a 0*a 2*b 3/2 - a 0*a 3*b 0/4 + a 0*a 3*b 2/2 - a 1^2*b 3/4 + 3*a 1*a 2*b 0/4 + a 1*a 3*b 1/4 - a 2^2*b 3/4 + a 2*a 3*b 2/4) + ∑ k ∈ Finset.range 6,
        ([(7*a 0^2*b 1/4 - a 0^2*b 3 - a 0*a 1*b 0/2 + a 0*a 1*b 2 + a 0*a 2*b 1/2 + a 0*a 3*b 0/2 - a 0*a 3*b 2/2 + a 1^2*b 1/4 + a 1*a 2*b 2/2 + a 2^2*b 1/8 + a 2*a 3*b 0/4 + a 3^2*b 1/8), (-a 0^2*b 1 + 3*a 0^2*b 3/2 - a 0*a 1*b 0 + a 0*a 2*b 3 + a 1^2*b 3/2 - a 1*a 2*b 0 + 7*a 2^2*b 3/16 - a 2*a 3*b 2/8 + a 3^2*b 3/16), (a 0^2*b 1/4 - a 0^2*b 3 + a 0*a 1*b 0/2 - a 0*a 1*b 2 - a 0*a 2*b 1/2 - a 0*a 2*b 3/4 - a 0*a 3*b 0/2 + a 0*a 3*b 2/4 - a 1^2*b 1/4 - 3*a 1*a 2*b 2/4 + a 1*a 3*b 3/4 - 3*a 2^2*b 1/16 - 3*a 2*a 3*b 0/8 - a 3^2*b 1/16), (a 0^2*b 3/4 + a 0*a 1*b 2/2 + a 0*a 2*b 1/4 - a 0*a 2*b 3/2 + a 0*a 3*b 0/4 - a 0*a 3*b 2/2 - a 1^2*b 3/4 + a 1*a 2*b 0/4 - a 1*a 3*b 1/4 - a 2^2*b 3/4 - a 2*a 3*b 2/4), (a 0*a 2*b 3/4 + a 0*a 3*b 2/4 + a 1*a 2*b 2/4 - a 1*a 3*b 3/4 + a 2^2*b 1/16 + a 2*a 3*b 0/8 - a 3^2*b 1/16), (a 2^2*b 3/16 + a 2*a 3*b 2/8 - a 3^2*b 3/16)].getD k 0 * cos (2 * π * ((k + 1 : ℕ) : ℝ) * t) +
          [(5*a 0^2*b 0/4 - a 0^2*b 2 - a 0*a 1*b 1/2 - a 0*a 1*b 3 + 3*a 0*a 2*b 0/2 - a 0*a 2*b 2/2 + a 0*a 3*b 1/2 + 3*a 1^2*b 0/4 - a 1*a 2*b 3 + a 1*a 3*b 2/2 + 5*a 2^2*b 0/8 + a 2*a 3*b 1/4 + a 3^2*b 0/8), (-a 0^2*b 0 + 3*a 0^2*b 2/2 + a 0*a 1*b 1 - a 0*a 2*b 0/2 + a 0*a 2*b 2 - a 0*a 3*b 1/2 + a 1^2*b 2/2 + a 1*a 2*b 1/2 + a 1*a 3*b 0/2 + 5*a 2^2*b 2/16 - a 2*a 3*b 3/8 + 3*a 3^2*b 2/16), (a 0^2*b 0/4 - a 0^2*b 2 - a 0*a 1*b 1/2 + a 0*a 1*b 3 - a 0*a 2*b 0/2 - a 0*a 2*b 2/4 + a 0*a 3*b 1/2 - a 0*a 3*b 3/4 - a 1^2*b 0/4 + 3*a 1*a 2*b 3/4 + a 1*a 3*b 2/4 - 5*a 2^2*b 0/16 + a 2*a 3*b 1/8 + a 3^2*b 0/16), (a 0^2*b 2/4 - a 0*a 1*b 3/2 + a 0*a 2*b 0/4 - a 0*a 2*b 2/2 - a 0*a 3*b 1/4 + a 0*a 3*b 3/2 - a 1^2*b 2/4 - a 1*a 2*b 1/4 - a 1*a 3*b 0/4 - a 2^2*b 2/4 + a 2*a 3*b 3/4), (a 0*a 2*b 2/4 - a 0*a 3*b 3/4 - a 1*a 2*b 3/4 - a 1*a 3*b 2/4 + a 2^2*b 0/16 - a 2*a 3*b 1/8 - a 3^2*b 0/16), (a 2^2*b 2/16 - a 2*a 3*b 3/8 - a 3^2*b 2/16)].getD k 0 * sin (2 * π * ((k + 1 : ℕ) : ℝ) * t)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := trig_expand t
  have hp := sin_sq_add_cos_sq (2 * π * t)
  simp only [fourTerm, fourTermP, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
    List.getD_cons_succ, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14]
  generalize sin (2 * π * t) = s at hp ⊢
  generalize cos (2 * π * t) = c at hp ⊢
  linear_combination (a 0^2*b 0*s/4 + 3*a 0^2*b 1*c/4 - a 0^2*b 1 + a 0^2*b 2*c*s - a 0^2*b 2*s + 3*a 0^2*b 3*c^2/4 - a 0^2*b 3*c - a 0^2*b 3*s^2/4 + a 0^2*b 3/4 - a 0*a 1*b 0*c/2 + a 0*a 1*b 0 - a 0*a 1*b 1*s/2 - a 0*a 1*b 2*c^2/2 + a 0*a 1*b 2*c - a 0*a 1*b 2*s^2/2 - a 0*a 1*b 2/2 - a 0*a 1*b 3*s + a 0*a 2*b 0*s/2 + 3*a 0*a 2*b 1*c^2/4 - a 0*a 2*b 1*c/2 - a 0*a 2*b 1*s^2/4 - a 0*a 2*b 1/4 + 3*a 0*a 2*b 2*c^2*s/4 - a 0*a 2*b 2*s^3/4 - a 0*a 2*b 2*s/2 + 3*a 0*a 2*b 3*c^3/4 - a 0*a 2*b 3*c^2/2 - a 0*a 2*b 3*c*s^2/4 - a 0*a 2*b 3*s^2/2 - a 0*a 2*b 3/2 - a 0*a 3*b 0*c^2/4 + a 0*a 3*b 0*c/2 - a 0*a 3*b 0*s^2/4 - a 0*a 3*b 0/4 - a 0*a 3*b 1*c*s + a 0*a 3*b 1*s/2 - a 0*a 3*b 2*c^3/4 + a 0*a 3*b 2*c^2/2 - 5*a 0*a 3*b 2*c*s^2/4 - a 0*a 3*b 2*c/2 + a 0*a 3*b 2*s^2/2 + a 0*a 3*b 2/2 - 3*a 0*a 3*b 3*c^2*s/4 + a 0*a 3*b 3*s^3/4 + 3*a 1^2*b 0*s/4 + a 1^2*b 1*c/4 + a 1^2*b 2*c*s + a 1^2*b 3*c^2/4 - 3*a 1^2*b 3*s^2/4 - a 1^2*b 3/4 - a 1*a 2*b 0*c^2/4 + 3*a 1*a 2*b 0*s^2/4 + 3*a 1*a 2*b 0/4 - a 1*a 2*b 2*c^3/4 + 3*a 1*a 2*b 2*c*s^2/4 + a 1*a 2*b 2*c/2 + a 1*a 2*b 3*c^2*s/4 - 3*a 1*a 2*b 3*s^3/4 - a 1*a 2*b 3*s + a 1*a 3*b 0*c*s + a 1*a 3*b 1*c^2/4 + a 1*a 3*b 1*s^2/4 + a 1*a 3*b 1/4 + 5*a 1*a 3*b 2*c^2*s/4 + a 1*a 3*b 2*s^3/4 + a 1*a 3*b 2*s/2 + a 1*a 3*b 3*c^3/4 - 3*a 1*a 3*b 3*c*s^2/4 - a 2^2*b 0*c^2*s/16 + 3*a 2^2*b 0*s^3/16 + 3*a 2^2*b 0*s/8 + 3*a 2^2*b 1*c^3/16 - a 2^2*b 1*c*s^2/16 - a 2^2*b 1*c/8 + a 2^2*b 2*c^3*s/8 + a 2^2*b 2*c*s^3/8 + a 2^2*b 2*c*s/8 + 3*a 2^2*b 3*c^4/16 - a 2^2*b 3*c^2/16 - 3*a 2^2*b 3*s^4/16 - 7*a 2^2*b 3*s^2/16 - a 2^2*b 3/4 - a 2*a 3*b 0*c^3/8 + 3*a 2*a 3*b 0*c*s^2/8 + a 2*a 3*b 0*c/4 - 3*a 2*a 3*b 1*c^2*s/8 + a 2*a 3*b 1*s^3/8 + a 2*a 3*b 1*s/4 - a 2*a 3*b 2*c^4/8 + a 2*a 3*b 2*c^2/8 + a 2*a 3*b 2*s^4/8 + 3*a 2*a 3*b 2*s^2/8 + a 2*a 3*b 2/4 - a 2*a 3*b 3*c^3*s/4 - a 2*a 3*b 3*c*s^3/4 - a 2*a 3*b 3*c*s/4 + 5*a 3^2*b 0*c^2*s/16 + a 3^2*b 0*s^3/16 + a 3^2*b 0*s/8 + a 3^2*b 1*c^3/16 + 5*a 3^2*b 1*c*s^2/16 + a 3^2*b 1*c/8 + 3*a 3^2*b 2*c^3*s/8 + 3*a 3^2*b 2*c*s^3/8 + 3*a 3^2*b 2*c*s/8 + a 3^2*b 3*c^4/16 + a 3^2*b 3*c^2/16 - a 3^2*b 3*s^4/16 - a 3^2*b 3*s^2/16) * hp

/-- The Fourier expansion of the integrand behind `exercise4I3` (supporting lemma for MLS p. 392,
Exercise 4). -/
private theorem exercise4I3_fourier (a b : Fin 4 → ℝ) (t : ℝ) :
    fourTermP b t ^ 2 * fourTerm a t =
      (a 0*b 0*b 1 - a 0*b 0*b 3/4 + 3*a 0*b 1*b 2/4 - a 1*b 0^2 - a 1*b 0*b 2/4 + a 1*b 1*b 3/4 - a 2*b 0*b 1/2 + a 2*b 0*b 3/2 + a 2*b 2*b 3/4 + a 3*b 0^2/4 - a 3*b 0*b 2/2 - a 3*b 1^2/4 - a 3*b 2^2/4) + ∑ k ∈ Finset.range 6,
        ([(-a 0*b 0*b 1/2 + a 0*b 0*b 3/2 + a 0*b 2*b 3/4 + 7*a 1*b 0^2/4 + a 1*b 0*b 2/2 + a 1*b 1^2/4 + a 1*b 2^2/8 + a 1*b 3^2/8 + a 2*b 0*b 1 - a 2*b 0*b 3/2 + a 2*b 1*b 2/2 - a 3*b 0^2), (-a 0*b 0*b 1 - a 0*b 1*b 2 - a 1*b 0^2 - a 2*b 2*b 3/8 + 3*a 3*b 0^2/2 + a 3*b 0*b 2 + a 3*b 1^2/2 + 7*a 3*b 2^2/16 + a 3*b 3^2/16), (a 0*b 0*b 1/2 - a 0*b 0*b 3/2 - 3*a 0*b 2*b 3/8 + a 1*b 0^2/4 - a 1*b 0*b 2/2 - a 1*b 1^2/4 - 3*a 1*b 2^2/16 - a 1*b 3^2/16 - a 2*b 0*b 1 + a 2*b 0*b 3/4 - 3*a 2*b 1*b 2/4 - a 3*b 0^2 - a 3*b 0*b 2/4 + a 3*b 1*b 3/4), (a 0*b 0*b 3/4 + a 0*b 1*b 2/4 + a 1*b 0*b 2/4 - a 1*b 1*b 3/4 + a 2*b 0*b 1/2 - a 2*b 0*b 3/2 - a 2*b 2*b 3/4 + a 3*b 0^2/4 - a 3*b 0*b 2/2 - a 3*b 1^2/4 - a 3*b 2^2/4), (a 0*b 2*b 3/8 + a 1*b 2^2/16 - a 1*b 3^2/16 + a 2*b 0*b 3/4 + a 2*b 1*b 2/4 + a 3*b 0*b 2/4 - a 3*b 1*b 3/4), (a 2*b 2*b 3/8 + a 3*b 2^2/16 - a 3*b 3^2/16)].getD k 0 * cos (2 * π * ((k + 1 : ℕ) : ℝ) * t) +
          [(5*a 0*b 0^2/4 + 3*a 0*b 0*b 2/2 + 3*a 0*b 1^2/4 + 5*a 0*b 2^2/8 + a 0*b 3^2/8 - a 1*b 0*b 1/2 + a 1*b 0*b 3/2 + a 1*b 2*b 3/4 - a 2*b 0^2 - a 2*b 0*b 2/2 + a 2*b 1*b 3/2 - a 3*b 0*b 1 - a 3*b 1*b 2), (-a 0*b 0^2 - a 0*b 0*b 2/2 + a 0*b 1*b 3/2 + a 1*b 0*b 1 - a 1*b 0*b 3/2 + a 1*b 1*b 2/2 + 3*a 2*b 0^2/2 + a 2*b 0*b 2 + a 2*b 1^2/2 + 5*a 2*b 2^2/16 + 3*a 2*b 3^2/16 - a 3*b 2*b 3/8), (a 0*b 0^2/4 - a 0*b 0*b 2/2 - a 0*b 1^2/4 - 5*a 0*b 2^2/16 + a 0*b 3^2/16 - a 1*b 0*b 1/2 + a 1*b 0*b 3/2 + a 1*b 2*b 3/8 - a 2*b 0^2 - a 2*b 0*b 2/4 + a 2*b 1*b 3/4 + a 3*b 0*b 1 - a 3*b 0*b 3/4 + 3*a 3*b 1*b 2/4), (a 0*b 0*b 2/4 - a 0*b 1*b 3/4 - a 1*b 0*b 3/4 - a 1*b 1*b 2/4 + a 2*b 0^2/4 - a 2*b 0*b 2/2 - a 2*b 1^2/4 - a 2*b 2^2/4 - a 3*b 0*b 1/2 + a 3*b 0*b 3/2 + a 3*b 2*b 3/4), (a 0*b 2^2/16 - a 0*b 3^2/16 - a 1*b 2*b 3/8 + a 2*b 0*b 2/4 - a 2*b 1*b 3/4 - a 3*b 0*b 3/4 - a 3*b 1*b 2/4), (a 2*b 2^2/16 - a 2*b 3^2/16 - a 3*b 2*b 3/8)].getD k 0 * sin (2 * π * ((k + 1 : ℕ) : ℝ) * t)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := trig_expand t
  have hp := sin_sq_add_cos_sq (2 * π * t)
  simp only [fourTerm, fourTermP, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
    List.getD_cons_succ, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14]
  generalize sin (2 * π * t) = s at hp ⊢
  generalize cos (2 * π * t) = c at hp ⊢
  linear_combination (a 0*b 0^2*s/4 - a 0*b 0*b 1*c/2 + a 0*b 0*b 1 + a 0*b 0*b 2*s/2 - a 0*b 0*b 3*c^2/4 + a 0*b 0*b 3*c/2 - a 0*b 0*b 3*s^2/4 - a 0*b 0*b 3/4 + 3*a 0*b 1^2*s/4 - a 0*b 1*b 2*c^2/4 + 3*a 0*b 1*b 2*s^2/4 + 3*a 0*b 1*b 2/4 + a 0*b 1*b 3*c*s - a 0*b 2^2*c^2*s/16 + 3*a 0*b 2^2*s^3/16 + 3*a 0*b 2^2*s/8 - a 0*b 2*b 3*c^3/8 + 3*a 0*b 2*b 3*c*s^2/8 + a 0*b 2*b 3*c/4 + 5*a 0*b 3^2*c^2*s/16 + a 0*b 3^2*s^3/16 + a 0*b 3^2*s/8 + 3*a 1*b 0^2*c/4 - a 1*b 0^2 - a 1*b 0*b 1*s/2 + 3*a 1*b 0*b 2*c^2/4 - a 1*b 0*b 2*c/2 - a 1*b 0*b 2*s^2/4 - a 1*b 0*b 2/4 - a 1*b 0*b 3*c*s + a 1*b 0*b 3*s/2 + a 1*b 1^2*c/4 + a 1*b 1*b 3*c^2/4 + a 1*b 1*b 3*s^2/4 + a 1*b 1*b 3/4 + 3*a 1*b 2^2*c^3/16 - a 1*b 2^2*c*s^2/16 - a 1*b 2^2*c/8 - 3*a 1*b 2*b 3*c^2*s/8 + a 1*b 2*b 3*s^3/8 + a 1*b 2*b 3*s/4 + a 1*b 3^2*c^3/16 + 5*a 1*b 3^2*c*s^2/16 + a 1*b 3^2*c/8 + a 2*b 0^2*c*s - a 2*b 0^2*s - a 2*b 0*b 1*c^2/2 + a 2*b 0*b 1*c - a 2*b 0*b 1*s^2/2 - a 2*b 0*b 1/2 + 3*a 2*b 0*b 2*c^2*s/4 - a 2*b 0*b 2*s^3/4 - a 2*b 0*b 2*s/2 - a 2*b 0*b 3*c^3/4 + a 2*b 0*b 3*c^2/2 - 5*a 2*b 0*b 3*c*s^2/4 - a 2*b 0*b 3*c/2 + a 2*b 0*b 3*s^2/2 + a 2*b 0*b 3/2 + a 2*b 1^2*c*s - a 2*b 1*b 2*c^3/4 + 3*a 2*b 1*b 2*c*s^2/4 + a 2*b 1*b 2*c/2 + 5*a 2*b 1*b 3*c^2*s/4 + a 2*b 1*b 3*s^3/4 + a 2*b 1*b 3*s/2 + a 2*b 2^2*c^3*s/8 + a 2*b 2^2*c*s^3/8 + a 2*b 2^2*c*s/8 - a 2*b 2*b 3*c^4/8 + a 2*b 2*b 3*c^2/8 + a 2*b 2*b 3*s^4/8 + 3*a 2*b 2*b 3*s^2/8 + a 2*b 2*b 3/4 + 3*a 2*b 3^2*c^3*s/8 + 3*a 2*b 3^2*c*s^3/8 + 3*a 2*b 3^2*c*s/8 + 3*a 3*b 0^2*c^2/4 - a 3*b 0^2*c - a 3*b 0^2*s^2/4 + a 3*b 0^2/4 - a 3*b 0*b 1*s + 3*a 3*b 0*b 2*c^3/4 - a 3*b 0*b 2*c^2/2 - a 3*b 0*b 2*c*s^2/4 - a 3*b 0*b 2*s^2/2 - a 3*b 0*b 2/2 - 3*a 3*b 0*b 3*c^2*s/4 + a 3*b 0*b 3*s^3/4 + a 3*b 1^2*c^2/4 - 3*a 3*b 1^2*s^2/4 - a 3*b 1^2/4 + a 3*b 1*b 2*c^2*s/4 - 3*a 3*b 1*b 2*s^3/4 - a 3*b 1*b 2*s + a 3*b 1*b 3*c^3/4 - 3*a 3*b 1*b 3*c*s^2/4 + 3*a 3*b 2^2*c^4/16 - a 3*b 2^2*c^2/16 - 3*a 3*b 2^2*s^4/16 - 7*a 3*b 2^2*s^2/16 - a 3*b 2^2/4 - a 3*b 2*b 3*c^3*s/4 - a 3*b 2*b 3*c*s^3/4 - a 3*b 2*b 3*c*s/4 + a 3*b 3^2*c^4/16 + a 3*b 3^2*c^2/16 - a 3*b 3^2*s^4/16 - a 3*b 3^2*s^2/16) * hp

/-- **MLS Chapter 8, Exercise 4 (p. 392): `∫₀¹ (∫₀ᵗ u₁) u₂ dt`** for the four-term sinusoids, the
quadratic polynomial `exercise4I1`. -/
theorem integral_exercise4I1 (a b : Fin 4 → ℝ) :
    ∫ t in (0 : ℝ)..1, fourTermPrimitive a t * fourTerm b t = exercise4I1 a b := by
  have e : (fun t => fourTermPrimitive a t * fourTerm b t) =
      fun t => (fourTermP a t * fourTerm b t) / (2 * π) := by
    funext t
    simp only [fourTermPrimitive]
    ring
  rw [e, intervalIntegral.integral_div]
  simp_rw [exercise4I1_fourier a b]
  rw [integral_trigPoly, exercise4I1]
  field_simp
  ring

/-- **MLS Chapter 8, Exercise 4 (p. 392): `∫₀¹ (∫₀ᵗ u₁)² u₂ dt`** for the four-term sinusoids, the
cubic polynomial `exercise4I2`. -/
theorem integral_exercise4I2 (a b : Fin 4 → ℝ) :
    ∫ t in (0 : ℝ)..1, fourTermPrimitive a t ^ 2 * fourTerm b t = exercise4I2 a b := by
  have e : (fun t => fourTermPrimitive a t ^ 2 * fourTerm b t) =
      fun t => (fourTermP a t ^ 2 * fourTerm b t) / (2 * π) ^ 2 := by
    funext t
    simp only [fourTermPrimitive]
    ring
  rw [e, intervalIntegral.integral_div]
  simp_rw [exercise4I2_fourier a b]
  rw [integral_trigPoly, exercise4I2]
  field_simp
  ring

/-- **MLS Chapter 8, Exercise 4 (p. 392): `½ ∫₀¹ (∫₀ᵗ u₂)² u₁ dt`** for the four-term sinusoids,
the cubic polynomial `exercise4I3`. -/
theorem integral_exercise4I3 (a b : Fin 4 → ℝ) :
    (1 / 2) * ∫ t in (0 : ℝ)..1, fourTermPrimitive b t ^ 2 * fourTerm a t = exercise4I3 a b := by
  have e : (fun t => fourTermPrimitive b t ^ 2 * fourTerm a t) =
      fun t => (fourTermP b t ^ 2 * fourTerm a t) / (2 * π) ^ 2 := by
    funext t
    simp only [fourTermPrimitive]
    ring
  rw [e, intervalIntegral.integral_div]
  simp_rw [exercise4I3_fourier a b]
  rw [integral_trigPoly, exercise4I3]
  field_simp
  ring

/-- **MLS Chapter 8, Exercise 4 (p. 392): the primitive of a four-term sinusoid**, `σ̇ = u` for
`σ = fourTermPrimitive a`, `u = fourTerm a`. -/
theorem hasDerivAt_fourTermPrimitive (a : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fourTermPrimitive a) (fourTerm a t) t := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have h4 : HasDerivAt (fun t : ℝ => 4 * π * t) (4 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * π)
  have h := ((((h2.cos.const_sub 1).const_mul (a 0)).add (h2.sin.const_mul (a 1))).add
    ((h4.cos.const_sub 1).const_mul (a 2 / 2))).add (h4.sin.const_mul (a 3 / 2))
  have h' := h.div_const (2 * π)
  convert h' using 1
  · funext s
    simp [fourTermPrimitive, fourTermP]
  · simp only [fourTerm]
    field_simp
    ring

/-- **MLS Chapter 8, Exercise 4 (p. 392): the primitive vanishes at both ends of the period**
`[0, 1]`. -/
theorem fourTermPrimitive_zero_one (a : Fin 4 → ℝ) :
    fourTermPrimitive a 0 = 0 ∧ fourTermPrimitive a 1 = 0 := by
  have c4 : cos (4 * π) = 1 := by
    rw [show 4 * π = ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring, cos_nat_mul_two_pi]
  have s4 : sin (4 * π) = 0 := by
    rw [show 4 * π = ((4 : ℕ) : ℝ) * π by push_cast; ring, sin_nat_mul_pi]
  refine ⟨?_, ?_⟩ <;> simp [fourTermPrimitive, fourTermP, c4, s4]

/-- **MLS Chapter 8, Exercise 4 (p. 392): the polynomial equations.** Every trajectory on `[0, 1]`
of the system of p. 363 under the four-term sinusoids `u₁` (coefficients `a`) and `u₂`
(coefficients `b`), from any initial state, ends at `q₁(1) = q₁(0)`, `q₂(1) = q₂(0)`,
`q₁₂(1) = q₁₂(0) + I₁`, `q₁₂₁(1) = q₁₂₁(0) − q₁(0) I₁ − I₂` and `q₁₂₂(1) = q₁₂₂(0) + I₃`, with `I₁`
quadratic and `I₂, I₃` cubic polynomials in `(aᵢ, bᵢ)` (`exercise4I1`, `exercise4I2`,
`exercise4I3`). Convention: the state order `(q₁, q₂, q₁₂, q₁₂₁, q₁₂₂)`, coefficients indexed from
`0`. -/
theorem IsTrajectory.exercise4_polynomial (a b : Fin 4 → ℝ) {x : ℝ → Fin 5 → ℝ}
    (hx : IsTrajectory secondOrderFields (exercise4Input a b) 1 x) :
    x 1 = x 0 + ![0, 0, exercise4I1 a b, -(x 0 0 * exercise4I1 a b) - exercise4I2 a b,
      exercise4I3 a b] := by
  have hu : Continuous (exercise4Input a b) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [exercise4Input, fourTerm] <;> fun_prop
  obtain ⟨ha0, ha1⟩ := fourTermPrimitive_zero_one a
  obtain ⟨hb0, hb1⟩ := fourTermPrimitive_zero_one b
  obtain ⟨h0, h1, h2, h3, h4⟩ := hx.secondOrder_endpoint_zeroMean hu
    (σ := fourTermPrimitive a) (τ := fourTermPrimitive b)
    (fun t => by simpa [exercise4Input] using hasDerivAt_fourTermPrimitive a t)
    (fun t => by simpa [exercise4Input] using hasDerivAt_fourTermPrimitive b t) ha0 ha1 hb0 hb1
  simp only [exercise4Input, Matrix.cons_val_one, Matrix.cons_val_zero] at h2 h3 h4
  rw [integral_exercise4I1] at h2 h3
  rw [integral_exercise4I2] at h3
  rw [integral_exercise4I3] at h4
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

end Nonholonomic
end RoboLean
