import RoboLean.Examples.NonholonomicBrockett
import RoboLean.Nonholonomic.SteeringIntegrals
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Steering the `m`-input system (8.4)–(8.5) by sinusoids: MLS Algorithm 1, step 2

MLS Chapter 8, §2.1, printed pp. 360–361: the `m`-input system (8.4) `q̇ᵢ = uᵢ`,
`q̇ᵢⱼ = qᵢuⱼ − qⱼuᵢ`, written (8.5) `q̇ = u`, `Ẏ = quᵀ − uqᵀ`, and Algorithm 1: "1. Steer the `qᵢ`
to their desired values using any input and ignoring the evolution of the `qᵢⱼ`. 2. Using
sinusoids at integrally related frequencies, find `u₀` such that the input steers the `qᵢⱼ` to
their desired values. By the choice of input, the `qᵢ` are unchanged."

**What is formalized.** Step 2 for one pair of inputs: with `uᵢ = a sin 2πt`, `uⱼ = b cos 2πt`
(`i ≠ j`) and the other inputs zero, every trajectory of (8.5) on `[0, 1]`, from every initial
state, returns every `qₖ` and changes `Y` by `−(ab/(2π))(Eᵢⱼ − Eⱼᵢ)`: `qᵢⱼ` moves by `−ab/(2π)` and
every other `qₖₗ`, `k < l`, returns (`IsTrajectory.brockettSystem_steering`). Choosing `a, b`
sets `qᵢⱼ`; a sequence of such steps over the pairs `i < j` is not formalized here, nor is
Brockett's result on the frequencies of the optimal inputs (p. 361, cited without proof).

**Conventions.** The state is `(q, Y)` with the whole matrix `Y` (`brockettSystemFields`, MLS
eq. (8.5)); the book's `qᵢⱼ`, `i < j`, are the entries `Yᵢⱼ`; trajectories are the library's
`IsTrajectory` on `[0, 1]`.
-/

noncomputable section

open Real Set
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

variable {m : ℕ}

/-- **MLS Algorithm 1, step 2 (p. 361), for one pair: the input `uᵢ = a sin 2πt`,
`uⱼ = b cos 2πt`, the others zero,** for the `m`-input system (8.4)–(8.5). -/
def brockettPairInput (i j : Fin m) (a b : ℝ) (t : ℝ) : Fin m → ℝ :=
  Pi.single i (a * sin (2 * π * t)) + Pi.single j (b * cos (2 * π * t))

/-- A component continuous on `[0, 1]` with derivative `g` off a finite set differs from an
antiderivative `F` of `g` by a constant. -/
private theorem sub_eq_sub_zero' {f F g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {S : Finset ℝ}
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ S → HasDerivAt f (g t) t) (hF : ∀ t, HasDerivAt F (g t) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t - F t = f 0 - F 0 := by
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => f s - F s)
    (fun _ => (0 : ℝ)) ht.1 S.countable_toSet
    ((hf.mono (Icc_subset_Icc le_rfl ht.2)).sub (fun s _ => (hF s).continuousAt.continuousWithinAt))
    (fun s hs => by
      have h := (hd s ⟨hs.1.1, hs.1.2.trans_le ht.2⟩ hs.2).sub (hF s)
      rw [sub_self] at h
      exact h)
    intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- **MLS Algorithm 1, step 2, pp. 360–361, for the `m`-input system (8.4)–(8.5):** every
trajectory on `[0, 1]` with `uᵢ = a sin 2πt`, `uⱼ = b cos 2πt` (`i ≠ j`) and the other inputs
zero, from every initial state, returns `q` ("the `qᵢ` are unchanged") and ends with
`Y(1) = Y(0) − (ab/(2π))(Eᵢⱼ − Eⱼᵢ)`: `qᵢⱼ` moves by `−ab/(2π)` and every other `qₖₗ` returns. -/
theorem IsTrajectory.brockettSystem_steering {i j : Fin m} (hij : i ≠ j) {a b : ℝ}
    {x : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ)}
    (hx : IsTrajectory (brockettSystemFields m) (brockettPairInput i j a b) 1 x) :
    (x 1).1 = (x 0).1 ∧ ∀ k l, (x 1).2 k l = (x 0).2 k l - a * b / (2 * π) *
      ((if k = i ∧ l = j then 1 else 0) - (if k = j ∧ l = i then 1 else 0)) := by
  obtain ⟨hc, S, hS⟩ := hx
  have hπ : π ≠ 0 := pi_ne_zero
  set u := brockettPairInput i j a b with hu_def
  have hu : ∀ t k, u t k = (if k = i then a * sin (2 * π * t) else 0) +
      (if k = j then b * cos (2 * π * t) else 0) := by
    intro t k
    simp [hu_def, brockettPairInput, Pi.single_apply]
  have huc : ∀ k, Continuous fun t => u t k := by
    intro k
    simp only [hu]
    split_ifs <;> fun_prop
  set σ : ℝ → ℝ := fun t => a / (2 * π) * (1 - cos (2 * π * t)) with hσ_def
  set τ : ℝ → ℝ := fun t => b / (2 * π) * sin (2 * π * t) with hτ_def
  have hσ : ∀ t, HasDerivAt σ (a * sin (2 * π * t)) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul (2 * π)).cos.const_sub 1).const_mul (a / (2 * π))
    convert h using 1
    · simp only [id]
      rfl
    · simp only [id]
      field_simp
  have hτ : ∀ t, HasDerivAt τ (b * cos (2 * π * t)) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (2 * π)).sin.const_mul (b / (2 * π))
    convert h using 1
    · simp only [id]
      rfl
    · simp only [id]
      field_simp
  have hcσ : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
  have hcτ : Continuous τ := continuous_iff_continuousAt.2 fun t => (hτ t).continuousAt
  have hσ0 : σ 0 = 0 := by simp [hσ_def]
  have hσ1 : σ 1 = 0 := by simp [hσ_def]
  have hτ0 : τ 0 = 0 := by simp [hτ_def]
  have hτ1 : τ 1 = 0 := by simp [hτ_def]
  set U : Fin m → ℝ → ℝ := fun k t => (if k = i then σ t else 0) + (if k = j then τ t else 0)
    with hU_def
  have hU : ∀ k t, HasDerivAt (U k) (u t k) t := by
    intro k t
    rw [hu]
    simp only [hU_def]
    split_ifs
    · exact (hσ t).add (hτ t)
    · simpa using hσ t
    · simpa using hτ t
    · simpa using hasDerivAt_const t (0 : ℝ)
  have hU0 : ∀ k, U k 0 = 0 := fun k => by simp [hU_def, hσ0, hτ0]
  have hU1 : ∀ k, U k 1 = 0 := fun k => by simp [hU_def, hσ1, hτ1]
  have hUc : ∀ k, Continuous (U k) := fun k =>
    continuous_iff_continuousAt.2 fun t => (hU k t).continuousAt
  -- the two cross integrals
  have hij' : ∫ t in (0 : ℝ)..1, σ t * (b * cos (2 * π * t)) = -(a * b / (4 * π)) := by
    have h := integral_one_sub_cos_pow_mul_cos_self 1
    have e : (fun t => σ t * (b * cos (2 * π * t))) = fun t => a * b / (2 * π) *
        ((1 - cos (2 * π * t)) ^ 1 * cos (2 * π * ((1 : ℕ) : ℝ) * t)) := by
      funext t
      simp only [hσ_def]
      push_cast
      ring_nf
    rw [e, intervalIntegral.integral_const_mul, h]
    field_simp
    ring
  have c1 : Continuous fun t => τ t * (a * sin (2 * π * t)) := hcτ.mul (by fun_prop)
  have c2 : Continuous fun t => σ t * (b * cos (2 * π * t)) := hcσ.mul (by fun_prop)
  have hji' : ∫ t in (0 : ℝ)..1, τ t * (a * sin (2 * π * t)) = a * b / (4 * π) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => σ t * τ t)
      (f' := fun t => τ t * (a * sin (2 * π * t)) + σ t * (b * cos (2 * π * t)))
      (fun t _ => by
        convert (hσ t).mul (hτ t) using 1
        ring)
      ((c1.add c2).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_add (c1.intervalIntegrable 0 1) (c2.intervalIntegrable 0 1),
      hij', hσ0, hσ1, hτ0, hτ1] at h
    linarith
  have hint0 : ∀ n, ∫ t in (0 : ℝ)..1, u t n = 0 := by
    intro n
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hU n t)
      ((huc n).intervalIntegrable 0 1), hU0, hU1, sub_zero]
  have hcross : ∀ k l, ∫ t in (0 : ℝ)..1, (U k t * u t l - u t k * U l t) =
      -(a * b / (2 * π)) *
        ((if k = i ∧ l = j then 1 else 0) - (if k = j ∧ l = i then 1 else 0)) := by
    intro k l
    set cki : ℝ := if k = i then 1 else 0
    set ckj : ℝ := if k = j then 1 else 0
    set cli : ℝ := if l = i then 1 else 0
    set clj : ℝ := if l = j then 1 else 0
    have e : (fun t => U k t * u t l - u t k * U l t) = fun t =>
        (cki * clj - ckj * cli) * (σ t * (b * cos (2 * π * t))) -
          (cki * clj - ckj * cli) * (τ t * (a * sin (2 * π * t))) := by
      funext t
      rw [hu, hu]
      simp only [hU_def, cki, ckj, cli, clj]
      split_ifs <;> ring
    have j2 : IntervalIntegrable (fun t => (cki * clj - ckj * cli) * (σ t * (b * cos (2 * π * t))))
        MeasureTheory.volume 0 1 := (continuous_const.mul c2).intervalIntegrable 0 1
    have j1 : IntervalIntegrable (fun t => (cki * clj - ckj * cli) * (τ t * (a * sin (2 * π * t))))
        MeasureTheory.volume 0 1 := (continuous_const.mul c1).intervalIntegrable 0 1
    rw [e, intervalIntegral.integral_sub j2 j1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hij', hji']
    have hc : cki * clj - ckj * cli =
        (if k = i ∧ l = j then 1 else 0) - (if k = j ∧ l = i then 1 else 0) := by
      simp only [cki, ckj, cli, clj]
      by_cases hk : k = i <;> by_cases hk' : k = j <;> by_cases hl : l = i <;>
        by_cases hl' : l = j <;> simp_all
    rw [hc]
    field_simp
    ring
  have hco : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ S →
      (∀ k, HasDerivAt (fun s => (x s).1 k) (u t k) t) ∧
        ∀ k l, HasDerivAt (fun s => (x s).2 k l) ((x t).1 k * u t l - u t k * (x t).1 l) t := by
    intro t ht hts
    have h := hS t ht hts
    rw [brockettSystem_driftFree] at h
    have h1 := hasFDerivAt_fst.comp_hasDerivAt t h
    have h2 := hasFDerivAt_snd.comp_hasDerivAt t h
    exact ⟨fun k => hasDerivAt_pi.1 h1 k, fun k l => hasDerivAt_pi.1 (hasDerivAt_pi.1 h2 k) l⟩
  have hqc : ∀ k, ContinuousOn (fun s => (x s).1 k) (Icc 0 1) := fun k =>
    (show Continuous fun z : (Fin m → ℝ) × (Fin m → Fin m → ℝ) => z.1 k by fun_prop
      ).comp_continuousOn hc
  have hYc : ∀ k l, ContinuousOn (fun s => (x s).2 k l) (Icc 0 1) := fun k l =>
    (show Continuous fun z : (Fin m → ℝ) × (Fin m → Fin m → ℝ) => z.2 k l by fun_prop
      ).comp_continuousOn hc
  have hq : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, (x t).1 k = (x 0).1 k + U k t := by
    intro k t ht
    have h := sub_eq_sub_zero' (hqc k) (fun s hs hss => (hco s hs hss).1 k) (hU k) ht
    rw [hU0] at h
    linarith
  refine ⟨funext fun k => by rw [hq k 1 ⟨zero_le_one, le_rfl⟩, hU1, add_zero], fun k l => ?_⟩
  have hgc : Continuous fun s => U k s * u s l - u s k * U l s :=
    ((hUc k).mul (huc l)).sub ((huc k).mul (hUc l))
  have h := sub_eq_sub_zero' (f := fun s => (x s).2 k l)
    (F := fun s => (x 0).1 k * U l s - (x 0).1 l * U k s +
      ∫ r in (0 : ℝ)..s, (U k r * u r l - u r k * U l r))
    (g := fun s => ((x 0).1 k + U k s) * u s l - u s k * ((x 0).1 l + U l s))
    (hYc k l) (fun s hs hss => by
      have := (hco s hs hss).2 k l
      rwa [hq k s (Ioo_subset_Icc_self hs), hq l s (Ioo_subset_Icc_self hs)] at this)
    (fun s => by
      have := (((hU l s).const_mul ((x 0).1 k)).sub ((hU k s).const_mul ((x 0).1 l))).add
        ((hgc.integral_hasStrictDerivAt 0 s).hasDerivAt)
      convert this using 1
      ring) ⟨zero_le_one, le_rfl⟩
  simp only [hU0, hU1, intervalIntegral.integral_same, mul_zero, sub_zero, add_zero,
    zero_add] at h
  rw [hcross k l] at h
  linarith

/-- **Trajectories of the `m`-input system (8.5) exist for continuous inputs** (MLS p. 360; for
Algorithm 1, p. 361): from every initial state there is a solution on all of `ℝ`, by iterated
integrals, so the hypotheses of `IsTrajectory.brockettSystem_steering` are met for all `a, b`
(`IsTrajectory.of_hasDerivAt`). -/
theorem brockettSystem_exists_solution {u : ℝ → Fin m → ℝ} (hu : Continuous u)
    (z₀ : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :
    ∃ x : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ), x 0 = z₀ ∧
      ∀ t, HasDerivAt x (driftFree (brockettSystemFields m) (x t) (u t)) t := by
  have huk : ∀ k, Continuous fun t => u t k := fun k => (continuous_apply k).comp hu
  have hprim : ∀ {f : ℝ → ℝ}, Continuous f → ∀ (c t : ℝ),
      HasDerivAt (fun t => c + ∫ s in (0 : ℝ)..t, f s) (f t) t := fun hf c t =>
    ((hf.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add c
  have hcont : ∀ {f : ℝ → ℝ}, Continuous f → ∀ c : ℝ,
      Continuous fun t => c + ∫ s in (0 : ℝ)..t, f s := fun hf c =>
    continuous_iff_continuousAt.2 fun t => (hprim hf c t).continuousAt
  set q : ℝ → Fin m → ℝ := fun t k => z₀.1 k + ∫ s in (0 : ℝ)..t, u s k with hq
  have hqc : ∀ k, Continuous fun t => q t k := fun k => hcont (huk k) _
  set Y : ℝ → Fin m → Fin m → ℝ :=
    fun t k l => z₀.2 k l + ∫ s in (0 : ℝ)..t, (q s k * u s l - u s k * q s l) with hY
  refine ⟨fun t => (q t, Y t), ?_, fun t => ?_⟩
  · simp [q, Y]
  · rw [brockettSystem_driftFree]
    refine HasDerivAt.prodMk ?_ ?_
    · rw [hasDerivAt_pi]
      exact fun k => hprim (huk k) _ t
    · rw [hasDerivAt_pi]
      exact fun k => hasDerivAt_pi.2 fun l =>
        hprim (((hqc k).mul (huk l)).sub ((huk k).mul (hqc l))) _ t

end Examples
end RoboLean
