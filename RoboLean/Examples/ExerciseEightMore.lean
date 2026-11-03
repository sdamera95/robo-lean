import RoboLean.Examples.BrockettGeneral
import RoboLean.Nonholonomic.Concatenation
import RoboLean.Nonholonomic.ChainedForm

/-!
# Chapter 8, Exercise 3(c): steering `(0, 0)` to `(0, Ỹ)` for the `m`-input system (MLS p. 392)

MLS Chapter 8, Exercise 3, printed pp. 391–392: for `q̇ = u`, `Ẏ = q uᵀ − u qᵀ`, `u ∈ ℝᵐ`,
`Y ∈ so(m)`, "(c) Find the input `u` to steer the system from `(0, 0)` to `(0, Ỹ) ∈ ℝᵐ × so(m)`."

**What is formalized.** The input is found by concatenation (the second method of p. 361 for the
first-order system, Algorithm 1): write `Ỹ = Σ_{i<j} Ỹᵢⱼ (Eᵢⱼ − Eⱼᵢ)` and, for each pair `i < j` in
turn, apply on a unit interval the pair input `uᵢ = sin 2πt`, `uⱼ = −2π Ỹᵢⱼ cos 2πt`, the others
zero, which returns `q` and moves `Y` by `Ỹᵢⱼ (Eᵢⱼ − Eⱼᵢ)` from every state (the library's
`IsTrajectory.brockettSystem_steering`). The theorem is stated from any initial state `(q₀, Y₀)`
to `(q₀, Y₀ + Ỹ)`, which contains the exercise's `(0, 0)` to `(0, Ỹ)`.

Exercise 3(b), the optimal input for `q(0) = q(1) = 0`, `Y(0) = 0`, `Y(1) = ŷ` with the printed
`y ∈ ℝ³` (so `m = 3`), is not formalized here.

**Conventions.** The state is the library's `(q, Y) ∈ ℝᵐ × ℝ^{m×m}` of (8.4)–(8.5), with `Y`
skew-symmetric along trajectories from skew initial data; trajectories are those of
`IsTrajectory`; the concatenated input is the library's `concatInput` (continuous on each piece).
-/

noncomputable section

open Set Real

namespace RoboLean
namespace Examples

open RoboLean.Nonholonomic

variable {m : ℕ}

/-- **MLS Chapter 8, Exercise 3(c) (p. 392): one pair step from any state.** For `i ≠ j` and any
`c`, from every state `(q₀, Y₀)` there is a trajectory on `[0, 1]` of (8.5) ending at
`(q₀, Y₀ + c(Eᵢⱼ − Eⱼᵢ))`. -/
theorem brockettSystem_pairStep {i j : Fin m} (hij : i ≠ j) (c : ℝ)
    (z₀ : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :
    ∃ u x, IsTrajectory (brockettSystemFields m) u 1 x ∧ x 0 = z₀ ∧ (x 1).1 = z₀.1 ∧
      ∀ k l, (x 1).2 k l = z₀.2 k l +
        c * ((if k = i ∧ l = j then 1 else 0) - (if k = j ∧ l = i then 1 else 0)) := by
  have hu : Continuous (brockettPairInput i j 1 (-(2 * π * c))) := by
    unfold brockettPairInput
    refine continuous_pi fun k => ?_
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> fun_prop
  obtain ⟨x, hx0, hx⟩ := brockettSystem_exists_solution hu z₀
  have ht : IsTrajectory (brockettSystemFields m) (brockettPairInput i j 1 (-(2 * π * c))) 1 x :=
    IsTrajectory.of_hasDerivAt 1 hx
  obtain ⟨h1, h2⟩ := IsTrajectory.brockettSystem_steering hij ht
  refine ⟨_, x, ht, hx0, by rw [h1, hx0], fun k l => ?_⟩
  rw [h2 k l, hx0]
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- **MLS Chapter 8, Exercise 3(c) (p. 392): finitely many pair steps concatenated.** For a finite
set `s` of pairs `(i, j)` with `i ≠ j` and coefficients `c`, from every state `(q₀, Y₀)` there is a
trajectory of (8.5) on `[0, |s|]` ending at `(q₀, Y₀ + Σ_{(i,j) ∈ s} c(i,j)(Eᵢⱼ − Eⱼᵢ))`. -/
theorem brockettSystem_pairSteps (c : Fin m × Fin m → ℝ) :
    ∀ s : Finset (Fin m × Fin m), (∀ p ∈ s, p.1 ≠ p.2) →
      ∀ z₀ : (Fin m → ℝ) × (Fin m → Fin m → ℝ), ∃ u x,
        IsTrajectory (brockettSystemFields m) u (s.card : ℝ) x ∧ x 0 = z₀ ∧
        (x s.card).1 = z₀.1 ∧ ∀ k l, (x s.card).2 k l = z₀.2 k l + ∑ p ∈ s,
          c p * ((if k = p.1 ∧ l = p.2 then 1 else 0) - (if k = p.2 ∧ l = p.1 then 1 else 0)) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ z₀
    refine ⟨fun _ => 0, fun _ => z₀, IsTrajectory.of_hasDerivAt _ fun t => ?_, rfl, rfl,
      fun k l => by simp⟩
    simpa [driftFree] using hasDerivAt_const t z₀
  | insert p s hps ih =>
    intro hs z₀
    obtain ⟨u, x, hx, hx0, hx1, hx2⟩ := brockettSystem_pairStep (hs p (Finset.mem_insert_self p s))
      (c p) z₀
    obtain ⟨v, y, hy, hy0, hy1, hy2⟩ := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) (x 1)
    have hT : ((insert p s).card : ℝ) = 1 + s.card := by
      rw [Finset.card_insert_of_notMem hps]
      push_cast
      ring
    have hend : concatPath x y 1 ((insert p s).card : ℝ) = y s.card := by
      rw [hT]
      unfold concatPath
      split_ifs with h
      · have h0 : (s.card : ℝ) = 0 := by
          have : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
          linarith
        rw [h0, hy0]
        congr 1
        norm_num
      · congr 1
        ring
    refine ⟨concatInput u v 1, concatPath x y 1, ?_, ?_, ?_, fun k l => ?_⟩
    · rw [hT]
      exact hx.concat hy hy0.symm zero_le_one (Nat.cast_nonneg _)
    · simp [concatPath, hx0]
    · rw [hend, hy1, hx1]
    · rw [hend, hy2, hx2, Finset.sum_insert hps]
      ring

/-- **MLS Chapter 8, Exercise 3(c) (p. 392): steering to any skew-symmetric `Ỹ`.** For every
skew-symmetric `Ỹ` (`Ỹₖₗ = −Ỹₗₖ`) and every state `(q₀, Y₀)` there are a time `T ≥ 0`, an input
(the construction concatenates the pair inputs for the pairs `i < j`, one unit of time each) and a
trajectory of (8.5) on `[0, T]` from `(q₀, Y₀)` to `(q₀, Y₀ + Ỹ)`; in particular from `(0, 0)` to
`(0, Ỹ)`. -/
theorem brockettSystem_steer_skew {Y : Fin m → Fin m → ℝ} (hY : ∀ k l, Y k l = -Y l k)
    (z₀ : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) :
    ∃ T u x, 0 ≤ T ∧ IsTrajectory (brockettSystemFields m) u T x ∧ x 0 = z₀ ∧
      x T = (z₀.1, fun k l => z₀.2 k l + Y k l) := by
  set s := (Finset.univ : Finset (Fin m × Fin m)).filter fun p => p.1 < p.2 with hs
  obtain ⟨u, x, hx, hx0, hx1, hx2⟩ := brockettSystem_pairSteps (fun p => Y p.1 p.2) s
    (fun p hp => (Finset.mem_filter.1 hp).2.ne) z₀
  refine ⟨s.card, u, x, Nat.cast_nonneg _, hx, hx0, Prod.ext hx1 (funext fun k => funext fun l => ?_)⟩
  rw [hx2 k l]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero, add_zero,
    add_zero]
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · rw [Finset.sum_eq_single (k, l), Finset.sum_eq_zero]
    · simp
    · intro p hp
      simp only [Finset.mem_filter, hs, Finset.mem_univ, true_and] at hp
      exact absurd (hp.2.1 ▸ hp.2.2 ▸ hp.1) (not_lt.2 hkl.le)
    · intro p hp hne
      simp only [Finset.mem_filter] at hp
      exact absurd (Prod.ext hp.2.1.symm hp.2.2.symm) hne
    · intro h
      simp [hs, hkl] at h
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · have := hY k k
      linarith
    · intro p hp
      simp only [Finset.mem_filter, hs, Finset.mem_univ, true_and] at hp
      exact absurd (hp.2.1 ▸ hp.2.2 ▸ hp.1) (lt_irrefl _)
    · intro p hp
      simp only [Finset.mem_filter, hs, Finset.mem_univ, true_and] at hp
      exact absurd (hp.2.1 ▸ hp.2.2 ▸ hp.1) (lt_irrefl _)
  · rw [Finset.sum_eq_zero, Finset.sum_eq_single (l, k)]
    · simp [hY l k]
    · intro p hp hne
      simp only [Finset.mem_filter] at hp
      exact absurd (Prod.ext hp.2.2.symm hp.2.1.symm) hne
    · intro h
      simp [hs, hkl] at h
    · intro p hp
      simp only [Finset.mem_filter, hs, Finset.mem_univ, true_and] at hp
      exact absurd (hp.2.1 ▸ hp.2.2 ▸ hp.1) (not_lt.2 hkl.le)

end Examples
end RoboLean
