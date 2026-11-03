import RoboLean.Nonholonomic.Steering

/-!
# Algorithm 3 steers the one-chain system to any configuration: MLS Proposition 8.3

MLS Chapter 8, printed pp. 365–366: Algorithm 3 ("1. Steer `q₁` and `q₂` to their desired values.
2. For each `q_{k+2}`, `k ≥ 1`, steer [`q_{k+2}`] to its final value using `u₁ = a sin 2πt`,
`u₂ = b cos 2πkt`, where `a` and `b` satisfy `q_{k+2}(1) − q_{k+2}(0) = (a/4π)^k b/k!`") and
Proposition 8.3: "Algorithm 3 can steer (8.7) to an arbitrary configuration."

**Conventions.** The input of Algorithm 3 on `[0, n − 1]` is `algorithm3Input c a b`: the constant
`c` on `[0, 1)`, and on `[k, k + 1)`, `k ≥ 1`, the sinusoids of step `k` with amplitudes `a k`,
`b k`, shifted to start at time `k`. Trajectories are those of `IsTrajectory`; the input is
continuous away from the integer times.
-/

noncomputable section

open Set Filter Topology Real

namespace RoboLean
namespace Nonholonomic

/-- **MLS Algorithm 3, p. 365: the input of the whole algorithm,** the constant `c` on `[0, 1)`
(step 1) and, on `[k, k + 1)` for `k ≥ 1`, `u₁ = a_k sin 2π(t − k)`, `u₂ = b_k cos 2πk(t − k)`
(step 2 for `q_{k+2}`). -/
def algorithm3Input (c : Fin 2 → ℝ) (a b : ℕ → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  if t < 1 then c else chainSinusoid (a ⌊t⌋₊) (b ⌊t⌋₊) ⌊t⌋₊ (t - ⌊t⌋₊)

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- Changing the input on the open interval `(0, T)` keeps a trajectory (supporting lemma for
MLS Algorithm 3, p. 365, and Proposition 8.3, p. 366). -/
private theorem IsTrajectory.congr_input {g : Fin m → E → E} {u v : ℝ → Fin m → ℝ} {T : ℝ}
    {x : ℝ → E} (hx : IsTrajectory g u T x) (huv : ∀ t ∈ Ioo 0 T, u t = v t) :
    IsTrajectory g v T x := by
  obtain ⟨hc, S, hS⟩ := hx
  exact ⟨hc, S, fun t ht htS => huv t ht ▸ hS t ht htS⟩

/-- Concatenation of a trajectory on `[0, T]` with a trajectory on `[0, 1]` for the input shifted
by `T`, started where the first ends, is a trajectory on `[0, T + 1]` (supporting lemma for MLS
Algorithm 3, p. 365, and Proposition 8.3, p. 366: the steps run one after another). -/
private theorem IsTrajectory.glue {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {T : ℝ}
    {x y : ℝ → E} (hT : 0 ≤ T) (hx : IsTrajectory g u T x)
    (hy : IsTrajectory g (fun s => u (s + T)) 1 y) (hxy : x T = y 0) :
    IsTrajectory g u (T + 1) (fun t => if t ≤ T then x t else y (t - T)) := by
  obtain ⟨hxc, S₁, hS₁⟩ := hx
  obtain ⟨hyc, S₂, hS₂⟩ := hy
  refine ⟨?_, S₁ ∪ S₂.image (· + T) ∪ {T}, fun t ht htS => ?_⟩
  · have h1 : ContinuousOn (fun t => if t ≤ T then x t else y (t - T)) (Icc 0 T) :=
      hxc.congr fun t ht => by simp [ht.2]
    have h2 : ContinuousOn (fun t => if t ≤ T then x t else y (t - T)) (Icc T (T + 1)) := by
      refine (hyc.comp (continuous_sub_right T).continuousOn fun t ht =>
        ⟨sub_nonneg.2 ht.1, by linarith [ht.2]⟩).congr fun t ht => ?_
      by_cases h : t ≤ T
      · have : t = T := le_antisymm h ht.1
        simp [this, hxy]
      · simp [h]
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hT (by linarith)] at this
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or] at htS
    obtain ⟨⟨h1, h2⟩, h3⟩ := htS
    rcases lt_or_gt_of_ne h3 with h | h
    · have he : (fun t => if t ≤ T then x t else y (t - T)) =ᶠ[𝓝 t] x := by
        filter_upwards [Iio_mem_nhds h] with s hs
        simp [(mem_Iio.1 hs).le]
      exact ((hS₁ t ⟨ht.1, h⟩ h1).congr_of_eventuallyEq he).congr_deriv (by simp [h.le])
    · have he : (fun t => if t ≤ T then x t else y (t - T)) =ᶠ[𝓝 t] fun s => y (s - T) := by
        filter_upwards [Ioi_mem_nhds h] with s hs
        simp [not_le.2 (mem_Ioi.1 hs)]
      have hd := hS₂ (t - T) ⟨by linarith, by linarith [ht.2]⟩ fun h' => h2 ⟨_, h', by ring⟩
      simp only [sub_add_cancel] at hd
      exact ((hd.comp_sub_const t T).congr_of_eventuallyEq he).congr_deriv
        (by simp [not_le.2 h])

end Helpers

/-- **Step 1 of MLS Algorithm 3, p. 365:** the constant input `(q_f,1 − q_0,1, q_f,2 − q_0,2)` on
`[0, 1]` steers `q₁` and `q₂` from their initial to their desired values (supporting lemma for
MLS Proposition 8.3, p. 366). -/
private theorem chain_step_one {n : ℕ} (hn : 2 ≤ n) (q₀ qf : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, x 0 = q₀ ∧
      IsTrajectory (chainFields n)
        (fun _ => ![qf ⟨0, by omega⟩ - q₀ ⟨0, by omega⟩, qf ⟨1, by omega⟩ - q₀ ⟨1, by omega⟩]) 1 x ∧
      ∀ j : Fin n, j.val ≤ 1 → x 1 j = qf j := by
  set c : Fin 2 → ℝ :=
    ![qf ⟨0, by omega⟩ - q₀ ⟨0, by omega⟩, qf ⟨1, by omega⟩ - q₀ ⟨1, by omega⟩] with hc
  obtain ⟨x, hx0, hx⟩ := chain_exists_solution n (continuous_const (y := c)) q₀
  refine ⟨x, hx0, IsTrajectory.of_hasDerivAt 1 hx, fun j hj => ?_⟩
  have hint : ∀ i : Fin 2, (∀ t, HasDerivAt (fun t => x t j) (c i) t) → x 1 j = x 0 j + c i := by
    intro i hd
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun t _ => hd t) intervalIntegrable_const
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at h
    linarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with h | h
  · have hj' : j = ⟨0, by omega⟩ := Fin.ext h
    rw [hint 0 fun t => by
      simpa [chain_driftFree_of_val_eq_zero _ _ h] using hasDerivAt_pi.1 (hx t) j, hx0, hj']
    simp [hc]
  · have hj' : j = ⟨1, by omega⟩ := Fin.ext h
    rw [hint 1 fun t => by
      simpa [chain_driftFree_of_val_eq_one _ _ h] using hasDerivAt_pi.1 (hx t) j, hx0, hj']
    simp [hc]

/-- **MLS Proposition 8.3, p. 366: Algorithm 3 can steer (8.7) to an arbitrary configuration.**
For `n ≥ 2` and all `q₀`, `q_f`, there are a constant `c` and amplitudes `a_k`, `b_k` such that
the one-chain system has a trajectory on `[0, n − 1]` under `algorithm3Input c a b` from `q₀` to
`q_f`. -/
theorem chain_algorithm3_steers {n : ℕ} (hn : 2 ≤ n) (q₀ qf : Fin n → ℝ) :
    ∃ (c : Fin 2 → ℝ) (a b : ℕ → ℝ) (x : ℝ → Fin n → ℝ),
      IsTrajectory (chainFields n) (algorithm3Input c a b) ((n - 1 : ℕ) : ℝ) x ∧ x 0 = q₀ ∧
        x ((n - 1 : ℕ) : ℝ) = qf := by
  obtain ⟨x₁, hx₁0, hx₁, hx₁f⟩ := chain_step_one hn q₀ qf
  set c : Fin 2 → ℝ :=
    ![qf ⟨0, by omega⟩ - q₀ ⟨0, by omega⟩, qf ⟨1, by omega⟩ - q₀ ⟨1, by omega⟩]
  have key : ∀ m : ℕ, 1 ≤ m → m ≤ n - 1 → ∃ (a b : ℕ → ℝ) (x : ℝ → Fin n → ℝ),
      IsTrajectory (chainFields n) (algorithm3Input c a b) (m : ℝ) x ∧ x 0 = q₀ ∧
        ∀ j : Fin n, j.val ≤ m → x m j = qf j := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      refine ⟨0, 0, x₁, ?_, hx₁0, by simpa using hx₁f⟩
      rw [Nat.cast_one]
      exact hx₁.congr_input fun t ht => by simp [algorithm3Input, ht.2]
    | succ m hm ih =>
      intro hmn
      obtain ⟨a, b, x, hx, hx0, hxf⟩ := ih (by omega)
      set i : Fin n := ⟨m + 1, by omega⟩
      set bm : ℝ := (qf i - x m i) * (m.factorial : ℝ) * (4 * π) ^ m
      obtain ⟨y, hy0, hy⟩ := chain_exists_trajectory_sinusoid n m 1 bm (x m)
      set a' := Function.update a m 1
      set b' := Function.update b m bm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hx' : IsTrajectory (chainFields n) (algorithm3Input c a' b') m x := by
        refine hx.congr_input fun t ht => ?_
        have hfl : ⌊t⌋₊ ≠ m := ((Nat.floor_lt ht.1.le).2 ht.2).ne
        simp only [algorithm3Input, a', b', Function.update_of_ne hfl]
      have hy' : IsTrajectory (chainFields n) (fun s => algorithm3Input c a' b' (s + m)) 1 y := by
        refine hy.congr_input fun s hs => ?_
        have hfl : ⌊s + m⌋₊ = m :=
          (Nat.floor_eq_iff (by linarith [hs.1])).2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hlt : ¬ s + m < 1 := by linarith [hs.1]
        simp only [algorithm3Input, hlt, ↓reduceIte, hfl, a', b', Function.update_self,
          add_sub_cancel_right]
      obtain ⟨hst1, hst2⟩ := hy.chain_steering hm 1 bm
      refine ⟨a', b', fun t => if t ≤ m then x t else y (t - m), ?_, by simp [hx0], ?_⟩
      · rw [Nat.cast_succ]
        exact hx'.glue (Nat.cast_nonneg m) hy' hy0.symm
      · intro j hj
        have hle : ¬ (m : ℝ) + 1 ≤ m := by linarith
        simp only [Nat.cast_succ, hle, ↓reduceIte, add_sub_cancel_left]
        rcases Nat.lt_or_ge m j.val with h | h
        · have hj' : j = i := Fin.ext (by simp [i]; omega)
          have h2 := hst2 j (by omega)
          rw [hy0, hj'] at *
          have hπ : (4 * π : ℝ) ≠ 0 := by positivity
          have hf : (m.factorial : ℝ) ≠ 0 := by positivity
          have : (1 / (4 * π)) ^ m * bm / (m.factorial : ℝ) = qf i - x m i := by
            simp only [bm, div_pow, one_pow]
            field_simp
          linarith
        · rw [hst1 j h, hy0, hxf j h]
  obtain ⟨a, b, x, hx, hx0, hxf⟩ := key (n - 1) (by omega) le_rfl
  exact ⟨c, a, b, x, hx, hx0, funext fun j => hxf j (by have := j.isLt; omega)⟩

end Nonholonomic
end RoboLean
