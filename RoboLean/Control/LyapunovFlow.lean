import RoboLean.Control.SolutionFlow

/-!
# Global forward existence and a solution flow under a trapping Lyapunov function (MLS pp. 179, 193)

MLS assumes, for the system `ẋ = f(x, t)` of eq. (4.31), "the standard conditions for the
existence and uniqueness of solutions" (p. 179). For the closed loops of a manipulator under PD
control (Proposition 4.9, p. 193) the field is only locally Lipschitz, and global existence rests on
the total energy `V`, which does not increase along solutions. This module proves that this
suffices, for an autonomous field `F` on a proper normed space (for example `ℝⁿ`), with the system
written `fun _ => F` (time first, ignored), solutions taken from time `0` in the sense of
`IsSolution` (continuous on `[0, ∞)`, actual derivative `F(x(t))` at every `t > 0`).

Assumed:
* `F` is locally Lipschitz;
* every sublevel set `{x | V x ≤ c}` is compact, and `V` is continuous (used for the continuity
  of the flow only);
* `V` does not increase along any local solution: if `γ` solves `ẋ = F(x)` on `[0, T]` (one-sided
  derivatives at the end points, the form Mathlib's Picard–Lindelöf theorem produces), then
  `V (γ s) ≤ V (γ 0)` for `s ∈ [0, T]`.

Proved:
* `exists_isSolution_of_lyapunov`: from every initial state there is a solution on `[0, ∞)`;
* `exists_hasFlow_of_lyapunov`: there is a solution flow, `HasFlow F φ` (existence, uniqueness of
  solutions from every initial time `t₀ ≥ 0`, continuous dependence on the initial state).

Route: on the compact set `S₁`, the closed `1`-thickening of a sublevel set `S`, the field is
Lipschitz and bounded, so Picard–Lindelöf gives from every point of `S` a solution on a fixed
interval `[0, 2h]`; it stays in `S` because `V` does not increase. Restarting at time `h` and gluing
the overlapping pieces (they agree by Mathlib's uniqueness theorem
`ODE_solution_unique_of_mem_Icc_right` on `S`) gives a solution on `[0, ∞)`. Uniqueness and
continuous dependence come from Grönwall's bound `dist_le_of_trajectories_ODE_of_mem` on a
sublevel set, which contains both trajectories.

Limits: without the trapping hypothesis a locally Lipschitz field can have solutions that escape
in finite time (`ẋ = x²` from `x(0) = 1` has the solution `1 / (1 − t)`, which leaves every
bounded set before `t = 1`), so no global flow exists in general. Whether a given `V` satisfies the
hypotheses (in particular the nonincrease along local solutions) is a separate obligation for each
closed loop.
-/

noncomputable section

open Set Filter Topology Metric

namespace RoboLean
namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gluing local solutions into a solution on `[0, ∞)`: if from every point `y` of a set `A`
there is a solution `σ y` on `[0, 2h]`, the state `σ y h` lies in `A` again, and the solution
restarted from `σ y h` agrees with `σ y` on the overlap, then from every `x₀ ∈ A` there is a
solution of `ẋ = F(x)` from time `0` (MLS p. 179). -/
private theorem exists_isSolution_of_glue {F : E → E} {A : Set E} {h : ℝ} (hpos : 0 < h)
    {σ : E → ℝ → E} (hσ0 : ∀ y ∈ A, σ y 0 = y)
    (hσ : ∀ y ∈ A, ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt (σ y) (F (σ y t)) (Icc 0 (2 * h)) t)
    (hA : ∀ y ∈ A, σ y h ∈ A) (hagree : ∀ y ∈ A, ∀ s ∈ Icc 0 h, σ (σ y h) s = σ y (s + h))
    {x₀ : E} (hx₀ : x₀ ∈ A) : ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsSolution (fun _ => F) 0 γ := by
  have hcont : ∀ z ∈ A, ContinuousOn (σ z) (Icc 0 (2 * h)) := fun z hz t ht =>
    (hσ z hz t ht).continuousWithinAt
  -- the restart points `p (n + 1) = σ (p n) h` and the glued curve
  set p : ℕ → E := fun n => (fun z => σ z h)^[n] x₀
  have hp0 : p 0 = x₀ := rfl
  have hpsucc : ∀ n, p (n + 1) = σ (p n) h := fun n => Function.iterate_succ_apply' _ _ _
  have hpA : ∀ n, p n ∈ A := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [hpsucc]; exact hA _ ih
  set γ : ℝ → E := fun t => σ (p ⌊t / h⌋₊) (t - ⌊t / h⌋₊ * h) with hγ
  -- on `[n h, (n + 2) h)` the glued curve is the `n`-th piece
  have hkey : ∀ n : ℕ, ∀ t ∈ Ico (n * h) ((n + 2) * h), γ t = σ (p n) (t - n * h) := by
    intro n t ht
    have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
    set m := ⌊t / h⌋₊ with hm
    have hm1 : (m : ℝ) * h ≤ t := (le_div_iff₀ hpos).1 (Nat.floor_le (div_nonneg ht0 hpos.le))
    have hm2 : t < ((m : ℝ) + 1) * h := (div_lt_iff₀ hpos).1 (Nat.lt_floor_add_one _)
    have hnm : (n : ℝ) < m + 1 := lt_of_mul_lt_mul_right (ht.1.trans_lt hm2) hpos.le
    have hmn : (m : ℝ) < n + 2 := lt_of_mul_lt_mul_right (hm1.trans_lt ht.2) hpos.le
    have hnm' : n < m + 1 := by exact_mod_cast hnm
    have hmn' : m < n + 2 := by exact_mod_cast hmn
    rcases (by omega : m = n ∨ m = n + 1) with h1 | h1
    · simp only [hγ, ← hm, h1]
    · simp only [hγ, ← hm, h1, hpsucc]
      rw [hagree _ (hpA n)]
      · congr 1; push_cast; ring
      · rw [h1] at hm1
        push_cast at hm1 ⊢
        refine ⟨by linarith, by linarith [ht.2]⟩
  have hex : ∀ t, 0 < t → ∃ n : ℕ, n * h < t ∧ t < (n + 2) * h := by
    intro t ht
    refine ⟨⌊t / h - 1 / 2⌋₊, ?_, ?_⟩
    · rcases le_or_gt 0 (t / h - 1 / 2) with h1 | h1
      · have := Nat.floor_le h1
        have : (⌊t / h - 1 / 2⌋₊ : ℝ) + 1 / 2 ≤ t / h := by linarith
        rw [le_div_iff₀ hpos] at this
        nlinarith
      · rw [Nat.floor_of_nonpos h1.le]; simpa using ht
    · have := Nat.lt_floor_add_one (t / h - 1 / 2)
      have : t / h < (⌊t / h - 1 / 2⌋₊ : ℝ) + 2 := by linarith
      exact (div_lt_iff₀ hpos).1 this
  have hderiv : ∀ t, 0 < t → HasDerivAt γ (F (γ t)) t := by
    intro t ht
    obtain ⟨n, h1, h2⟩ := hex t ht
    have hd : HasDerivAt (fun s => σ (p n) (s - n * h)) (F (σ (p n) (t - n * h))) t := by
      apply HasDerivAt.comp_sub_const
      exact (hσ (p n) (hpA n) (t - n * h) ⟨by linarith, by linarith⟩).hasDerivAt
        (Icc_mem_nhds (by linarith) (by linarith))
    have heq : γ =ᶠ[𝓝 t] fun s => σ (p n) (s - n * h) := by
      filter_upwards [Ioo_mem_nhds h1 h2] with s hs using hkey n s ⟨hs.1.le, hs.2⟩
    rw [hkey n t ⟨h1.le, h2⟩]
    exact hd.congr_of_eventuallyEq heq
  refine ⟨γ, ?_, ?_, fun t ht => hderiv t ht⟩
  · simp [hγ, hp0, hσ0 x₀ hx₀]
  · intro t ht
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0 | h0
    · subst h0
      have hc : ContinuousWithinAt (σ x₀) (Ici 0) 0 :=
        (hcont x₀ hx₀ 0 ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE (by linarith))
      refine hc.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Icc_mem_nhdsGE hpos] with s hs
        simpa [hp0] using hkey 0 s ⟨by simpa using hs.1, by simp; linarith [hs.2]⟩
      · simpa [hp0] using hkey 0 0 ⟨by simp, by simp; linarith⟩
    · exact (hderiv t h0).continuousAt.continuousWithinAt

/-- A solution from time `0` of a continuous autonomous system has, on every `[0, T]`, the
derivative `F(y(s))` within `[0, T]` (MLS eq. (4.31), p. 179); the form of the Lyapunov
hypothesis below. -/
private theorem hasDerivWithinAt_Icc_of_isSolution {F : E → E} (hF : Continuous F) {y : ℝ → E}
    (hy : IsSolution (fun _ => F) 0 y) {T : ℝ} :
    ∀ s ∈ Icc 0 T, HasDerivWithinAt y (F (y s)) (Icc 0 T) s := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h
    exact (hy.hasDerivWithinAt_Ici hF).mono Icc_subset_Ici_self
  · exact (hy.2 s h).hasDerivWithinAt

/-- `V` does not increase along a solution from any initial time `t₀` (MLS p. 193, where the
total energy plays this role), given that it does not increase along local solutions from `0`. -/
private theorem le_of_isSolution {F : E → E} (hF : Continuous F) {V : E → ℝ}
    (hdec : ∀ T, 0 ≤ T → ∀ γ : ℝ → E,
      (∀ s ∈ Set.Icc 0 T, HasDerivWithinAt γ (F (γ s)) (Set.Icc 0 T) s) →
      ∀ s ∈ Set.Icc 0 T, V (γ s) ≤ V (γ 0))
    {t₀ : ℝ} {x : ℝ → E} (hx : IsSolution (fun _ => F) t₀ x) {t : ℝ} (ht : t₀ ≤ t) :
    V (x t) ≤ V (x t₀) := by
  have hx' : IsSolution (fun _ => F) 0 (fun s => x (s + t₀)) := by
    simpa using hx.comp_sub_const (-t₀)
  have := hdec (t - t₀) (sub_nonneg.2 ht) _ (hasDerivWithinAt_Icc_of_isSolution hF hx')
    (t - t₀) ⟨sub_nonneg.2 ht, le_rfl⟩
  simpa using this

/-- Grönwall's bound inside a sublevel set (MLS p. 179): for each level `c` there is `K` such
that two solutions from `t₀` that start in `{V ≤ c}` satisfy
`‖x(t) − y(t)‖ ≤ ‖x(t₀) − y(t₀)‖ e^{K (t − t₀)}` for `t ≥ t₀`. Both stay in the compact set
`{V ≤ c}`, on which the locally Lipschitz field is `K`-Lipschitz. -/
private theorem exists_dist_le_of_lyapunov {F : E → E} (hF : LocallyLipschitz F) {V : E → ℝ}
    (hcpt : ∀ c, IsCompact {x | V x ≤ c})
    (hdec : ∀ T, 0 ≤ T → ∀ γ : ℝ → E,
      (∀ s ∈ Set.Icc 0 T, HasDerivWithinAt γ (F (γ s)) (Set.Icc 0 T) s) →
      ∀ s ∈ Set.Icc 0 T, V (γ s) ≤ V (γ 0))
    (c : ℝ) :
    ∃ K : NNReal, ∀ t₀ : ℝ, ∀ x y : ℝ → E, IsSolution (fun _ => F) t₀ x →
      IsSolution (fun _ => F) t₀ y → V (x t₀) ≤ c → V (y t₀) ≤ c → ∀ t, t₀ ≤ t →
      dist (x t) (y t) ≤ dist (x t₀) (y t₀) * Real.exp (K * (t - t₀)) := by
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hcpt c) hF.locallyLipschitzOn
  refine ⟨K, fun t₀ x y hx hy hx0 hy0 t ht => ?_⟩
  exact dist_le_of_trajectories_ODE_of_mem (v := fun _ => F) (s := fun _ => {x | V x ≤ c})
    (fun _ _ => hK) (hx.1.mono Icc_subset_Ici_self)
    (fun _ hs => hx.hasDerivWithinAt_Ici_of_mem hF.continuous hs.1)
    (fun _ hs => (le_of_isSolution hF.continuous hdec hx hs.1).trans hx0)
    (hy.1.mono Icc_subset_Ici_self)
    (fun _ hs => hy.hasDerivWithinAt_Ici_of_mem hF.continuous hs.1)
    (fun _ hs => (le_of_isSolution hF.continuous hdec hy hs.1).trans hy0) le_rfl t ⟨ht, le_rfl⟩

variable [ProperSpace E]

/-- Uniform local existence on a set where the field is Lipschitz and bounded (the local step
behind MLS p. 179's standing assumption): if `F` is `K`-Lipschitz and bounded by `L` on `S₁`,
`closedBall y 1 ⊆ S₁` and `L T ≤ 1`, then a solution of `ẋ = F(x)` from `y` exists on `[0, T]`
(one-sided derivatives at the end points). From Mathlib's Picard–Lindelöf theorem with radius
`1`. -/
private theorem exists_local_of_lipschitzOnWith {F : E → E} {S₁ : Set E} {K L : NNReal}
    (hK : LipschitzOnWith K F S₁) (hL : ∀ x ∈ S₁, ‖F x‖ ≤ L) {T : ℝ} (hT : 0 ≤ T)
    (hTL : (L : ℝ) * T ≤ 1) {y : E} (hy : closedBall y 1 ⊆ S₁) :
    ∃ σ : ℝ → E, σ 0 = y ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt σ (F (σ t)) (Icc 0 T) t := by
  have hy' : closedBall y ((1 : NNReal) : ℝ) ⊆ S₁ := by simpa using hy
  have hm : (L : ℝ) * max (T - ((⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) : ℝ))
      (((⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) : ℝ) - 0) ≤
        ((1 : NNReal) : ℝ) - ((0 : NNReal) : ℝ) := by
    simpa [max_eq_left hT] using hTL
  obtain ⟨σ, hσ0, hσ⟩ := (IsPicardLindelof.of_time_independent (fun x hx => hL x (hy' hx))
    (hK.mono hy') hm).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨σ, hσ0, hσ⟩

/-- **Global forward existence under a trapping Lyapunov function** (the existence half of MLS's
standing assumption, p. 179, for a field that is only locally Lipschitz, as for the PD closed loop
of p. 193 with its total energy as `V`): if `F` is locally Lipschitz on a proper normed space,
`V` has compact sublevel sets, and `V` does not increase along any solution on any
interval `[0, T]` (derivatives within `[0, T]`), then from every `x₀` there is a curve `γ` with
`γ 0 = x₀` that solves `ẋ = F(x)` from time `0`. The system is `fun _ => F`; `IsSolution` asks
continuity on `[0, ∞)` and the actual derivative `F(γ t)` at every `t > 0`. -/
theorem exists_isSolution_of_lyapunov {F : E → E} (hF : LocallyLipschitz F) {V : E → ℝ}
    (hcpt : ∀ c, IsCompact {x | V x ≤ c})
    (hdec : ∀ T, 0 ≤ T → ∀ γ : ℝ → E,
      (∀ s ∈ Set.Icc 0 T, HasDerivWithinAt γ (F (γ s)) (Set.Icc 0 T) s) →
      ∀ s ∈ Set.Icc 0 T, V (γ s) ≤ V (γ 0))
    (x₀ : E) : ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsSolution (fun _ => F) 0 γ := by
  set S : Set E := {x | V x ≤ V x₀} with hS
  have hS₁ : IsCompact (cthickening 1 S) := (hcpt (V x₀)).cthickening
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS₁ hF.locallyLipschitzOn
  obtain ⟨C, hC⟩ := hS₁.exists_bound_of_continuousOn hF.continuous.continuousOn
  set L : NNReal := C.toNNReal
  have hL : ∀ x ∈ cthickening 1 S, ‖F x‖ ≤ L := fun x hx =>
    (hC x hx).trans (Real.le_coe_toNNReal C)
  set h : ℝ := 1 / (2 * ((L : ℝ) + 1)) with hh
  have hpos : 0 < h := by positivity
  have hTL : (L : ℝ) * (2 * h) ≤ 1 := by
    have : (L : ℝ) * (2 * h) = L / (L + 1) := by rw [hh]; field_simp
    rw [this, div_le_one (by positivity)]
    linarith
  have hloc : ∀ y, ∃ σ : ℝ → E, y ∈ S →
      σ 0 = y ∧ ∀ t ∈ Icc 0 (2 * h), HasDerivWithinAt σ (F (σ t)) (Icc 0 (2 * h)) t := by
    intro y
    by_cases hy : y ∈ S
    · obtain ⟨σ, h0, hd⟩ := exists_local_of_lipschitzOnWith hK hL (by positivity) hTL
        (closedBall_subset_cthickening hy 1)
      exact ⟨σ, fun _ => ⟨h0, hd⟩⟩
    · exact ⟨fun _ => y, fun h => absurd h hy⟩
  choose σ hσ using hloc
  -- the local solutions from `S` stay in `S`, where `F` is `K`-Lipschitz
  have hσS : ∀ y ∈ S, ∀ t ∈ Icc 0 (2 * h), σ y t ∈ S := by
    intro y hy t ht
    have := hdec (2 * h) (by positivity) (σ y) (hσ y hy).2 t ht
    rw [(hσ y hy).1] at this
    exact this.trans hy
  have hKS : LipschitzOnWith K F S := hK.mono (self_subset_cthickening S)
  have hcont : ∀ z ∈ S, ContinuousOn (σ z) (Icc 0 (2 * h)) := fun z hz t ht =>
    ((hσ z hz).2 t ht).continuousWithinAt
  -- consecutive pieces agree on their overlap
  have hagree : ∀ y ∈ S, ∀ s ∈ Icc 0 h, σ (σ y h) s = σ y (s + h) := by
    intro y hy
    have hy' : σ y h ∈ S := hσS y hy h ⟨hpos.le, by linarith⟩
    refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => S)
      (fun _ _ => hKS) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (hcont _ hy').mono (Icc_subset_Icc le_rfl (by linarith))
    · intro t ht
      exact (((hσ _ hy').2 t ⟨ht.1, by linarith [ht.2]⟩).mono
        (Icc_subset_Icc ht.1 le_rfl)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith [ht.2]))
    · exact fun t ht => hσS _ hy' t ⟨ht.1, by linarith [ht.2]⟩
    · exact (hcont y hy).comp (continuous_id.add continuous_const).continuousOn
        (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    · intro t ht
      exact ((((hσ y hy).2 (t + h) ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))).comp_add_const t
        h).hasDerivWithinAt
    · exact fun t ht => hσS y hy (t + h) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · simp [(hσ _ hy').1]
  exact exists_isSolution_of_glue hpos (fun y hy => (hσ y hy).1) (fun y hy => (hσ y hy).2)
    (fun y hy => hσS y hy h ⟨hpos.le, by linarith⟩) hagree (show x₀ ∈ S by simp [hS])

/-- **A locally Lipschitz autonomous field trapped by a Lyapunov function has a solution flow**
(MLS's standing existence and uniqueness assumption, p. 179, as used for eq. (4.46), p. 188, and
intended for the PD closed loop of p. 193 with its total energy as `V`): under the hypotheses of
`exists_isSolution_of_lyapunov` there is `φ` with `HasFlow F φ`. Existence is
`exists_isSolution_of_lyapunov`; uniqueness of solutions from every `t₀ ≥ 0` and continuous
dependence on the initial state come from Grönwall's bound on a compact sublevel set of `V`, which
contains both trajectories. The system is `fun _ => F`, solutions from time `0`. -/
theorem exists_hasFlow_of_lyapunov {F : E → E} (hF : LocallyLipschitz F) {V : E → ℝ}
    (hV : Continuous V) (hcpt : ∀ c, IsCompact {x | V x ≤ c})
    (hdec : ∀ T, 0 ≤ T → ∀ γ : ℝ → E,
      (∀ s ∈ Set.Icc 0 T, HasDerivWithinAt γ (F (γ s)) (Set.Icc 0 T) s) →
      ∀ s ∈ Set.Icc 0 T, V (γ s) ≤ V (γ 0)) :
    ∃ φ : ℝ → E → E, HasFlow F φ := by
  choose γ hγ0 hγ using exists_isSolution_of_lyapunov hF hcpt hdec
  refine ⟨fun t x => γ x t, ⟨hγ0, hγ, ?_, ?_⟩⟩
  · intro t₀ _ x hx t ht
    have hy : IsSolution (fun _ => F) t₀ (fun s => γ (x t₀) (s - t₀)) := by
      simpa using (hγ (x t₀)).comp_sub_const t₀
    obtain ⟨K, hK⟩ := exists_dist_le_of_lyapunov hF hcpt hdec (V (x t₀))
    have := hK t₀ x _ hx hy le_rfl (by simp [hγ0]) t ht
    simp only [sub_self, hγ0, dist_self, zero_mul] at this
    exact dist_le_zero.mp this
  · intro t ht
    refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨K, hK⟩ := exists_dist_le_of_lyapunov hF hcpt hdec (V x₀ + 1)
    have hU : IsOpen {y | V y < V x₀ + 1} := isOpen_lt hV continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ (by simp)
    refine continuousAt_of_locally_lipschitz hr (Real.exp (K * t)) fun y hy => ?_
    have h1 : V y ≤ V x₀ + 1 := le_of_lt (hball hy)
    have := hK 0 (fun s => γ y s) (fun s => γ x₀ s) (hγ y) (hγ x₀) (by simpa [hγ0] using h1)
      (by simp [hγ0]) t ht
    simp only [hγ0, sub_zero] at this
    rwa [mul_comm]

end Stability
end RoboLean
