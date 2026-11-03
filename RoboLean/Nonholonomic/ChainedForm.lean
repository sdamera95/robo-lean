import RoboLean.Nonholonomic.Controllability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The one-chain system: MLS Chapter 8, §2.3

MLS Chapter 8, printed pp. 364–365: the one-chain system (8.7)
`q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₂ u₁, …, q̇ₙ = qₙ₋₁ u₁`, its input fields (8.8)
`g₁ = (1, 0, q₂, …, qₙ₋₁)`, `g₂ = (0, 1, 0, …, 0)`, the iterated brackets
`ad_{g₁} g₂ = [g₁, g₂]`, `ad^k_{g₁} g₂ = [g₁, ad^{k−1}_{g₁} g₂]` (p. 364), Lemma 8.1
(`ad^k_{g₁} g₂ = (−1)^k e_{k+2}` for `k ≥ 1`) and Proposition 8.2 (the one-chain system is
completely nonholonomic: `g₁, g₂, ad^i_{g₁} g₂`, `1 ≤ i ≤ n − 2`, are independent, p. 365).

**Conventions.** The state space is `Fin n → ℝ`; the book's coordinate `qᵢ` is the entry with
index `i − 1`, so `q₁` is entry `0`, `q₂` entry `1` and `q_{k+2}` entry `k + 1`. `chainBasis n j`
is the vector with entry `1` at index `j` and `0` elsewhere; it is the zero vector when `j ≥ n`.
The bracket is the library's (Mathlib's `lieBracket`, the book's sign, p. 324). Inputs and
trajectories are those of the drift-free system (7.10) (`driftFree`, `IsTrajectory`); the input
of a trajectory may be any function of time, not only a piecewise constant one.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS p. 364: the iterated bracket `ad^k_f g`,** `ad^0_f g = g` and
`ad^{k+1}_f g = [f, ad^k_f g]`. -/
def adIter (f : E → E) (k : ℕ) (g : E → E) : E → E := (fun h => lieBracket ℝ f h)^[k] g

/-- **MLS p. 364:** `ad^{k+1}_f g = [f, ad^k_f g]`. -/
theorem adIter_succ (f : E → E) (k : ℕ) (g : E → E) :
    adIter f (k + 1) g = lieBracket ℝ f (adIter f k g) := by
  exact Function.iterate_succ_apply' _ k g

/-- **MLS p. 364:** `ad^k_{g₁} g₂` spans the level `k + 1` of the filtration of p. 340, for
generators `g` with `g₁ = g 0`. -/
theorem adIter_mem_filtrationFields {m : ℕ} (g : Fin m → E → E) (i₀ i : Fin m) (k : ℕ) :
    adIter (g i₀) k (g i) ∈ filtrationFields g (k + 1) := by
  induction k with
  | zero =>
    rw [filtrationFields_one]
    exact Set.mem_range_self i
  | succ k ih =>
    rw [adIter_succ]
    exact lieBracket_mem_filtrationFields g i₀ ih

/-- **MLS eq. (8.8), p. 364: the unit vector `e_{j+1}`** of `ℝⁿ` (index `j`, zero when `j ≥ n`). -/
def chainBasis (n j : ℕ) : Fin n → ℝ := fun i => if i.val = j then 1 else 0

/-- **MLS eq. (8.8), p. 364:** `chainBasis n j` is the zero vector when `j ≥ n`. -/
theorem chainBasis_eq_zero {n j : ℕ} (h : n ≤ j) : chainBasis n j = 0 := by
  funext i
  have : i.val ≠ j := by omega
  simp [chainBasis, this]

/-- **MLS eq. (8.8), p. 364: the linear part of `g₁`,** `q ↦ (0, 0, q₂, …, qₙ₋₁)`. -/
def chainShift (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q i => if h : 2 ≤ i.val then q ⟨i.val - 1, by omega⟩ else 0
      map_add' := by
        intro q r
        funext i
        by_cases h : 2 ≤ i.val <;> simp [h]
      map_smul' := by
        intro c q
        funext i
        by_cases h : 2 ≤ i.val <;> simp [h] }

/-- **MLS eq. (8.8), p. 364: the input field `g₁ = (1, 0, q₂, q₃, …, qₙ₋₁)`** of the one-chain
system. -/
def chainG1 (n : ℕ) (q : Fin n → ℝ) : Fin n → ℝ := chainBasis n 0 + chainShift n q

/-- **MLS eq. (8.8), p. 364: the input field `g₂ = (0, 1, 0, …, 0)`** of the one-chain system. -/
def chainG2 (n : ℕ) (_q : Fin n → ℝ) : Fin n → ℝ := chainBasis n 1

/-- **MLS eqs. (8.7)–(8.8), p. 364: the input fields `(g₁, g₂)` of the one-chain system.** -/
def chainFields (n : ℕ) : Fin 2 → (Fin n → ℝ) → Fin n → ℝ := ![chainG1 n, chainG2 n]

/-- The entries of `chainShift` (supporting lemma for MLS eq. (8.8), p. 364). -/
private theorem chainShift_apply (n : ℕ) (q : Fin n → ℝ) (i : Fin n) :
    chainShift n q i = if h : 2 ≤ i.val then q ⟨i.val - 1, by omega⟩ else 0 := by
  rfl

/-- The right-hand side of (8.7) entry by entry (supporting lemma for MLS eq. (8.7), p. 364). -/
private theorem chain_driftFree_apply (n : ℕ) (q : Fin n → ℝ) (u : Fin 2 → ℝ) (i : Fin n) :
    driftFree (chainFields n) q u i =
      u 0 * (chainBasis n 0 i + chainShift n q i) + u 1 * chainBasis n 1 i := by
  simp [driftFree, Fin.sum_univ_two, chainFields, chainG1, chainG2]

/-- **MLS eq. (8.7), p. 364: `q̇₁ = u₁`,** the entry with index `0` of the right-hand side. -/
theorem chain_driftFree_of_val_eq_zero {n : ℕ} (q : Fin n → ℝ) (u : Fin 2 → ℝ) {i : Fin n}
    (hi : i.val = 0) : driftFree (chainFields n) q u i = u 0 := by
  rw [chain_driftFree_apply, chainShift_apply]
  simp [chainBasis, hi]

/-- **MLS eq. (8.7), p. 364: `q̇₂ = u₂`,** the entry with index `1` of the right-hand side. -/
theorem chain_driftFree_of_val_eq_one {n : ℕ} (q : Fin n → ℝ) (u : Fin 2 → ℝ) {i : Fin n}
    (hi : i.val = 1) : driftFree (chainFields n) q u i = u 1 := by
  rw [chain_driftFree_apply, chainShift_apply]
  simp [chainBasis, hi]

/-- **MLS eq. (8.7), p. 364: `q̇ᵢ₊₁ = qᵢ u₁` for `i ≥ 2`,** the entry with index `j + 1`,
`j ≥ 1`, of the right-hand side. -/
theorem chain_driftFree_of_val_eq_succ {n : ℕ} (q : Fin n → ℝ) (u : Fin 2 → ℝ) {i j : Fin n}
    (hij : i.val = j.val + 1) (hj : 1 ≤ j.val) : driftFree (chainFields n) q u i = u 0 * q j := by
  rw [chain_driftFree_apply, chainShift_apply]
  have h2 : 2 ≤ i.val := by omega
  have hj' : (⟨i.val - 1, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  simp [chainBasis, h2, hj', show i.val ≠ 0 by omega, show i.val ≠ 1 by omega]

/-- **MLS Lemma 8.1, p. 364: `ad^k_{g₁} g₂ = (−1)^k e_{k+2}`** for the fields (8.8), for every
`k` (the book states `k ≥ 1`; `k = 0` is `g₂ = e₂`). The field is constant; `e_{k+2}` is the zero
vector when `k + 2 > n`. -/
theorem chain_adIter (n k : ℕ) :
    adIter (chainG1 n) k (chainG2 n) = fun _ => (-1 : ℝ) ^ k • chainBasis n (k + 1) := by
  have hD : ∀ q, HasFDerivAt (chainG1 n) (chainShift n) q := fun q =>
    (chainShift n).hasFDerivAt.const_add (chainBasis n 0)
  have hS : ∀ j, 1 ≤ j → chainShift n (chainBasis n j) = chainBasis n (j + 1) := by
    intro j hj
    funext i
    rw [chainShift_apply]
    simp only [chainBasis]
    by_cases h : 2 ≤ i.val
    · by_cases h' : i.val = j + 1
      · simp [h']
        omega
      · simp [h, h', show i.val - 1 ≠ j by omega]
    · simp [h, show i.val ≠ j + 1 by omega]
  induction k with
  | zero =>
    funext q
    simp [adIter, chainG2]
  | succ k ih =>
    rw [adIter_succ, ih]
    funext q
    rw [lieBracket, (hasFDerivAt_const _ q).fderiv, (hD q).fderiv, map_smul,
      hS (k + 1) (by omega), pow_succ]
    simp [mul_comm]

/-- A subspace containing `g₁(q)` and `e₂, …, eₙ` is `ℝⁿ` (supporting lemma for MLS Proposition
8.2, p. 365). -/
private theorem chain_eq_top_of_mem {n : ℕ} {q : Fin n → ℝ} (W : Submodule ℝ (Fin n → ℝ))
    (h1 : ∀ j : Fin n, 1 ≤ j.val → chainBasis n j.val ∈ W) (h0 : chainG1 n q ∈ W) : W = ⊤ := by
  have hb : ∀ i : Fin n, (fun j => if i = j then (1 : ℝ) else 0) = chainBasis n i.val := by
    intro i
    funext j
    simp [chainBasis, Fin.ext_iff, eq_comm]
  have hsh : chainShift n q ∈ W := by
    rw [pi_eq_sum_univ (chainShift n q)]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hb]
    by_cases hi : i.val = 0
    · rw [chainShift_apply]
      simp [show ¬ 2 ≤ i.val by omega]
    · exact Submodule.smul_mem _ _ (h1 i (by omega))
  have he0 : ∀ i : Fin n, i.val = 0 → chainBasis n i.val ∈ W := by
    intro i hi
    have : chainBasis n 0 = chainG1 n q - chainShift n q := by simp [chainG1]
    rw [hi, this]
    exact Submodule.sub_mem _ h0 hsh
  rw [Submodule.eq_top_iff']
  intro x
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  rw [hb]
  by_cases hi : i.val = 0
  · exact he0 i hi
  · exact h1 i (by omega)

/-- `e_{j+1} = (−1)^j ad^j_{g₁} g₂ (q)` (supporting lemma for MLS Lemma 8.1, p. 364). -/
private theorem chainBasis_eq_smul_adIter (n j : ℕ) (q : Fin n → ℝ) :
    chainBasis n (j + 1) = (-1 : ℝ) ^ j • adIter (chainG1 n) j (chainG2 n) q := by
  rw [chain_adIter, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- **MLS Proposition 8.2, p. 365, the rank computation:** the values at `q` of `g₁`, `g₂` and
`ad^i_{g₁} g₂`, `1 ≤ i ≤ n − 2`, span `ℝⁿ`: level `n − 1` of the filtration is `ℝⁿ` at every
point, for `n ≥ 2` (for `n = 1` level `0` is the zero subspace). -/
theorem chain_filtrationAt_eq_top {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) :
    filtrationAt (chainFields n) (n - 1) q = ⊤ := by
  refine chain_eq_top_of_mem (q := q) _ (fun j hj => ?_) ?_
  · have := j.isLt
    have hmem := adIter_mem_filtrationFields (chainFields n) 0 1 (j.val - 1)
    have hle := filtrationFields_mono (chainFields n) (show j.val - 1 + 1 ≤ n - 1 by omega) hmem
    have hj' : j.val = j.val - 1 + 1 := by omega
    rw [hj', chainBasis_eq_smul_adIter n _ q]
    exact Submodule.smul_mem _ _ (mem_spanAt hle q)
  · have h1 : chainG1 n ∈ filtrationFields (chainFields n) 1 := by
      rw [filtrationFields_one]
      exact Set.mem_range_self (0 : Fin 2)
    exact mem_spanAt (filtrationFields_mono (chainFields n) (by omega) h1) q

/-- **MLS Proposition 8.2, p. 365: the one-chain system satisfies the controllability rank
condition** of Theorem 7.5 (p. 329): `L(g₁, g₂)` has rank `n` at every point. -/
theorem chain_lieAlgebraAt_eq_top (n : ℕ) (q : Fin n → ℝ) :
    lieAlgebraAt (chainFields n) q = ⊤ := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [Submodule.eq_top_iff']
    intro x
    interval_cases n
    · exact Subsingleton.elim x 0 ▸ zero_mem _
    · have hg : chainG1 1 ∈ {f | InLieAlgebra (chainFields 1) f} := InLieAlgebra.gen 0
      have hx : x = x 0 • chainG1 1 q := by
        funext i
        fin_cases i
        simp [chainG1, chainBasis, chainShift_apply]
      rw [hx]
      exact Submodule.smul_mem _ _ (mem_spanAt hg q)
  · exact lieAlgebraAt_eq_top_of_filtrationAt (chainFields n) (chain_filtrationAt_eq_top hn q)

/-- **MLS Proposition 8.2, p. 365, "controllable", from Chow's theorem taken as the named
statement `ChowStatement` (MLS Theorem 7.5, p. 329, not proved):** if Chow's theorem holds on
`ℝⁿ`, the one-chain system with unconstrained inputs is locally controllable at every point. -/
theorem chain_isLocallyControllableAt {n : ℕ} (hC : ChowStatement (Fin n → ℝ)) (q : Fin n → ℝ) :
    IsLocallyControllableAt (chainFields n) Set.univ q := by
  refine hC 2 (chainFields n) (fun j => ?_) q (chain_lieAlgebraAt_eq_top n q)
  fin_cases j
  · exact contDiff_const.add (chainShift n).contDiff
  · exact contDiff_const

/-- **MLS Proposition 8.2, p. 365, the book's form:** the `n` vectors `g₁(q)`, `g₂(q)` and
`ad^i_{g₁} g₂ (q)`, `1 ≤ i ≤ n − 2`, are linearly independent at every `q` (listed as `g₁(q)`
at index `0` and `ad^{j−1}_{g₁} g₂ (q)` at index `j ≥ 1`). -/
theorem chain_linearIndependent (n : ℕ) (q : Fin n → ℝ) :
    LinearIndependent ℝ (fun j : Fin n =>
      if j.val = 0 then chainG1 n q else adIter (chainG1 n) (j.val - 1) (chainG2 n) q) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
  have h1 : ∀ j : Fin n, 1 ≤ j.val → chainBasis n j.val ∈ Submodule.span ℝ (Set.range
      (fun j : Fin n => if j.val = 0 then chainG1 n q
        else adIter (chainG1 n) (j.val - 1) (chainG2 n) q)) := by
    intro j hj
    have hj' : j.val = j.val - 1 + 1 := by omega
    rw [hj', chainBasis_eq_smul_adIter n _ q]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
    simp [show j.val ≠ 0 by omega]
  have h0 : chainG1 n q ∈ Submodule.span ℝ (Set.range
      (fun j : Fin n => if j.val = 0 then chainG1 n q
        else adIter (chainG1 n) (j.val - 1) (chainG2 n) q)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Subsingleton.elim (chainG1 0 q) 0]
      exact zero_mem _
    · exact Submodule.subset_span ⟨⟨0, hn⟩, by simp⟩
  rw [chain_eq_top_of_mem _ h1 h0]

/-- **MLS p. 329: a curve with a derivative at every time is a trajectory** of (7.10) on
`[0, T]`. -/
theorem IsTrajectory.of_hasDerivAt {m : ℕ} {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {x : ℝ → E}
    (T : ℝ) (hx : ∀ t, HasDerivAt x (driftFree g (x t) (u t)) t) : IsTrajectory g u T x := by
  exact ⟨fun t _ => (hx t).continuousAt.continuousWithinAt, ∅, fun t _ _ => hx t⟩

/-- **MLS eq. (8.7), p. 364, and the proof of Proposition 8.3, p. 366: trajectories exist.** For
continuous inputs and every initial state the one-chain system has a solution defined for all
times, given by iterated integrals (`q₁ = q₁(0) + ∫ u₁`, `q₂ = q₂(0) + ∫ u₂`,
`qᵢ₊₁ = qᵢ₊₁(0) + ∫ qᵢ u₁`). -/
theorem chain_exists_solution (n : ℕ) {u : ℝ → Fin 2 → ℝ} (hu : Continuous u) (q₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, x 0 = q₀ ∧
      ∀ t, HasDerivAt x (driftFree (chainFields n) (x t) (u t)) t := by
  have hu0 : Continuous fun t => u t 0 := (continuous_apply 0).comp hu
  have hu1 : Continuous fun t => u t 1 := (continuous_apply 1).comp hu
  let c : ℕ → ℝ := fun i => if h : i < n then q₀ ⟨i, h⟩ else 0
  let y : ℕ → ℝ → ℝ := fun i => Nat.rec (motive := fun _ => ℝ → ℝ)
    (fun t => c 0 + ∫ s in (0 : ℝ)..t, u s 0)
    (fun i yi => if i = 0 then fun t => c 1 + ∫ s in (0 : ℝ)..t, u s 1
      else fun t => c (i + 1) + ∫ s in (0 : ℝ)..t, yi s * u s 0) i
  have hprim : ∀ {f : ℝ → ℝ}, Continuous f → ∀ (a t : ℝ),
      HasDerivAt (fun t => a + ∫ s in (0 : ℝ)..t, f s) (f t) t := fun hf a t =>
    ((hf.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add a
  have hy0 : y 0 = fun t => c 0 + ∫ s in (0 : ℝ)..t, u s 0 := rfl
  have hy1 : y 1 = fun t => c 1 + ∫ s in (0 : ℝ)..t, u s 1 := rfl
  have hy2 : ∀ i, y (i + 2) = fun t => c (i + 2) + ∫ s in (0 : ℝ)..t, y (i + 1) s * u s 0 :=
    fun i => by simp [y]
  have hcont : ∀ i, Continuous (y i) := by
    intro i
    induction i with
    | zero => exact continuous_iff_continuousAt.2 fun t => (hprim hu0 _ t).continuousAt
    | succ i ih =>
      rcases i with _ | i
      · exact continuous_iff_continuousAt.2 fun t => (hprim hu1 _ t).continuousAt
      · rw [hy2]
        exact continuous_iff_continuousAt.2 fun t => (hprim (ih.mul hu0) _ t).continuousAt
  refine ⟨fun t i => y i.val t, ?_, fun t => ?_⟩
  · funext i
    obtain ⟨i, hi⟩ := i
    rcases i with _ | _ | i
    · simp [hy0, c, hi]
    · simp [hy1, c, hi]
    · simp [hy2, c, hi]
  · rw [hasDerivAt_pi]
    intro i
    obtain ⟨i, hi⟩ := i
    rcases i with _ | _ | i
    · rw [chain_driftFree_of_val_eq_zero _ _ rfl]
      exact hprim hu0 _ t
    · rw [chain_driftFree_of_val_eq_one _ _ rfl]
      exact hprim hu1 _ t
    · rw [chain_driftFree_of_val_eq_succ (j := ⟨i + 1, by omega⟩) _ _ rfl (by simp)]
      show HasDerivAt (y (i + 2)) _ t
      rw [hy2, mul_comm]
      exact hprim ((hcont (i + 1)).mul hu0) _ t

end Nonholonomic
end RoboLean
