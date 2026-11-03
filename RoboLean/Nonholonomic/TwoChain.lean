import RoboLean.Nonholonomic.Steering
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The two-input two-chained system: MLS Chapter 8, Exercise 5

MLS Chapter 8, Exercise 5, printed p. 392: the two-input, two-chained system
`ẋ₀ = u₁, ẋ₁ = y₀u₁, …, ẋ_{n_x} = x_{n_x−1}u₁` and `ẏ₀ = u₂, (ẏ₁ = x₀u₂), …,
ẏ_{n_y} = y_{n_y−1}u₂`, "where `y₁ := x₀y₀ − x₁` to account for skew-symmetry of the Lie bracket";
(a) controllability; (b) the inputs `u₁ = a sin 2πt`, `u₂ = b cos 2πkt` and the final value of
`q_k`, `k ≥ 1`, with an explicit formula in `(a, b)`; (c) the inputs `u₁ = b cos 2πkt`,
`u₂ = a sin 2πt` for `y_k`, `k ≥ 2`; (d) an algorithm.

**What is formalized.** The state is `(x, w)` with `x = (x₀, y₀, x₁, …, x_{n+1}) ∈ ℝⁿ⁺³` (so
`n_x = n + 1 ≥ 1`) and `w = (y₂, …, y_{p+1}) ∈ ℝᵖ` (so `n_y = p + 1`); `y₁ = x₀y₀ − x₁` is not a
state, as printed, and `ẏ₂ = y₁u₂`.
* (a) The controllability rank condition at every point (the reading of "controllable" used by the
  library, Theorem 7.5, p. 329): `ad^k_{g₁}g₂ = (−1)^k e_{x_k}` and `ad^k_{g₂}g₁ = (−1)^k e_{y_k}`
  (`k ≥ 2`) are constant fields, and with `g₁, g₂` they span the state space.
* The coordinates `(x₀, y₀, x₁, …)` of a trajectory form a trajectory of the one-chain system
  (8.7), and the coordinates `(y₀, x₀, y₁, y₂, …)` form one with the inputs exchanged; trajectories
  exist for continuous inputs from every initial state.
* (b), reading the printed `q_k` as `x_k`: from any initial state, `u₁ = a sin 2πt`,
  `u₂ = b cos 2πkt` returns `x₀, y₀, x₁, …, x_{k−1}` and moves `x_k` by `(a/4π)^k b/k!`.
* (c) From any initial state, `u₁ = b cos 2πkt`, `u₂ = a sin 2πt` returns `y₀, x₀, y₁, …, y_{k−1}`
  and moves `y_k` by `(a/4π)^k b/k!`, `k ≥ 2`.
* (d) is not formalized: a step for `x_k` also moves the `y`-coordinates and conversely, and the
  book gives no algorithm to compare against.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

variable {n p : ℕ}

/-- **MLS Chapter 8, Exercise 5, p. 392: the state `(x, w)`** with `x = (x₀, y₀, x₁, …, x_{n+1})`
and `w = (y₂, …, y_{p+1})`. -/
abbrev TwoChainState (n p : ℕ) := (Fin (n + 3) → ℝ) × (Fin p → ℝ)

/-- **MLS Chapter 8, Exercise 5, p. 392: `y₁ := x₀y₀ − x₁`.** -/
def twoChainY1 (x : Fin (n + 3) → ℝ) : ℝ := x 0 * x 1 - x 2

/-- **MLS Chapter 8, Exercise 5, p. 392: the shift `w ↦ (0, y₂, …, y_p)`** of the `y`-chain. -/
def twoChainShift (p : ℕ) : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w j => if h : 1 ≤ j.val then w ⟨j.val - 1, by omega⟩ else 0
      map_add' := by
        intro v w
        funext j
        by_cases h : 1 ≤ j.val <;> simp [h]
      map_smul' := by
        intro c w
        funext j
        by_cases h : 1 ≤ j.val <;> simp [h] }

/-- **MLS Chapter 8, Exercise 5, p. 392: `g₁`,** `ẋ₀ = 1, ẋ₁ = y₀, ẋᵢ₊₁ = xᵢ`, zero on the
`y`-chain. -/
def twoChainG1 (z : TwoChainState n p) : TwoChainState n p := (chainG1 (n + 3) z.1, 0)

/-- **MLS Chapter 8, Exercise 5, p. 392: `g₂`,** `ẏ₀ = 1, ẏ₂ = y₁ = x₀y₀ − x₁, ẏᵢ₊₁ = yᵢ`. -/
def twoChainG2 (z : TwoChainState n p) : TwoChainState n p :=
  (chainG2 (n + 3) z.1, twoChainY1 z.1 • chainBasis p 0 + twoChainShift p z.2)

/-- **MLS Chapter 8, Exercise 5, p. 392: the input fields `(g₁, g₂)`.** -/
def twoChainFields : Fin 2 → TwoChainState n p → TwoChainState n p := ![twoChainG1, twoChainG2]

/-- The value of the index `2` (supporting lemma for MLS p. 392). -/
private theorem val_two_fin (m : ℕ) : ((2 : Fin (m + 3)) : ℕ) = 2 := by
  show 2 % (m + 3) = 2
  exact Nat.mod_eq_of_lt (by omega)

/-- The value of the index `1` (supporting lemma for MLS p. 392). -/
private theorem val_one_fin (m : ℕ) : ((1 : Fin (m + 3)) : ℕ) = 1 := by
  show 1 % (m + 3) = 1
  exact Nat.mod_eq_of_lt (by omega)

/-- The entries of `g₁` on the shared coordinates (supporting lemma for MLS p. 392). -/
private theorem chainG1_shared (x : Fin (n + 3) → ℝ) :
    chainG1 (n + 3) x 0 = 1 ∧ chainG1 (n + 3) x 1 = 0 ∧ chainG1 (n + 3) x 2 = x 1 := by
  refine ⟨by simp [chainG1, chainBasis, chainShift, LinearMap.toContinuousLinearMap],
    by simp [chainG1, chainBasis, chainShift, LinearMap.toContinuousLinearMap], ?_⟩
  simp only [chainG1, Pi.add_apply, chainBasis]
  rw [show chainShift (n + 3) x 2 = if h : 2 ≤ (2 : Fin (n + 3)).val then
    x ⟨(2 : Fin (n + 3)).val - 1, by omega⟩ else 0 from rfl]
  simp only [val_two_fin n]
  simp

/-- The entries of the `y`-shift (supporting lemma for MLS p. 392). -/
private theorem twoChainShift_apply (w : Fin p → ℝ) (j : Fin p) :
    twoChainShift p w j = if h : 1 ≤ j.val then w ⟨j.val - 1, by omega⟩ else 0 := rfl

/-- The entries of the chain shift (supporting lemma for MLS p. 392). -/
private theorem chainShift_apply' (m : ℕ) (q : Fin m → ℝ) (i : Fin m) :
    chainShift m q i = if h : 2 ≤ i.val then q ⟨i.val - 1, by omega⟩ else 0 := rfl

/-- **MLS Chapter 8, Exercise 5, p. 392: the system.** The `x`-part of `u₁g₁ + u₂g₂` is the
right-hand side of the one-chain system (8.7) in `(x₀, y₀, x₁, …)`, and the `w`-part is
`u₂(y₁, y₂, …, y_p)`. -/
theorem twoChain_driftFree (z : TwoChainState n p) (u : Fin 2 → ℝ) :
    driftFree twoChainFields z u =
      (driftFree (chainFields (n + 3)) z.1 u,
        u 1 • (twoChainY1 z.1 • chainBasis p 0 + twoChainShift p z.2)) := by
  simp [driftFree, Fin.sum_univ_two, twoChainFields, twoChainG1, twoChainG2, chainFields]

/-- The derivative of `g₁`, a constant plus a linear map (supporting lemma for MLS p. 392). -/
private theorem hasFDerivAt_twoChainG1 (z : TwoChainState n p) :
    HasFDerivAt twoChainG1
      (((chainShift (n + 3)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        (0 : TwoChainState n p →L[ℝ] Fin p → ℝ)) z := by
  have h1 := (ContinuousLinearMap.hasFDerivAt
    (f := (chainShift (n + 3)).comp (ContinuousLinearMap.fst ℝ (Fin (n + 3) → ℝ) (Fin p → ℝ)))
    (x := z)).const_add (chainBasis (n + 3) 0)
  exact h1.prodMk (hasFDerivAt_const 0 z)

/-- The derivative of `g₂` on a vector `c` (supporting lemma for MLS p. 392):
`Dg₂(z)c = (0, (c_{x₀}y₀ + x₀c_{y₀} − c_{x₁}) e_{y₂} + shift c_w)`. -/
private theorem fderiv_twoChainG2_apply (z c : TwoChainState n p) :
    fderiv ℝ twoChainG2 z c =
      (0, (c.1 0 * z.1 1 + z.1 0 * c.1 1 - c.1 2) • chainBasis p 0 + twoChainShift p c.2) := by
  have hp : ∀ i : Fin (n + 3), HasFDerivAt (fun z : TwoChainState n p => z.1 i)
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)) z := fun i =>
    ContinuousLinearMap.hasFDerivAt (f := (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin (n + 3) → ℝ) (Fin p → ℝ))) (x := z)
  have hφ := ((hp 0).mul (hp 1)).sub (hp 2)
  have hw : HasFDerivAt (fun z : TwoChainState n p => twoChainShift p z.2)
      ((twoChainShift p).comp (ContinuousLinearMap.snd ℝ _ _)) z :=
    ContinuousLinearMap.hasFDerivAt (f := (twoChainShift p).comp
      (ContinuousLinearMap.snd ℝ (Fin (n + 3) → ℝ) (Fin p → ℝ))) (x := z)
  have h := (hasFDerivAt_const (chainBasis (n + 3) 1) z).prodMk
    ((hφ.smul_const (chainBasis p 0)).add hw)
  have h' : HasFDerivAt twoChainG2 _ z := h
  rw [h'.fderiv]
  ext x
  · simp
  · simp
    left
    ring

/-- `chainShift` moves `e_j` to `e_{j+1}` for `j ≥ 1` (supporting lemma for MLS p. 392). -/
private theorem chainShift_chainBasis (m j : ℕ) (hj : 1 ≤ j) :
    chainShift m (chainBasis m j) = chainBasis m (j + 1) := by
  funext i
  rw [chainShift_apply']
  simp only [chainBasis]
  by_cases h : 2 ≤ i.val
  · by_cases h' : i.val = j + 1
    · simp [h']
      omega
    · simp [h, h', show i.val - 1 ≠ j by omega]
  · simp [h, show i.val ≠ j + 1 by omega]

/-- The `y`-shift moves `e_j` to `e_{j+1}` (supporting lemma for MLS p. 392). -/
private theorem twoChainShift_chainBasis (j : ℕ) :
    twoChainShift p (chainBasis p j) = chainBasis p (j + 1) := by
  funext i
  rw [twoChainShift_apply]
  simp only [chainBasis]
  by_cases h : 1 ≤ i.val
  · by_cases h' : i.val = j + 1
    · simp [h']
    · simp [h, h', show i.val - 1 ≠ j by omega]
  · simp [h, show i.val ≠ j + 1 by omega]

/-- The bracket of a field with a constant field (supporting lemma for MLS p. 392). -/
private theorem lieBracket_const_right (f : TwoChainState n p → TwoChainState n p)
    (c : TwoChainState n p) (z : TwoChainState n p) :
    lieBracket ℝ f (fun _ => c) z = -fderiv ℝ f z c := by
  show fderiv ℝ (fun _ => c) z (f z) - fderiv ℝ f z c = _
  simp

/-- **MLS Chapter 8, Exercise 5(a), p. 392: `ad^k_{g₁}g₂ = (−1)^k e_{x_k}`** for `k ≥ 1`, a
constant field (`e_{x_k}` has index `k + 1` in `(x₀, y₀, x₁, …)`, zero when `k > n + 1`); the
`y`-chain does not enter. -/
theorem twoChain_adIter_g1 (k : ℕ) (hk : 1 ≤ k) :
    adIter (twoChainG1 (n := n) (p := p)) k twoChainG2 =
      fun _ => ((-1 : ℝ) ^ k • chainBasis (n + 3) (k + 1), 0) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [adIter_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · funext z
      show fderiv ℝ twoChainG2 z (twoChainG1 z) - fderiv ℝ twoChainG1 z (twoChainG2 z) = _
      rw [fderiv_twoChainG2_apply, (hasFDerivAt_twoChainG1 z).fderiv]
      have h2 : chainShift (n + 3) (chainBasis (n + 3) 1) = chainBasis (n + 3) 2 :=
        chainShift_chainBasis _ 1 le_rfl
      obtain ⟨c0, c1, c2⟩ := chainG1_shared z.1
      ext i
      · simp [twoChainG1, twoChainG2, chainG2, h2]
      · simp [twoChainG1, c0, c1, c2]
    · rw [ih hk0]
      funext z
      rw [lieBracket_const_right, (hasFDerivAt_twoChainG1 z).fderiv]
      ext i
      · simp [map_smul, chainShift_chainBasis _ (k + 1) (by omega), pow_succ]
      · simp

/-- **MLS Chapter 8, Exercise 5(a), p. 392: `ad_{g₂}g₁ = e_{x₁}`.** -/
theorem twoChain_adIter_g2_one :
    adIter (twoChainG2 (n := n) (p := p)) 1 twoChainG1 =
      fun _ => (chainBasis (n + 3) 2, 0) := by
  have h := twoChain_adIter_g1 (n := n) (p := p) 1 le_rfl
  funext z
  show lieBracket ℝ twoChainG2 twoChainG1 z = _
  rw [lieBracket_swap]
  have hz := congrFun h z
  simp only [adIter, Function.iterate_one] at hz
  rw [hz]
  ext <;> simp

/-- **MLS Chapter 8, Exercise 5(a), p. 392: `ad^k_{g₂}g₁ = (−1)^k e_{y_k}`** for `k ≥ 2`, a
constant field (`e_{y_k}` has index `k − 2` in `w = (y₂, …)`, zero when `k > p + 1`). -/
theorem twoChain_adIter_g2 (k : ℕ) (hk : 2 ≤ k) :
    adIter (twoChainG2 (n := n) (p := p)) k twoChainG1 =
      fun _ => (0, (-1 : ℝ) ^ k • chainBasis p (k - 2)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [adIter_succ]
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · rw [twoChain_adIter_g2_one]
      funext z
      rw [lieBracket_const_right, fderiv_twoChainG2_apply]
      ext i
      · simp
      · simp [chainBasis]
    · rw [ih hk2]
      funext z
      rw [lieBracket_const_right, fderiv_twoChainG2_apply]
      have hk' : k + 1 - 2 = k - 2 + 1 := by omega
      ext i
      · simp
      · simp [map_smul, twoChainShift_chainBasis, hk', pow_succ]

/-- `chainBasis m i.val` is the standard basis vector `Pi.single i 1` (supporting lemma for MLS
p. 392). -/
private theorem chainBasis_val {m : ℕ} (i : Fin m) : chainBasis m i.val = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [chainBasis]
  · simp [chainBasis, h, Fin.val_ne_of_ne h]

/-- Iterated brackets of the generators lie in `L(g₁, g₂)` (supporting lemma for MLS p. 392). -/
private theorem inLieAlgebra_adIter (a b : Fin 2) (k : ℕ) :
    InLieAlgebra (twoChainFields (n := n) (p := p)) (adIter (twoChainFields a) k (twoChainFields b)) := by
  induction k with
  | zero => exact InLieAlgebra.gen b
  | succ k ih =>
    rw [adIter_succ]
    exact InLieAlgebra.bracket (InLieAlgebra.gen a) ih

/-- **MLS Chapter 8, Exercise 5(a), p. 392 ("controllable"), with Theorem 7.5, p. 329: the
controllability rank condition** for the two-chained system at every point: `L(g₁, g₂)` spans the
state space. -/
theorem twoChain_lieAlgebraAt (z : TwoChainState n p) :
    lieAlgebraAt (twoChainFields (n := n) (p := p)) z = ⊤ := by
  set L := lieAlgebraAt (twoChainFields (n := n) (p := p)) z
  have hmem : ∀ f, InLieAlgebra (twoChainFields (n := n) (p := p)) f → f z ∈ L :=
    fun f hf => mem_spanAt (S := {f | InLieAlgebra twoChainFields f}) hf z
  have hx : ∀ i : Fin (n + 3), 2 ≤ i.val → ((Pi.single i 1 : Fin (n + 3) → ℝ), (0 : Fin p → ℝ)) ∈ L := by
    intro i hi
    have h := hmem _ (inLieAlgebra_adIter 0 1 (i.val - 1))
    have he := twoChain_adIter_g1 (n := n) (p := p) (i.val - 1) (by omega)
    simp only [twoChainFields, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [he, show i.val - 1 + 1 = i.val by omega, chainBasis_val] at h
    have h' := L.smul_mem ((-1 : ℝ) ^ (i.val - 1)) h
    convert h' using 1
    ext j <;> simp [smul_smul, ← pow_add, ← two_mul, pow_mul]
  have hy : ∀ j : Fin p, ((0 : Fin (n + 3) → ℝ), (Pi.single j 1 : Fin p → ℝ)) ∈ L := by
    intro j
    have h := hmem _ (inLieAlgebra_adIter 1 0 (j.val + 2))
    have he := twoChain_adIter_g2 (n := n) (p := p) (j.val + 2) (by omega)
    simp only [twoChainFields, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [he, show j.val + 2 - 2 = j.val by omega, chainBasis_val] at h
    have h' := L.smul_mem ((-1 : ℝ) ^ (j.val + 2)) h
    convert h' using 1
    ext k <;> simp [smul_smul, ← pow_add, ← two_mul, pow_mul]
  have hY : ∀ w : Fin p → ℝ, ((0 : Fin (n + 3) → ℝ), w) ∈ L := by
    intro w
    have hw : ((0 : Fin (n + 3) → ℝ), w) = ∑ j, w j • ((0 : Fin (n + 3) → ℝ), (Pi.single j 1 : Fin p → ℝ)) := by
      ext k
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hw]
    exact L.sum_mem fun j _ => L.smul_mem _ (hy j)
  have hX2 : ∀ v : Fin (n + 3) → ℝ, v 0 = 0 → v 1 = 0 → (v, (0 : Fin p → ℝ)) ∈ L := by
    intro v h0 h1
    have hv : (v, (0 : Fin p → ℝ)) = ∑ i, v i • ((Pi.single i 1 : Fin (n + 3) → ℝ), (0 : Fin p → ℝ)) := by
      ext k
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hv]
    refine L.sum_mem fun i _ => ?_
    by_cases hi : 2 ≤ i.val
    · exact L.smul_mem _ (hx i hi)
    · have : v i = 0 := by
        rcases (show i = 0 ∨ i = 1 by
          rcases i with ⟨_ | _ | _, _⟩ <;> simp_all) with rfl | rfl
        · exact h0
        · exact h1
      rw [this, zero_smul]
      exact L.zero_mem
  have hg1 : twoChainG1 z ∈ L := hmem _ (InLieAlgebra.gen 0)
  have hg2 : twoChainG2 z ∈ L := hmem _ (InLieAlgebra.gen 1)
  have he0 : ((Pi.single 0 1 : Fin (n + 3) → ℝ), (0 : Fin p → ℝ)) ∈ L := by
    have hs : (chainShift (n + 3) z.1, (0 : Fin p → ℝ)) ∈ L :=
      hX2 _ (by simp [chainShift_apply']) (by simp [chainShift_apply'])
    convert L.sub_mem hg1 hs using 1
    ext i
    · simp [twoChainG1, chainG1, ← chainBasis_val]
    · simp [twoChainG1]
  have he1 : ((Pi.single 1 1 : Fin (n + 3) → ℝ), (0 : Fin p → ℝ)) ∈ L := by
    convert L.sub_mem hg2 (hY (twoChainY1 z.1 • chainBasis p 0 + twoChainShift p z.2)) using 1
    ext i
    · simp [twoChainG2, chainG2, ← chainBasis_val]
    · simp [twoChainG2]
  have hX : ∀ v : Fin (n + 3) → ℝ, (v, (0 : Fin p → ℝ)) ∈ L := by
    intro v
    have hr := hX2 (v - v 0 • Pi.single 0 1 - v 1 • Pi.single 1 1) (by simp) (by simp)
    convert L.add_mem (L.add_mem hr (L.smul_mem (v 0) he0)) (L.smul_mem (v 1) he1) using 1
    ext i
    · simp
      ring
    · simp
  rw [eq_top_iff]
  rintro ⟨v, w⟩ -
  have := L.add_mem (hX v) (hY w)
  simpa using this

/-- **MLS Chapter 8, Exercise 5, p. 392: the `x`-chain.** The coordinates `(x₀, y₀, x₁, …)` of a
trajectory of the two-chained system form a trajectory of the one-chain system (8.7) with the same
inputs. -/
theorem IsTrajectory.twoChain_fst {u : ℝ → Fin 2 → ℝ} {T : ℝ} {z : ℝ → TwoChainState n p}
    (hz : IsTrajectory twoChainFields u T z) :
    IsTrajectory (chainFields (n + 3)) u T fun t => (z t).1 := by
  obtain ⟨hc, S, hd⟩ := hz
  refine ⟨continuous_fst.comp_continuousOn hc, S, fun t ht htS => ?_⟩
  have h := (hd t ht htS).fst
  rw [twoChain_driftFree] at h
  exact h

/-- **MLS Chapter 8, Exercise 5, p. 392: the `y`-chain coordinates** `(y₀, x₀, y₁, y₂, …, y_{p+1})`
with `y₁ = x₀y₀ − x₁`. -/
def twoChainYCoords (z : TwoChainState n p) : Fin (p + 3) → ℝ := fun i =>
  if i.val = 0 then z.1 1 else if i.val = 1 then z.1 0 else if i.val = 2 then twoChainY1 z.1
    else if h : 3 ≤ i.val then z.2 ⟨i.val - 3, by omega⟩ else 0

/-- **MLS Chapter 8, Exercise 5, p. 392: the inputs exchanged,** `(u₁, u₂) ↦ (u₂, u₁)`. -/
def swapInput (u : ℝ → Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ := ![u t 1, u t 0]

/-- **MLS Chapter 8, Exercise 5, p. 392: the `y`-chain.** The coordinates
`(y₀, x₀, y₁, y₂, …)` of a trajectory form a trajectory of the one-chain system (8.7) with the
inputs exchanged: `ẏ₀ = u₂, ẋ₀ = u₁, ẏ₁ = x₀u₂, ẏᵢ₊₁ = yᵢu₂`. -/
theorem IsTrajectory.twoChain_yCoords {u : ℝ → Fin 2 → ℝ} {T : ℝ} {z : ℝ → TwoChainState n p}
    (hz : IsTrajectory twoChainFields u T z) :
    IsTrajectory (chainFields (p + 3)) (swapInput u) T fun t => twoChainYCoords (z t) := by
  obtain ⟨hc, S, hd⟩ := hz
  have hcont : Continuous (fun z : TwoChainState n p => twoChainYCoords z) := by
    refine continuous_pi fun i => ?_
    unfold twoChainYCoords twoChainY1
    split_ifs <;> fun_prop
  refine ⟨hcont.comp_continuousOn hc, S, fun t ht htS => ?_⟩
  have h := hd t ht htS
  rw [twoChain_driftFree] at h
  have h1 := h.fst
  have h2 := h.snd
  have hx : ∀ i, HasDerivAt (fun t => (z t).1 i) (driftFree (chainFields (n + 3)) (z t).1 (u t) i) t :=
    fun i => (hasDerivAt_pi.1 h1) i
  have hw : ∀ j, HasDerivAt (fun t => (z t).2 j)
      ((u t 1 • (twoChainY1 (z t).1 • chainBasis p 0 + twoChainShift p (z t).2)) j) t :=
    fun j => (hasDerivAt_pi.1 h2) j
  have e0 := chain_driftFree_of_val_eq_zero (z t).1 (u t) (i := 0) rfl
  have e1 := chain_driftFree_of_val_eq_one (z t).1 (u t) (i := 1) rfl
  have e2 := chain_driftFree_of_val_eq_succ (z t).1 (u t) (i := 2) (j := 1) rfl le_rfl
  refine hasDerivAt_pi.2 fun i => ?_
  rcases i with ⟨i, hi⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | h3
  · have := hx 1
    rw [e1] at this
    have hfun : (fun t => twoChainYCoords (z t) ⟨0, hi⟩) = fun t => (z t).1 1 := by
      funext s
      simp [twoChainYCoords]
    rw [hfun]
    convert this using 1
    rw [chain_driftFree_of_val_eq_zero _ _ rfl]
    rfl
  · have := hx 0
    rw [e0] at this
    have hfun : (fun t => twoChainYCoords (z t) ⟨1, hi⟩) = fun t => (z t).1 0 := by
      funext s
      simp [twoChainYCoords]
    rw [hfun]
    convert this using 1
    rw [chain_driftFree_of_val_eq_one _ _ rfl]
    rfl
  · have := ((hx 0).mul (hx 1)).sub (hx 2)
    rw [e0, e1, e2] at this
    have hfun : (fun t => twoChainYCoords (z t) ⟨2, hi⟩) =
        fun t => (z t).1 0 * (z t).1 1 - (z t).1 2 := by
      funext s
      simp [twoChainYCoords, twoChainY1]
    rw [hfun]
    convert this using 1
    rw [chain_driftFree_of_val_eq_succ (twoChainYCoords (z t)) (swapInput u t) (j := 1) rfl le_rfl]
    simp [twoChainYCoords, swapInput]
    ring
  · have := hw ⟨i - 3, by omega⟩
    have hval : (twoChainYCoords (z t) : Fin (p + 3) → ℝ) ⟨i, hi⟩ = (z t).2 ⟨i - 3, by omega⟩ := by
      simp [twoChainYCoords, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, h3]
    have hfun : (fun t => twoChainYCoords (z t) ⟨i, hi⟩) = fun t => (z t).2 ⟨i - 3, by omega⟩ := by
      funext s
      simp [twoChainYCoords, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, h3]
    rw [hfun]
    convert this using 1
    rw [chain_driftFree_of_val_eq_succ (twoChainYCoords (z t)) (swapInput u t)
      (j := ⟨i - 1, by omega⟩) (by simp; omega) (by simp; omega)]
    simp only [swapInput, Matrix.cons_val_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [twoChainShift_apply]
    by_cases h4 : i = 3
    · subst h4
      simp [twoChainYCoords, chainBasis]
    · simp [twoChainYCoords, chainBasis, show i - 1 ≠ 0 by omega, show i - 1 ≠ 1 by omega,
        show i - 1 ≠ 2 by omega, show 3 ≤ i - 1 by omega, show i - 3 ≠ 0 by omega,
        show 1 ≤ i - 3 by omega]
      left
      congr 1

/-- **MLS Chapter 8, Exercise 5(b), p. 392, reading `q_k` as `x_k`:** for `k ≥ 1`, every
trajectory on `[0, 1]` with `u₁ = a sin 2πt`, `u₂ = b cos 2πkt`, from any initial state, returns
`x₀, y₀, x₁, …, x_{k−1}` (indices `≤ k` of `(x₀, y₀, x₁, …)`) and moves `x_k` (index `k + 1`) by
`(a/4π)^k b/k!`. -/
theorem IsTrajectory.twoChain_steering_x {k : ℕ} (hk : 1 ≤ k) (a b : ℝ)
    {z : ℝ → TwoChainState n p} (hz : IsTrajectory twoChainFields (chainSinusoid a b k) 1 z) :
    (∀ j : Fin (n + 3), j.val ≤ k → (z 1).1 j = (z 0).1 j) ∧
      ∀ j : Fin (n + 3), j.val = k + 1 →
        (z 1).1 j - (z 0).1 j = (a / (4 * Real.pi)) ^ k * b / (k.factorial : ℝ) :=
  hz.twoChain_fst.chain_steering hk a b

/-- **MLS Chapter 8, Exercise 5(c), p. 392:** for `k ≥ 2`, every trajectory on `[0, 1]` with
`u₁ = b cos 2πkt`, `u₂ = a sin 2πt`, from any initial state, returns `y₀, x₀, y₁, …, y_{k−1}` and
moves `y_k` (the entry `k − 2` of `w`) by `(a/4π)^k b/k!`. -/
theorem IsTrajectory.twoChain_steering_y {k : ℕ} (hk : 2 ≤ k) (a b : ℝ)
    {z : ℝ → TwoChainState n p}
    (hz : IsTrajectory twoChainFields (swapInput (chainSinusoid a b k)) 1 z) :
    (∀ j : Fin (p + 3), j.val ≤ k → twoChainYCoords (z 1) j = twoChainYCoords (z 0) j) ∧
      ∀ j : Fin p, j.val = k - 2 →
        (z 1).2 j - (z 0).2 j = (a / (4 * Real.pi)) ^ k * b / (k.factorial : ℝ) := by
  have hy := hz.twoChain_yCoords
  have hs : swapInput (swapInput (chainSinusoid a b k)) = chainSinusoid a b k := by
    funext t i
    fin_cases i <;> rfl
  rw [hs] at hy
  obtain ⟨h1, h2⟩ := hy.chain_steering (by omega) a b
  refine ⟨h1, fun j hj => ?_⟩
  have h := h2 ⟨j.val + 3, by omega⟩ (by simp; omega)
  simpa [twoChainYCoords] using h

/-- **MLS Chapter 8, Exercise 5, p. 392: trajectories exist.** For continuous inputs and every
initial state the two-chained system has a solution defined for all times: the `x`-chain and the
`y`-chain are one-chain systems (8.7) whose shared coordinates `x₀, y₀` and `y₁ = x₀y₀ − x₁`
agree for all times once they agree initially. -/
theorem twoChain_exists_solution {u : ℝ → Fin 2 → ℝ} (hu : Continuous u) (z₀ : TwoChainState n p) :
    ∃ z : ℝ → TwoChainState n p, z 0 = z₀ ∧
      ∀ t, HasDerivAt z (driftFree twoChainFields (z t) (u t)) t := by
  obtain ⟨X, hX0, hX⟩ := chain_exists_solution (n + 3) hu z₀.1
  have hsw : Continuous (swapInput u) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (continuous_apply 1).comp hu
    · exact (continuous_apply 0).comp hu
  obtain ⟨Y, hY0, hY⟩ := chain_exists_solution (p + 3) hsw (twoChainYCoords z₀)
  -- the shared coordinates agree for all times
  have hcomp : ∀ i, ∀ t, HasDerivAt (fun t => X t i) (driftFree (chainFields (n + 3)) (X t) (u t) i) t :=
    fun i t => (hasDerivAt_pi.1 (hX t)) i
  have hcompY : ∀ i, ∀ t, HasDerivAt (fun t => Y t i)
      (driftFree (chainFields (p + 3)) (Y t) (swapInput u t) i) t :=
    fun i t => (hasDerivAt_pi.1 (hY t)) i
  have hconst : ∀ {f : ℝ → ℝ}, (∀ t, HasDerivAt f 0 t) → ∀ t, f t = f 0 := fun hf t =>
    is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt) (fun s => (hf s).deriv) t 0
  have hY0' : ∀ t, Y t 0 = X t 1 := by
    intro t
    have h := hconst (f := fun t => Y t 0 - X t 1) (fun s => by
      refine ((hcompY 0 s).sub (hcomp 1 s)).congr_deriv ?_
      rw [chain_driftFree_of_val_eq_zero _ _ rfl, chain_driftFree_of_val_eq_one _ _ rfl]
      exact sub_self _) t
    have h0 : Y 0 0 = X 0 1 := by rw [hY0, hX0]; simp [twoChainYCoords]
    linarith
  have hY1' : ∀ t, Y t 1 = X t 0 := by
    intro t
    have h := hconst (f := fun t => Y t 1 - X t 0) (fun s => by
      refine ((hcompY 1 s).sub (hcomp 0 s)).congr_deriv ?_
      rw [chain_driftFree_of_val_eq_one _ _ rfl, chain_driftFree_of_val_eq_zero _ _ rfl]
      exact sub_self _) t
    have h0 : Y 0 1 = X 0 0 := by rw [hY0, hX0]; simp [twoChainYCoords]
    linarith
  have hY2' : ∀ t, Y t 2 = twoChainY1 (X t) := by
    intro t
    have h := hconst (f := fun t => Y t 2 - (X t 0 * X t 1 - X t 2)) (fun s => by
      have := (hcompY 2 s).sub (((hcomp 0 s).mul (hcomp 1 s)).sub (hcomp 2 s))
      rw [chain_driftFree_of_val_eq_succ (Y s) _ (i := 2) (j := 1) rfl le_rfl,
        chain_driftFree_of_val_eq_zero _ _ rfl, chain_driftFree_of_val_eq_one _ _ rfl,
        chain_driftFree_of_val_eq_succ (X s) _ (i := 2) (j := 1) rfl le_rfl, hY1' s] at this
      convert this using 1
      simp [swapInput]
      ring) t
    have hm : 2 % (p + 3) = 2 := Nat.mod_eq_of_lt (by omega)
    have h0 : Y 0 2 = twoChainY1 (X 0) := by rw [hY0, hX0]; simp [twoChainYCoords, hm]
    simp only [twoChainY1] at h h0 ⊢
    linarith
  refine ⟨fun t => (X t, fun j => Y t ⟨j.val + 3, by omega⟩), ?_, fun t => ?_⟩
  · ext j
    · simp [hX0]
    · simp [hY0, twoChainYCoords]
  · rw [twoChain_driftFree]
    refine (hX t).prodMk (hasDerivAt_pi.2 fun j => ?_)
    have h := hcompY ⟨j.val + 3, by omega⟩ t
    rw [chain_driftFree_of_val_eq_succ (Y t) _ (j := ⟨j.val + 2, by omega⟩) rfl (by simp)] at h
    convert h using 1
    simp only [swapInput, Matrix.cons_val_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [twoChainShift_apply]
    by_cases hj : j.val = 0
    · simp [hj, chainBasis]
      left
      rw [← hY2' t]
      congr 1
    · simp [hj, chainBasis, show 1 ≤ j.val by omega]
      left
      congr 1
      exact Fin.ext (by dsimp only; omega)

end Nonholonomic
end RoboLean

end
