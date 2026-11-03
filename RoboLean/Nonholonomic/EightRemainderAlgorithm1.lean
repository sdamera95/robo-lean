import RoboLean.Examples.BrockettGeneral
import RoboLean.Nonholonomic.SevenRemainder
import RoboLean.Nonholonomic.ChainedForm

/-!
# Algorithm 1 steers the `m`-input system (8.4)–(8.5) to every configuration (MLS p. 361)

**What MLS prints.** "Algorithm 1. Steering first-order canonical systems. 1. Steer the `qᵢ` to
their desired values using any input and ignoring the evolution of the `qᵢⱼ`. 2. Using sinusoids at
integrally related frequencies, find `u₀` such that the input steers the `qᵢⱼ` to their desired
values. By the choice of input, the `qᵢ` are unchanged" (p. 361).

**Proved here.** For every `m`, from every state `(q₀, Y₀)` to every state `(q_f, Y_f)` with
`Y_f − Y₀` skew-symmetric, Algorithm 1's input steers (8.5) in time `1 + N`, `N` the number of
pairs `i < j`: step 1 is the constant input `q_f − q₀` on `[0, 1]`; step 2 runs the pair input of
`brockettPairInput` with `uᵢ = sin 2πt`, `uⱼ = b cos 2πt` on `[k, k + 1)` for the `k`-th pair, each
step moving only `qᵢⱼ` (`algorithm1_steers`). The skew-symmetry of `Y_f − Y₀` is necessary: along
every trajectory `Yₖₗ + Yₗₖ` is constant (`IsTrajectory.brockettSystem_symm_eq`), so the book's
coordinates `qᵢⱼ`, `i < j`, are free and the entries below the diagonal follow.

**Conventions.** The state is `(q, Y)` with the whole matrix `Y` (MLS eq. (8.5)); one pair per unit
of time, in the order of a list of the pairs `i < j`; step 2 uses the frequency `2π` for every pair,
one pair at a time, where the book allows several pairs at once at integrally related frequencies.
-/

noncomputable section

open Real Set Filter Topology
open RoboLean.Examples

namespace RoboLean
namespace Nonholonomic

variable {m : ℕ}

/-- **MLS Algorithm 1, p. 361: the input of the whole algorithm,** the constant `c` on `[0, 1)`
(step 1) and, on `[k, k + 1)` for `k ≥ 1`, the pair input `uᵢ = sin 2π(t − k)`,
`uⱼ = b_{k−1} cos 2π(t − k)` for the `(k − 1)`-th pair `(i, j)` of the list `P` (step 2), zero
after the list. -/
def algorithm1Input (c : Fin m → ℝ) (P : List (Fin m × Fin m)) (b : ℕ → ℝ) (t : ℝ) :
    Fin m → ℝ :=
  if t < 1 then c else
    match P[⌊t⌋₊ - 1]? with
    | some p => brockettPairInput p.1 p.2 1 (b (⌊t⌋₊ - 1)) (t - ⌊t⌋₊)
    | none => 0

/-- **MLS eq. (8.5), p. 360: `Yₖₗ + Yₗₖ` is constant along every trajectory,** since the rate
`quᵀ − uqᵀ` of `Y` is skew-symmetric; so `Y(T) − Y(0)` is skew-symmetric. -/
theorem IsTrajectory.brockettSystem_symm_eq {u : ℝ → Fin m → ℝ} {T : ℝ}
    {x : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ)}
    (hx : IsTrajectory (brockettSystemFields m) u T x) (hT : 0 ≤ T) (k l : Fin m) :
    (x T).2 k l + (x T).2 l k = (x 0).2 k l + (x 0).2 l k := by
  set L : ((Fin m → ℝ) × (Fin m → Fin m → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) l).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin m → ℝ) k).comp
          (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin m → Fin m → ℝ))) +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin m → ℝ) l).comp
          (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin m → Fin m → ℝ))) with hL
  have hLapp : ∀ z : (Fin m → ℝ) × (Fin m → Fin m → ℝ), L z = z.2 k l + z.2 l k := fun z => rfl
  have h := hx.apply_eq_of_fderiv_eq_zero hT (h := L) (fun _ _ => L.differentiableAt)
    (fun t _ j => by
      rw [L.fderiv, hLapp]
      simp [brockettSystemFields, Pi.single_apply])
  rwa [hLapp, hLapp] at h

/-- Changing the input on the open interval `(0, T)` keeps a trajectory (supporting lemma for
MLS Algorithm 1, p. 361). -/
theorem IsTrajectory.of_eqOn_input {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Fin m → E → E} {u v : ℝ → Fin m → ℝ} {T : ℝ} {x : ℝ → E} (hx : IsTrajectory g u T x)
    (huv : ∀ t ∈ Ioo 0 T, u t = v t) : IsTrajectory g v T x := by
  obtain ⟨hc, S, hS⟩ := hx
  exact ⟨hc, S, fun t ht htS => huv t ht ▸ hS t ht htS⟩

/-- A trajectory on `[0, T]` followed by a trajectory on `[0, 1]` for the input shifted by `T`,
started where the first ends, is a trajectory on `[0, T + 1]` (supporting lemma for MLS
Algorithm 1, p. 361: the steps run one after another). -/
theorem IsTrajectory.append_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {T : ℝ} {x y : ℝ → E} (hT : 0 ≤ T)
    (hx : IsTrajectory g u T x) (hy : IsTrajectory g (fun s => u (s + T)) 1 y)
    (hxy : x T = y 0) :
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

/-- The skew matrix `d (Eᵢⱼ − Eⱼᵢ)` (supporting definition for MLS Algorithm 1, p. 361). -/
def pairMatrix (d : ℝ) (p : Fin m × Fin m) : Fin m → Fin m → ℝ :=
  fun k l => d * ((if k = p.1 ∧ l = p.2 then 1 else 0) - (if k = p.2 ∧ l = p.1 then 1 else 0))

/-- **MLS Algorithm 1, p. 361: the pairs `i < j`,** listed once each (supporting definition). -/
def pairsList (m : ℕ) : List (Fin m × Fin m) :=
  (Finset.univ.filter fun p : Fin m × Fin m => p.1 < p.2).toList

/-- **MLS Algorithm 1, p. 361: "Steer the `qᵢ` to their desired values using any input and ignoring
the evolution of the `qᵢⱼ`. Using sinusoids … the input steers the `qᵢⱼ` to their desired values.
By the choice of input, the `qᵢ` are unchanged."** For every `m`, all `(q₀, Y₀)` and all
`(q_f, Y_f)` with `Y_f − Y₀` skew-symmetric, with `P` the list of the pairs `i < j`, there are a
constant `c` and amplitudes `b` such that (8.5) has a trajectory on `[0, 1 + |P|]` under
`algorithm1Input c P b` from `(q₀, Y₀)` to `(q_f, Y_f)`. -/
theorem algorithm1_steers (q₀ qf : Fin m → ℝ) (Y₀ Yf : Fin m → Fin m → ℝ)
    (hskew : ∀ k l, Yf k l - Y₀ k l = -(Yf l k - Y₀ l k)) :
    let P := pairsList m
    ∃ (c : Fin m → ℝ) (b : ℕ → ℝ) (x : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ)),
      IsTrajectory (brockettSystemFields m) (algorithm1Input c P b) (1 + P.length) x ∧
        x 0 = (q₀, Y₀) ∧ x (1 + P.length) = (qf, Yf) := by
  intro P
  have hP' : ∀ p ∈ P, p.1 < p.2 := fun p hp => by
    simpa [P, pairsList] using hp
  have hπ : π ≠ 0 := pi_ne_zero
  set c : Fin m → ℝ := qf - q₀ with hc
  -- step 1
  obtain ⟨x₁, hx₁0, hx₁⟩ := brockettSystem_exists_solution (continuous_const (y := c)) (q₀, Y₀)
  have hx₁T : IsTrajectory (brockettSystemFields m) (fun _ => c) 1 x₁ :=
    IsTrajectory.of_hasDerivAt 1 hx₁
  have hq₁ : (x₁ 1).1 = qf := by
    funext k
    have hd : ∀ t, HasDerivAt (fun t => (x₁ t).1 k) (c k) t := fun t => by
      have h := hasDerivAt_pi.1 (hx₁ t).fst k
      rw [brockettSystem_driftFree] at h
      exact h
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun t _ => hd t) intervalIntegrable_const
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at h
    rw [hx₁0] at h
    simp only [hc, Pi.sub_apply] at h
    linarith
  set Y₁ := (x₁ 1).2 with hY₁
  set D : Fin m → Fin m → ℝ := Yf - Y₁ with hD
  have hDskew : ∀ k l, D k l = -D l k := by
    intro k l
    have h := hx₁T.brockettSystem_symm_eq zero_le_one k l
    rw [hx₁0] at h
    have := hskew k l
    simp only [hD, Pi.sub_apply, hY₁]
    linarith
  set b : ℕ → ℝ := fun n => match P[n]? with
    | some p => -(2 * π) * D p.1 p.2
    | none => 0 with hb
  set S : ℕ → Fin m → Fin m → ℝ :=
    fun n => ((P.take n).map fun p => pairMatrix (D p.1 p.2) p).sum with hS
  -- the steps of step 2
  have key : ∀ n : ℕ, n ≤ P.length → ∃ x : ℝ → (Fin m → ℝ) × (Fin m → Fin m → ℝ),
      IsTrajectory (brockettSystemFields m) (algorithm1Input c P b) (1 + n) x ∧
        x 0 = (q₀, Y₀) ∧ x (1 + n) = (qf, Y₁ + S n) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨x₁, ?_, hx₁0, ?_⟩
      · simp only [CharP.cast_eq_zero, add_zero]
        exact hx₁T.of_eqOn_input fun t ht => by simp [algorithm1Input, ht.2]
      · simp only [CharP.cast_eq_zero, add_zero, hS, List.take_zero, List.map_nil,
          List.sum_nil, add_zero]
        exact Prod.ext hq₁ rfl
    | succ n ih =>
      intro hn
      obtain ⟨x, hx, hx0, hxf⟩ := ih (by omega)
      have hlt : n < P.length := by omega
      set p := P[n] with hp
      have hpP : P[n]? = some p := List.getElem?_eq_getElem hlt
      have hp12 : p.1 ≠ p.2 := (hP' p (List.getElem_mem hlt)).ne
      obtain ⟨y, hy0, hy⟩ := brockettSystem_exists_solution
        (u := brockettPairInput p.1 p.2 1 (b n))
        (continuous_pi fun k => by
          simp only [brockettPairInput, Pi.add_apply, Pi.single_apply]
          split_ifs <;> fun_prop)
        (x (1 + n))
      have hyT : IsTrajectory (brockettSystemFields m) (brockettPairInput p.1 p.2 1 (b n)) 1 y :=
        IsTrajectory.of_hasDerivAt 1 hy
      have hy' : IsTrajectory (brockettSystemFields m)
          (fun s => algorithm1Input c P b (s + (1 + n))) 1 y := by
        refine hyT.of_eqOn_input fun s hs => ?_
        have hfl : ⌊s + (1 + (n : ℝ))⌋₊ = n + 1 := by
          rw [Nat.floor_eq_iff (by linarith [hs.1])]
          push_cast
          constructor <;> linarith [hs.1, hs.2]
        have hnot : ¬ s + (1 + (n : ℝ)) < 1 := by linarith [hs.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
        simp only [algorithm1Input, hnot, ↓reduceIte, hfl, Nat.add_sub_cancel, hpP]
        congr 1
        push_cast
        ring
      obtain ⟨hst1, hst2⟩ := Examples.IsTrajectory.brockettSystem_steering hp12 hyT
      refine ⟨fun t => if t ≤ 1 + n then x t else y (t - (1 + n)), ?_, by
        simp [hx0, show (0 : ℝ) ≤ 1 + n by positivity], ?_⟩
      · rw [show (1 : ℝ) + ((n + 1 : ℕ) : ℝ) = (1 + (n : ℝ)) + 1 by push_cast; ring]
        exact hx.append_unit (by positivity) hy' hy0.symm
      · have hle : ¬ (1 + ((n + 1 : ℕ) : ℝ)) ≤ 1 + n := by push_cast; linarith
        simp only [hle, ↓reduceIte]
        have ht1 : (1 + ((n + 1 : ℕ) : ℝ)) - (1 + n) = 1 := by push_cast; ring
        rw [ht1]
        apply Prod.ext
        · rw [hst1, hy0, hxf]
        · funext k l
          rw [hst2 k l, hy0, hxf]
          have hbn : b n = -(2 * π) * D p.1 p.2 := by simp [hb, hpP]
          have hSn : S (n + 1) = S n + pairMatrix (D p.1 p.2) p := by
            simp only [hS, List.take_add_one, hpP, Option.toList_some, List.map_append,
              List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [hSn]
          simp only [Pi.add_apply, pairMatrix, hbn]
          field_simp
          ring
  obtain ⟨x, hx, hx0, hxf⟩ := key P.length le_rfl
  refine ⟨c, b, x, hx, hx0, ?_⟩
  rw [hxf]
  congr 1
  -- the accumulated displacement is `D`
  funext k l
  have hsum : S P.length k l = D k l := by
    simp only [hS, List.take_length, P, pairsList, Finset.sum_map_toList, Finset.sum_apply]
    simp only [pairMatrix, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    have e1 : ∀ a c : Fin m, (∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2),
        if a = p.1 ∧ c = p.2 then D p.1 p.2 else 0) = if a < c then D a c else 0 := by
      intro a c
      by_cases h : a < c
      · rw [Finset.sum_eq_single (a, c)]
        · simp [h]
        · intro p _ hne
          have : ¬ (a = p.1 ∧ c = p.2) := fun h' => hne (Prod.ext h'.1.symm h'.2.symm)
          simp [this]
        · intro hnot
          simp [h] at hnot
      · simp only [h, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have : ¬ (a = p.1 ∧ c = p.2) := by
          rintro ⟨rfl, rfl⟩
          exact h hp
        simp [this]
    have e2 : (∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2),
        if k = p.2 ∧ l = p.1 then D p.1 p.2 else 0) = if l < k then D l k else 0 := by
      rw [← e1 l k]
      exact Finset.sum_congr rfl fun p _ => by
        by_cases h : k = p.2 ∧ l = p.1
        · simp [h]
        · have h' : ¬ (l = p.1 ∧ k = p.2) := fun h' => h ⟨h'.2, h'.1⟩
          simp only [h, h', ↓reduceIte]
    rw [e1, e2]
    rcases lt_trichotomy k l with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · have := hDskew k k
      simp only [lt_irrefl, ↓reduceIte, sub_zero]
      linarith
    · simp [h, not_lt.2 h.le, hDskew k l]
  simp only [Pi.add_apply, hsum, hD, Pi.sub_apply, add_sub_cancel]
