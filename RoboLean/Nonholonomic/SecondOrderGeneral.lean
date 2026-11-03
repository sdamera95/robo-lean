import RoboLean.Nonholonomic.SteeringSecondOrder
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The second-order model system (8.6) for `m` inputs: MLS Chapter 8, §2.2

MLS Chapter 8, §2.2, printed pp. 361–363: the system (8.6) `q̇ᵢ = uᵢ`, `q̇ᵢⱼ = qᵢuⱼ` (`i < j`),
`q̇ᵢⱼₖ = qᵢⱼuₖ` "(mod Jacobi identity)", the relation "`q₂₃₁ − q₁₃₂ = q₁q₂₃ − q₂q₁₃`" (p. 362),
Algorithm 2 (step 3: sinusoids moving the previously steered states in a closed loop), and the
two-input formulas of p. 363.

**What is formalized.**

* (8.6) for every `m` on the state `(q, Q, W)` with all index pairs and triples
  (`secondOrderGeneralFields`): `q̇ = u`, `Q̇ₖₗ = qₖuₗ`, `Ẇₖₗₙ = Qₖₗuₙ`; the book's coordinates are
  `qᵢⱼ = Qᵢⱼ`, `qᵢⱼₖ = Wᵢⱼₖ` for `i < j`.
* The relation behind "mod Jacobi identity": for all indices `a, b, c`,
  `W_{bca} − W_{acb} − (q_a Q_{bc} − q_b Q_{ac})` is constant along every trajectory
  (`IsTrajectory.secondOrderJacobi_eq`); from the origin it gives the printed
  `q₂₃₁ − q₁₃₂ = q₁q₂₃ − q₂q₁₃` (`IsTrajectory.secondOrder_jacobi_printed`, `m ≥ 3`). The printed
  relation holds only for trajectories on which it holds initially (it is a first integral, not an
  identity of the coordinates).
* Algorithm 2, step 3, for any two distinct inputs `i ≠ j` of the `m`-input system: with
  `uᵢ = a sin 2πt`, `uⱼ = b cos 4πt` and the other inputs zero, every trajectory on `[0, 1]` returns
  `qᵢ, qⱼ, qᵢⱼ, qᵢⱼⱼ` and moves `qᵢⱼᵢ` by `−a²b/(16π²)`; with the sine on `i` and the cosine on
  `j`, the coordinates `qⱼ, qᵢ, qⱼᵢ, qⱼᵢⱼ` return and `qⱼᵢᵢ` moves by `+a²b/(32π²)`
  (`IsTrajectory.secondOrderGeneral_steering`, `IsTrajectory.secondOrderGeneral_steering_swap`), the
  two formulas of p. 363 on the indices `(i, j)`. Both follow from the `m = 2` formulas because
  these five coordinates of (8.6) form the `m = 2` system for the inputs `uᵢ, uⱼ`
  (`IsTrajectory.secondOrder_proj`); every other coordinate `qₖ`, `qₖₗ` and `qₖₗₙ` (`k ≠ l`)
  returns (`IsTrajectory.secondOrderGeneral_steering_others`, by the period integrals
  `∫₀¹ Uₗuₙ = 0` of the inputs and their primitives), so on the book's coordinates only `qᵢⱼᵢ` or
  `qⱼᵢᵢ` moves. Trajectories exist for continuous inputs (`secondOrderGeneral_exists_solution`).

**Not formalized.** The count `(m + 1)m(m − 1)/3` of controllable
`qᵢⱼₖ` (it rests on Exercise 17 of Chapter 7); steps 1 and 2 of Algorithm 2 as a procedure; the
`m`-input system (8.4) steered by sinusoids and Brockett's frequency result (p. 361, cited without
proof).

**Conventions.** Indices `Fin m`, the book's `qᵢ` is entry `i − 1`; trajectories are the library's
`IsTrajectory` on `[0, 1]`; the `m = 2` system is `secondOrderFields` on `Fin 5 → ℝ` ordered
`(q₁, q₂, q₁₂, q₁₂₁, q₁₂₂)`.
-/

noncomputable section

open Set Real

namespace RoboLean
namespace Nonholonomic

variable {m : ℕ}

/-- **The state of (8.6)** (MLS p. 361): `(q, Q, W)` with `q : Fin m → ℝ`, `Q` indexed by pairs and
`W` by triples (the book keeps `Qᵢⱼ`, `Wᵢⱼₖ` for `i < j`). -/
abbrev SecondOrderState (m : ℕ) :=
  (Fin m → ℝ) × (Fin m → Fin m → ℝ) × (Fin m → Fin m → Fin m → ℝ)

/-- **MLS eq. (8.6), p. 361: the input fields** `gⱼ(q, Q, W) = (eⱼ, (k, l) ↦ qₖ δₗⱼ,
(k, l, n) ↦ Qₖₗ δₙⱼ)`, on all index pairs and triples. -/
def secondOrderGeneralFields (m : ℕ) : Fin m → SecondOrderState m → SecondOrderState m :=
  fun j z => (Pi.single j 1, fun k l => z.1 k * (Pi.single j (1 : ℝ) : Fin m → ℝ) l,
    fun k l n => z.2.1 k l * (Pi.single j (1 : ℝ) : Fin m → ℝ) n)

/-- **MLS eq. (8.6), p. 361: `q̇ = u`, `Q̇ₖₗ = qₖuₗ`, `Ẇₖₗₙ = Qₖₗuₙ`.** -/
theorem secondOrderGeneral_driftFree (z : SecondOrderState m) (u : Fin m → ℝ) :
    driftFree (secondOrderGeneralFields m) z u =
      (u, fun k l => z.1 k * u l, fun k l n => z.2.1 k l * u n) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext k
    simp [driftFree, secondOrderGeneralFields, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext k l
    simp [driftFree, secondOrderGeneralFields, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply,
      Pi.single_apply, mul_comm]
  · funext k l n
    simp [driftFree, secondOrderGeneralFields, Prod.snd_sum, Finset.sum_apply, Pi.single_apply,
      mul_comm]

/-- The coordinates of a curve with derivative (8.6) have the derivatives of (8.6). -/
private theorem coords_hasDerivAt {x : ℝ → SecondOrderState m} {v : Fin m → ℝ} {t : ℝ}
    (h : HasDerivAt x (driftFree (secondOrderGeneralFields m) (x t) v) t) :
    (∀ k, HasDerivAt (fun s => (x s).1 k) (v k) t) ∧
      (∀ k l, HasDerivAt (fun s => (x s).2.1 k l) ((x t).1 k * v l) t) ∧
        ∀ k l n, HasDerivAt (fun s => (x s).2.2 k l n) ((x t).2.1 k l * v n) t := by
  rw [secondOrderGeneral_driftFree] at h
  have h1 := hasFDerivAt_fst.comp_hasDerivAt t h
  have h2 := hasFDerivAt_snd.comp_hasDerivAt t h
  have h21 := hasFDerivAt_fst.comp_hasDerivAt t h2
  have h22 := hasFDerivAt_snd.comp_hasDerivAt t h2
  refine ⟨fun k => hasDerivAt_pi.1 h1 k, fun k l => hasDerivAt_pi.1 (hasDerivAt_pi.1 h21 k) l,
    fun k l n => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 h22 k) l) n⟩

/-- **MLS p. 362, the relation behind "mod Jacobi identity":**
`W_{bca} − W_{acb} − (q_a Q_{bc} − q_b Q_{ac})` (for `(a, b, c) = (1, 2, 3)`:
`q₂₃₁ − q₁₃₂ − (q₁q₂₃ − q₂q₁₃)`). -/
def secondOrderJacobi (a b c : Fin m) (z : SecondOrderState m) : ℝ :=
  z.2.2 b c a - z.2.2 a c b - (z.1 a * z.2.1 b c - z.1 b * z.2.1 a c)

/-- **MLS p. 362: the Jacobi relation is a first integral of (8.6):** along every trajectory on
`[0, T]`, `T ≥ 0`, `W_{bca} − W_{acb} − (q_a Q_{bc} − q_b Q_{ac})` takes the same value at `T` as
at `0`. -/
theorem IsTrajectory.secondOrderJacobi_eq {u : ℝ → Fin m → ℝ} {T : ℝ}
    {x : ℝ → SecondOrderState m} (hx : IsTrajectory (secondOrderGeneralFields m) u T x)
    (hT : 0 ≤ T) (a b c : Fin m) :
    secondOrderJacobi a b c (x T) = secondOrderJacobi a b c (x 0) := by
  obtain ⟨hc, S, hS⟩ := hx
  have hJc : Continuous (secondOrderJacobi (m := m) a b c) := by
    unfold secondOrderJacobi
    fun_prop
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => secondOrderJacobi a b c (x t))
    (fun _ => (0 : ℝ)) hT S.countable_toSet (hJc.comp_continuousOn hc) (fun t ht => ?_)
    intervalIntegrable_const
  · simp only [intervalIntegral.integral_zero] at h
    linarith
  · obtain ⟨hq, hQ, hW⟩ := coords_hasDerivAt (hS t ht.1 ht.2)
    have := ((hW b c a).sub (hW a c b)).sub
      (((hq a).mul (hQ b c)).sub ((hq b).mul (hQ a c)))
    convert this using 1
    · funext s
      simp only [secondOrderJacobi, Pi.sub_apply, Pi.mul_apply]
    · ring

/-- **MLS p. 362: "`q₂₃₁ − q₁₃₂ = q₁q₂₃ − q₂q₁₃`"** along every trajectory of (8.6) on `[0, T]` from
the origin, `m ≥ 3` (indices `0, 1, 2` for the book's `1, 2, 3`). -/
theorem IsTrajectory.secondOrder_jacobi_printed (hm : 3 ≤ m) {u : ℝ → Fin m → ℝ} {T : ℝ}
    {x : ℝ → SecondOrderState m} (hx : IsTrajectory (secondOrderGeneralFields m) u T x)
    (hT : 0 ≤ T) (h0 : x 0 = 0) :
    (x T).2.2 ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ -
        (x T).2.2 ⟨0, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ =
      (x T).1 ⟨0, by omega⟩ * (x T).2.1 ⟨1, by omega⟩ ⟨2, by omega⟩ -
        (x T).1 ⟨1, by omega⟩ * (x T).2.1 ⟨0, by omega⟩ ⟨2, by omega⟩ := by
  have h := hx.secondOrderJacobi_eq hT ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
  rw [h0] at h
  simp only [secondOrderJacobi] at h
  simp at h
  linarith

/-- **The coordinates `(qᵢ, qⱼ, qᵢⱼ, qᵢⱼᵢ, qᵢⱼⱼ)` of (8.6)** (for MLS p. 363), ordered as the
`m = 2` system `(q₁, q₂, q₁₂, q₁₂₁, q₁₂₂)`. -/
def secondOrderProj (i j : Fin m) (z : SecondOrderState m) : Fin 5 → ℝ :=
  ![z.1 i, z.1 j, z.2.1 i j, z.2.2 i j i, z.2.2 i j j]

/-- **MLS p. 363: the coordinates `(qᵢ, qⱼ, qᵢⱼ, qᵢⱼᵢ, qᵢⱼⱼ)` of a trajectory of (8.6) form a
trajectory of the `m = 2` system** with the inputs `(uᵢ, uⱼ)`, whatever the other inputs. -/
theorem IsTrajectory.secondOrder_proj {u : ℝ → Fin m → ℝ} {T : ℝ} {x : ℝ → SecondOrderState m}
    (hx : IsTrajectory (secondOrderGeneralFields m) u T x) (i j : Fin m) :
    IsTrajectory secondOrderFields (fun t => ![u t i, u t j]) T
      (fun t => secondOrderProj i j (x t)) := by
  obtain ⟨hc, S, hS⟩ := hx
  refine ⟨?_, S, fun t ht hts => ?_⟩
  · have hP : Continuous (secondOrderProj (m := m) i j) := by
      refine continuous_pi fun r => ?_
      fin_cases r <;> simp [secondOrderProj] <;> fun_prop
    exact hP.comp_continuousOn hc
  · obtain ⟨hq, hQ, hW⟩ := coords_hasDerivAt (hS t ht hts)
    rw [secondOrder_driftFree, hasDerivAt_pi]
    intro r
    fin_cases r
    · simpa [secondOrderProj] using hq i
    · simpa [secondOrderProj] using hq j
    · simpa [secondOrderProj] using hQ i j
    · simpa [secondOrderProj] using hW i j i
    · simpa [secondOrderProj] using hW i j j

/-- **MLS p. 363 for `m` inputs: the input `uᵢ = a sin 2πt`, `uⱼ = b cos 4πt`, the others zero**
(Algorithm 2, step 3). -/
def secondOrderGeneralInput (i j : Fin m) (a b : ℝ) (t : ℝ) : Fin m → ℝ :=
  Pi.single i (a * sin (2 * π * t)) + Pi.single j (b * cos (4 * π * t))

/-- **MLS Algorithm 2, step 3, and p. 363, for any two inputs `i ≠ j` of (8.6):** every trajectory
on `[0, 1]` with `uᵢ = a sin 2πt`, `uⱼ = b cos 4πt` and the other inputs zero returns `qᵢ, qⱼ,
qᵢⱼ, qᵢⱼⱼ` and ends with `qᵢⱼᵢ(1) = qᵢⱼᵢ(0) − a²b/(16π²)`. -/
theorem IsTrajectory.secondOrderGeneral_steering {i j : Fin m} (hij : i ≠ j) {a b : ℝ}
    {x : ℝ → SecondOrderState m}
    (hx : IsTrajectory (secondOrderGeneralFields m) (secondOrderGeneralInput i j a b) 1 x) :
    secondOrderProj i j (x 1) =
      secondOrderProj i j (x 0) + ![0, 0, 0, -(a ^ 2 * b / (16 * π ^ 2)), 0] := by
  have hp := hx.secondOrder_proj i j
  have hu : (fun t => ![secondOrderGeneralInput i j a b t i, secondOrderGeneralInput i j a b t j]) =
      secondOrderInput a b := by
    funext t r
    fin_cases r <;> simp [secondOrderGeneralInput, secondOrderInput, hij, Ne.symm hij]
  rw [hu] at hp
  exact hp.secondOrder_steering

/-- **MLS p. 363, the swapped inputs, for any two inputs `i ≠ j` of (8.6):** every trajectory on
`[0, 1]` with `uᵢ = a sin 2πt`, `uⱼ = b cos 4πt` and the other inputs zero returns `qⱼ, qᵢ, qⱼᵢ,
qⱼᵢⱼ` and ends with `qⱼᵢᵢ(1) = qⱼᵢᵢ(0) + a²b/(32π²)` (the book's `q₁₂₂` for `j = 1`, `i = 2`). -/
theorem IsTrajectory.secondOrderGeneral_steering_swap {i j : Fin m} (hij : i ≠ j) {a b : ℝ}
    {x : ℝ → SecondOrderState m}
    (hx : IsTrajectory (secondOrderGeneralFields m) (secondOrderGeneralInput i j a b) 1 x) :
    secondOrderProj j i (x 1) =
      secondOrderProj j i (x 0) + ![0, 0, 0, 0, a ^ 2 * b / (32 * π ^ 2)] := by
  have hp := hx.secondOrder_proj j i
  have hu : (fun t => ![secondOrderGeneralInput i j a b t j, secondOrderGeneralInput i j a b t i]) =
      secondOrderInputSwap a b := by
    funext t r
    fin_cases r <;> simp [secondOrderGeneralInput, secondOrderInputSwap, hij, Ne.symm hij]
  rw [hu] at hp
  exact hp.secondOrder_steering_swap

/-- A component continuous on `[0, 1]` with derivative `g` off a finite set differs from an
antiderivative `F` of `g` by a constant. -/
private theorem sub_eq_sub_zero {f F g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {S : Finset ℝ}
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

/-- **MLS Algorithm 2, step 3, and p. 363: "all the other states return",** for any two inputs
`i, j` of (8.6) (distinct in Algorithm 2; the proof does not use it): every trajectory on
`[0, 1]` with `uᵢ = a sin 2πt`, `uⱼ = b cos 4πt` and the other inputs zero returns every `qₖ`,
every `qₖₗ`, and every `qₖₗₙ` with `k ≠ l` one of whose indices is neither `i` nor `j`. With
`IsTrajectory.secondOrderGeneral_steering` and `IsTrajectory.secondOrderGeneral_steering_swap`
this accounts for every coordinate of the book
(`k < l`): only `qᵢⱼᵢ` (for `i < j`, by `−a²b/(16π²)`) or `qⱼᵢᵢ` (for `j < i`, by `+a²b/(32π²)`)
moves. -/
theorem IsTrajectory.secondOrderGeneral_steering_others {i j : Fin m} {a b : ℝ}
    {x : ℝ → SecondOrderState m}
    (hx : IsTrajectory (secondOrderGeneralFields m) (secondOrderGeneralInput i j a b) 1 x) :
    (∀ k, (x 1).1 k = (x 0).1 k) ∧ (∀ k l, (x 1).2.1 k l = (x 0).2.1 k l) ∧
      ∀ k l n, k ≠ l → ((k ≠ i ∧ k ≠ j) ∨ (l ≠ i ∧ l ≠ j) ∨ (n ≠ i ∧ n ≠ j)) →
        (x 1).2.2 k l n = (x 0).2.2 k l n := by
  obtain ⟨hc, S, hS⟩ := hx
  have hπ : π ≠ 0 := pi_ne_zero
  set u := secondOrderGeneralInput i j a b with hu_def
  have hu : ∀ t k, u t k = (if k = i then a * sin (2 * π * t) else 0) +
      (if k = j then b * cos (4 * π * t) else 0) := by
    intro t k
    simp [hu_def, secondOrderGeneralInput, Pi.single_apply]
  have huc : ∀ k, Continuous fun t => u t k := by
    intro k
    simp only [hu]
    split_ifs <;> fun_prop
  set σ : ℝ → ℝ := fun t => a / (2 * π) * (1 - cos (2 * π * t)) with hσ_def
  set τ : ℝ → ℝ := fun t => b / (4 * π) * sin (4 * π * t) with hτ_def
  have hσ : ∀ t, HasDerivAt σ (a * sin (2 * π * t)) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul (2 * π)).cos.const_sub 1).const_mul (a / (2 * π))
    convert h using 1
    · simp only [id]
      rfl
    · simp only [id]
      field_simp
  have hτ : ∀ t, HasDerivAt τ (b * cos (4 * π * t)) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (4 * π)).sin.const_mul (b / (4 * π))
    convert h using 1
    · simp only [id]
      rfl
    · simp only [id]
      field_simp
  have hσ0 : σ 0 = 0 := by simp [hσ_def]
  have hσ1 : σ 1 = 0 := by simp [hσ_def]
  have hτ0 : τ 0 = 0 := by simp [hτ_def]
  have hτ1 : τ 1 = 0 := by
    simp only [hτ_def, mul_one]
    rw [show 4 * π = ((4 : ℕ) : ℝ) * π by push_cast; ring, sin_nat_mul_pi, mul_zero]
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
  have hii : ∫ t in (0 : ℝ)..1, σ t * (a * sin (2 * π * t)) = 0 := by
    have hcσ : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => σ t ^ 2 / 2)
      (f' := fun t => σ t * (a * sin (2 * π * t)))
      (fun t _ => by
        convert ((hσ t).pow 2).div_const 2 using 1
        simp only [Nat.cast_ofNat]
        ring)
      ((hcσ.mul (by fun_prop)).intervalIntegrable 0 1)
    rw [h, hσ0, hσ1]
    ring
  have hjj : ∫ t in (0 : ℝ)..1, τ t * (b * cos (4 * π * t)) = 0 := by
    have hcτ : Continuous τ := continuous_iff_continuousAt.2 fun t => (hτ t).continuousAt
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => τ t ^ 2 / 2)
      (f' := fun t => τ t * (b * cos (4 * π * t)))
      (fun t _ => by
        convert ((hτ t).pow 2).div_const 2 using 1
        simp only [Nat.cast_ofNat]
        ring)
      ((hcτ.mul (by fun_prop)).intervalIntegrable 0 1)
    rw [h, hτ0, hτ1]
    ring
  have hij : ∫ t in (0 : ℝ)..1, σ t * (b * cos (4 * π * t)) = 0 := by
    have h := integral_one_sub_cos_pow_mul_cos_of_lt (i := 1) (k := 2) (by norm_num)
    have e : (fun t => σ t * (b * cos (4 * π * t))) = fun t => a * b / (2 * π) *
        ((1 - cos (2 * π * t)) ^ 1 * cos (2 * π * ((2 : ℕ) : ℝ) * t)) := by
      funext t
      simp only [hσ_def]
      push_cast
      ring_nf
    rw [e, intervalIntegral.integral_const_mul, h, mul_zero]
  have hji : ∫ t in (0 : ℝ)..1, τ t * (a * sin (2 * π * t)) = 0 := by
    have hcσ : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
    have hcτ : Continuous τ := continuous_iff_continuousAt.2 fun t => (hτ t).continuousAt
    have c1 : Continuous fun t => τ t * (a * sin (2 * π * t)) := hcτ.mul (by fun_prop)
    have c2 : Continuous fun t => σ t * (b * cos (4 * π * t)) := hcσ.mul (by fun_prop)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => σ t * τ t)
      (f' := fun t => τ t * (a * sin (2 * π * t)) + σ t * (b * cos (4 * π * t)))
      (fun t _ => by
        convert (hσ t).mul (hτ t) using 1
        ring)
      ((c1.add c2).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_add (c1.intervalIntegrable 0 1) (c2.intervalIntegrable 0 1),
      hij, add_zero, hσ0, hσ1, hτ0, hτ1] at h
    rw [h]
    ring
  have hP2 : ∀ l n, ∫ t in (0 : ℝ)..1, U l t * u t n = 0 := by
    intro l n
    set cli : ℝ := if l = i then 1 else 0
    set clj : ℝ := if l = j then 1 else 0
    set cni : ℝ := if n = i then 1 else 0
    set cnj : ℝ := if n = j then 1 else 0
    have e : (fun t => U l t * u t n) = fun t =>
        cli * cni * (σ t * (a * sin (2 * π * t))) + cli * cnj * (σ t * (b * cos (4 * π * t))) +
        clj * cni * (τ t * (a * sin (2 * π * t))) + clj * cnj * (τ t * (b * cos (4 * π * t))) := by
      funext t
      rw [hu]
      simp only [hU_def, cli, clj, cni, cnj]
      split_ifs <;> ring
    have hcσ : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
    have hcτ : Continuous τ := continuous_iff_continuousAt.2 fun t => (hτ t).continuousAt
    have i1 : IntervalIntegrable (fun t => cli * cni * (σ t * (a * sin (2 * π * t))))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hcσ.mul (by fun_prop))).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun t => cli * cnj * (σ t * (b * cos (4 * π * t))))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hcσ.mul (by fun_prop))).intervalIntegrable 0 1
    have i3 : IntervalIntegrable (fun t => clj * cni * (τ t * (a * sin (2 * π * t))))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hcτ.mul (by fun_prop))).intervalIntegrable 0 1
    have i4 : IntervalIntegrable (fun t => clj * cnj * (τ t * (b * cos (4 * π * t))))
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hcτ.mul (by fun_prop))).intervalIntegrable 0 1
    rw [e, intervalIntegral.integral_add ((i1.add i2).add i3) i4,
      intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hii, hij, hji, hjj]
    ring
  have hint0 : ∀ n, ∫ t in (0 : ℝ)..1, u t n = 0 := by
    intro n
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hU n t)
      ((huc n).intervalIntegrable 0 1), hU0, hU1, sub_zero]
  have hco : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ S →
      (∀ k, HasDerivAt (fun s => (x s).1 k) (u t k) t) ∧
        (∀ k l, HasDerivAt (fun s => (x s).2.1 k l) ((x t).1 k * u t l) t) ∧
        ∀ k l n, HasDerivAt (fun s => (x s).2.2 k l n) ((x t).2.1 k l * u t n) t :=
    fun t ht hts => coords_hasDerivAt (hS t ht hts)
  have hqc : ∀ k, ContinuousOn (fun s => (x s).1 k) (Icc 0 1) := fun k =>
    ((continuous_apply k).comp continuous_fst).comp_continuousOn hc
  have hQc : ∀ k l, ContinuousOn (fun s => (x s).2.1 k l) (Icc 0 1) := fun k l =>
    (show Continuous fun z : SecondOrderState m => z.2.1 k l by fun_prop).comp_continuousOn hc
  have hWc : ∀ k l n, ContinuousOn (fun s => (x s).2.2 k l n) (Icc 0 1) := fun k l n =>
    (show Continuous fun z : SecondOrderState m => z.2.2 k l n by fun_prop).comp_continuousOn hc
  have hq : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, (x t).1 k = (x 0).1 k + U k t := by
    intro k t ht
    have h := sub_eq_sub_zero (hqc k) (fun s hs hss => (hco s hs hss).1 k) (hU k) ht
    rw [hU0] at h
    linarith
  set V : Fin m → Fin m → ℝ → ℝ := fun k l t => ∫ s in (0 : ℝ)..t, U k s * u s l with hV_def
  have hV : ∀ k l t, HasDerivAt (V k l) (U k t * u t l) t := fun k l t =>
    (((hUc k).mul (huc l)).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hQ : ∀ k l, ∀ t ∈ Icc (0 : ℝ) 1,
      (x t).2.1 k l = (x 0).2.1 k l + (x 0).1 k * U l t + V k l t := by
    intro k l t ht
    have h := sub_eq_sub_zero (f := fun s => (x s).2.1 k l)
      (F := fun s => (x 0).1 k * U l s + V k l s) (g := fun s => ((x 0).1 k + U k s) * u s l)
      (hQc k l) (fun s hs hss => by
        have := (hco s hs hss).2.1 k l
        rwa [hq k s (Ioo_subset_Icc_self hs)] at this)
      (fun s => by
        have := ((hU l s).const_mul ((x 0).1 k)).add (hV k l s)
        convert this using 1
        ring) ht
    simp only [hU0, hV_def, intervalIntegral.integral_same, mul_zero, add_zero] at h
    linarith
  refine ⟨fun k => by rw [hq k 1 ⟨zero_le_one, le_rfl⟩, hU1, add_zero],
    fun k l => ?_, fun k l n hkl hidx => ?_⟩
  · rw [hQ k l 1 ⟨zero_le_one, le_rfl⟩, hU1, mul_zero, add_zero]
    have : V k l 1 = 0 := hP2 k l
    rw [this, add_zero]
  · have hV0 : (∀ t, V k l t = 0) ∨ ∀ t, u t n = 0 := by
      rcases hidx with ⟨hk, hk'⟩ | ⟨hl, hl'⟩ | ⟨hn, hn'⟩
      · left
        intro t
        simp [hV_def, hU_def, hk, hk']
      · left
        intro t
        simp [hV_def, hu, hl, hl']
      · right
        intro t
        simp [hu, hn, hn']
    have h := sub_eq_sub_zero (f := fun s => (x s).2.2 k l n)
      (F := fun s => ∫ r in (0 : ℝ)..s, ((x 0).2.1 k l + (x 0).1 k * U l r + V k l r) * u r n)
      (g := fun s => ((x 0).2.1 k l + (x 0).1 k * U l s + V k l s) * u s n)
      (hWc k l n) (fun s hs hss => by
        have := (hco s hs hss).2.2 k l n
        rwa [hQ k l s (Ioo_subset_Icc_self hs)] at this)
      (fun s => ((((continuous_const.add (continuous_const.mul (hUc l))).add
        (continuous_iff_continuousAt.2 fun r => (hV k l r).continuousAt)).mul
        (huc n)).integral_hasStrictDerivAt 0 s).hasDerivAt) ⟨zero_le_one, le_rfl⟩
    simp only [intervalIntegral.integral_same, sub_zero] at h
    have hz : ∫ r in (0 : ℝ)..1, ((x 0).2.1 k l + (x 0).1 k * U l r + V k l r) * u r n = 0 := by
      rcases hV0 with hV0 | hV0
      · have e : (fun r => ((x 0).2.1 k l + (x 0).1 k * U l r + V k l r) * u r n) =
            fun r => (x 0).2.1 k l * u r n + (x 0).1 k * (U l r * u r n) := by
          funext r
          rw [hV0 r]
          ring
        have j1 : IntervalIntegrable (fun r => (x 0).2.1 k l * u r n) MeasureTheory.volume 0 1 :=
          (show Continuous fun r => (x 0).2.1 k l * u r n from
            continuous_const.mul (huc n)).intervalIntegrable 0 1
        have j2 : IntervalIntegrable (fun r => (x 0).1 k * (U l r * u r n))
            MeasureTheory.volume 0 1 :=
          (show Continuous fun r => (x 0).1 k * (U l r * u r n) from
            continuous_const.mul ((hUc l).mul (huc n))).intervalIntegrable 0 1
        rw [e, intervalIntegral.integral_add j1 j2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, hint0 n, hP2 l n]
        ring
      · simp [hV0]
    linarith

/-- **Trajectories of (8.6) exist for continuous inputs** (MLS p. 361; for Algorithm 2, p. 362):
from every initial state there is a solution on all of `ℝ`, by iterated integrals; so the
hypotheses of `IsTrajectory.secondOrderGeneral_steering` are met for all `a, b`
(`IsTrajectory.of_hasDerivAt`). -/
theorem secondOrderGeneral_exists_solution {u : ℝ → Fin m → ℝ} (hu : Continuous u)
    (z₀ : SecondOrderState m) :
    ∃ x : ℝ → SecondOrderState m, x 0 = z₀ ∧
      ∀ t, HasDerivAt x (driftFree (secondOrderGeneralFields m) (x t) (u t)) t := by
  have huk : ∀ k, Continuous fun t => u t k := fun k => (continuous_apply k).comp hu
  have hprim : ∀ {f : ℝ → ℝ}, Continuous f → ∀ (c t : ℝ),
      HasDerivAt (fun t => c + ∫ s in (0 : ℝ)..t, f s) (f t) t := fun hf c t =>
    ((hf.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add c
  have hcont : ∀ {f : ℝ → ℝ}, Continuous f → ∀ c : ℝ,
      Continuous fun t => c + ∫ s in (0 : ℝ)..t, f s := fun hf c =>
    continuous_iff_continuousAt.2 fun t => (hprim hf c t).continuousAt
  set q : ℝ → Fin m → ℝ := fun t k => z₀.1 k + ∫ s in (0 : ℝ)..t, u s k with hq
  have hqc : ∀ k, Continuous fun t => q t k := fun k => hcont (huk k) _
  set Q : ℝ → Fin m → Fin m → ℝ := fun t k l => z₀.2.1 k l + ∫ s in (0 : ℝ)..t, q s k * u s l
    with hQ
  have hQc : ∀ k l, Continuous fun t => Q t k l := fun k l => hcont ((hqc k).mul (huk l)) _
  set W : ℝ → Fin m → Fin m → Fin m → ℝ :=
    fun t k l n => z₀.2.2 k l n + ∫ s in (0 : ℝ)..t, Q s k l * u s n with hW
  refine ⟨fun t => (q t, Q t, W t), ?_, fun t => ?_⟩
  · simp [q, Q, W]
  · rw [secondOrderGeneral_driftFree]
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
    · rw [hasDerivAt_pi]
      exact fun k => hprim (huk k) _ t
    · rw [hasDerivAt_pi]
      exact fun k => hasDerivAt_pi.2 fun l => hprim ((hqc k).mul (huk l)) _ t
    · rw [hasDerivAt_pi]
      exact fun k => hasDerivAt_pi.2 fun l => hasDerivAt_pi.2 fun n =>
        hprim ((hQc k l).mul (huk n)) _ t

end Nonholonomic
end RoboLean
