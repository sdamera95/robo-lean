import RoboLean.Nonholonomic.TwoInputs
import RoboLean.Nonholonomic.Controllability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Brockett's system and its optimal steering: MLS Chapter 8, §2.1

MLS Chapter 8, printed pp. 358–361: Brockett's system (8.2) `q̇₁ = u₁, q̇₂ = u₂,
q̇₃ = q₁ u₂ − q₂ u₁` with `g₁ = (1, 0, −q₂)`, `g₂ = (0, 1, q₁)`, `[g₁, g₂] = (0, 0, 2)`, "degree of
nonholonomy 2 and growth vector (2, 3)" (p. 359); the stationary inputs of the least squares problem
(8.3), `u̇ = Λ u`, `Λ = [[0, −λ], [λ, 0]]`, `u(t) = e^{Λt} u(0)`, the state from the origin
`(q₁, q₂)(t) = (e^{Λt} − I) Λ⁻¹ u(0)`, the condition `λ = 2nπ` for `q₁(1) = q₂(1) = 0`, the value
`q₃(1)` and the cost `∫₀¹ ‖u‖² = ‖u(0)‖²` (p. 360); and the `m`-input system (8.4)–(8.5)
`q̇ᵢ = uᵢ`, `q̇ᵢⱼ = qᵢ uⱼ − qⱼ uᵢ`, `Ẏ = q uᵀ − u qᵀ` (p. 360).

**Corrected printing (p. 360).** With the printed `Λ` and (8.2), the state from the origin has
`q₃(1) = +(u₁(0)² + u₂(0)²)/λ`, not `−(1/λ)(u₁(0)² + u₂(0)²)`: the integrand is
`q₁ u₂ − q₂ u₁ = (‖u(0)‖²/λ)(1 − cos λt)`. Hence the cost to reach `(0, 0, a)` is `‖u(0)‖² = λ a`
(printed `−λ a`), and for `a > 0` the least cost among these inputs is at `n = +1` (printed
`n = −1`); the value `‖u(0)‖² = 2π a` is unaffected.

**What is formalized.** Coordinates `q 0 = q₁`, `q 1 = q₂`, `q 2 = q₃`. The stationary inputs are
given explicitly and checked against (8.3) and (8.2); they are not shown to minimize the cost (the
book derives only the stationarity conditions). The `m`-input system is a drift-free system on
`(Fin m → ℝ) × (Fin m → Fin m → ℝ)` with the whole matrix `Y`; `Y` stays skew-symmetric when it
starts so, and its entries `Yᵢⱼ`, `i < j`, are the book's `qᵢⱼ`.
-/

noncomputable section

open Real Set VectorField Matrix
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS eq. (8.2), p. 359: `g₁ = (1, 0, −q₂)`** of Brockett's system. -/
def brockettG1 (q : Fin 3 → ℝ) : Fin 3 → ℝ := ![1, 0, -q 1]

/-- **MLS eq. (8.2), p. 359: `g₂ = (0, 1, q₁)`** of Brockett's system. -/
def brockettG2 (q : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 1, q 0]

/-- **MLS eq. (8.2), p. 358: the input fields `(g₁, g₂)` of Brockett's system.** -/
def brockettFields : Fin 2 → (Fin 3 → ℝ) → Fin 3 → ℝ := ![brockettG1, brockettG2]

/-- **MLS eq. (8.2), p. 358: `q̇ = (u₁, u₂, q₁ u₂ − q₂ u₁)`.** -/
theorem brockett_driftFree (q : Fin 3 → ℝ) (u : Fin 2 → ℝ) :
    driftFree brockettFields q u = ![u 0, u 1, q 0 * u 1 - q 1 * u 0] := by
  ext i
  fin_cases i <;> simp [driftFree, Fin.sum_univ_two, brockettFields, brockettG1, brockettG2]
  ring

/-- The derivative of `t ↦ G(q + t v)` at `0`, assembled from its components (supporting lemma
for MLS p. 359). -/
private theorem deriv_line {n : ℕ} (G : (Fin n → ℝ) → Fin n → ℝ) (q v w : Fin n → ℝ)
    (h : ∀ i, HasDerivAt (fun t : ℝ => G (q + t • v) i) (w i) 0) :
    deriv (fun t : ℝ => G (q + t • v)) 0 = w := by
  have hd : HasDerivAt (fun t : ℝ => G (q + t • v)) w 0 := by
    rw [hasDerivAt_pi]
    exact h
  exact hd.deriv

/-- The line `t ↦ a + t c` has derivative `c` at `0` (supporting lemma for MLS p. 359). -/
private theorem hasDerivAt_line (a c : ℝ) : HasDerivAt (fun t : ℝ => a + t * c) c 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add a

/-- `g₁` is differentiable (supporting lemma for MLS p. 359). -/
private theorem brockettG1_differentiable : Differentiable ℝ brockettG1 := by
  intro q
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [brockettG1]
  fun_prop

/-- `g₂` is differentiable (supporting lemma for MLS p. 359). -/
private theorem brockettG2_differentiable : Differentiable ℝ brockettG2 := by
  intro q
  refine differentiableAt_pi.2 fun i => ?_
  fin_cases i <;> simp [brockettG2]
  fun_prop

/-- **MLS p. 359: `[g₁, g₂] = (0, 0, 2)`.** -/
theorem brockett_lieBracket (q : Fin 3 → ℝ) :
    lieBracket ℝ brockettG1 brockettG2 q = ![0, 0, 2] := by
  rw [lieBracket_eq_deriv (brockettG1_differentiable q) (brockettG2_differentiable q),
    deriv_line brockettG2 q (brockettG1 q) ![0, 0, 1] ?_,
    deriv_line brockettG1 q (brockettG2 q) ![0, 0, -1] ?_]
  · ext i
    fin_cases i <;> simp
    norm_num
  all_goals
    intro i
    fin_cases i <;> simp [brockettG1, brockettG2] <;>
      first
      | exact hasDerivAt_const _ _
      | exact hasDerivAt_neg _
      | exact hasDerivAt_id _
      | simpa using hasDerivAt_line (q 0) 1

/-- `g₁(q), g₂(q), [g₁, g₂](q)` are independent (supporting lemma for MLS p. 359). -/
private theorem brockett_triple (q : Fin 3 → ℝ) :
    LinearIndependent ℝ ![brockettFields 0 q, brockettFields 1 q,
      lieBracket ℝ (brockettFields 0) (brockettFields 1) q] := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![brockettG1 q, brockettG2 q, ![0, 0, 2]])
    (by simp [Matrix.det_fin_three, brockettG1, brockettG2])
  convert h using 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact brockett_lieBracket q

/-- **MLS p. 359: degree of nonholonomy `2`** at every point. -/
theorem brockett_isDegreeOfNonholonomy (q : Fin 3 → ℝ) :
    IsDegreeOfNonholonomy brockettFields q 2 := by
  exact isDegreeOfNonholonomy_two brockettFields (Module.finrank_fin_fun ℝ) (brockett_triple q)

/-- **MLS p. 359: growth vector `(2, 3)`** (relative growth vector `(2, 1)`) at every point. -/
theorem brockett_growthVector (q : Fin 3 → ℝ) :
    growthVector brockettFields 2 q = ![2, 3] ∧
      relativeGrowthVector brockettFields 2 q = ![2, 1] := by
  exact growthVector_two brockettFields (brockett_triple q)

/-- **MLS p. 359 and Theorem 7.5, p. 329: the controllability rank condition** for Brockett's
system, `L(g₁, g₂)` has rank `3` at every point. -/
theorem brockett_lieAlgebraAt (q : Fin 3 → ℝ) : lieAlgebraAt brockettFields q = ⊤ := by
  refine lieAlgebraAt_eq_top_of_filtrationAt brockettFields
    (filtrationAt_eq_top_of_linearIndependent brockettFields (i := 2) (Module.finrank_fin_fun ℝ)
      (brockett_triple q) ?_)
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt brockettFields 0 (by norm_num) q
  · exact generator_mem_filtrationAt brockettFields 1 (by norm_num) q
  · exact lieBracket_mem_filtrationAt_two brockettFields le_rfl q

/-- **MLS p. 360: the stationary input `u(t) = e^{Λt} u(0)`**,
`u₁ = u₁(0) cos λt − u₂(0) sin λt`, `u₂ = u₁(0) sin λt + u₂(0) cos λt`. -/
def brockettInput (lam : ℝ) (u₀ : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![u₀ 0 * cos (lam * t) - u₀ 1 * sin (lam * t), u₀ 0 * sin (lam * t) + u₀ 1 * cos (lam * t)]

/-- **MLS eq. (8.3), p. 359: the stationary input solves `u̇ = Λ u`,** `Λ = [[0, −λ], [λ, 0]]`, the
Euler–Lagrange equations `q̈₁ + λ q̇₂ = 0`, `q̈₂ − λ q̇₁ = 0` with `λ` constant. -/
theorem brockettInput_hasDerivAt (lam : ℝ) (u₀ : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (brockettInput lam u₀) (!![0, -lam; lam, 0] *ᵥ brockettInput lam u₀ t) t := by
  have hl : HasDerivAt (fun s => lam * s) lam t := by simpa using (hasDerivAt_id t).const_mul lam
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · convert ((hl.cos).const_mul (u₀ 0)).sub ((hl.sin).const_mul (u₀ 1)) using 1
    · funext s
      simp [brockettInput]
    · simp [brockettInput, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · convert ((hl.sin).const_mul (u₀ 0)).add ((hl.cos).const_mul (u₀ 1)) using 1
    · funext s
      simp [brockettInput]
    · simp [brockettInput, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring

/-- **MLS p. 360: the state from the origin,** `(q₁, q₂)(t) = (e^{Λt} − I) Λ⁻¹ u(0)` and
`q₃(t) = (‖u(0)‖²/λ)(t − sin(λt)/λ)`. -/
def brockettState (lam : ℝ) (u₀ : Fin 2 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![(u₀ 0 * sin (lam * t) + u₀ 1 * (cos (lam * t) - 1)) / lam,
    (u₀ 1 * sin (lam * t) - u₀ 0 * (cos (lam * t) - 1)) / lam,
    (u₀ 0 ^ 2 + u₀ 1 ^ 2) / lam * (t - sin (lam * t) / lam)]

/-- **MLS p. 360:** the state starts at the origin. -/
theorem brockettState_zero (lam : ℝ) (u₀ : Fin 2 → ℝ) : brockettState lam u₀ 0 = 0 := by
  ext i
  fin_cases i <;> simp [brockettState]

/-- **MLS eq. (8.2), p. 358, and p. 360:** for `λ ≠ 0` the state solves (8.2) with the stationary
input at every time. -/
theorem brockettState_hasDerivAt {lam : ℝ} (hlam : lam ≠ 0) (u₀ : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (brockettState lam u₀)
      (driftFree brockettFields (brockettState lam u₀ t) (brockettInput lam u₀ t)) t := by
  have hl : HasDerivAt (fun s => lam * s) lam t := by simpa using (hasDerivAt_id t).const_mul lam
  rw [brockett_driftFree, hasDerivAt_pi]
  intro i
  fin_cases i
  · convert (((hl.sin).const_mul (u₀ 0)).add (((hl.cos).sub_const 1).const_mul (u₀ 1))).div_const
      lam using 1
    · funext s
      simp [brockettState]
    · simp [brockettInput]
      field_simp
      ring
  · convert (((hl.sin).const_mul (u₀ 1)).sub (((hl.cos).sub_const 1).const_mul (u₀ 0))).div_const
      lam using 1
    · funext s
      simp [brockettState]
    · simp [brockettInput]
      field_simp
      ring
  · convert ((hasDerivAt_id t).sub ((hl.sin).div_const lam)).const_mul
      ((u₀ 0 ^ 2 + u₀ 1 ^ 2) / lam) using 1
    · funext s
      simp [brockettState]
    simp [brockettInput, brockettState]
    field_simp
    linear_combination (u₀ 0 ^ 2 + u₀ 1 ^ 2) * sin_sq_add_cos_sq (lam * t)

/-- **MLS p. 360: `q₁(1) = q₂(1) = 0` forces `λ = 2nπ`,** for `λ ≠ 0` and `u(0) ≠ 0`. -/
theorem brockettState_one_eq_zero_iff {lam : ℝ} (hlam : lam ≠ 0) {u₀ : Fin 2 → ℝ} (hu₀ : u₀ ≠ 0) :
    (brockettState lam u₀ 1 0 = 0 ∧ brockettState lam u₀ 1 1 = 0) ↔ ∃ n : ℤ, lam = 2 * n * π := by
  have hr : 0 < u₀ 0 ^ 2 + u₀ 1 ^ 2 := by
    by_contra h
    apply hu₀
    have h0 : u₀ 0 = 0 := by nlinarith [sq_nonneg (u₀ 0), sq_nonneg (u₀ 1)]
    have h1 : u₀ 1 = 0 := by nlinarith [sq_nonneg (u₀ 0), sq_nonneg (u₀ 1)]
    ext i
    fin_cases i <;> simp [h0, h1]
  simp only [brockettState, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, div_eq_zero_iff,
    hlam, or_false]
  constructor
  · rintro ⟨hA, hB⟩
    have hc : cos lam = 1 := by
      have h := congrArg₂ (fun x y => x ^ 2 + y ^ 2) hA hB
      have h2 : (u₀ 0 ^ 2 + u₀ 1 ^ 2) * (2 - 2 * cos lam) = 0 := by
        linear_combination h - (u₀ 0 ^ 2 + u₀ 1 ^ 2) * sin_sq_add_cos_sq lam
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd h3 hr.ne'
      · linarith
    obtain ⟨n, hn⟩ := (cos_eq_one_iff lam).1 hc
    exact ⟨n, by rw [← hn]; ring⟩
  · rintro ⟨n, rfl⟩
    have hs : sin (2 * n * π) = 0 := by
      rw [show 2 * (n : ℝ) * π = ((2 * n : ℤ) : ℝ) * π by push_cast; ring]
      exact sin_int_mul_pi _
    have hc : cos (2 * n * π) = 1 := by
      rw [show 2 * (n : ℝ) * π = (n : ℝ) * (2 * π) by ring]
      exact cos_int_mul_two_pi _
    simp [hs, hc]

/-- **MLS p. 360, corrected printing: `q₃(1) = +‖u(0)‖²/λ`** for `λ = 2nπ`; the state at time `1`
is `(0, 0, ‖u(0)‖²/(2nπ))` (MLS prints `q₃(1) = −(1/λ)(u₁²(0) + u₂²(0))`). The book takes
`n ≠ 0`; for `n = 0` both sides are zero by Mathlib's convention `x / 0 = 0`. -/
theorem brockettState_one (n : ℤ) (u₀ : Fin 2 → ℝ) :
    brockettState (2 * n * π) u₀ 1 = ![0, 0, (u₀ 0 ^ 2 + u₀ 1 ^ 2) / (2 * n * π)] := by
  have hs : sin (2 * n * π) = 0 := by
    rw [show 2 * (n : ℝ) * π = ((2 * n : ℤ) : ℝ) * π by push_cast; ring]
    exact sin_int_mul_pi _
  have hc : cos (2 * n * π) = 1 := by
    rw [show 2 * (n : ℝ) * π = (n : ℝ) * (2 * π) by ring]
    exact cos_int_mul_two_pi _
  ext i
  fin_cases i <;> simp [brockettState, hs, hc]

/-- **MLS p. 360: the cost `∫₀¹ ‖u‖² dt = ‖u(0)‖²`** of the stationary input. -/
theorem brockettInput_cost (lam : ℝ) (u₀ : Fin 2 → ℝ) :
    ∫ t in (0 : ℝ)..1, brockettInput lam u₀ t ⬝ᵥ brockettInput lam u₀ t = u₀ 0 ^ 2 + u₀ 1 ^ 2 := by
  have h : ∀ t, brockettInput lam u₀ t ⬝ᵥ brockettInput lam u₀ t = u₀ 0 ^ 2 + u₀ 1 ^ 2 := by
    intro t
    simp only [brockettInput, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (u₀ 0 ^ 2 + u₀ 1 ^ 2) * sin_sq_add_cos_sq (lam * t)
  simp [h]

/-- **MLS p. 360, corrected printing: the least cost among the stationary inputs.** If the
stationary input with `λ = 2nπ`, `n ≠ 0`, steers the origin to `(0, 0, a)` with `a > 0`, then
`n ≥ 1`, its cost is `‖u(0)‖² = 2nπ a ≥ 2π a`, with equality exactly for `n = 1` (MLS prints `−λ a`
and `n = −1`). -/
theorem brockett_cost_ge {n : ℤ} (hn : n ≠ 0) {u₀ : Fin 2 → ℝ} {a : ℝ} (ha : 0 < a)
    (h : brockettState (2 * n * π) u₀ 1 2 = a) :
    1 ≤ n ∧ u₀ 0 ^ 2 + u₀ 1 ^ 2 = 2 * n * π * a ∧ 2 * π * a ≤ u₀ 0 ^ 2 + u₀ 1 ^ 2 ∧
      (u₀ 0 ^ 2 + u₀ 1 ^ 2 = 2 * π * a ↔ n = 1) := by
  have h3 : brockettState (2 * n * π) u₀ 1 2 = (u₀ 0 ^ 2 + u₀ 1 ^ 2) / (2 * n * π) := by
    rw [brockettState_one n]
    rfl
  rw [h3] at h
  have hr : 0 ≤ u₀ 0 ^ 2 + u₀ 1 ^ 2 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hd : (2 * n * π : ℝ) ≠ 0 := by positivity
  have hcost : u₀ 0 ^ 2 + u₀ 1 ^ 2 = 2 * n * π * a := by
    rw [← h]
    field_simp
  have hpos : (0 : ℝ) < n := by
    by_contra hneg
    push Not at hneg
    have : 2 * (n : ℝ) * π * a ≤ 0 := by
      have : 2 * (n : ℝ) * π ≤ 0 := by nlinarith [pi_pos]
      nlinarith
    have hlt : 2 * (n : ℝ) * π * a < 0 := by
      have : 2 * (n : ℝ) * π < 0 := by
        have : (n : ℝ) < 0 := lt_of_le_of_ne hneg hn0
        nlinarith [pi_pos]
      nlinarith
    linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hpos
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  refine ⟨hn1, hcost, ?_, ?_⟩
  · rw [hcost]
    nlinarith [pi_pos]
  · rw [hcost]
    constructor
    · intro he
      have : ((n : ℝ) - 1) * (2 * π * a) = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact_mod_cast (sub_eq_zero.1 h1)
      · nlinarith [pi_pos]
    · rintro rfl
      simp

/-- **MLS eqs. (8.4)–(8.5), p. 360: the input fields of the `m`-input system** on
`ℝ^m × ℝ^{m×m}`: `gⱼ(q, Y) = (eⱼ, q eⱼᵀ − eⱼ qᵀ)`. -/
def brockettSystemFields (m : ℕ) :
    Fin m → (Fin m → ℝ) × (Fin m → Fin m → ℝ) → (Fin m → ℝ) × (Fin m → Fin m → ℝ) :=
  fun j z => (Pi.single j 1, fun a b =>
    z.1 a * (Pi.single j (1 : ℝ) : Fin m → ℝ) b - (Pi.single j (1 : ℝ) : Fin m → ℝ) a * z.1 b)

/-- **MLS eq. (8.5), p. 360: `q̇ = u`, `Ẏ = q uᵀ − u qᵀ`.** -/
theorem brockettSystem_driftFree (m : ℕ) (z : (Fin m → ℝ) × (Fin m → Fin m → ℝ)) (u : Fin m → ℝ) :
    driftFree (brockettSystemFields m) z u = (u, fun a b => z.1 a * u b - u a * z.1 b) := by
  ext i
  · simp [driftFree, brockettSystemFields, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [driftFree, brockettSystemFields, Prod.snd_sum, Finset.sum_apply, Pi.single_apply,
      mul_sub, Finset.sum_sub_distrib]
    ring

/-- **MLS eq. (8.4), p. 360: `q̇ᵢⱼ = qᵢ uⱼ − qⱼ uᵢ`,** and the rate of `Y` is skew-symmetric
(`Y ∈ so(m)` is preserved). -/
theorem brockettSystem_driftFree_snd (m : ℕ) (z : (Fin m → ℝ) × (Fin m → Fin m → ℝ))
    (u : Fin m → ℝ) (i j : Fin m) :
    (driftFree (brockettSystemFields m) z u).2 i j = z.1 i * u j - z.1 j * u i ∧
      (driftFree (brockettSystemFields m) z u).2 j i =
        -(driftFree (brockettSystemFields m) z u).2 i j := by
  rw [brockettSystem_driftFree]
  exact ⟨by ring, by ring⟩

end Examples
end RoboLean
