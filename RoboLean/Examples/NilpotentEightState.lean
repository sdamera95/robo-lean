import RoboLean.Nonholonomic.Nilpotent
import RoboLean.Nonholonomic.TwoInputs
import RoboLean.Nonholonomic.Controllability
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# An eight-state nilpotent system: MLS Chapter 8, Exercise 1

MLS Chapter 8, Exercise 1, printed p. 391: "Show that the following system
`q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₁u₂, q̇₄ = ½q₁²u₂, q̇₅ = q₁q₂u₂, q̇₆ = ⅙q₁³u₁, q̇₇ = ½q₁²q₂u₂,
q̇₈ = ½q₁q₂²u₂` is controllable and nilpotent of degree four. Can you find a nonlinear change of
coordinates to transform this system into a one-chained form?" (display rendered).

**What is formalized.**
* As printed the system is not controllable: `q₆ − q₁⁴/24` is constant along every trajectory,
  since `q̇₆ = ⅙q₁³u₁ = d/dt(q₁⁴/24)`; hence no state with a different value of it is reachable,
  and `IsControllable` fails for every input set.
* Corrected printing: with `q̇₆ = ⅙q₁³u₂` (the pattern of the other rows, every coordinate after
  `q₂` driven by `u₂`), the fields `g₁ = e₁`, `g₂ = (0, 1, q₁, ½q₁², q₁q₂, ⅙q₁³, ½q₁²q₂, ½q₁q₂²)`
  have the brackets `[g₁, g₂] = (0, 0, 1, q₁, q₂, ½q₁², q₁q₂, ½q₂²)`, `[g₁, [g₁, g₂]]`,
  `[g₂, [g₁, g₂]]` and the four constant brackets of length four `e₆, e₇, e₇, e₈`: the
  controllability rank condition at every point (Theorem 7.5, p. 329), the growth vector
  `(2, 3, 5, 8)`, the degree of nonholonomy `4`, and the order of nilpotency `4` in the sense of
  p. 344 (every Lie product of length greater than `4` is zero; `[g₁, [g₁, [g₁, g₂]]] ≠ 0`).
* The question on a one-chained form is not formalized; the one-chain system on `ℝ⁸` has growth
  vector `(2, 3, 4, 5, 6, 7, 8)` (Lemma 8.1), and the invariance of the growth vector under
  changes of coordinates and of inputs that would settle the question negatively is not proved
  here.

Coordinates `q 0 = q₁`, …, `q 7 = q₈`; fields as functions of `(q₁, q₂)` (`baseField`).
-/

noncomputable section

open Set VectorField Matrix MeasureTheory
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Chapter 8, Exercise 1, p. 391, as printed: `g₁ = (1, 0, 0, 0, 0, ⅙q₁³, 0, 0)`.** -/
def eightPrintedG1 (q : Fin 8 → ℝ) : Fin 8 → ℝ := ![1, 0, 0, 0, 0, q 0 ^ 3 / 6, 0, 0]

/-- **MLS Chapter 8, Exercise 1, p. 391: `g₂ = (0, 1, q₁, ½q₁², q₁q₂, 0, ½q₁²q₂, ½q₁q₂²)`** as
printed. -/
def eightPrintedG2 (q : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![0, 1, q 0, q 0 ^ 2 / 2, q 0 * q 1, 0, q 0 ^ 2 * q 1 / 2, q 0 * q 1 ^ 2 / 2]

/-- **MLS Chapter 8, Exercise 1, p. 391: the input fields of the system as printed.** -/
def eightPrintedFields : Fin 2 → (Fin 8 → ℝ) → Fin 8 → ℝ := ![eightPrintedG1, eightPrintedG2]

/-- **MLS Chapter 8, Exercise 1, p. 391: the printed system** `q̇₁ = u₁, q̇₂ = u₂, q̇₃ = q₁u₂,
q̇₄ = ½q₁²u₂, q̇₅ = q₁q₂u₂, q̇₆ = ⅙q₁³u₁, q̇₇ = ½q₁²q₂u₂, q̇₈ = ½q₁q₂²u₂`. -/
theorem eightPrinted_driftFree (q : Fin 8 → ℝ) (u : Fin 2 → ℝ) :
    driftFree eightPrintedFields q u = ![u 0, u 1, q 0 * u 1, q 0 ^ 2 / 2 * u 1, q 0 * q 1 * u 1,
      q 0 ^ 3 / 6 * u 0, q 0 ^ 2 * q 1 / 2 * u 1, q 0 * q 1 ^ 2 / 2 * u 1] := by
  ext i
  fin_cases i <;>
    simp [driftFree, Fin.sum_univ_two, eightPrintedFields, eightPrintedG1, eightPrintedG2] <;> ring

/-- **MLS Chapter 8, Exercise 1, p. 391, as printed: a first integral.** Along every trajectory on
`[0, T]`, `T ≥ 0`, the quantity `q₆ − q₁⁴/24` keeps its initial value, since
`q̇₆ = ⅙q₁³u₁ = d/dt (q₁⁴/24)`. -/
theorem IsTrajectory.eightPrinted_firstIntegral {u : ℝ → Fin 2 → ℝ} {T : ℝ} {x : ℝ → Fin 8 → ℝ}
    (hx : IsTrajectory eightPrintedFields u T x) (hT : 0 ≤ T) :
    x T 5 - x T 0 ^ 4 / 24 = x 0 5 - x 0 0 ^ 4 / 24 := by
  obtain ⟨hc, S, hd⟩ := hx
  have hφc : ContinuousOn (fun t => x t 5 - x t 0 ^ 4 / 24) (Icc 0 T) := by
    have h5 : ContinuousOn (fun t => x t 5) (Icc 0 T) := (continuous_apply 5).comp_continuousOn hc
    have h0 : ContinuousOn (fun t => x t 0) (Icc 0 T) := (continuous_apply 0).comp_continuousOn hc
    exact h5.sub ((h0.pow 4).div_const 24)
  have hφd : ∀ t ∈ Ioo 0 T \ (S : Set ℝ),
      HasDerivAt (fun t => x t 5 - x t 0 ^ 4 / 24) 0 t := by
    rintro t ⟨ht, htS⟩
    have h := hd t ht htS
    have h5 := (hasDerivAt_pi.1 h) 5
    have h0 := (hasDerivAt_pi.1 h) 0
    have e5 : driftFree eightPrintedFields (x t) (u t) 5 = x t 0 ^ 3 / 6 * u t 0 := by
      rw [eightPrinted_driftFree]
      rfl
    have e0 : driftFree eightPrintedFields (x t) (u t) 0 = u t 0 := by
      rw [eightPrinted_driftFree]
      rfl
    rw [e5] at h5
    rw [e0] at h0
    convert h5.sub ((h0.pow 4).div_const 24) using 1
    push_cast
    ring
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le (fun t => x t 5 - x t 0 ^ 4 / 24)
    (fun _ => (0 : ℝ)) hT S.countable_toSet hφc
    (fun t ht => hφd t ⟨ht.1, ht.2⟩) intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hftc
  linarith

/-- **MLS Chapter 8, Exercise 1, p. 391: the printed system is not controllable** (corrected
printing needed): for every input set, the state `e₆` (all coordinates zero except `q₆ = 1`) is not
reachable from the origin, by the first integral `q₆ − q₁⁴/24`. -/
theorem eightPrinted_not_isControllable (U : Set (Fin 2 → ℝ)) :
    ¬ IsControllable eightPrintedFields U := by
  intro h
  obtain ⟨T, hT, u, x, -, hx, h0, hT', -⟩ := h 0 (Pi.single 5 1)
  have hI := IsTrajectory.eightPrinted_firstIntegral hx hT.le
  rw [h0, hT'] at hI
  simp at hI

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: `g₁ = e₁`** as a function of
`(q₁, q₂)`. -/
def eightG1 (_a _b : ℝ) : Fin 8 → ℝ := ![1, 0, 0, 0, 0, 0, 0, 0]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing (`q̇₆ = ⅙q₁³u₂`):
`g₂ = (0, 1, q₁, ½q₁², q₁q₂, ⅙q₁³, ½q₁²q₂, ½q₁q₂²)`** as a function of `(q₁, q₂)`. -/
def eightG2 (a b : ℝ) : Fin 8 → ℝ := ![0, 1, a, a ^ 2 / 2, a * b, a ^ 3 / 6, a ^ 2 * b / 2, a * b ^ 2 / 2]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: the input fields `(g₁, g₂)`.** -/
def eightFields : Fin 2 → (Fin 8 → ℝ) → Fin 8 → ℝ := ![baseField eightG1, baseField eightG2]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing:
`[g₁, g₂] = (0, 0, 1, q₁, q₂, ½q₁², q₁q₂, ½q₂²)`.** -/
def eightC (a b : ℝ) : Fin 8 → ℝ := ![0, 0, 1, a, b, a ^ 2 / 2, a * b, b ^ 2 / 2]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing:
`[g₁, [g₁, g₂]] = (0, 0, 0, 1, 0, q₁, q₂, 0)`.** -/
def eightB1 (a b : ℝ) : Fin 8 → ℝ := ![0, 0, 0, 1, 0, a, b, 0]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing:
`[g₂, [g₁, g₂]] = (0, 0, 0, 0, 1, 0, q₁, q₂)`.** -/
def eightB2 (a b : ℝ) : Fin 8 → ℝ := ![0, 0, 0, 0, 1, 0, a, b]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: `[g₁, [g₁, [g₁, g₂]]] = e₆`.** -/
def eightE6 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 1, 0, 0]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing:
`[g₂, [g₁, [g₁, g₂]]] = [g₁, [g₂, [g₁, g₂]]] = e₇`.** -/
def eightE7 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, 1, 0]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: `[g₂, [g₂, [g₁, g₂]]] = e₈`.** -/
def eightE8 : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 1]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: the system** `q̇₁ = u₁, q̇₂ = u₂,
q̇₃ = q₁u₂, q̇₄ = ½q₁²u₂, q̇₅ = q₁q₂u₂, q̇₆ = ⅙q₁³u₂, q̇₇ = ½q₁²q₂u₂, q̇₈ = ½q₁q₂²u₂`. -/
theorem eight_driftFree (q : Fin 8 → ℝ) (u : Fin 2 → ℝ) :
    driftFree eightFields q u = ![u 0, u 1, q 0 * u 1, q 0 ^ 2 / 2 * u 1, q 0 * q 1 * u 1,
      q 0 ^ 3 / 6 * u 1, q 0 ^ 2 * q 1 / 2 * u 1, q 0 * q 1 ^ 2 / 2 * u 1] := by
  ext i
  fin_cases i <;> simp [driftFree, Fin.sum_univ_two, eightFields, baseField, eightG1, eightG2] <;>
    ring

private theorem diff_base {H : ℝ → ℝ → Fin 8 → ℝ} (h : ∀ i, Differentiable ℝ fun q : Fin 8 → ℝ =>
    H (q 0) (q 1) i) (q : Fin 8 → ℝ) : DifferentiableAt ℝ (baseField H) q :=
  differentiableAt_pi.2 fun i => (h i) q

private theorem diff_g1 (q : Fin 8 → ℝ) : DifferentiableAt ℝ (baseField eightG1) q :=
  diff_base (fun i => by fin_cases i <;> simp [eightG1]) q

private theorem diff_g2 (q : Fin 8 → ℝ) : DifferentiableAt ℝ (baseField eightG2) q :=
  diff_base (fun i => by fin_cases i <;> simp [eightG2] <;> fun_prop) q

private theorem diff_c (q : Fin 8 → ℝ) : DifferentiableAt ℝ (baseField eightC) q :=
  diff_base (fun i => by fin_cases i <;> simp [eightC] <;> fun_prop) q

private theorem diff_b1 (q : Fin 8 → ℝ) : DifferentiableAt ℝ (baseField eightB1) q :=
  diff_base (fun i => by fin_cases i <;> simp [eightB1] <;> fun_prop) q

private theorem diff_b2 (q : Fin 8 → ℝ) : DifferentiableAt ℝ (baseField eightB2) q :=
  diff_base (fun i => by fin_cases i <;> simp [eightB2] <;> fun_prop) q

private theorem d_g1a (a b : ℝ) : HasDerivAt (fun a => eightG1 a b) 0 a := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightG1] <;> poly_hasDerivAt

private theorem d_g1b (a b : ℝ) : HasDerivAt (fun b => eightG1 a b) 0 b := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightG1] <;> poly_hasDerivAt

private theorem d_g2a (a b : ℝ) : HasDerivAt (fun a => eightG2 a b) (eightC a b) a := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightG2, eightC] <;> poly_hasDerivAt

private theorem d_g2b (a b : ℝ) :
    HasDerivAt (fun b => eightG2 a b) ![0, 0, 0, 0, a, 0, a ^ 2 / 2, a * b] b := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightG2] <;> poly_hasDerivAt

private theorem d_ca (a b : ℝ) : HasDerivAt (fun a => eightC a b) (eightB1 a b) a := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightC, eightB1] <;> poly_hasDerivAt

private theorem d_cb (a b : ℝ) : HasDerivAt (fun b => eightC a b) (eightB2 a b) b := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightC, eightB2] <;> poly_hasDerivAt

private theorem d_b1a (a b : ℝ) : HasDerivAt (fun a => eightB1 a b) eightE6 a := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightB1, eightE6] <;> poly_hasDerivAt

private theorem d_b1b (a b : ℝ) : HasDerivAt (fun b => eightB1 a b) eightE7 b := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightB1, eightE7] <;> poly_hasDerivAt

private theorem d_b2a (a b : ℝ) : HasDerivAt (fun a => eightB2 a b) eightE7 a := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightB2, eightE7] <;> poly_hasDerivAt

private theorem d_b2b (a b : ℝ) : HasDerivAt (fun b => eightB2 a b) eightE8 b := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i <;> simp [eightB2, eightE8] <;> poly_hasDerivAt

/-- `[gⱼ, H] = ∂H/∂qⱼ` for a field `H` of `(q₁, q₂)` with zero first two coordinates (supporting
lemma for MLS p. 391). -/
private theorem eight_bracket_vert (j : Fin 2) {H Ha Hb : ℝ → ℝ → Fin 8 → ℝ}
    (hd : ∀ q, DifferentiableAt ℝ (baseField H) q) (h0 : ∀ a b, H a b 0 = 0)
    (h1 : ∀ a b, H a b 1 = 0) (ha : ∀ a b, HasDerivAt (fun a => H a b) (Ha a b) a)
    (hb : ∀ a b, HasDerivAt (fun b => H a b) (Hb a b) b) :
    lieBracket ℝ (eightFields j) (baseField H) = baseField (![Ha, Hb] j) := by
  funext q
  fin_cases j
  · show lieBracket ℝ (baseField eightG1) (baseField H) q = _
    rw [lieBracket_baseField (diff_g1 q) (hd q) (d_g1a _ _) (d_g1b _ _) (ha _ _) (hb _ _)]
    simp [h0, h1, eightG1, baseField]
  · show lieBracket ℝ (baseField eightG2) (baseField H) q = _
    rw [lieBracket_baseField (diff_g2 q) (hd q) (d_g2a _ _) (d_g2b _ _) (ha _ _) (hb _ _)]
    simp [h0, h1, eightG2, baseField]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing:
`[g₁, g₂] = (0, 0, 1, q₁, q₂, ½q₁², q₁q₂, ½q₂²)`.** -/
theorem eight_lieBracket : lieBracket ℝ (eightFields 0) (eightFields 1) = baseField eightC := by
  funext q
  show lieBracket ℝ (baseField eightG1) (baseField eightG2) q = _
  rw [lieBracket_baseField (diff_g1 q) (diff_g2 q) (d_g1a _ _) (d_g1b _ _) (d_g2a _ _) (d_g2b _ _)]
  simp [eightG1, eightG2, baseField]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: `[g₁, [g₁, g₂]]` and
`[g₂, [g₁, g₂]]`.** -/
theorem eight_lieBracket_c (j : Fin 2) :
    lieBracket ℝ (eightFields j) (baseField eightC) = baseField (![eightB1, eightB2] j) :=
  eight_bracket_vert j diff_c (fun _ _ => rfl) (fun _ _ => rfl) d_ca d_cb

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: `[g₁, [g₁, [g₁, g₂]]] = e₆` and
`[g₂, [g₁, [g₁, g₂]]] = e₇`.** -/
theorem eight_lieBracket_b1 (j : Fin 2) :
    lieBracket ℝ (eightFields j) (baseField eightB1) = fun _ => ![eightE6, eightE7] j := by
  rw [eight_bracket_vert j diff_b1 (fun _ _ => rfl) (fun _ _ => rfl) d_b1a d_b1b]
  fin_cases j <;> rfl

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: `[g₁, [g₂, [g₁, g₂]]] = e₇` and
`[g₂, [g₂, [g₁, g₂]]] = e₈`.** -/
theorem eight_lieBracket_b2 (j : Fin 2) :
    lieBracket ℝ (eightFields j) (baseField eightB2) = fun _ => ![eightE7, eightE8] j := by
  rw [eight_bracket_vert j diff_b2 (fun _ _ => rfl) (fun _ _ => rfl) d_b2a d_b2b]
  fin_cases j <;> rfl

/-- The eight vectors at `q` (supporting definition for MLS p. 391). -/
private def eightVecs (q : Fin 8 → ℝ) : Fin 8 → Fin 8 → ℝ :=
  ![eightG1 (q 0) (q 1), eightG2 (q 0) (q 1), eightC (q 0) (q 1), eightB1 (q 0) (q 1),
    eightB2 (q 0) (q 1), eightE6, eightE7, eightE8]

private theorem eightVecs_independent (q : Fin 8 → ℝ) : LinearIndependent ℝ (eightVecs q) := by
  refine Matrix.linearIndependent_rows_of_det_ne_zero (A := Matrix.of (eightVecs q)) ?_
  have hu : (Matrix.of (eightVecs q)).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [eightVecs, eightG1, eightG2, eightC, eightB1, eightB2, eightE6, eightE7, eightE8]
  rw [Matrix.det_of_isUpperTriangular hu]
  simp [Fin.prod_univ_succ, eightVecs, eightG1, eightG2, eightC, eightB1, eightB2, eightE6, eightE7,
    eightE8]

/-- The field values of the eight brackets lie in the filtration level `4` (supporting lemma for
MLS p. 391). -/
private theorem eightVecs_mem (q : Fin 8 → ℝ) (k : Fin 8) :
    eightVecs q k ∈ filtrationAt eightFields 4 q := by
  have h1 : ∀ j, eightFields j ∈ filtrationFields eightFields 1 := fun j => by
    rw [filtrationFields_one]
    exact ⟨j, rfl⟩
  have hc : baseField eightC ∈ filtrationFields eightFields 2 := by
    rw [← eight_lieBracket]
    exact lieBracket_mem_filtrationFields eightFields 0 (h1 1)
  have hb : ∀ j, baseField (![eightB1, eightB2] j) ∈ filtrationFields eightFields 3 := fun j => by
    rw [← eight_lieBracket_c j]
    exact lieBracket_mem_filtrationFields eightFields j hc
  have hb1 := hb 0
  have hb2 := hb 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb1 hb2
  have he1 : ∀ j, (fun _ => ![eightE6, eightE7] j) ∈ filtrationFields eightFields 4 := fun j => by
    rw [← eight_lieBracket_b1 j]
    exact lieBracket_mem_filtrationFields eightFields j hb1
  have he2 : ∀ j, (fun _ => ![eightE7, eightE8] j) ∈ filtrationFields eightFields 4 := fun j => by
    rw [← eight_lieBracket_b2 j]
    exact lieBracket_mem_filtrationFields eightFields j hb2
  have mono : ∀ {i} {f}, f ∈ filtrationFields eightFields i → i ≤ 4 →
      f q ∈ filtrationAt eightFields 4 q := fun hf hi =>
    mem_spanAt (filtrationFields_mono eightFields hi hf) q
  fin_cases k
  · exact mono (h1 0) (by norm_num)
  · exact mono (h1 1) (by norm_num)
  · exact mono hc (by norm_num)
  · exact mono hb1 (by norm_num)
  · exact mono hb2 (by norm_num)
  · exact mono (he1 0) le_rfl
  · exact mono (he1 1) le_rfl
  · exact mono (he2 1) le_rfl

/-- `Δ₄(q) = ℝ⁸` (supporting lemma for MLS p. 391). -/
private theorem eight_filtrationAt_four (q : Fin 8 → ℝ) : filtrationAt eightFields 4 q = ⊤ :=
  filtrationAt_eq_top_of_linearIndependent eightFields (Module.finrank_fin_fun ℝ)
    (eightVecs_independent q) (eightVecs_mem q)

/-- **MLS Chapter 8, Exercise 1, p. 391 ("controllable"), corrected printing, with Theorem 7.5,
p. 329: the controllability rank condition** at every point, `L(g₁, g₂)` has rank `8`. -/
theorem eight_lieAlgebraAt (q : Fin 8 → ℝ) : lieAlgebraAt eightFields q = ⊤ :=
  lieAlgebraAt_eq_top_of_filtrationAt eightFields (eight_filtrationAt_four q)

/-- The negative of a field of `q₁, q₂` is one (supporting lemma for MLS p. 391). -/
private theorem isBase_neg {X : (Fin 8 → ℝ) → Fin 8 → ℝ} (hX : IsBase X) : IsBase (-X) := by
  intro q v h0 h1
  simp [hX q v h0 h1]

/-- The classification of the Lie products by length (supporting statement for MLS p. 391). -/
private def EightClass (l : ℕ) (A : (Fin 8 → ℝ) → Fin 8 → ℝ) : Prop :=
  (l = 1 → A = eightFields 0 ∨ A = eightFields 1) ∧
    (l = 2 → A = 0 ∨ A = baseField eightC ∨ A = -baseField eightC) ∧
    (l = 3 → A = 0 ∨ A = baseField eightB1 ∨ A = -baseField eightB1 ∨ A = baseField eightB2 ∨
      A = -baseField eightB2) ∧
    (2 ≤ l → IsBase A ∧ ∀ q, A q 0 = 0 ∧ A q 1 = 0) ∧
    (4 ≤ l → ∃ v : Fin 8 → ℝ, v 0 = 0 ∧ v 1 = 0 ∧ A = fun _ => v) ∧
    (5 ≤ l → A = 0)

private theorem eightClass_const {l : ℕ} (hl : 4 ≤ l) {v : Fin 8 → ℝ} (h0 : v 0 = 0)
    (h1 : v 1 = 0) (h5 : 5 ≤ l → v = 0) : EightClass l (fun _ => v) := by
  refine ⟨fun h => by omega, fun h => by omega, fun h => by omega,
    fun _ => ⟨isBase_const v, fun _ => ⟨h0, h1⟩⟩, fun _ => ⟨v, h0, h1, rfl⟩, fun h => ?_⟩
  funext q
  simp [h5 h]

private theorem eightFields_isBase (j : Fin 2) : IsBase (eightFields j) := by
  fin_cases j
  · exact isBase_baseField eightG1
  · exact isBase_baseField eightG2

private theorem vert_neg {X : (Fin 8 → ℝ) → Fin 8 → ℝ} (h : ∀ q, X q 0 = 0 ∧ X q 1 = 0) :
    ∀ q, (-X) q 0 = 0 ∧ (-X) q 1 = 0 := fun q => by simp [(h q).1, (h q).2]

private theorem eightClass_three {A : (Fin 8 → ℝ) → Fin 8 → ℝ}
    (h : A = 0 ∨ A = baseField eightB1 ∨ A = -baseField eightB1 ∨ A = baseField eightB2 ∨
      A = -baseField eightB2) : EightClass 3 A := by
  have vb1 : ∀ q, baseField eightB1 q 0 = 0 ∧ baseField eightB1 q 1 = 0 :=
    fun q => ⟨rfl, rfl⟩
  have vb2 : ∀ q, baseField eightB2 q 0 = 0 ∧ baseField eightB2 q 1 = 0 :=
    fun q => ⟨rfl, rfl⟩
  refine ⟨fun h => by omega, fun h => by omega, fun _ => h, fun _ => ?_, fun h => by omega,
    fun h => by omega⟩
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨isBase_const 0, fun _ => ⟨rfl, rfl⟩⟩
  · exact ⟨isBase_baseField _, vb1⟩
  · exact ⟨isBase_neg (isBase_baseField _), vert_neg vb1⟩
  · exact ⟨isBase_baseField _, vb2⟩
  · exact ⟨isBase_neg (isBase_baseField _), vert_neg vb2⟩

private theorem eight_gen_c (i : Fin 2) (B : (Fin 8 → ℝ) → Fin 8 → ℝ)
    (hB : B = 0 ∨ B = baseField eightC ∨ B = -baseField eightC) :
    EightClass 3 (lieBracket ℝ (eightFields i) B) := by
  apply eightClass_three
  rcases hB with rfl | rfl | rfl
  · exact Or.inl (lieBracket_zero_right)
  · rw [eight_lieBracket_c i]
    fin_cases i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rw [lieBracket_neg_right, eight_lieBracket_c i]
    fin_cases i
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem eight_gen_b (i : Fin 2) (B : (Fin 8 → ℝ) → Fin 8 → ℝ)
    (hB : B = 0 ∨ B = baseField eightB1 ∨ B = -baseField eightB1 ∨ B = baseField eightB2 ∨
      B = -baseField eightB2) :
    ∃ v : Fin 8 → ℝ, v 0 = 0 ∧ v 1 = 0 ∧ lieBracket ℝ (eightFields i) B = fun _ => v := by
  rcases hB with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl, rfl, lieBracket_zero_right⟩
  · exact ⟨![eightE6, eightE7] i, by fin_cases i <;> rfl, by fin_cases i <;> rfl,
      eight_lieBracket_b1 i⟩
  · refine ⟨-![eightE6, eightE7] i, by fin_cases i <;> simp [eightE6, eightE7],
      by fin_cases i <;> simp [eightE6, eightE7], ?_⟩
    rw [lieBracket_neg_right, eight_lieBracket_b1 i]
    rfl
  · exact ⟨![eightE7, eightE8] i, by fin_cases i <;> rfl, by fin_cases i <;> rfl,
      eight_lieBracket_b2 i⟩
  · refine ⟨-![eightE7, eightE8] i, by fin_cases i <;> simp [eightE7, eightE8],
      by fin_cases i <;> simp [eightE7, eightE8], ?_⟩
    rw [lieBracket_neg_right, eight_lieBracket_b2 i]
    rfl

private theorem eightClass_bracket {a b : ℕ} {A B : (Fin 8 → ℝ) → Fin 8 → ℝ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hA : EightClass a A) (hB : EightClass b B) :
    EightClass (a + b) (lieBracket ℝ A B) := by
  obtain ⟨hA1, hA2, hA3, hAv, hA4, hA5⟩ := hA
  obtain ⟨hB1, hB2, hB3, hBv, hB4, hB5⟩ := hB
  have hgen : ∀ {i : Fin 2} {v : Fin 8 → ℝ}, v 0 = 0 → v 1 = 0 →
      lieBracket ℝ (eightFields i) (fun _ => v) = 0 :=
    fun h0 h1 => lieBracket_const_eq_zero_of_isBase (eightFields_isBase _) h0 h1
  have hvv : 2 ≤ a → 2 ≤ b → lieBracket ℝ A B = 0 := by
    intro h2a h2b
    obtain ⟨hAb, hAq⟩ := hAv h2a
    obtain ⟨hBb, hBq⟩ := hBv h2b
    funext q
    exact lieBracket_eq_zero_of_isBase hAb hBb q (hAq q).1 (hAq q).2 (hBq q).1 (hBq q).2
  by_cases h5 : 5 ≤ a + b
  · suffices hz : lieBracket ℝ A B = 0 by
      rw [hz]
      exact eightClass_const (v := 0) (by omega) rfl rfl (fun _ => rfl)
    by_cases ha5 : 5 ≤ a
    · rw [hA5 ha5, lieBracket_zero_left]
    by_cases hb5 : 5 ≤ b
    · rw [hB5 hb5, lieBracket_zero_right]
    by_cases ha1 : a = 1
    · obtain ⟨v, h0, h1, rfl⟩ := hB4 (by omega)
      rcases hA1 ha1 with rfl | rfl
      · exact hgen h0 h1
      · exact hgen h0 h1
    by_cases hb1 : b = 1
    · obtain ⟨v, h0, h1, rfl⟩ := hA4 (by omega)
      rw [lieBracket_antisymm]
      rcases hB1 hb1 with rfl | rfl
      · rw [hgen h0 h1, neg_zero]
      · rw [hgen h0 h1, neg_zero]
    exact hvv (by omega) (by omega)
  by_cases h4 : a + b = 4
  · have hc : ∃ v : Fin 8 → ℝ, v 0 = 0 ∧ v 1 = 0 ∧ lieBracket ℝ A B = fun _ => v := by
      rcases (show (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b) by omega) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h2a, h2b⟩
      · rcases hA1 rfl with rfl | rfl
        · exact eight_gen_b 0 B (hB3 rfl)
        · exact eight_gen_b 1 B (hB3 rfl)
      · obtain ⟨v, h0, h1, hv⟩ : ∃ v : Fin 8 → ℝ, v 0 = 0 ∧ v 1 = 0 ∧
            lieBracket ℝ B A = fun _ => v := by
          rcases hB1 rfl with rfl | rfl
          · exact eight_gen_b 0 A (hA3 rfl)
          · exact eight_gen_b 1 A (hA3 rfl)
        refine ⟨-v, by simp [h0], by simp [h1], ?_⟩
        rw [lieBracket_antisymm, hv]
        rfl
      · exact ⟨0, rfl, rfl, hvv h2a h2b⟩
    obtain ⟨v, h0, h1, hv⟩ := hc
    rw [hv, h4]
    exact eightClass_const le_rfl h0 h1 (fun h => by omega)
  rcases (show (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h2 : lieBracket ℝ A B = 0 ∨ lieBracket ℝ A B = baseField eightC ∨
        lieBracket ℝ A B = -baseField eightC := by
      rcases hA1 rfl with rfl | rfl <;> rcases hB1 rfl with rfl | rfl
      · exact Or.inl lieBracket_self
      · exact Or.inr (Or.inl eight_lieBracket)
      · refine Or.inr (Or.inr ?_)
        rw [lieBracket_antisymm, eight_lieBracket]
      · exact Or.inl lieBracket_self
    have vc : ∀ q, baseField eightC q 0 = 0 ∧ baseField eightC q 1 = 0 := fun q => ⟨rfl, rfl⟩
    refine ⟨fun h => by omega, fun _ => h2, fun h => by omega, fun _ => ?_, fun h => by omega,
      fun h => by omega⟩
    rcases h2 with h | h | h <;> rw [h]
    · exact ⟨isBase_const 0, fun _ => ⟨rfl, rfl⟩⟩
    · exact ⟨isBase_baseField eightC, vc⟩
    · exact ⟨isBase_neg (isBase_baseField eightC), vert_neg vc⟩
  · rcases hA1 rfl with rfl | rfl
    · exact eight_gen_c 0 B (hB2 rfl)
    · exact eight_gen_c 1 B (hB2 rfl)
  · have hc : EightClass 3 (lieBracket ℝ B A) := by
      rcases hB1 rfl with rfl | rfl
      · exact eight_gen_c 0 A (hA2 rfl)
      · exact eight_gen_c 1 A (hA2 rfl)
    have h3 := hc.2.2.1 rfl
    apply eightClass_three
    rw [lieBracket_antisymm]
    rcases h3 with h | h | h | h | h <;> rw [h]
    · exact Or.inl neg_zero
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl (neg_neg _))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (neg_neg _))))

private theorem eightClass_of_isLieProduct {l : ℕ} {A : (Fin 8 → ℝ) → Fin 8 → ℝ}
    (h : IsLieProduct eightFields l A) : EightClass l A := by
  induction h with
  | gen j =>
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  | bracket hA hB ihA ihB => exact eightClass_bracket hA.one_le hB.one_le ihA ihB

/-- **MLS Chapter 8, Exercise 1, p. 391 ("nilpotent of degree four"), corrected printing, in the
sense of p. 344: order of nilpotency `4`.** Every Lie product of `g₁, g₂` of length greater than
`4` is zero, and `[g₁, [g₁, [g₁, g₂]]] = e₆` is not. -/
theorem eight_isNilpotencyOrder : IsNilpotencyOrder eightFields 4 := by
  refine ⟨fun l A hA hl => (eightClass_of_isLieProduct hA).2.2.2.2.2 hl, ?_⟩
  refine ⟨lieBracket ℝ (eightFields 0) (lieBracket ℝ (eightFields 0)
      (lieBracket ℝ (eightFields 0) (eightFields 1))),
    IsLieProduct.bracket (IsLieProduct.gen 0) (IsLieProduct.bracket (IsLieProduct.gen 0)
      (IsLieProduct.bracket (IsLieProduct.gen 0) (IsLieProduct.gen 1))), ?_⟩
  rw [eight_lieBracket, eight_lieBracket_c 0]
  simp only [Matrix.cons_val_zero]
  rw [eight_lieBracket_b1 0]
  intro h
  have := congrFun (congrFun h 0) 5
  simp [eightE6] at this

/-- `Δ₃(q)` is spanned by `g₁, g₂, [g₁, g₂], [g₁, [g₁, g₂]], [g₂, [g₁, g₂]]` at `q` (supporting
lemma for MLS p. 391). -/
private theorem eight_filtrationAt_three (q : Fin 8 → ℝ) :
    filtrationAt eightFields 3 q = Submodule.span ℝ (Set.range fun i : Fin 5 => eightVecs q
      ⟨i.val, by omega⟩) := by
  set V := Submodule.span ℝ (Set.range fun i : Fin 5 => eightVecs q ⟨i.val, by omega⟩)
  have hv : ∀ i : Fin 5, eightVecs q ⟨i.val, by omega⟩ ∈ V := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · refine filtrationAt_le_of_isLieProduct fun l A hA hl => ?_
    obtain ⟨h1, h2, h3, -, -, -⟩ := eightClass_of_isLieProduct hA
    rcases (show l = 1 ∨ l = 2 ∨ l = 3 by have := hA.one_le; omega) with rfl | rfl | rfl
    · rcases h1 rfl with rfl | rfl
      · exact hv 0
      · exact hv 1
    · rcases h2 rfl with rfl | rfl | rfl
      · exact V.zero_mem
      · exact hv 2
      · exact V.neg_mem (hv 2)
    · rcases h3 rfl with rfl | rfl | rfl | rfl | rfl
      · exact V.zero_mem
      · exact hv 3
      · exact V.neg_mem (hv 3)
      · exact hv 4
      · exact V.neg_mem (hv 4)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have h1 : ∀ j, eightFields j ∈ filtrationFields eightFields 1 := fun j => by
      rw [filtrationFields_one]
      exact ⟨j, rfl⟩
    have hc : baseField eightC ∈ filtrationFields eightFields 2 := by
      rw [← eight_lieBracket]
      exact lieBracket_mem_filtrationFields eightFields 0 (h1 1)
    have hb : ∀ j, baseField (![eightB1, eightB2] j) ∈ filtrationFields eightFields 3 := fun j => by
      rw [← eight_lieBracket_c j]
      exact lieBracket_mem_filtrationFields eightFields j hc
    have mono : ∀ {i} {f}, f ∈ filtrationFields eightFields i → i ≤ 3 →
        f q ∈ filtrationAt eightFields 3 q := fun hf hi =>
      mem_spanAt (filtrationFields_mono eightFields hi hf) q
    fin_cases i
    · exact mono (h1 0) (by norm_num)
    · exact mono (h1 1) (by norm_num)
    · exact mono hc (by norm_num)
    · exact mono (hb 0) le_rfl
    · exact mono (hb 1) le_rfl

private theorem eight_growth (q : Fin 8 → ℝ) :
    growth eightFields 1 q = 2 ∧ growth eightFields 2 q = 3 ∧ growth eightFields 3 q = 5 ∧
      growth eightFields 4 q = 8 ∧ growth eightFields 5 q = 8 := by
  have hind := eightVecs_independent q
  have hsub : ∀ k : ℕ, (hk : k ≤ 8) → LinearIndependent ℝ fun i : Fin k => eightVecs q
      ⟨i.val, by omega⟩ := fun k hk =>
    hind.comp _ (fun i j h => Fin.ext (by simpa using congrArg Fin.val h))
  have h2 : LinearIndependent ℝ ![eightFields 0 q, eightFields 1 q] := by
    convert hsub 2 (by norm_num) using 1
    funext j
    fin_cases j <;> rfl
  have h3 : LinearIndependent ℝ ![eightFields 0 q, eightFields 1 q,
      lieBracket ℝ (eightFields 0) (eightFields 1) q] := by
    rw [eight_lieBracket]
    convert hsub 3 (by norm_num) using 1
    funext j
    fin_cases j <;> rfl
  refine ⟨growth_one_eq_two eightFields h2, growth_two_eq_three eightFields h3, ?_, ?_, ?_⟩
  · rw [growth, eight_filtrationAt_three, finrank_span_eq_card (hsub 5 (by norm_num)),
      Fintype.card_fin]
  · rw [growth_eq_finrank_of_filtrationAt_eq_top eightFields (eight_filtrationAt_four q) le_rfl,
      Module.finrank_fin_fun]
  · rw [growth_eq_finrank_of_filtrationAt_eq_top eightFields (eight_filtrationAt_four q)
      (by norm_num), Module.finrank_fin_fun]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing, with Definition 7.3, p. 341: growth
vector `(2, 3, 5, 8)`** (relative growth vector `(2, 1, 2, 3)`) at every point. -/
theorem eight_growthVector (q : Fin 8 → ℝ) :
    growthVector eightFields 4 q = ![2, 3, 5, 8] ∧
      relativeGrowthVector eightFields 4 q = ![2, 1, 2, 3] := by
  obtain ⟨h1, h2, h3, h4, -⟩ := eight_growth q
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i <;> simp [growthVector, h1, h2, h3, h4]
  · funext i
    fin_cases i <;> simp [relativeGrowthVector, h1, h2, h3, h4, growth_zero]

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing, with Definition 7.2, p. 340: degree of
nonholonomy `4`** at every point. -/
theorem eight_isDegreeOfNonholonomy (q : Fin 8 → ℝ) : IsDegreeOfNonholonomy eightFields q 4 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := eight_growth q
  refine ⟨by norm_num, by rw [h4, h5], fun i hi1 hi2 => ?_⟩
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
  · rw [h1, h2]; norm_num
  · rw [h2, h3]; norm_num
  · rw [h3, h4]; norm_num

end Examples
end RoboLean
