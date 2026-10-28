import RoboLean.Nonholonomic.VectorField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The kinematic car: MLS Examples 7.5 and 7.10

MLS Chapter 7: Example 7.5, printed pp. 336–337, eq. (7.14); Example 7.10, p. 343.

**What MLS states.** With `q = (x, y, θ, φ)` and wheelbase `l`, the constraints
`sin(θ + φ) ẋ − cos(θ + φ) ẏ − l cos φ θ̇ = 0`, `sin θ ẋ − cos θ ẏ = 0` and the control system
(7.14) `q̇ = (cos θ, sin θ, (1/l) tan φ, 0) u₁ + (0, 0, 0, 1) u₂`. Example 7.10 prints
`g₃ = [g₁, g₂] = (0, 0, −1/(l cos² φ), 0)` and `g₄ = [g₁, g₃] = (−sin θ/(l cos² φ),
cos θ/cos² φ, 0, 0)`, "linearly independent when `φ ≠ ±π`", and "regular away from `φ = ±π/2`, at
which point `g₁` is undefined".

**Corrected printing.** The second entry of `g₄` is `cos θ/(l cos² φ)` (the printed entry lacks
`1/l`), and the determinant of `g₁, …, g₄` is `1/(l² cos⁴ φ)`, so the fields are independent
exactly where `cos φ ≠ 0`, i.e. `φ ≠ ±π/2` (mod `2π`), not `φ ≠ ±π` as printed.

**Formalized.** Coordinates `q 0 = x`, `q 1 = y`, `q 2 = θ`, `q 3 = φ`; every statement assumes
`cos φ ≠ 0` where `g₁` is used (Mathlib's `tan` is `sin / cos`, zero where `cos φ = 0`) and
`l ≠ 0`. These are convention checks of the printed formulas; they say nothing about a vehicle.
-/

noncomputable section

open Real VectorField Matrix
open scoped ContDiff

namespace RoboLean
namespace Examples

/-- **MLS eq. (7.14), p. 337, first column: `g₁(q) = (cos θ, sin θ, (1/l) tan φ, 0)`** for the
kinematic car with `q = (x, y, θ, φ)`. -/
def carG1 (l : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![cos (q 2), sin (q 2), tan (q 3) / l, 0]

/-- **MLS eq. (7.14), p. 337, second column: `g₂ = (0, 0, 0, 1)`.** -/
def carG2 (_q : Fin 4 → ℝ) : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- **MLS Example 7.10, p. 343: `g₃ = (0, 0, −1/(l cos² φ), 0)`.** -/
def carG3 (l : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ := ![0, 0, -1 / (l * cos (q 3) ^ 2), 0]

/-- **MLS Example 7.10, p. 343, corrected printing:
`g₄ = (−sin θ/(l cos² φ), cos θ/(l cos² φ), 0, 0)`** (the printed second entry lacks `1/l`). -/
def carG4 (l : ℝ) (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-sin (q 2) / (l * cos (q 3) ^ 2), cos (q 2) / (l * cos (q 3) ^ 2), 0, 0]

/-- **MLS Example 7.5, p. 337: the no-slip constraints**
`[[sin(θ + φ), −cos(θ + φ), −l cos φ, 0], [sin θ, −cos θ, 0, 0]] q̇ = 0`. -/
def carConstraint (l : ℝ) (q : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![sin (q 2 + q 3), -cos (q 2 + q 3), -(l * cos (q 3)), 0; sin (q 2), -cos (q 2), 0, 0]

/-- The derivative of `t ↦ G(q + t v)` at `0`, assembled from its components (supporting lemma
for MLS p. 343). -/
private theorem deriv_line {n : ℕ} (G : (Fin n → ℝ) → Fin n → ℝ) (q v w : Fin n → ℝ)
    (h : ∀ i, HasDerivAt (fun t : ℝ => G (q + t • v) i) (w i) 0) :
    deriv (fun t : ℝ => G (q + t • v)) 0 = w := by
  have hd : HasDerivAt (fun t : ℝ => G (q + t • v)) w 0 := by
    rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_pi']
    intro i
    convert (h i).hasFDerivAt using 1
    ext
    simp
  exact hd.deriv

/-- The line `t ↦ a + t c` has derivative `c` at `0` (supporting lemma for MLS p. 343). -/
private theorem hasDerivAt_line (a c : ℝ) : HasDerivAt (fun t : ℝ => a + t * c) c 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add a

/-- **MLS p. 343 ("at which point `g₁` is undefined"):** `g₁` is smooth near every `q` with
`cos φ ≠ 0`. -/
theorem carG1_contDiffAt (l : ℝ) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    ContDiffAt ℝ ∞ (carG1 l) q := by
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i <;> simp [carG1]
  · fun_prop
  · fun_prop
  · exact ((Real.contDiffAt_tan.2 hq).comp q (contDiffAt_apply _ _ _ _)).div_const l
  · fun_prop

/-- **MLS p. 322 for (7.14):** `g₂` is smooth. -/
theorem carG2_contDiff : ContDiff ℝ ∞ carG2 := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [carG2] <;> fun_prop

/-- **MLS Example 7.10, p. 343: `[g₁, g₂] = g₃`** at every `q` with `cos φ ≠ 0`. -/
theorem car_lieBracket_g1_g2 {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    lieBracket ℝ (carG1 l) carG2 q = carG3 l q := by
  have h1 := (carG1_contDiffAt l hq).differentiableAt (by simp)
  have h2 := (carG2_contDiff.differentiable (by simp)) q
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h2,
    deriv_line carG2 q (carG1 l q) 0 ?_, deriv_line (carG1 l) q (carG2 q) (-carG3 l q) ?_]
  · simp
  · intro i
    fin_cases i <;> simp [carG1, carG2, carG3]
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · have h := ((Real.hasDerivAt_tan (x := q 3 + 0 * 1) (by simpa using hq)).comp 0
        (hasDerivAt_line (q 3) 1)).div_const l
      convert h using 1
      · funext t
        simp
      · simp only [add_zero, mul_one]
        field_simp
    · exact hasDerivAt_const _ _
  · intro i
    fin_cases i <;> simp [carG2] <;> exact hasDerivAt_const _ _

/-- **MLS Example 7.10, p. 343, corrected printing: `[g₁, g₃] = g₄`** at every `q` with
`cos φ ≠ 0`. -/
theorem car_lieBracket_g1_g3 {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    lieBracket ℝ (carG1 l) (carG3 l) q = carG4 l q := by
  have h1 := (carG1_contDiffAt l hq).differentiableAt (by simp)
  have h3 : DifferentiableAt ℝ (carG3 l) q := by
    refine differentiableAt_pi.2 fun i => ?_
    fin_cases i <;> simp [carG3]
    fun_prop (disch := simp [hl, hq])
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h3,
    deriv_line (carG3 l) q (carG1 l q) 0 ?_, deriv_line (carG1 l) q (carG3 l q) (-carG4 l q) ?_]
  · simp
  · intro i
    fin_cases i <;> simp [carG1, carG3, carG4]
    · convert (hasDerivAt_line (q 2) (-1 / (l * cos (q 3) ^ 2))).cos using 1
      simp
      ring
    · convert (hasDerivAt_line (q 2) (-1 / (l * cos (q 3) ^ 2))).sin using 1
      simp
      ring
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
  · intro i
    fin_cases i <;> simp [carG1, carG3] <;> exact hasDerivAt_const _ _

/-- **MLS Example 7.5, p. 337:** the constraints annihilate `g₁` where `cos φ ≠ 0`. -/
theorem carConstraint_mulVec_g1 {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    carConstraint l q *ᵥ carG1 l q = 0 := by
  ext i
  fin_cases i <;> simp [carConstraint, carG1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [sin_add, cos_add, tan_eq_sin_div_cos]
    field_simp
    linear_combination sin (q 3) * sin_sq_add_cos_sq (q 2)
  · ring

/-- **MLS Example 7.5, p. 337:** the constraints annihilate `g₂`. -/
theorem carConstraint_mulVec_g2 (l : ℝ) (q : Fin 4 → ℝ) : carConstraint l q *ᵥ carG2 q = 0 := by
  ext i
  fin_cases i <;> simp [carConstraint, carG2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- **MLS Examples 7.5 and 7.10, pp. 337 and 343:** the constraints applied to `g₃ = [g₁, g₂]`
give `(1/cos φ, 0)`, nonzero where `cos φ ≠ 0`. -/
theorem carConstraint_mulVec_g3 {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    carConstraint l q *ᵥ carG3 l q = ![(cos (q 3))⁻¹, 0] := by
  ext i
  fin_cases i <;> simp [carConstraint, carG3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  field_simp

/-- **MLS Example 7.10, p. 343, corrected printing:** the matrix with rows `g₁, …, g₄` has
determinant `1/(l² cos⁴ φ)` where `cos φ ≠ 0`. -/
theorem car_det {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    (Matrix.of ![carG1 l q, carG2 q, carG3 l q, carG4 l q]).det = 1 / (l ^ 2 * cos (q 3) ^ 4) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, carG1, carG2, carG3, carG4, Fin.succAbove]
  field_simp
  linear_combination sin_sq_add_cos_sq (q 2)

/-- **MLS Example 7.10, p. 343, corrected printing:** the four fields are linearly independent at
every `q` with `cos φ ≠ 0` (MLS prints `φ ≠ ±π`). -/
theorem car_linearIndependent {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : cos (q 3) ≠ 0) :
    LinearIndependent ℝ ![carG1 l q, carG2 q, carG3 l q, carG4 l q] := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![carG1 l q, carG2 q, carG3 l q, carG4 l q])
    (by rw [car_det hl hq]; positivity)
  exact h

end Examples
end RoboLean
