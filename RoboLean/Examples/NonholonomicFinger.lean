import RoboLean.Nonholonomic.VectorField
import RoboLean.Examples.RollingContact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The spherical finger rolling on a plane: MLS Examples 7.6 and 7.11

MLS Chapter 7: Example 7.6, printed pp. 337–339, eqs. (7.17)–(7.19); Example 7.11, pp. 343–344.

**What MLS states.** For a unit sphere rolling on a plane with `q = (α_f, α_o, ψ) ∈ ℝ⁵` the
rolling constraints (7.17) read
`[[1, 0, −cos q₅, sin q₅, 0], [0, cos q₁, sin q₅, cos q₅, 0], [0, sin q₁, 0, 0, 1]] q̇ = 0` (p. 338)
and the control system (7.19) is `q̇ = g₁ u₁ + g₂ u₂` with
`g₁ = (0, sec q₁, −sin q₅, −cos q₅, −tan q₁)`, `g₂ = (−1, 0, −cos q₅, sin q₅, 0)`, `u₁ = ω_x`,
`u₂ = ω_y`. Example 7.11 prints `g₃ = [g₁, g₂]`, `g₄ = [g₁, g₃]`, `g₅ = [g₂, g₃]` and states that
`g₁, …, g₅` are independent "in a neighborhood not containing `q₁ = π/2`".

**Formalized.** Coordinates `q 0 = q₁ = u_f`, `q 1 = q₂ = v_f`, `q 2 = q₃ = u_o`, `q 3 = q₄ = v_o`,
`q 4 = q₅ = ψ`; `sec q₁ = (cos q₁)⁻¹`, and every statement that uses `g₁` assumes `cos q₁ ≠ 0`.
The printed brackets hold, the determinant of `g₁, …, g₅` is `sec q₁`, and (7.19) is the case
`ρ = 1` of (5.39) (`example57_contactRates`) along every rolling motion. These are convention
checks of the printed formulas; they say nothing about a physical finger.
-/

noncomputable section

open Real VectorField Matrix Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Examples

open Surface Rolling

/-- **MLS eq. (7.19), p. 339: `g₁(q) = (0, sec q₁, −sin q₅, −cos q₅, −tan q₁)`.** -/
def fingerG1 (q : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![0, (cos (q 0))⁻¹, -sin (q 4), -cos (q 4), -tan (q 0)]

/-- **MLS eq. (7.19), p. 339: `g₂(q) = (−1, 0, −cos q₅, sin q₅, 0)`.** -/
def fingerG2 (q : Fin 5 → ℝ) : Fin 5 → ℝ := ![-1, 0, -cos (q 4), sin (q 4), 0]

/-- **MLS Example 7.11, p. 344:
`g₃ = (0, tan q₁ sec q₁, −tan q₁ sin q₅, −tan q₁ cos q₅, −sec² q₁)`.** -/
def fingerG3 (q : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![0, tan (q 0) / cos (q 0), -(tan (q 0) * sin (q 4)), -(tan (q 0) * cos (q 4)),
    -1 / cos (q 0) ^ 2]

/-- **MLS Example 7.11, p. 344: `g₄ = (0, 0, −cos q₅, sin q₅, 0)`.** -/
def fingerG4 (q : Fin 5 → ℝ) : Fin 5 → ℝ := ![0, 0, -cos (q 4), sin (q 4), 0]

/-- **MLS Example 7.11, p. 344: `g₅ = (0, −(1 + sin² q₁) sec³ q₁, 2 sin q₅ sec² q₁,
2 cos q₅ sec² q₁, 2 tan q₁ sec² q₁)`.** -/
def fingerG5 (q : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![0, -(1 + sin (q 0) ^ 2) / cos (q 0) ^ 3, 2 * sin (q 4) / cos (q 0) ^ 2,
    2 * cos (q 4) / cos (q 0) ^ 2, 2 * tan (q 0) / cos (q 0) ^ 2]

/-- **MLS Example 7.6, p. 338: the rolling constraints (7.17) for the unit sphere on the plane,**
`[[1, 0, −cos q₅, sin q₅, 0], [0, cos q₁, sin q₅, cos q₅, 0], [0, sin q₁, 0, 0, 1]] q̇ = 0`. -/
def fingerConstraint (q : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 5) ℝ :=
  !![1, 0, -cos (q 4), sin (q 4), 0; 0, cos (q 0), sin (q 4), cos (q 4), 0;
    0, sin (q 0), 0, 0, 1]

/-- The derivative of `t ↦ G(q + t v)` at `0`, assembled from its components (supporting lemma
for MLS p. 344). -/
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

/-- The line `t ↦ a + t c` has derivative `c` at `0` (supporting lemma for MLS p. 344). -/
private theorem hasDerivAt_line (a c : ℝ) : HasDerivAt (fun t : ℝ => a + t * c) c 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add a

/-- `g₃` of MLS Example 7.11 is smooth near every `q` with `cos q₁ ≠ 0` (supporting lemma for
MLS p. 344). -/
private theorem fingerG3_contDiffAt {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    ContDiffAt ℝ ∞ fingerG3 q := by
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i <;> simp [fingerG3, tan_eq_sin_div_cos] <;> fun_prop (disch := simpa using hq)

/-- **MLS p. 344 ("a neighborhood not containing `q₁ = π/2`"):** `g₁` is smooth near every `q`
with `cos q₁ ≠ 0`. -/
theorem fingerG1_contDiffAt {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    ContDiffAt ℝ ∞ fingerG1 q := by
  refine contDiffAt_pi.2 fun i => ?_
  fin_cases i <;> simp [fingerG1, tan_eq_sin_div_cos] <;> fun_prop (disch := simpa using hq)

/-- **MLS p. 322 for (7.19):** `g₂` is smooth. -/
theorem fingerG2_contDiff : ContDiff ℝ ∞ fingerG2 := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [fingerG2] <;> fun_prop

/-- **MLS Example 7.11, p. 344: `[g₁, g₂] = g₃`** at every `q` with `cos q₁ ≠ 0`. -/
theorem finger_lieBracket_g1_g2 {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    lieBracket ℝ fingerG1 fingerG2 q = fingerG3 q := by
  have h1 := (fingerG1_contDiffAt hq).differentiableAt (by simp)
  have h2 := (fingerG2_contDiff.differentiable (by simp)) q
  have hq' : cos (q 0 + 0 * -1) ≠ 0 := by simpa using hq
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h2,
    deriv_line fingerG2 q (fingerG1 q)
      ![0, 0, -(tan (q 0) * sin (q 4)), -(tan (q 0) * cos (q 4)), 0] ?_,
    deriv_line fingerG1 q (fingerG2 q) ![0, -(tan (q 0) / cos (q 0)), 0, 0, 1 / cos (q 0) ^ 2] ?_]
  · ext i
    fin_cases i <;> simp [fingerG3]
    ring
  · intro i
    fin_cases i <;> simp [fingerG1, fingerG2, tan_eq_sin_div_cos]
    · exact hasDerivAt_const _ _
    · convert ((hasDerivAt_line (q 0) (-1)).cos).inv hq' using 1
      · funext t
        simp only [Pi.inv_apply]
        ring_nf
      · simp
        field_simp
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · convert (((hasDerivAt_line (q 0) (-1)).sin).div ((hasDerivAt_line (q 0) (-1)).cos) hq').neg
        using 1
      · funext t
        simp only [Pi.neg_apply, Pi.div_apply]
        ring_nf
      · simp
        field_simp
        linear_combination -(sin_sq_add_cos_sq (q 0))
  · intro i
    fin_cases i <;> simp [fingerG1, fingerG2, tan_eq_sin_div_cos]
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · convert ((hasDerivAt_line (q 4) (-(sin (q 0) / cos (q 0)))).cos).neg using 1
      · funext t
        simp only [Pi.neg_apply]
        ring_nf
      · simp
        ring
    · convert (hasDerivAt_line (q 4) (-(sin (q 0) / cos (q 0)))).sin using 1
      · funext t
        ring_nf
      · simp
        ring
    · exact hasDerivAt_const _ _

/-- **MLS Example 7.11, p. 344: `[g₁, g₃] = g₄`** at every `q` with `cos q₁ ≠ 0`. -/
theorem finger_lieBracket_g1_g3 {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    lieBracket ℝ fingerG1 fingerG3 q = fingerG4 q := by
  have h1 := (fingerG1_contDiffAt hq).differentiableAt (by simp)
  have h3 := (fingerG3_contDiffAt hq).differentiableAt (by simp)
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h3,
    deriv_line fingerG3 q (fingerG1 q)
      ![0, 0, tan (q 0) ^ 2 * cos (q 4), -(tan (q 0) ^ 2 * sin (q 4)), 0] ?_,
    deriv_line fingerG1 q (fingerG3 q)
      ![0, 0, cos (q 4) / cos (q 0) ^ 2, -(sin (q 4) / cos (q 0) ^ 2), 0] ?_]
  · ext i
    fin_cases i <;> simp [fingerG4, tan_eq_sin_div_cos]
    · field_simp
      linear_combination cos (q 4) * sin_sq_add_cos_sq (q 0)
    · field_simp
      linear_combination -sin (q 4) * sin_sq_add_cos_sq (q 0)
  · intro i
    fin_cases i <;> simp [fingerG1, fingerG3, tan_eq_sin_div_cos]
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · convert ((hasDerivAt_line (q 4) (-1 / cos (q 0) ^ 2)).sin).neg using 1
      simp
      ring
    · convert ((hasDerivAt_line (q 4) (-1 / cos (q 0) ^ 2)).cos).neg using 1
      simp
      ring
    · exact hasDerivAt_const _ _
  · intro i
    fin_cases i <;> simp [fingerG1, fingerG3, tan_eq_sin_div_cos]
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · convert (((hasDerivAt_line (q 4) (-(sin (q 0) / cos (q 0)))).sin).const_mul
        (sin (q 0) / cos (q 0))).neg using 1
      · funext t
        simp only [Pi.neg_apply]
        ring_nf
      · simp
        ring
    · convert (((hasDerivAt_line (q 4) (-(sin (q 0) / cos (q 0)))).cos).const_mul
        (sin (q 0) / cos (q 0))).neg using 1
      · funext t
        simp only [Pi.neg_apply]
        ring_nf
      · simp
        ring
    · exact hasDerivAt_const _ _

/-- **MLS Example 7.11, p. 344: `[g₂, g₃] = g₅`** at every `q` with `cos q₁ ≠ 0`. -/
theorem finger_lieBracket_g2_g3 {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    lieBracket ℝ fingerG2 fingerG3 q = fingerG5 q := by
  have h2 := (fingerG2_contDiff.differentiable (by simp)) q
  have h3 := (fingerG3_contDiffAt hq).differentiableAt (by simp)
  have hq' : cos (q 0 + 0 * -1) ≠ 0 := by simpa using hq
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h2 h3,
    deriv_line fingerG3 q (fingerG2 q)
      ![0, -(1 + sin (q 0) ^ 2) / cos (q 0) ^ 3, sin (q 4) / cos (q 0) ^ 2,
        cos (q 4) / cos (q 0) ^ 2, 2 * sin (q 0) / cos (q 0) ^ 3] ?_,
    deriv_line fingerG2 q (fingerG3 q)
      ![0, 0, -(sin (q 4) / cos (q 0) ^ 2), -(cos (q 4) / cos (q 0) ^ 2), 0] ?_]
  · ext i
    fin_cases i <;> simp [fingerG5, tan_eq_sin_div_cos]
    · ring
    · ring
    · field_simp
  · intro i
    fin_cases i <;> simp [fingerG2, fingerG3, tan_eq_sin_div_cos]
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · convert ((hasDerivAt_line (q 4) (-1 / cos (q 0) ^ 2)).cos).neg using 1
      simp
      ring
    · convert (hasDerivAt_line (q 4) (-1 / cos (q 0) ^ 2)).sin using 1
      simp
      ring
    · exact hasDerivAt_const _ _
  · intro i
    fin_cases i <;> simp [fingerG2, fingerG3, tan_eq_sin_div_cos]
    · exact hasDerivAt_const _ _
    · convert (((hasDerivAt_line (q 0) (-1)).sin.div (hasDerivAt_line (q 0) (-1)).cos hq').div
        (hasDerivAt_line (q 0) (-1)).cos hq') using 1
      · funext t
        simp only [Pi.div_apply]
        ring_nf
      · simp
        field_simp
        linear_combination sin_sq_add_cos_sq (q 0)
    · convert (((hasDerivAt_line (q 0) (-1)).sin.div (hasDerivAt_line (q 0) (-1)).cos
        hq').mul_const (sin (q 4))).neg using 1
      · funext t
        simp only [Pi.neg_apply, Pi.div_apply]
        ring_nf
      · simp
        field_simp
        linear_combination -sin (q 4) * sin_sq_add_cos_sq (q 0)
    · convert (((hasDerivAt_line (q 0) (-1)).sin.div (hasDerivAt_line (q 0) (-1)).cos
        hq').mul_const (cos (q 4))).neg using 1
      · funext t
        simp only [Pi.neg_apply, Pi.div_apply]
        ring_nf
      · simp
        field_simp
        linear_combination -cos (q 4) * sin_sq_add_cos_sq (q 0)
    · convert (hasDerivAt_const (0 : ℝ) (-1 : ℝ)).div ((hasDerivAt_line (q 0) (-1)).cos.pow 2)
        (pow_ne_zero 2 hq') using 1
      · funext t
        simp only [Pi.div_apply, Pi.pow_apply]
        ring_nf
      · simp
        field_simp

/-- **MLS Example 7.6, p. 338:** the constraints (7.17) annihilate `g₁` where `cos q₁ ≠ 0`. -/
theorem fingerConstraint_mulVec_g1 {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    fingerConstraint q *ᵥ fingerG1 q = 0 := by
  ext i
  fin_cases i <;> simp [fingerConstraint, fingerG1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    tan_eq_sin_div_cos]
  · ring
  · rw [mul_inv_cancel₀ hq]
    linear_combination -(sin_sq_add_cos_sq (q 4))
  · ring

/-- **MLS Example 7.6, p. 338:** the constraints (7.17) annihilate `g₂`. -/
theorem fingerConstraint_mulVec_g2 (q : Fin 5 → ℝ) : fingerConstraint q *ᵥ fingerG2 q = 0 := by
  ext i
  fin_cases i <;> simp [fingerConstraint, fingerG2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination sin_sq_add_cos_sq (q 4)
  · ring

/-- **MLS Examples 7.6 and 7.11, pp. 338 and 344:** the constraints applied to `g₃ = [g₁, g₂]` give
`(0, 0, −1)` where `cos q₁ ≠ 0`. -/
theorem fingerConstraint_mulVec_g3 {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    fingerConstraint q *ᵥ fingerG3 q = ![0, 0, -1] := by
  ext i
  fin_cases i <;> simp [fingerConstraint, fingerG3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    tan_eq_sin_div_cos]
  · ring
  · have h : cos (q 0) * (sin (q 0) / cos (q 0) / cos (q 0)) = sin (q 0) / cos (q 0) := by
      field_simp
    rw [h]
    linear_combination (-(sin (q 0) / cos (q 0))) * sin_sq_add_cos_sq (q 4)
  · field_simp
    linear_combination sin_sq_add_cos_sq (q 0)

/-- **MLS Example 7.11, p. 344:** the matrix with rows `g₁, …, g₅` has determinant `sec q₁` where
`cos q₁ ≠ 0`. -/
theorem finger_det {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    (Matrix.of ![fingerG1 q, fingerG2 q, fingerG3 q, fingerG4 q, fingerG5 q]).det =
      (cos (q 0))⁻¹ := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, fingerG1, fingerG2, fingerG3, fingerG4,
    fingerG5, Fin.succAbove, tan_eq_sin_div_cos]
  have h0 : sin (q 0) ^ 2 - 1 = -cos (q 0) ^ 2 := by linear_combination sin_sq_add_cos_sq (q 0)
  have hr : (cos (q 0))⁻¹ =
      (sin (q 0) ^ 2 - 1) ^ 2 * (sin (q 4) ^ 2 + cos (q 4) ^ 2) / cos (q 0) ^ 5 := by
    rw [sin_sq_add_cos_sq, h0]
    field_simp
  rw [hr]
  field_simp
  linear_combination
    (2 * (sin (q 4) ^ 2 + cos (q 4) ^ 2) * (1 - sin (q 0) ^ 2) ^ 3) * sin_sq_add_cos_sq (q 4) +
      (-2 * (sin (q 4) ^ 2 + cos (q 4) ^ 2) * (1 - sin (q 0) ^ 2) *
        (1 - sin (q 0) ^ 2 + cos (q 0) ^ 2)) * sin_sq_add_cos_sq (q 0)

/-- **MLS Example 7.11, p. 344:** the five fields are linearly independent at every `q` with
`cos q₁ ≠ 0`. -/
theorem finger_linearIndependent {q : Fin 5 → ℝ} (hq : cos (q 0) ≠ 0) :
    LinearIndependent ℝ ![fingerG1 q, fingerG2 q, fingerG3 q, fingerG4 q, fingerG5 q] := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero
    (A := Matrix.of ![fingerG1 q, fingerG2 q, fingerG3 q, fingerG4 q, fingerG5 q])
    (by rw [finger_det hq]; exact inv_ne_zero hq)
  exact h

/-- **MLS eq. (7.19), p. 339, as eq. (5.39), p. 253, at `ρ = 1`.** Along a rolling motion of the
unit sphere on the plane (the hypotheses of `example57_contactRates` with `ρ = 1`), the contact
coordinates `q = (α_f, α_o, ψ)` satisfy `q̇ = g₁(q) ω_x + g₂(q) ω_y`, with `(ω_x, ω_y)` the rolling
velocities `w = (ω_x, ω_y, ω_z)`: the inputs `u₁ = ω_x`, `u₂ = ω_y` of p. 338. -/
theorem example711_contactRates {αf αo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ}
    {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t) (hψ : HasDerivAt ψ ψ' t)
    (hft : αf t ∈ sphereDomain) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose (sphereChart 1 (-1)) planeChart (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (sphereChart 1 (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) :
    let w := (Twist.adjoint (contactFrame (sphereChart 1 (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    ![αf' 0, αf' 1, αo' 0, αo' 1, ψ'] =
      w 0 • fingerG1 ![αf t 0, αf t 1, αo t 0, αo t 1, ψ t] +
        w 1 • fingerG2 ![αf t 0, αf t 1, αo t 0, αo t 1, ψ t] := by
  intro w
  have e1 : (![0, (cos (αf t 0))⁻¹, -1 * sin (ψ t), -1 * cos (ψ t), -tan (αf t 0)] : Fin 5 → ℝ) =
      fingerG1 ![αf t 0, αf t 1, αo t 0, αo t 1, ψ t] := by
    ext i
    fin_cases i <;> simp [fingerG1]
  have e2 : (![-1, 0, -1 * cos (ψ t), 1 * sin (ψ t), 0] : Fin 5 → ℝ) =
      fingerG2 ![αf t 0, αf t 1, αo t 0, αo t 1, ψ t] := by
    ext i
    fin_cases i <;> simp [fingerG2]
  rw [← e1, ← e2]
  exact example57_contactRates one_pos hαf hαo hψ hft hg hD hr

end Examples
end RoboLean
