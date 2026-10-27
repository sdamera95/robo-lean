import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The four-bar linkage at its uncertainty configuration

MLS Chapter 3, §5.3, printed pp. 135–138, Figure 3.20(b). The four-bar linkage is planar; a planar
twist is `(v_x, v_y, ω)` and a revolute joint through `q = (q_x, q_y)` has the planar twist
`(q_y, -q_x, 1)` (p. 136). At the uncertainty configuration, where the input link, the coupler
and the output link are aligned with the ground, the book prints the structure equations

`[0 0; r r - l₁; 1 1] (θ̇₁₁, θ̇₁₂) = [0 0; -r -r + l₁; 1 1] (θ̇₂₁, θ̇₂₂)`

and the two joint-rate vectors `θ̇_N₁ = (1, -1, -1, 1)` and `θ̇_N₂ = (r - l₁, -r, r - l₁, -r)`,
"two independent, instantaneously admissible velocities" (p. 138).

Formalized here, for all real `r` and `l₁`, with the printed matrices as data: both vectors
satisfy the printed velocity constraint; they are linearly independent when `l₁ ≠ 0`; and the
end-effector twists they produce, `(0, l₁, 0)` and `(0, 0, -l₁)`, are linearly independent when
`l₁ ≠ 0`, so the tool can move instantaneously in two independent directions. The book's joint
`θᵢⱼ` is coordinate `2(i - 1) + (j - 1)` of the rate vector (`θ̇₁₁, θ̇₁₂, θ̇₂₁, θ̇₂₂`). The matrices
are
the printed ones; their derivation from the mechanism's geometry is not formalized here.
-/

noncomputable section

namespace RoboLean.Examples

/-- The printed planar Jacobian of the first chain at the uncertainty configuration
(MLS p. 138): columns `ξ₁₁′ = (0, r, 1)` and `ξ₁₂′ = (0, r - l₁, 1)`, planar twists
`(v_x, v_y, ω)`. -/
def fourBarUncertaintyJacobian₁ (r l₁ : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, 0; r, r - l₁; 1, 1]

/-- The printed planar Jacobian of the second chain at the uncertainty configuration
(MLS p. 138): columns `ξ₂₁′ = (0, -r, 1)` and `ξ₂₂′ = (0, -r + l₁, 1)`. -/
def fourBarUncertaintyJacobian₂ (r l₁ : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, 0; -r, -r + l₁; 1, 1]

/-- **The printed velocity constraint at the uncertainty configuration (MLS p. 138, the planar
form of eq. (3.67)):** the joint rates `(θ̇₁₁, θ̇₁₂, θ̇₂₁, θ̇₂₂)` are admissible when both chains
produce the same end-effector twist. -/
def FourBarUncertaintyAdmissible (r l₁ : ℝ) (θ' : Fin 4 → ℝ) : Prop :=
  (fourBarUncertaintyJacobian₁ r l₁).mulVec ![θ' 0, θ' 1] =
    (fourBarUncertaintyJacobian₂ r l₁).mulVec ![θ' 2, θ' 3]

/-- The first printed admissible velocity `θ̇_N₁ = (1, -1, -1, 1)` (MLS p. 138). -/
def fourBarUncertaintyRates₁ : Fin 4 → ℝ := ![1, -1, -1, 1]

/-- The second printed admissible velocity `θ̇_N₂ = (r - l₁, -r, r - l₁, -r)` (MLS p. 138). -/
def fourBarUncertaintyRates₂ (r l₁ : ℝ) : Fin 4 → ℝ := ![r - l₁, -r, r - l₁, -r]

/-- **MLS p. 138:** `θ̇_N₁` is an admissible velocity at the uncertainty configuration, for all
`r` and `l₁`. -/
theorem fourBarUncertaintyAdmissible_rates₁ (r l₁ : ℝ) :
    FourBarUncertaintyAdmissible r l₁ fourBarUncertaintyRates₁ := by
  unfold FourBarUncertaintyAdmissible
  ext i
  fin_cases i <;>
    simp [fourBarUncertaintyJacobian₁, fourBarUncertaintyJacobian₂, fourBarUncertaintyRates₁,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **MLS p. 138:** `θ̇_N₂` is an admissible velocity at the uncertainty configuration, for all
`r` and `l₁`. -/
theorem fourBarUncertaintyAdmissible_rates₂ (r l₁ : ℝ) :
    FourBarUncertaintyAdmissible r l₁ (fourBarUncertaintyRates₂ r l₁) := by
  unfold FourBarUncertaintyAdmissible
  ext i
  fin_cases i
  · simp [fourBarUncertaintyJacobian₁, fourBarUncertaintyJacobian₂, fourBarUncertaintyRates₂,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [fourBarUncertaintyJacobian₁, fourBarUncertaintyJacobian₂, fourBarUncertaintyRates₂,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [fourBarUncertaintyJacobian₁, fourBarUncertaintyJacobian₂, fourBarUncertaintyRates₂,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **MLS p. 138: "two independent, instantaneously admissible velocities".** For `l₁ ≠ 0` the
two printed rate vectors are linearly independent. -/
theorem linearIndependent_fourBarUncertaintyRates {r l₁ : ℝ} (hl : l₁ ≠ 0) :
    LinearIndependent ℝ ![fourBarUncertaintyRates₁, fourBarUncertaintyRates₂ r l₁] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [fourBarUncertaintyRates₁, fourBarUncertaintyRates₂, Pi.add_apply, Pi.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, Pi.zero_apply] at h0 h1
  have ht : t * l₁ = 0 := by linear_combination -h0 - h1
  have ht0 : t = 0 := (mul_eq_zero.mp ht).resolve_right hl
  subst ht0
  refine ⟨?_, rfl⟩
  linarith

/-- The end-effector twists produced by the two printed velocities (MLS p. 138): `(0, l₁, 0)` and
`(0, 0, -l₁)` in planar twist coordinates `(v_x, v_y, ω)`. -/
theorem fourBarUncertainty_toolTwists (r l₁ : ℝ) :
    (fourBarUncertaintyJacobian₁ r l₁).mulVec ![fourBarUncertaintyRates₁ 0,
        fourBarUncertaintyRates₁ 1] = ![0, l₁, 0] ∧
      (fourBarUncertaintyJacobian₁ r l₁).mulVec ![fourBarUncertaintyRates₂ r l₁ 0,
        fourBarUncertaintyRates₂ r l₁ 1] = ![0, 0, -l₁] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [fourBarUncertaintyJacobian₁, fourBarUncertaintyRates₁, fourBarUncertaintyRates₂,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **MLS p. 138: the mechanism can move instantaneously in two independent directions.** For
`l₁ ≠ 0` the end-effector twists produced by the two printed velocities are linearly
independent. -/
theorem linearIndependent_fourBarUncertainty_toolTwists {l₁ : ℝ} (hl : l₁ ≠ 0) :
    LinearIndependent ℝ ![(![0, l₁, 0] : Fin 3 → ℝ), ![0, 0, -l₁]] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp at h1 h2
  exact ⟨h1.resolve_right hl, h2.resolve_right hl⟩

end RoboLean.Examples
