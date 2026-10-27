import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Example 3.17: the self-motion of a planar three-link manipulator

MLS Example 3.17, printed pp. 131–132, Figure 3.17. The planar three-link arm with link lengths
`l₁, l₂, l₃` (zero configuration along `+x`, angles measured from `+x` counterclockwise) holds its
end-effector position `(x, y)` fixed under the two constraints

`l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) + l₃ cos(θ₁ + θ₂ + θ₃) = x`,
`l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) + l₃ sin(θ₁ + θ₂ + θ₃) = y`.

The book prints the Jacobian (3.64) of `p : θ ↦ (x, y)` and the vector
`V_N = (l₂ l₃ sin θ₃, -l₂ l₃ sin θ₃ - l₁ l₃ sin(θ₂ + θ₃), l₁ l₂ sin θ₂ + l₁ l₃ sin(θ₂ + θ₃))` that
spans its null space; "any velocity `θ̇ = α V_N` is tangent to the self-motion manifold and
maintains the position of the end-effector."

Formalized here, for all real link lengths and angles: the position map and the printed Jacobian
(3.64) as its derivative along joint trajectories; `(∂p/∂θ) V_N = 0`; `V_N` is the cross product
of the two rows of (3.64), so when `V_N ≠ 0` (the rows are independent) the null space is exactly
the line spanned by `V_N`; along a joint trajectory with rates `α V_N` the position has derivative
zero. The book's index `i` is Lean's `i - 1` (`θ 0 = θ₁`). This is the position map only, not a
`SerialChain` with twists.
-/

noncomputable section

namespace RoboLean.Examples

/-- The end-effector position of the planar three-link arm of MLS Example 3.17, p. 131, as
printed: `(l₁ c₁ + l₂ c₁₂ + l₃ c₁₂₃, l₁ s₁ + l₂ s₁₂ + l₃ s₁₂₃)`, zero configuration along `+x`. -/
def planarThreeLinkPosition (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![l₁ * Real.cos (θ 0) + l₂ * Real.cos (θ 0 + θ 1) + l₃ * Real.cos (θ 0 + θ 1 + θ 2),
    l₁ * Real.sin (θ 0) + l₂ * Real.sin (θ 0 + θ 1) + l₃ * Real.sin (θ 0 + θ 1 + θ 2)]

/-- **MLS eq. (3.64), p. 131:** the Jacobian `∂p/∂θ` of the planar three-link arm as printed,
with `sᵢⱼₖ = sin(θᵢ + θⱼ + θₖ)` and similarly `cᵢⱼₖ`. -/
def planarThreeLinkJacobian (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-l₁ * Real.sin (θ 0) - l₂ * Real.sin (θ 0 + θ 1) - l₃ * Real.sin (θ 0 + θ 1 + θ 2),
      -l₂ * Real.sin (θ 0 + θ 1) - l₃ * Real.sin (θ 0 + θ 1 + θ 2),
      -l₃ * Real.sin (θ 0 + θ 1 + θ 2);
    l₁ * Real.cos (θ 0) + l₂ * Real.cos (θ 0 + θ 1) + l₃ * Real.cos (θ 0 + θ 1 + θ 2),
      l₂ * Real.cos (θ 0 + θ 1) + l₃ * Real.cos (θ 0 + θ 1 + θ 2),
      l₃ * Real.cos (θ 0 + θ 1 + θ 2)]

/-- **MLS p. 132: the null vector `V_N` of Example 3.17**, as printed. -/
def planarThreeLinkNullVector (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![l₂ * l₃ * Real.sin (θ 2),
    -l₂ * l₃ * Real.sin (θ 2) - l₁ * l₃ * Real.sin (θ 1 + θ 2),
    l₁ * l₂ * Real.sin (θ 1) + l₁ * l₃ * Real.sin (θ 1 + θ 2)]

/-- **MLS eq. (3.64), p. 131: the printed Jacobian is the derivative of the position map.** Along
a joint trajectory with rates `θ̇` at `t`, each coordinate of `p(θ(s))` has derivative
`((∂p/∂θ) θ̇)` at `t`. -/
theorem hasDerivAt_planarThreeLinkPosition (l₁ l₂ l₃ : ℝ) {θ : ℝ → Fin 3 → ℝ}
    {θ' : Fin 3 → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) (r : Fin 2) :
    HasDerivAt (fun s => planarThreeLinkPosition l₁ l₂ l₃ (θ s) r)
      ((planarThreeLinkJacobian l₁ l₂ l₃ (θ t)).mulVec θ' r) t := by
  have h01 := (hθ 0).add (hθ 1)
  have h012 := h01.add (hθ 2)
  fin_cases r
  · refine ((((hθ 0).cos.const_mul l₁).add (h01.cos.const_mul l₂)).add
      (h012.cos.const_mul l₃)).congr_deriv ?_
    simp [planarThreeLinkJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · refine ((((hθ 0).sin.const_mul l₁).add (h01.sin.const_mul l₂)).add
      (h012.sin.const_mul l₃)).congr_deriv ?_
    simp [planarThreeLinkJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring

/-- The null vector as the cross product of the Jacobian rows (the computation behind
`planarThreeLinkNullVector_eq_cross`), stated before its first use. -/
private theorem nullVector_eq_cross_aux (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) :
    planarThreeLinkNullVector l₁ l₂ l₃ θ =
      crossProduct (planarThreeLinkJacobian l₁ l₂ l₃ θ 0)
        (planarThreeLinkJacobian l₁ l₂ l₃ θ 1) := by
  have e₁ : Real.sin (θ 1) = Real.sin (θ 0 + θ 1) * Real.cos (θ 0) -
      Real.cos (θ 0 + θ 1) * Real.sin (θ 0) := by
    rw [← Real.sin_sub]; ring_nf
  have e₂ : Real.sin (θ 2) = Real.sin (θ 0 + θ 1 + θ 2) * Real.cos (θ 0 + θ 1) -
      Real.cos (θ 0 + θ 1 + θ 2) * Real.sin (θ 0 + θ 1) := by
    rw [← Real.sin_sub]; ring_nf
  have e₁₂ : Real.sin (θ 1 + θ 2) = Real.sin (θ 0 + θ 1 + θ 2) * Real.cos (θ 0) -
      Real.cos (θ 0 + θ 1 + θ 2) * Real.sin (θ 0) := by
    rw [← Real.sin_sub]; ring_nf
  funext i
  fin_cases i <;>
    simp [planarThreeLinkNullVector, planarThreeLinkJacobian, cross_apply, e₁, e₂, e₁₂] <;> ring

/-- **MLS p. 132: `V_N` is in the null space of the Jacobian (3.64)**, for all link lengths and
angles. -/
theorem planarThreeLinkJacobian_mulVec_nullVector (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) :
    (planarThreeLinkJacobian l₁ l₂ l₃ θ).mulVec (planarThreeLinkNullVector l₁ l₂ l₃ θ) = 0 := by
  rw [nullVector_eq_cross_aux]
  funext r
  fin_cases r
  · exact dot_self_cross _ _
  · exact dot_cross_self _ _

/-- `V_N` is the cross product of the two rows of the Jacobian (3.64) (MLS p. 132; why it spans
the null space of a `2 × 3` matrix with independent rows). -/
theorem planarThreeLinkNullVector_eq_cross (l₁ l₂ l₃ : ℝ) (θ : Fin 3 → ℝ) :
    planarThreeLinkNullVector l₁ l₂ l₃ θ =
      crossProduct (planarThreeLinkJacobian l₁ l₂ l₃ θ 0)
        (planarThreeLinkJacobian l₁ l₂ l₃ θ 1) := by
  exact nullVector_eq_cross_aux l₁ l₂ l₃ θ

/-- A vector orthogonal to `u` and `v` is a multiple of `u × v` when `u × v ≠ 0` (the null space
of a `2 × 3` matrix with independent rows). -/
private theorem exists_eq_smul_cross_of_dotProduct_eq_zero {u v x : Fin 3 → ℝ}
    (hc : crossProduct u v ≠ 0) (hu : u ⬝ᵥ x = 0) (hv : v ⬝ᵥ x = 0) :
    ∃ α : ℝ, x = α • crossProduct u v := by
  set c := crossProduct u v with hcdef
  have key : (c ⬝ᵥ c) • x - (c ⬝ᵥ x) • c =
      -(u ⬝ᵥ x) • crossProduct c v + (v ⬝ᵥ x) • crossProduct c u := by
    funext i
    fin_cases i <;>
      simp [hcdef, cross_apply, dotProduct, Fin.sum_univ_three] <;> ring
  rw [hu, hv, neg_zero, zero_smul, zero_smul, add_zero, sub_eq_zero] at key
  have hcc : c ⬝ᵥ c ≠ 0 := fun h => hc (dotProduct_self_eq_zero.mp h)
  refine ⟨(c ⬝ᵥ x) / (c ⬝ᵥ c), ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hcc, one_smul]

/-- **MLS p. 132: "The Jacobian has a null space spanned by the vector `V_N`".** If `V_N ≠ 0`, the
joint rates `θ̇` with `(∂p/∂θ) θ̇ = 0` are exactly the multiples `α V_N`. -/
theorem planarThreeLinkJacobian_mulVec_eq_zero_iff {l₁ l₂ l₃ : ℝ} {θ : Fin 3 → ℝ}
    (hN : planarThreeLinkNullVector l₁ l₂ l₃ θ ≠ 0) (θ' : Fin 3 → ℝ) :
    (planarThreeLinkJacobian l₁ l₂ l₃ θ).mulVec θ' = 0 ↔
      ∃ α : ℝ, θ' = α • planarThreeLinkNullVector l₁ l₂ l₃ θ := by
  constructor
  · intro h
    rw [planarThreeLinkNullVector_eq_cross] at hN ⊢
    exact exists_eq_smul_cross_of_dotProduct_eq_zero hN (congrFun h 0) (congrFun h 1)
  · rintro ⟨α, rfl⟩
    rw [Matrix.mulVec_smul, planarThreeLinkJacobian_mulVec_nullVector, smul_zero]

/-- **MLS p. 132: "Any velocity `θ̇ = α V_N` ... maintains the position of the end-effector."**
Along a joint trajectory whose rates at `t` are `α V_N(θ(t))`, both coordinates of the end-effector
position have derivative zero at `t`. -/
theorem hasDerivAt_planarThreeLinkPosition_nullVector (l₁ l₂ l₃ α : ℝ) {θ : ℝ → Fin 3 → ℝ}
    {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (α * planarThreeLinkNullVector l₁ l₂ l₃ (θ t) i) t)
    (r : Fin 2) :
    HasDerivAt (fun s => planarThreeLinkPosition l₁ l₂ l₃ (θ s) r) 0 t := by
  refine (hasDerivAt_planarThreeLinkPosition l₁ l₂ l₃ hθ r).congr_deriv ?_
  have : (fun i => α * planarThreeLinkNullVector l₁ l₂ l₃ (θ t) i) =
      α • planarThreeLinkNullVector l₁ l₂ l₃ (θ t) := rfl
  rw [this, Matrix.mulVec_smul, planarThreeLinkJacobian_mulVec_nullVector, smul_zero,
    Pi.zero_apply]

end RoboLean.Examples
