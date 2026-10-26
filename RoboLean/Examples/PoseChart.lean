import RoboLean.Dynamics.PoseChart

/-!
# Concrete instances of the pose chart of `SE(3)`: a regular point and the singular set

MLS Chapter 2, eqs. (2.19)–(2.20), printed p. 32; Chapter 6, §2.1, p. 277 (a local parameterization
`x ∈ ℝ⁶` of the object pose), eq. (6.23), p. 279, and Exercise 4(b), p. 314. Coordinates are
`ξ = (p, α, β, γ)`, position first, angles in the order `(α, β, γ)`; twist rows `(v, ω)`.

* The regular point `ξ₀ = (0, 0, π/2, 0)` (`poseChartRegularPoint`, `β = π/2`): the chart centered
  at `I` maps it to the pose `(R_y(π/2), 0)` written as `R_z(0) R_y(π/2) R_z(0)`
  (`eulerChart_poseChartRegularPoint`); the relabeled chart Jacobian has determinant `−1`
  (`det_eulerChartJacobianFin_poseChartRegularPoint`), so the chart Jacobian is a bijection
  (`eulerChartJacobian_poseChartRegularPoint_bijective`) and the relabeled one is onto
  (`eulerChartJacobianFin_poseChartRegularPoint_surjective`), the hypothesis of the reading of
  (6.23) against a chart (`Composite.effective_dynamics_chart_iff`) at this point.
* The singular set: every coordinate value of the identity orientation in the chart centered at `I`
  has `sin β = 0` (`sin_eq_zero_of_eulerChart_eq_identity`, MLS p. 32), while the chart centered at
  `eulerCenter I` reaches the identity at the regular point
  (`eulerChart_eulerCenter_one_poseChartRegularPoint`); at `ξ = 0` the chart Jacobian is not
  one-to-one (`not_injective_eulerChartJacobian_zero`).

These are convention checks and satisfying instances of the hypotheses of `Composite`'s pose-chart
theorems; nothing here models a physical object.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Examples

open Composite

/-- **A regular point of the pose chart (MLS eq. (2.19), p. 32; p. 277):** the coordinates
`ξ₀ = (p, α, β, γ) = (0, 0, 0, 0, π/2, 0)`, position first, with middle Euler angle `β = π/2`. -/
def poseChartRegularPoint : Fin 6 → ℝ := ![0, 0, 0, 0, Real.pi / 2, 0]

/-- The Euler angles of the regular point are `(α, β, γ) = (0, π/2, 0)` (MLS eq. (2.19),
p. 32). -/
private theorem eulerAngles_poseChartRegularPoint :
    eulerAngles poseChartRegularPoint = ![0, Real.pi / 2, 0] := by
  funext i
  fin_cases i <;> rfl

/-- The middle Euler angle of the regular point has `sin β = 1` (MLS p. 32). -/
private theorem sin_eulerAngles_poseChartRegularPoint :
    Real.sin (eulerAngles poseChartRegularPoint 1) = 1 := by
  rw [eulerAngles_poseChartRegularPoint]
  simp

/-- **The pose at the regular point (MLS eq. (2.19), p. 32; p. 277):** the chart centered at `I`
maps `ξ₀ = (0, 0, π/2, 0)` (coordinates `(p, α, β, γ)`, position first) to the pose with rotation
`R_z(0) R_y(π/2) R_z(0)` and translation `0`. -/
theorem eulerChart_poseChartRegularPoint :
    eulerChart 1 poseChartRegularPoint = ⟨Rotation.zyz 0 (Real.pi / 2) 0, 0⟩ := by
  ext1
  · rw [eulerChart, eulerRotation, eulerAngles_poseChartRegularPoint, one_mul]
    rfl
  · apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> rfl

/-- **The relabeled chart Jacobian at the regular point has determinant `−1` (MLS Exercise 4(b),
p. 314; p. 32):** `det = −sin(π/2)`, twist rows `(v, ω)` relabeled to `Fin 6`. -/
theorem det_eulerChartJacobianFin_poseChartRegularPoint :
    (eulerChartJacobianFin 1 poseChartRegularPoint).det = -1 := by
  rw [det_eulerChartJacobianFin, sin_eulerAngles_poseChartRegularPoint]

/-- **The chart Jacobian at the regular point is a bijection (MLS Exercise 4(b), p. 314,
"nonsingular"; p. 32, `sin β ≠ 0`)**, from the coordinate rates `(ṗ, α̇, β̇, γ̇)` to the body twist
`(v, ω)`. -/
theorem eulerChartJacobian_poseChartRegularPoint_bijective :
    Function.Bijective (eulerChartJacobian 1 poseChartRegularPoint).mulVec := by
  have hβ : Real.sin (eulerAngles poseChartRegularPoint 1) ≠ 0 := by
    rw [sin_eulerAngles_poseChartRegularPoint]
    exact one_ne_zero
  exact ⟨eulerChartJacobian_injective 1 hβ, eulerChartJacobian_surjective 1 hβ⟩

/-- **The relabeled chart Jacobian at the regular point is onto (MLS eq. (6.23), p. 279, read
against a chart; Exercise 4(b), p. 314):** the hypothesis of
`Composite.effective_dynamics_chart_iff` with `p = k = 6`, twist rows `(v, ω)` relabeled to
`Fin 6`. -/
theorem eulerChartJacobianFin_poseChartRegularPoint_surjective :
    Function.Surjective (eulerChartJacobianFin 1 poseChartRegularPoint).mulVec := by
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    det_eulerChartJacobianFin_poseChartRegularPoint]
  exact isUnit_one.neg

/-- **The identity is singular for ZYZ angles (MLS p. 32, "singularities in the parameterization
... occur at `R = I`"):** every coordinate value `ξ = (p, α, β, γ)` at which the chart centered at
`I` has the identity orientation has `sin β = 0`. -/
theorem sin_eq_zero_of_eulerChart_eq_identity {ξ : Fin 6 → ℝ}
    (h : (eulerChart 1 ξ).rotation = 1) : Real.sin (eulerAngles ξ 1) = 0 := by
  by_contra hs
  have hr := (exists_eulerChart_eq_iff 1 (eulerChart 1 ξ)).mp ⟨ξ, rfl, hs⟩
  rw [h, inv_one, one_mul] at hr
  simp [Rotation.zyzRadial] at hr

/-- **The identity is a regular value of a recentered chart (MLS p. 32; p. 277):** the chart
centered at `eulerCenter I = R_y(π/2)⁻¹` reaches the identity orientation at the regular point
`ξ₀ = (0, 0, π/2, 0)`, coordinates `(p, α, β, γ)`. -/
theorem eulerChart_eulerCenter_one_poseChartRegularPoint :
    (eulerChart (eulerCenter 1) poseChartRegularPoint).rotation = 1 := by
  change eulerCenter 1 * Rotation.zyz (eulerAngles poseChartRegularPoint 0)
    (eulerAngles poseChartRegularPoint 1) (eulerAngles poseChartRegularPoint 2) = 1
  rw [eulerAngles_poseChartRegularPoint, eulerCenter, one_mul]
  exact inv_mul_cancel _

/-- **The chart Jacobian at `ξ = 0` is not one-to-one (MLS p. 32, the singular set `sin β = 0`;
Exercise 4(b), p. 314):** coordinates `(p, α, β, γ)`, twist rows `(v, ω)`. -/
theorem not_injective_eulerChartJacobian_zero :
    ¬ Function.Injective (eulerChartJacobian 1 0).mulVec :=
  not_injective_eulerChartJacobian 1 (by simp [eulerAngles])

end Examples
end RoboLean
