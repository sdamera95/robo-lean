import RoboLean.Kinematics.JacobianDerivative
import RoboLean.Examples.PlanarTwoLink

/-!
# The planar two-link arm: Jacobian columns as partial derivatives

The kinematic planar two-link arm `planarTwoLink a b` (MLS Example 3.1, p. 87, and Example 3.8,
printed p. 118; zero configuration along `+y`) as an instance of
`RoboLean.Kinematics.JacobianDerivative`: the partial derivatives `∂g_st/∂θᵢ g_st⁻¹` of its
forward kinematics are the hats of the spatial Jacobian columns printed in Example 3.8,
`ξ₁ = (0, 0, 0, 0, 0, 1)` and `ξ₂' = (l₁ cos θ₁, l₁ sin θ₁, 0, 0, 0, 1)` with `l₁ = a`, the same
columns as the trajectory form (`planarTwoLink_spatialJacobian_zero`,
`planarTwoLink_spatialJacobian_one`). Twist order `(v, ω)`. Convention checks of the general
statements, not separate results.
-/

noncomputable section

namespace RoboLean.Examples

/-- **MLS eq. (3.53), p. 116, and Example 3.8, p. 118, first column.** For the planar two-link
arm, `∂g_st/∂θ₁ g_st⁻¹` is the hat of `ξ₁ = (0, 0, 0, 0, 0, 1)` at every joint vector. -/
theorem planarTwoLink_fkPartial_mul_inv_zero (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).fkPartial q 0 * (((planarTwoLink a b).fk q)⁻¹).toHomogeneous =
      (⟨vec 0 0 0, vec 0 0 1⟩ : Twist).hat := by
  rw [SerialChain.fkPartial_mul_inv_eq_hat_spatialJacobian, planarTwoLink_spatialJacobian_zero]

/-- **MLS eq. (3.53), p. 116, and Example 3.8, p. 118, second column.** For the planar two-link
arm, `∂g_st/∂θ₂ g_st⁻¹` is the hat of `ξ₂' = (l₁ cos θ₁, l₁ sin θ₁, 0, 0, 0, 1)`, `l₁ = a`. -/
theorem planarTwoLink_fkPartial_mul_inv_one (a b : ℝ) (q : Fin 2 → ℝ) :
    (planarTwoLink a b).fkPartial q 1 * (((planarTwoLink a b).fk q)⁻¹).toHomogeneous =
      (⟨vec (a * Real.cos (q 0)) (a * Real.sin (q 0)) 0, vec 0 0 1⟩ : Twist).hat := by
  rw [SerialChain.fkPartial_mul_inv_eq_hat_spatialJacobian, planarTwoLink_spatialJacobian_one]

/-- **MLS eqs. (3.51)–(3.52), p. 115, and Example 3.8, p. 118: the derivative in a direction.**
For the planar two-link arm, the derivative of the entry `(a', b')` of `g_st` at `q` applied to a
direction `v` is the entry of `(v₁ ξ₁ + v₂ ξ₂')^ g_st(q)` with the printed columns. -/
theorem planarTwoLink_fderiv_fk_toHomogeneous_apply (a b : ℝ) (q v : Fin 2 → ℝ)
    (i j : HomogeneousIndex) :
    fderiv ℝ (fun φ : Fin 2 → ℝ => ((planarTwoLink a b).fk φ).toHomogeneous i j) q v =
      ((v 0 • (⟨vec 0 0 0, vec 0 0 1⟩ : Twist) +
          v 1 • (⟨vec (a * Real.cos (q 0)) (a * Real.sin (q 0)) 0, vec 0 0 1⟩ : Twist)).hat *
        ((planarTwoLink a b).fk q).toHomogeneous) i j := by
  rw [SerialChain.fderiv_fk_toHomogeneous_apply, Fin.sum_univ_two,
    planarTwoLink_spatialJacobian_zero, planarTwoLink_spatialJacobian_one]

end RoboLean.Examples
