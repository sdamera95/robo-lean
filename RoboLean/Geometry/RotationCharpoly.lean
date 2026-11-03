import RoboLean.Geometry.RotationLog
import RoboLean.Geometry.RotationEigenvalues

/-!
# The characteristic polynomial of a rotation (MLS Chapter 2, Exercise 3(b))

MLS Chapter 2, Exercise 3(b), printed p. 73: "Show that the eigenvalues of `R` are `1`, `e^{iθ}`
and `e^{-iθ}`", for `R = exp(ω̂θ)` with `ω` a unit vector. Here: every `R ∈ SO(3)` has
characteristic polynomial `(X - 1)(X² - (tr R - 1) X + 1)` (its adjugate is `Rᵀ`, so the sum of
its principal `2 × 2` minors is its trace, and `det R = 1`), and for `R = exp(ω̂θ)` the trace is
`1 + 2 cos θ`, giving `(X - 1)(X² - 2 cos θ X + 1)`, whose roots are `1` and `e^{±iθ}`
(`Rotation.complex_quadratic_eq`). Characteristic polynomials are Mathlib's `Matrix.charpoly`.
-/

noncomputable section

open Matrix Polynomial

namespace RoboLean.Rotation

/-- MLS Exercise 3(b), printed p. 73: the characteristic polynomial of a rotation matrix
`R ∈ SO(3)` (eq. (2.2), p. 24) is `(X - 1)(X² - (tr R - 1) X + 1)`; in particular `1` is an
eigenvalue. -/
theorem charpoly_rotation (R : Rotation) :
    R.val.charpoly = (X - 1) * (X ^ 2 - C (Matrix.trace R.val - 1) * X + 1) := by
  have hadj : adjugate R.val = R.valᵀ :=
    calc adjugate R.val = (R.valᵀ * R.val) * adjugate R.val := by
          rw [transpose_mul, Matrix.one_mul]
      _ = R.valᵀ * (R.val * adjugate R.val) := by rw [Matrix.mul_assoc]
      _ = R.valᵀ := by rw [mul_adjugate, det_eq_one, one_smul, Matrix.mul_one]
  have e := fun i => congrFun (congrFun hadj i) i
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp [adjugate_fin_three] at e0 e1 e2
  have ed := det_eq_one R
  rw [det_fin_three] at ed
  have c0 := congrArg C e0
  have c1 := congrArg C e1
  have c2 := congrArg C e2
  have cd := congrArg C ed
  simp only [map_sub, map_mul, map_add, map_one] at c0 c1 c2 cd
  rw [Matrix.charpoly, det_fin_three]
  simp [Matrix.trace, Fin.sum_univ_three]
  linear_combination X * (c0 + c1 + c2) - cd

/-- **MLS Exercise 3(b)**, printed p. 73: for a unit vector `ω`, the characteristic polynomial of
`R = exp(ω̂θ)` is `(X - 1)(X² - 2 cos θ X + 1)`, with roots `1`, `e^{iθ}` and `e^{-iθ}`. -/
theorem charpoly_exp_of_norm_eq_one {ω : Vec3} (hω : ‖ω‖ = 1) (θ : ℝ) :
    (exp ω θ).val.charpoly = (X - 1) * (X ^ 2 - C (2 * Real.cos θ) * X + 1) := by
  rw [charpoly_rotation, trace_exp_of_norm_eq_one ω hω θ]
  ring_nf

end RoboLean.Rotation
