import RoboLean.Geometry.RotationSurjectivity
import RoboLean.Geometry.ElementaryRotations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Eigenvalues of skew-symmetric and rotation matrices (MLS Chapter 2, Exercise 3)

MLS Chapter 2, Exercise 3, printed p. 73, "Properties of rotation matrices", for `R = exp(ω̂θ)`
with `ω` a unit vector:

* (a) the eigenvalues of `ω̂` are `0, i, -i`: its characteristic polynomial is `X³ + X`
  `= X (X - i)(X + i)`; the eigenvector of `0` is `ω` (`ω̂ ω = 0`), and on the plane `N_ω^⊥` the
  map `ω̂` is the quarter turn `u ↦ ω × u` with `ω × (ω × u) = -u` (the real form of the complex
  eigenvectors `u ∓ i (ω × u)` of `±i`);
* (b) the eigenvalues of `R` are `1, e^{iθ}, e^{-iθ}`: the eigenvector of `1` is `ω`
  (`Rotation.exp_act_unit_axis`), `R` acts on `N_ω^⊥` as the rotation by `θ`
  (`Rotation.exp_act_of_inner_eq_zero`), and for the axis `e_z` the characteristic polynomial of
  `R_z(θ)` is `(X - 1)(X² - 2 cos θ X + 1)` with `X² - 2 cos θ X + 1 = (X - e^{iθ})(X - e^{-iθ})`;
  the characteristic polynomial for a general axis is not computed here;
* (c) `det R = r₁ᵀ (r₂ × r₃)` for the columns `r₁, r₂, r₃` (true for every `3 × 3` matrix).

Characteristic polynomials are Mathlib's `Matrix.charpoly`, `det (X I - A)`.
-/

noncomputable section

open Matrix Polynomial

namespace RoboLean.Rotation

/-- **MLS Exercise 3(a)**, printed p. 73: the characteristic polynomial of `ω̂` (eq. (2.4),
p. 26) is `X³ + ‖ω‖² X`. -/
theorem charpoly_hat (ω : Vec3) :
    (Vec3.hat ω).charpoly = X ^ 3 + C (‖ω‖ ^ 2) * X := by
  have hn : ‖ω‖ ^ 2 = ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_three]
  rw [hn, Matrix.charpoly, Matrix.det_fin_three]
  simp [Vec3.hat]
  ring

/-- **MLS Exercise 3(a)**, printed p. 73: for a unit vector `ω` the characteristic polynomial of
`ω̂` is `X (X² + 1)`, with roots `0` and `±i` (`(z - i)(z + i) = z² + 1` over `ℂ`). -/
theorem charpoly_hat_of_norm_eq_one {ω : Vec3} (hω : ‖ω‖ = 1) :
    (Vec3.hat ω).charpoly = X * (X ^ 2 + 1) := by
  rw [charpoly_hat, hω]
  simp
  ring

/-- MLS Exercise 3(a), printed p. 73: `(z - i)(z + i) = z² + 1` over `ℂ`, so the roots of `X² + 1`
are `±i`. -/
theorem complex_sq_add_one_eq (z : ℂ) : (z - Complex.I) * (z + Complex.I) = z ^ 2 + 1 := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **MLS Exercise 3(a)**, printed p. 73: for a unit vector `ω` and `u ⊥ ω`, `ω̂` maps `u` to
`ω × u` and `ω × u` to `-u`, the real form of the eigenvectors `u ∓ i (ω × u)` of `±i`. -/
theorem cross_cross_of_inner_eq_zero {ω : Vec3} (hω : ‖ω‖ = 1) {u : Vec3}
    (hu : inner ℝ ω u = 0) : Vec3.cross ω (Vec3.cross ω u) = -u := by
  apply WithLp.ofLp_injective
  have h1 : WithLp.ofLp ω ⬝ᵥ WithLp.ofLp ω = 1 := by
    have := real_inner_self_eq_norm_sq ω
    rw [hω, one_pow] at this
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using this
  have h2 : WithLp.ofLp ω ⬝ᵥ WithLp.ofLp u = 0 := by
    rw [dotProduct_comm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hu
  rw [Vec3.cross_coordinates, Vec3.cross_coordinates, cross_cross_eq_smul_sub_smul', h1, h2,
    one_smul, zero_smul, zero_sub, WithLp.ofLp_neg]

/-- **MLS Exercise 3(b)**, printed p. 73, for the axis `e_z`: the characteristic polynomial of
`R_z(θ)` (p. 31) is `(X - 1)(X² - 2 cos θ X + 1)`. -/
theorem charpoly_zRotation (θ : ℝ) :
    (zRotation θ).val.charpoly = (X - 1) * (X ^ 2 - C (2 * Real.cos θ) * X + 1) := by
  rw [show (C (2 * Real.cos θ) : ℝ[X]) = 2 * C (Real.cos θ) by rw [map_mul, map_ofNat],
    zRotation_val, Matrix.charpoly, Matrix.det_fin_three]
  simp
  have := Real.sin_sq_add_cos_sq θ
  have h : (C (Real.sin θ)) ^ 2 + (C (Real.cos θ)) ^ 2 = (1 : ℝ[X]) := by
    rw [← map_pow, ← map_pow, ← map_add, this, map_one]
  linear_combination (X - 1) * h

/-- MLS Exercise 3(b), printed p. 73: `(z - e^{iθ})(z - e^{-iθ}) = z² - 2 cos θ z + 1` over `ℂ`, so
the roots of `X² - 2 cos θ X + 1` are `e^{±iθ}`. -/
theorem complex_quadratic_eq (θ : ℝ) (z : ℂ) :
    (z - Complex.exp (θ * Complex.I)) * (z - Complex.exp (-(θ * Complex.I))) =
      z ^ 2 - 2 * Real.cos θ * z + 1 := by
  have h : Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [Complex.ofReal_cos, Complex.cos, neg_mul]
  linear_combination h

/-- **MLS Exercise 3(c)**, printed p. 73: the determinant of a `3 × 3` matrix with columns
`r₁, r₂, r₃` is the triple product `r₁ᵀ (r₂ × r₃)`; in particular for a rotation matrix. -/
theorem det_eq_dotProduct_cross (M : Matrix (Fin 3) (Fin 3) ℝ) :
    M.det = (fun i => M i 0) ⬝ᵥ ((fun i => M i 1) ⨯₃ (fun i => M i 2)) := by
  rw [triple_product_eq_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end RoboLean.Rotation
