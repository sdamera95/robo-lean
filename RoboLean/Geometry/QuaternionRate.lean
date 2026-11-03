import RoboLean.Geometry.QuaternionRotation

/-!
# The quaternion rate equation (MLS Chapter 2, Exercise 6(e))

MLS Chapter 2, Exercise 6(e), printed p. 74: "Show that a rigid body rotating at unit velocity
about a unit vector in `ω ∈ ℝ³` can be represented by the quaternion differential equations
`Q̇ · Q* = (0, ω/2)`, where `·` represents quaternion multiplication."

The body rotating at unit angular velocity about `ω` from the identity has `R(t) = exp(ω̂t)`,
represented (p. 34, `QuaternionCoordinates.rotationMatrix_axisAngle`) by the axis-angle quaternion
`Q(t) = (cos(t/2), ω sin(t/2))`. Here: `Q` has derivative
`Q̇(t) = (-sin(t/2)/2, ω cos(t/2)/2)` (Mathlib's `HasDerivAt` in `ℍ[ℝ]`), and for a unit `ω`,
`Q̇(t) Q(t)* = (0, ω/2)`; equivalently `Q̇ = (0, ω/2) Q`. Quaternions are Mathlib's
`Quaternion ℝ`, scalar part first.
-/

noncomputable section

namespace RoboLean.QuaternionCoordinates

/-- **MLS Exercise 6(e)**, printed p. 74: the axis-angle quaternion `Q(t) = (cos(t/2), ω sin(t/2))`
of the rotation `exp(ω̂t)` (p. 34) has derivative `(-sin(t/2)/2, ω cos(t/2)/2)`. -/
theorem hasDerivAt_axisAngle (ω : Vec3) (t : ℝ) :
    HasDerivAt (fun s => axisAngle ω s)
      (ofScalarVector (-(Real.sin (t / 2) / 2)) ((Real.cos (t / 2) / 2) • ω)) t := by
  have h : (fun s => axisAngle ω s) =
      fun s => Real.cos (s / 2) • (1 : Quaternion ℝ) + Real.sin (s / 2) • ofScalarVector 0 ω := by
    funext s
    ext <;> simp [axisAngle, ofScalarVector]
  rw [h]
  have hc : HasDerivAt (fun s => Real.cos (s / 2)) (-Real.sin (t / 2) * (1 / 2)) t := by
    exact ((hasDerivAt_id t).div_const 2).cos
  have hs : HasDerivAt (fun s => Real.sin (s / 2)) (Real.cos (t / 2) * (1 / 2)) t := by
    exact ((hasDerivAt_id t).div_const 2).sin
  convert (hc.smul_const (1 : Quaternion ℝ)).add (hs.smul_const (ofScalarVector 0 ω)) using 1
  ext <;> simp [ofScalarVector, div_eq_mul_inv]

/-- **MLS Exercise 6(e)**, printed p. 74: for a unit vector `ω`, the axis-angle quaternion of a
body rotating at unit velocity about `ω` satisfies `Q̇ · Q* = (0, ω/2)`. -/
theorem axisAngle_rate_mul_star {ω : Vec3} (hω : ‖ω‖ = 1) (t : ℝ) :
    ofScalarVector (-(Real.sin (t / 2) / 2)) ((Real.cos (t / 2) / 2) • ω) * star (axisAngle ω t) =
      ofScalarVector 0 ((1 / 2 : ℝ) • ω) := by
  have hn : ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2 = 1 := by
    have := hω
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
    simpa [Fin.sum_univ_three] using this
  have hsc := Real.sin_sq_add_cos_sq (t / 2)
  ext <;> simp [ofScalarVector, axisAngle]
  · linear_combination (Real.sin (t / 2) * Real.cos (t / 2) / 2) * hn
  · linear_combination (ω 0 / 2) * hsc
  · linear_combination (ω 1 / 2) * hsc
  · linear_combination (ω 2 / 2) * hsc

/-- **MLS Exercise 6(e)**, printed p. 74, as a differential equation: for a unit vector `ω`, the
axis-angle quaternion `Q(t)` of `exp(ω̂t)` solves `Q̇ = (0, ω/2) · Q`. -/
theorem hasDerivAt_axisAngle_eq_mul {ω : Vec3} (hω : ‖ω‖ = 1) (t : ℝ) :
    HasDerivAt (fun s => axisAngle ω s) (ofScalarVector 0 ((1 / 2 : ℝ) • ω) * axisAngle ω t) t := by
  have hQ : star (axisAngle ω t) * axisAngle ω t = 1 := by
    rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, norm_axisAngle hω, one_mul]
    simp
  convert hasDerivAt_axisAngle ω t using 1
  rw [← axisAngle_rate_mul_star hω t, mul_assoc, hQ, mul_one]

end RoboLean.QuaternionCoordinates
