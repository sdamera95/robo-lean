import RoboLean.Geometry.PlanarRigidMotion

/-!
# `SO(2)` is the unit circle (MLS Exercise 10(a), p. 75)

A planar rotation is determined by its first column `(cos θ, sin θ)`, a point of the unit circle
`S¹ ⊂ ℝ²`, and every point of the circle is the first column of exactly one rotation. Convention:
the circle is `Metric.sphere 0 1` in the Euclidean plane `Vec2`; the rotation of the point
`(c, s)` is `[[c, −s], [s, c]]`.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace PlanarRotation

/-- Supporting lemma: a point `(c, s)` of the unit circle has `c² + s² = 1` (MLS Exercise 10(a),
p. 75). -/
private theorem sq_add_sq_of_mem_sphere (x : Metric.sphere (0 : Vec2) 1) :
    (x : Vec2) 0 ^ 2 + (x : Vec2) 1 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (x : Vec2)
  rw [mem_sphere_zero_iff_norm.mp x.2, Fin.sum_univ_two] at h
  linarith

/-- The planar rotation `[[c, −s], [s, c]]` of a point `(c, s)` of the unit circle (MLS
Exercise 10(a), p. 75). -/
def ofSphere (x : Metric.sphere (0 : Vec2) 1) : PlanarRotation :=
  ⟨!![(x : Vec2) 0, -(x : Vec2) 1; (x : Vec2) 1, (x : Vec2) 0], by
    rw [of_mem_specialOrthogonalGroup_fin_two_iff]
    exact ⟨rfl, rfl, by rw [neg_sq]; exact sq_add_sq_of_mem_sphere x⟩⟩

/-- **MLS Exercise 10(a), p. 75: `SO(2)` can be identified with the unit circle `S¹ ⊂ ℝ²`,** by the
first column `R ↦ (R₁₁, R₂₁)`, with inverse `(c, s) ↦ [[c, −s], [s, c]]`. Euclidean norm. -/
def equivSphere : PlanarRotation ≃ Metric.sphere (0 : Vec2) 1 where
  toFun R := ⟨WithLp.toLp 2 ![R.val 0 0, R.val 1 0], by
    obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.2
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp
    rw [h2, neg_sq] at h3
    linarith⟩
  invFun := ofSphere
  left_inv R := by
    obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofSphere, h1, h2]
  right_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [ofSphere]

/-- The rotation by `θ` of MLS Exercise 10(b), p. 75, corresponds to the point
`(cos θ, sin θ)` of the circle under the identification of Exercise 10(a). -/
theorem equivSphere_ofAngle (θ : ℝ) :
    ((equivSphere (ofAngle θ) : Metric.sphere (0 : Vec2) 1) : Vec2) =
      WithLp.toLp 2 ![Real.cos θ, Real.sin θ] := by
  simp [equivSphere, ofAngle]

end PlanarRotation
end RoboLean
