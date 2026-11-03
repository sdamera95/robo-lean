import RoboLean.Examples.InverseElbow
import RoboLean.Kinematics.Singularity

/-!
# A singular configuration of the inverse elbow manipulator: MLS Exercise 4(d)

MLS Chapter 3, Exercise 4(d), printed p. 147, for the inverse elbow manipulator of Figure 3.24(ii)
(`inverseElbow l₀ l₁ l₂`, with the recorded reading of `RoboLean.Examples.InverseElbow`): when
`sin θ₄ = 0` the elbow is stretched or folded, the moved base point, elbow point and wrist point are
collinear, and the three parallel joint axes 3, 4, 5 lie in one plane, so the configuration is
singular by Example 3.12 (pp. 125–126). Only this sufficient condition is proved. A statement about
the coordinate model.
-/

noncomputable section

open Real

namespace RoboLean.Examples

/-- **MLS Exercise 4(d), p. 147, for Figure 3.24(ii), with Example 3.12, pp. 125–126: the inverse
elbow is singular with its elbow stretched or folded.** If `sin θ₄ = 0`, the three parallel axes
about `(−c₁c₂, −s₁c₂, s₂)` through the moved base point, elbow point and wrist point lie in the plane
with unit normal `(c₁s₂c₃ − s₁s₃, s₁s₂c₃ + c₁s₃, c₂c₃)`, and the configuration is singular. -/
theorem inverseElbow_isSingular_of_sin_elbow_eq_zero (l₀ l₁ l₂ : ℝ) {θ : Fin 6 → ℝ}
    (h₄ : sin (θ 3) = 0) : (inverseElbow l₀ l₁ l₂).IsSingular θ := by
  have h0 := sin_sq_add_cos_sq (θ 0)
  have h1 := sin_sq_add_cos_sq (θ 1)
  have h2 := sin_sq_add_cos_sq (θ 2)
  set ν : Vec3 := vec (cos (θ 0) * sin (θ 1) * cos (θ 2) - sin (θ 0) * sin (θ 2))
    (sin (θ 0) * sin (θ 1) * cos (θ 2) + cos (θ 0) * sin (θ 2)) (cos (θ 1) * cos (θ 2)) with hνdef
  set qs : Fin 3 → Vec3 := ![vec 0 0 l₀,
    vec (-(l₁ * (cos (θ 0) * sin (θ 1) * sin (θ 2) + sin (θ 0) * cos (θ 2))))
      (l₁ * (cos (θ 0) * cos (θ 2) - sin (θ 0) * sin (θ 1) * sin (θ 2)))
      (l₀ - l₁ * (cos (θ 1) * sin (θ 2))),
    ((inverseElbow l₀ l₁ l₂).fk θ).translation] with hqs
  have hplane : ∀ i, inner ℝ ν (qs i) = inner ℝ ν (vec 0 0 l₀) := by
    intro i
    fin_cases i
    · rfl
    · simp only [hqs, hνdef]
      simp only [PiLp.inner_apply, Fin.sum_univ_three, vec, RCLike.inner_apply, conj_trivial]
      simp
      linear_combination (l₁ * sin (θ 2) * cos (θ 2) * (1 - sin (θ 1) ^ 2)) * h0 -
        (l₁ * sin (θ 2) * cos (θ 2)) * h1
    · simp only [hqs, hνdef, inverseElbow_fk_translation]
      simp only [PiLp.inner_apply, Fin.sum_univ_three, vec, RCLike.inner_apply, conj_trivial]
      simp only [cos_add, sin_add]
      simp
      linear_combination
        (sin (θ 1) ^ 2 * cos (θ 2) * (-(l₁ * sin (θ 2) + l₂ * (sin (θ 2) * cos (θ 3) +
            cos (θ 2) * sin (θ 3)))) +
          sin (θ 2) * (l₁ * cos (θ 2) + l₂ * (cos (θ 2) * cos (θ 3) - sin (θ 2) * sin (θ 3)))) * h0 +
        (cos (θ 2) * (-(l₁ * sin (θ 2) + l₂ * (sin (θ 2) * cos (θ 3) +
            cos (θ 2) * sin (θ 3))))) * h1 -
        (l₂ * (sin (θ 2) ^ 2 + cos (θ 2) ^ 2)) * h₄
  refine SerialChain.isSingular_of_three_parallel_coplanar_revolute _ θ le_rfl ![2, 3, 4]
    (by decide) (fun _ => vec (-(cos (θ 0) * cos (θ 1))) (-(sin (θ 0) * cos (θ 1))) (sin (θ 1))) qs
    ?_ (fun _ _ => Or.inl rfl) ν ?_ ?_ ?_
  · intro k
    rw [inverseElbow_spatialJacobian]
    fin_cases k <;> rfl
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [hνdef, Fin.sum_univ_three, vec]
    linear_combination (sin (θ 1) ^ 2 * cos (θ 2) ^ 2 + sin (θ 2) ^ 2) * h0 +
      cos (θ 2) ^ 2 * h1 + h2
  · intro i
    simp [hνdef, PiLp.inner_apply, Fin.sum_univ_three, vec]
    linear_combination (-(cos (θ 1) * sin (θ 1) * cos (θ 2))) * h0
  · intro i j
    rw [inner_sub_right, hplane i, hplane j, sub_self]

end RoboLean.Examples
