import RoboLean.Examples.Rhino
import RoboLean.Kinematics.Singularity

/-!
# A singular configuration of the Rhino robot: MLS Exercise 4(d)

MLS Chapter 3, Exercise 4(d), printed p. 147, for the Rhino robot of Figure 3.24(iv)
(`rhino l₀ l₁ l₂`, with the recorded reading of `RoboLean.Examples.Rhino`): "give a geometric
description of the singular configurations". One family: when `sin θ₂ = 0` the vertical plane of
the arm, with normal `(cos θ₂, sin θ₂, 0)`, contains the slide direction `e_y`; the slide twist
`(e_y, 0)` and the three parallel joints about `∓e_x` all lie in the three-dimensional space of
twists `(0, v_y, v_z, ω_x, 0, 0)` of motions in that plane, so four columns of the spatial Jacobian
are dependent and the configuration is singular (MLS p. 123). A second family: when `sin θ₄ = 0` the
elbow is stretched or folded and the three parallel axes are coplanar (Example 3.12). Only these
sufficient conditions are proved; the other singular configurations of the arm and Exercise 4(e) are
not treated. Statements about the coordinate model.
-/

noncomputable section

open Real

namespace RoboLean.Examples

/-- **MLS Exercise 4(d), p. 147, for Figure 3.24(iv): the Rhino is singular when the slide lies in
the plane of the arm.** If `sin θ₂ = 0`, the configuration is singular (MLS p. 123): the spatial
Jacobian columns of the slide and of the three parallel joints lie in the three-dimensional space
of planar twists `(0, v_y, v_z, ω_x, 0, 0)`. -/
theorem rhino_isSingular_of_sin_eq_zero (l₀ l₁ l₂ : ℝ) {θ : Fin 6 → ℝ} (h₂ : sin (θ 1) = 0) :
    (rhino l₀ l₁ l₂).IsSingular θ := by
  rw [SerialChain.isSingular_iff_not_linearIndependent _ θ le_rfl]
  intro hJ
  set E : Fin 3 → Twist :=
    ![⟨vec 0 1 0, vec 0 0 0⟩, ⟨vec 0 0 1, vec 0 0 0⟩, ⟨vec 0 0 0, vec 1 0 0⟩] with hE
  have key : ∀ V : Twist, V.linear 0 = 0 → V.angular 1 = 0 → V.angular 2 = 0 →
      V ∈ Submodule.span ℝ (Set.range E) := by
    intro V h0 h1 h2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![V.linear 1, V.linear 2, V.angular 0], ?_⟩
    apply Twist.ext <;> ext i <;> fin_cases i <;> simp [Fin.sum_univ_three, hE, vec, h0, h1, h2]
  let f : Fin 4 → Fin 6 := ![0, 2, 3, 4]
  have hfi : Function.Injective f := by decide
  have hli := hJ.comp f hfi
  have hspan : Submodule.span ℝ (Set.range ((rhino l₀ l₁ l₂).spatialJacobian θ ∘ f)) ≤
      Submodule.span ℝ (Set.range E) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    apply key <;> fin_cases k <;>
      simp [f, rhino_spatialJacobian, Twist.revolute, Vec3.cross, cross_apply, vec, h₂]
  have h4 := finrank_span_eq_card hli
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range E)) ≤ 3 :=
    (finrank_range_le_card E).trans (by simp)
  have hmono := Submodule.finrank_mono hspan
  simp only [Fintype.card_fin] at h4
  omega

/-- **MLS Exercise 4(d), p. 147, for Figure 3.24(iv), with Example 3.12, pp. 125–126: the Rhino is
singular with its elbow stretched or folded.** If `sin θ₄ = 0`, the three parallel joint axes about
`(−c₂, −s₂, 0)` pass through collinear points (the moved shoulder, elbow and wrist), so they lie in
one plane, with unit normal `(−s₂s₃, c₂s₃, c₃)`, and the configuration is singular. -/
theorem rhino_isSingular_of_sin_elbow_eq_zero (l₀ l₁ l₂ : ℝ) {θ : Fin 6 → ℝ}
    (h₄ : sin (θ 3) = 0) : (rhino l₀ l₁ l₂).IsSingular θ := by
  have h1 := sin_sq_add_cos_sq (θ 1)
  have h2 := sin_sq_add_cos_sq (θ 2)
  set ν : Vec3 := vec (-(sin (θ 1) * sin (θ 2))) (cos (θ 1) * sin (θ 2)) (cos (θ 2)) with hνdef
  set qs : Fin 3 → Vec3 := ![vec 0 (θ 0) l₀,
    vec (-(l₁ * (sin (θ 1) * cos (θ 2)))) (θ 0 + l₁ * (cos (θ 1) * cos (θ 2))) (l₀ - l₁ * sin (θ 2)),
    ((rhino l₀ l₁ l₂).fk θ).translation] with hqs
  have hplane : ∀ i, inner ℝ ν (qs i) = inner ℝ ν (vec 0 (θ 0) l₀) := by
    intro i
    fin_cases i
    · rfl
    · simp only [hqs, hνdef]
      simp only [PiLp.inner_apply, Fin.sum_univ_three, vec, RCLike.inner_apply, conj_trivial]
      simp
      linear_combination (l₁ * sin (θ 2) * cos (θ 2)) * h1
    · simp only [hqs, hνdef, rhino_fk_translation]
      simp only [PiLp.inner_apply, Fin.sum_univ_three, vec, RCLike.inner_apply, conj_trivial]
      simp only [cos_add, sin_add]
      simp
      linear_combination (sin (θ 2) * (l₁ * cos (θ 2) + l₂ * (cos (θ 2) * cos (θ 3) -
        sin (θ 2) * sin (θ 3)))) * h1 - (l₂ * (sin (θ 2) ^ 2 + cos (θ 2) ^ 2)) * h₄
  refine SerialChain.isSingular_of_three_parallel_coplanar_revolute _ θ le_rfl ![2, 3, 4]
    (by decide) (fun _ => vec (-cos (θ 1)) (-sin (θ 1)) 0) qs ?_ (fun _ _ => Or.inl rfl) ν ?_ ?_ ?_
  · intro k
    rw [rhino_spatialJacobian]
    fin_cases k <;> rfl
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [hνdef, Fin.sum_univ_three, vec]
    linear_combination (sin (θ 2) ^ 2) * h1 + h2
  · intro i
    simp [hνdef, PiLp.inner_apply, Fin.sum_univ_three, vec]
    ring
  · intro i j
    rw [inner_sub_right, hplane i, hplane j, sub_self]

end RoboLean.Examples
