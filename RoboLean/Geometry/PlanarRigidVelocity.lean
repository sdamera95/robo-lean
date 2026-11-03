import RoboLean.Geometry.PlanarRigidMotion

/-!
# Planar spatial and body velocities are twists (MLS Exercise 11(d), p. 76)

For a differentiable curve `g(t) = (p(t), R(t))` in `SE(2)`, with the derivative `ġ` of its
homogeneous matrix taken entry by entry, the matrices `V̂ˢ = ġ g⁻¹` and `V̂ᵇ = g⁻¹ ġ` are planar
twists `[[ω̂, v], [0, 0]]`: the spatial velocity `Vˢ = (vˢ, ωˢ) ∈ ℝ³` and the body velocity
`Vᵇ = (vᵇ, ωᵇ) ∈ ℝ³` of the exercise. Convention: entrywise derivatives of the `3 × 3` homogeneous
matrix, as the library's matrix curves elsewhere; `g⁻¹` is the inverse in `SE(2)`, whose homogeneous
matrix is the inverse matrix. The interpretation asked for by the exercise is not formalized.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace PlanarRigidTransform

/-- **MLS Exercise 11(d), p. 76, spatial velocity:** for a curve `g` in `SE(2)` whose homogeneous
matrix has the entrywise derivative `D` at `t`, `ġ g⁻¹ = D g(t)⁻¹` is a planar twist
`[[ω̂ˢ, vˢ], [0, 0]]`. -/
theorem exists_twistHat_eq_mul_inv {g : ℝ → PlanarRigidTransform} {D : Matrix (Fin 3) (Fin 3) ℝ}
    {t : ℝ} (hD : ∀ i j, HasDerivAt (fun s => (g s).toHomogeneous i j) (D i j) t) :
    ∃ (v : Vec2) (ω : ℝ), D * (g t)⁻¹.toHomogeneous = twistHat v ω := by
  have d00 : HasDerivAt (fun s => (g s).rotation.val 0 0) (D 0 0) t := hD 0 0
  have d01 : HasDerivAt (fun s => (g s).rotation.val 0 1) (D 0 1) t := hD 0 1
  have d10 : HasDerivAt (fun s => (g s).rotation.val 1 0) (D 1 0) t := hD 1 0
  have d11 : HasDerivAt (fun s => (g s).rotation.val 1 1) (D 1 1) t := hD 1 1
  have z0 : D 2 0 = 0 := (hD 2 0).unique (hasDerivAt_const t (0 : ℝ))
  have z1 : D 2 1 = 0 := (hD 2 1).unique (hasDerivAt_const t (0 : ℝ))
  have z2 : D 2 2 = 0 := (hD 2 2).unique (hasDerivAt_const t (1 : ℝ))
  have so : ∀ s, (g s).rotation.val 0 0 = (g s).rotation.val 1 1 ∧
      (g s).rotation.val 0 1 = -(g s).rotation.val 1 0 ∧
      (g s).rotation.val 0 0 ^ 2 + (g s).rotation.val 0 1 ^ 2 = 1 :=
    fun s => Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp (g s).rotation.2
  have const : ∀ {F : ℝ → ℝ} {c F' : ℝ}, (∀ s, F s = c) → HasDerivAt F F' t → F' = 0 := by
    intro F c F' hF h
    rw [show F = fun _ => c from funext hF] at h
    exact h.unique (hasDerivAt_const t c)
  have e1 := const (fun s => (so s).2.2) ((d00.pow 2).add (d01.pow 2))
  have e2 := const (c := 1) (fun s => by
      obtain ⟨h1, h2, h3⟩ := so s
      show (g s).rotation.val 1 0 ^ 2 + (g s).rotation.val 1 1 ^ 2 = 1
      rw [← h1]; rw [h2, neg_sq] at h3; linarith) ((d10.pow 2).add (d11.pow 2))
  have e3 := const (c := 0) (fun s => by
      obtain ⟨h1, h2, h3⟩ := so s
      show (g s).rotation.val 0 0 * (g s).rotation.val 1 0 +
        (g s).rotation.val 0 1 * (g s).rotation.val 1 1 = 0
      rw [h2, ← h1]; ring) ((d00.mul d10).add (d01.mul d11))
  simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one] at e1 e2
  refine ⟨WithLp.toLp 2 ![(D * (g t)⁻¹.toHomogeneous) 0 2, (D * (g t)⁻¹.toHomogeneous) 1 2],
    D 1 0 * (g t).rotation.val 0 0 + D 1 1 * (g t).rotation.val 0 1, ?_⟩
  have hinv : ((g t).rotation⁻¹).val = (g t).rotation.valᵀ := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toHomogeneous, twistHat, Matrix.mul_apply, Fin.sum_univ_three, hinv, z0, z1, z2] <;>
    first
      | ring1
      | linear_combination e1 / 2
      | linear_combination e2 / 2
      | linear_combination e3

/-- **MLS Exercise 11(d), p. 76, body velocity:** for a curve `g` in `SE(2)` whose homogeneous
matrix has the entrywise derivative `D` at `t`, `g⁻¹ ġ = g(t)⁻¹ D` is a planar twist
`[[ω̂ᵇ, vᵇ], [0, 0]]`. -/
theorem exists_twistHat_eq_inv_mul {g : ℝ → PlanarRigidTransform} {D : Matrix (Fin 3) (Fin 3) ℝ}
    {t : ℝ} (hD : ∀ i j, HasDerivAt (fun s => (g s).toHomogeneous i j) (D i j) t) :
    ∃ (v : Vec2) (ω : ℝ), (g t)⁻¹.toHomogeneous * D = twistHat v ω := by
  have d00 : HasDerivAt (fun s => (g s).rotation.val 0 0) (D 0 0) t := hD 0 0
  have d01 : HasDerivAt (fun s => (g s).rotation.val 0 1) (D 0 1) t := hD 0 1
  have d10 : HasDerivAt (fun s => (g s).rotation.val 1 0) (D 1 0) t := hD 1 0
  have d11 : HasDerivAt (fun s => (g s).rotation.val 1 1) (D 1 1) t := hD 1 1
  have z0 : D 2 0 = 0 := (hD 2 0).unique (hasDerivAt_const t (0 : ℝ))
  have z1 : D 2 1 = 0 := (hD 2 1).unique (hasDerivAt_const t (0 : ℝ))
  have z2 : D 2 2 = 0 := (hD 2 2).unique (hasDerivAt_const t (1 : ℝ))
  have so : ∀ s, (g s).rotation.val 0 0 = (g s).rotation.val 1 1 ∧
      (g s).rotation.val 0 1 = -(g s).rotation.val 1 0 ∧
      (g s).rotation.val 0 0 ^ 2 + (g s).rotation.val 0 1 ^ 2 = 1 :=
    fun s => Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp (g s).rotation.2
  have const : ∀ {F : ℝ → ℝ} {c F' : ℝ}, (∀ s, F s = c) → HasDerivAt F F' t → F' = 0 := by
    intro F c F' hF h
    rw [show F = fun _ => c from funext hF] at h
    exact h.unique (hasDerivAt_const t c)
  have e1 := const (c := 1) (fun s => by
      obtain ⟨h1, h2, h3⟩ := so s
      show (g s).rotation.val 0 0 ^ 2 + (g s).rotation.val 1 0 ^ 2 = 1
      rw [h2, neg_sq] at h3; linarith) ((d00.pow 2).add (d10.pow 2))
  have e2 := const (c := 1) (fun s => by
      obtain ⟨h1, h2, h3⟩ := so s
      show (g s).rotation.val 0 1 ^ 2 + (g s).rotation.val 1 1 ^ 2 = 1
      rw [← h1]; linarith) ((d01.pow 2).add (d11.pow 2))
  have e3 := const (c := 0) (fun s => by
      obtain ⟨h1, h2, h3⟩ := so s
      show (g s).rotation.val 0 0 * (g s).rotation.val 0 1 +
        (g s).rotation.val 1 0 * (g s).rotation.val 1 1 = 0
      rw [h2, ← h1]; ring) ((d00.mul d01).add (d10.mul d11))
  simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one] at e1 e2
  refine ⟨WithLp.toLp 2 ![((g t)⁻¹.toHomogeneous * D) 0 2, ((g t)⁻¹.toHomogeneous * D) 1 2],
    (g t).rotation.val 0 1 * D 0 0 + (g t).rotation.val 1 1 * D 1 0, ?_⟩
  have hinv : ((g t).rotation⁻¹).val = (g t).rotation.valᵀ := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toHomogeneous, twistHat, Matrix.mul_apply, Fin.sum_univ_three, hinv, z0, z1, z2] <;>
    first
      | ring1
      | linear_combination e1 / 2
      | linear_combination e2 / 2
      | linear_combination e3

end PlanarRigidTransform
end RoboLean
