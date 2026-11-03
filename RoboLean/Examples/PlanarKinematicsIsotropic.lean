import RoboLean.Examples.PlanarTwoLinkSingularity

/-!
# Isotropic points of the planar two-link arm (MLS Exercise 13(a))

MLS Exercise 13, printed p. 150: "A point in a manipulator's workspace is said to be isotropic if
the condition number of the Jacobian is 1. (a) Calculate conditions under which a two-link planar
manipulator has isotropic points and sketch their location in the plane."

Reading used here (a choice; the exercise does not say which Jacobian): the Jacobian is the
`2 × 2` Jacobian of the tool position, the library's `planarTwoLinkPositionJacobian` of the planar
two-link arm (zero configuration along `+y`; its `JᵀJ` is the same as for the zero configuration
along `+x` of Figure 3.7a, p. 97), and condition number `1` is stated as `JᵀJ = σ² I` with
`σ ≠ 0` (equal nonzero singular values). Result: for positive link lengths the arm has an
isotropic configuration exactly when `l₁² = 2 l₂²`, and the isotropic configurations are then
those with `cos θ₂ = -l₂/l₁ = -1/√2`; the isotropic points lie on the circle of radius `l₂` about
the base. Parts (b) and (c) are not treated.
-/

noncomputable section

open Real Matrix

namespace RoboLean

namespace Examples

/-- Isotropy of a square Jacobian (MLS Exercise 13, p. 150, "condition number 1"), stated as
`JᵀJ = σ² I` for some `σ ≠ 0`: all singular values equal and nonzero. -/
def IsIsotropic (J : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ σ : ℝ, σ ≠ 0 ∧ Jᵀ * J = (σ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

private theorem cos_diff_aux (a b : ℝ) : sin a * sin (a + b) + cos a * cos (a + b) = cos b := by
  have := cos_sub (a + b) a
  rw [add_sub_cancel_left] at this
  rw [this]
  ring

private theorem gram_eq (l₁ l₂ : ℝ) (θ : Fin 2 → ℝ) :
    (planarTwoLinkPositionJacobian l₁ l₂ θ)ᵀ * planarTwoLinkPositionJacobian l₁ l₂ θ =
      !![l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos (θ 1), l₂ * (l₁ * cos (θ 1) + l₂);
        l₂ * (l₁ * cos (θ 1) + l₂), l₂ ^ 2] := by
  have hc := cos_diff_aux (θ 0) (θ 1)
  have h0 := sin_sq_add_cos_sq (θ 0)
  have h1 := sin_sq_add_cos_sq (θ 0 + θ 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarTwoLinkPositionJacobian, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination l₁ ^ 2 * h0 + l₂ ^ 2 * h1 + 2 * l₁ * l₂ * hc
  · linear_combination l₁ * l₂ * hc + l₂ ^ 2 * h1
  · linear_combination l₁ * l₂ * hc + l₂ ^ 2 * h1
  · linear_combination l₂ ^ 2 * h1

/-- **MLS Exercise 13(a), p. 150: isotropic configurations of the planar two-link arm.** For
positive link lengths, the position Jacobian at `θ` is isotropic exactly when `l₁² = 2 l₂²` and
`cos θ₂ = -l₂ / l₁`. -/
theorem isIsotropic_planarTwoLinkPositionJacobian_iff {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (θ : Fin 2 → ℝ) :
    IsIsotropic (planarTwoLinkPositionJacobian l₁ l₂ θ) ↔
      l₁ ^ 2 = 2 * l₂ ^ 2 ∧ cos (θ 1) = -l₂ / l₁ := by
  rw [IsIsotropic, gram_eq]
  constructor
  · rintro ⟨σ, -, hσ⟩
    have e00 := congrFun (congrFun hσ 0) 0
    have e01 := congrFun (congrFun hσ 0) 1
    have e11 := congrFun (congrFun hσ 1) 1
    simp at e00 e01 e11
    have hc : l₁ * cos (θ 1) + l₂ = 0 := by
      rcases e01 with h | h
      · exact absurd h hl₂.ne'
      · exact h
    have hcos : cos (θ 1) = -l₂ / l₁ := by
      field_simp
      linarith
    refine ⟨?_, hcos⟩
    have : l₁ * (l₁ * cos (θ 1)) = -(l₁ * l₂) := by rw [show l₁ * cos (θ 1) = -l₂ by linarith]; ring
    nlinarith [e00, e11, this]
  · rintro ⟨hl, hcos⟩
    refine ⟨l₂, hl₂.ne', ?_⟩
    have hc : l₁ * cos (θ 1) = -l₂ := by
      rw [hcos]
      field_simp
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · nlinarith [hc, hl]
    · exact Or.inr (by linarith)
    · exact Or.inr (by linarith)

/-- **MLS Exercise 13(a), p. 150: location of the isotropic points.** At an isotropic
configuration of the planar two-link arm with positive link lengths the tool lies at distance
`l₂` from the base. -/
theorem norm_planarTwoLinkPosition_of_isIsotropic {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (θ : Fin 2 → ℝ) (h : IsIsotropic (planarTwoLinkPositionJacobian l₁ l₂ θ)) :
    ‖planarTwoLinkPosition l₁ l₂ θ‖ = l₂ := by
  obtain ⟨hl, hcos⟩ := (isIsotropic_planarTwoLinkPositionJacobian_iff hl₁ hl₂ θ).mp h
  have hc : l₁ * cos (θ 1) = -l₂ := by
    rw [hcos]
    field_simp
  have hsq := planarTwoLinkPosition_norm_sq l₁ l₂ θ
  have h2 : ‖planarTwoLinkPosition l₁ l₂ θ‖ ^ 2 = l₂ ^ 2 := by
    rw [hsq]
    nlinarith [hc, hl]
  exact (pow_left_inj₀ (norm_nonneg _) hl₂.le two_ne_zero).mp h2

end Examples

end RoboLean
