import RoboLean.Examples.ElbowManipulator
import RoboLean.Examples.PlanarKinematicsIsotropic
import RoboLean.Kinematics.MapJacobian

/-!
# Isotropic points of the elbow manipulator without a wrist (MLS Exercise 13(b)–(c))

MLS Chapter 3, Exercise 13, printed p. 150: "A point in a manipulator's workspace is said to be
isotropic if the condition number of the Jacobian is 1. … (b) Compute the isotropic points for an
elbow manipulator without a wrist. (c) Discuss why isotropic points are useful for tasks which involve
applying forces against the environment."

Reading (the same as for part (a), `isIsotropic_planarTwoLinkPositionJacobian_iff`): the elbow
manipulator without a wrist is the first three joints of Example 3.2 (pp. 89–90), and the Jacobian is
the `3 × 3` Jacobian of the position of the wrist centre, here the derivative of the printed position
`p(θ) = (−sin θ₁ ρ, cos θ₁ ρ, l₀ − l₁ sin θ₂ − l₂ sin(θ₂ + θ₃))`, `ρ = l₁ cos θ₂ + l₂ cos(θ₂ + θ₃)`
(`elbowManipulator_fk_translation`); condition number `1` is `JᵀJ = σ²I` with `σ ≠ 0`. Result: for
positive lengths the isotropic configurations are exactly those with `l₁² = 2l₂²`,
`cos θ₃ = −l₂/l₁` and `ρ² = l₂²`, and the isotropic points form the horizontal circle of radius `l₂`
about the shoulder `(0, 0, l₀)`. For part (c) the formal content recorded is the force reading: at an
isotropic configuration the joint torques `Jᵀf` balancing an end-effector force `f` have
`‖Jᵀf‖ = |σ| ‖f‖` for every `f`, the same gain in every direction. Lean `θ 0, θ 1, θ 2` are the
book's `θ₁, θ₂, θ₃`.
-/

noncomputable section

open Real Matrix

namespace RoboLean.Examples

open MapJacobian

/-- Isotropy of a square Jacobian of any size (MLS Exercise 13, p. 150, "condition number 1"):
`JᵀJ = σ² I` for some `σ ≠ 0`. For `2 × 2` matrices this is `IsIsotropic`. -/
def IsIsotropicMatrix {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ σ : ℝ, σ ≠ 0 ∧ Jᵀ * J = (σ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The position of the wrist centre of the elbow manipulator without a wrist (MLS Example 3.2,
pp. 90–91, the position `p(θ)` of the elbow manipulator, which does not depend on the wrist angles),
as a map of the first three joint angles:
`(−sin θ₁ ρ, cos θ₁ ρ, l₀ − l₁ sin θ₂ − l₂ sin(θ₂ + θ₃))`, `ρ = l₁ cos θ₂ + l₂ cos(θ₂ + θ₃)`. -/
def elbowArmPosition (l₀ l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-Real.sin (θ 0) * (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)),
    Real.cos (θ 0) * (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)),
    l₀ - l₁ * Real.sin (θ 1) - l₂ * Real.sin (θ 1 + θ 2)]

/-- The elbow manipulator's tool position (MLS Example 3.2, pp. 90–91) is `elbowArmPosition` of its
first three joint angles. -/
theorem elbowManipulator_fk_translation_eq_elbowArmPosition (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    WithLp.ofLp ((elbowManipulator l₀ l₁ l₂).fk θ).translation =
      elbowArmPosition l₀ l₁ l₂ ![θ 0, θ 1, θ 2] := by
  rw [elbowManipulator_fk_translation]
  funext i
  fin_cases i <;> simp [vec, elbowArmPosition]

/-- The position Jacobian of the elbow manipulator without a wrist (MLS Exercise 13(b), p. 150): the
columns are `∂p/∂θ₁ = (−cos θ₁ ρ, −sin θ₁ ρ, 0)`, `∂p/∂θ₂ = (sin θ₁ σ₂, −cos θ₁ σ₂, −ρ)` and
`∂p/∂θ₃ = (sin θ₁ l₂ sin(θ₂ + θ₃), −cos θ₁ l₂ sin(θ₂ + θ₃), −l₂ cos(θ₂ + θ₃))`, with
`σ₂ = l₁ sin θ₂ + l₂ sin(θ₂ + θ₃)`. -/
def elbowArmPositionJacobian (l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-Real.cos (θ 0) * (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)),
      Real.sin (θ 0) * (l₁ * Real.sin (θ 1) + l₂ * Real.sin (θ 1 + θ 2)),
      Real.sin (θ 0) * (l₂ * Real.sin (θ 1 + θ 2));
    -Real.sin (θ 0) * (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)),
      -Real.cos (θ 0) * (l₁ * Real.sin (θ 1) + l₂ * Real.sin (θ 1 + θ 2)),
      -Real.cos (θ 0) * (l₂ * Real.sin (θ 1 + θ 2));
    0, -(l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)), -(l₂ * Real.cos (θ 1 + θ 2))]

/-- The explicit matrix `elbowArmPositionJacobian` is the Jacobian (matrix of the derivative) of the
position map `elbowArmPosition` (MLS p. 150 with Example 3.2), for all real lengths and angles. -/
theorem jac_elbowArmPosition (l₀ l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) :
    jac (elbowArmPosition l₀ l₁ l₂) θ = elbowArmPositionJacobian l₁ l₂ θ := by
  have p0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 θ
  have p1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 θ
  have p2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 θ
  have hρ := (p1.cos.const_mul l₁).add ((p1.add p2).cos.const_mul l₂)
  have h0 := p0.sin.neg.mul hρ
  have h1 := p0.cos.mul hρ
  have h2 := ((hasFDerivAt_const l₀ θ).sub (p1.sin.const_mul l₁)).sub ((p1.add p2).sin.const_mul l₂)
  set L : Fin 3 → ((Fin 3 → ℝ) →L[ℝ] ℝ) := fun i =>
    ∑ j, elbowArmPositionJacobian l₁ l₂ θ i j •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j)
  have hL : ∀ i, HasFDerivAt (fun x => elbowArmPosition l₀ l₁ l₂ x i) (L i) θ := by
    intro i
    fin_cases i
    · convert h0 using 1
      · funext x
        simp [elbowArmPosition]
      · ext v
        simp [L, elbowArmPositionJacobian, Fin.sum_univ_three]
        ring
    · convert h1 using 1
      · funext x
        simp [elbowArmPosition]
      · ext v
        simp [L, elbowArmPositionJacobian, Fin.sum_univ_three]
        ring
    · convert h2 using 1
      · funext x
        simp [elbowArmPosition]
      · ext v
        simp [L, elbowArmPositionJacobian, Fin.sum_univ_three]
        ring
  ext i j
  rw [jac_apply_of_hasFDerivAt hL]
  simp [L, Pi.single_apply]

private theorem cos_diff_aux' (a b : ℝ) : sin a * sin (a + b) + cos a * cos (a + b) = cos b := by
  have := cos_sub (a + b) a
  rw [add_sub_cancel_left] at this
  rw [this]
  ring

private theorem gram_elbowArm (l₁ l₂ : ℝ) (θ : Fin 3 → ℝ) :
    (elbowArmPositionJacobian l₁ l₂ θ)ᵀ * elbowArmPositionJacobian l₁ l₂ θ =
      !![(l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) ^ 2, 0, 0;
        0, l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos (θ 2), l₂ * (l₁ * cos (θ 2) + l₂);
        0, l₂ * (l₁ * cos (θ 2) + l₂), l₂ ^ 2] := by
  have hc := cos_diff_aux' (θ 1) (θ 2)
  have h0 := sin_sq_add_cos_sq (θ 0)
  have h1 := sin_sq_add_cos_sq (θ 1)
  have h2 := sin_sq_add_cos_sq (θ 1 + θ 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elbowArmPositionJacobian, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) ^ 2 * h0
  · ring
  · ring
  · ring
  · linear_combination (l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2)) ^ 2 * h0 + l₁ ^ 2 * h1 +
      l₂ ^ 2 * h2 + 2 * l₁ * l₂ * hc
  · linear_combination l₂ * (l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2)) * sin (θ 1 + θ 2) * h0 +
      l₁ * l₂ * hc + l₂ ^ 2 * h2
  · ring
  · linear_combination l₂ * (l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2)) * sin (θ 1 + θ 2) * h0 +
      l₁ * l₂ * hc + l₂ ^ 2 * h2
  · linear_combination l₂ ^ 2 * sin (θ 1 + θ 2) ^ 2 * h0 + l₂ ^ 2 * h2

/-- **MLS Exercise 13(b), p. 150: isotropic configurations of the elbow manipulator without a
wrist.** For positive link lengths the position Jacobian at `θ` is isotropic exactly when
`l₁² = 2l₂²`, `cos θ₃ = −l₂/l₁` and `(l₁ cos θ₂ + l₂ cos(θ₂ + θ₃))² = l₂²`. -/
theorem isIsotropicMatrix_elbowArmPositionJacobian_iff {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (θ : Fin 3 → ℝ) :
    IsIsotropicMatrix (elbowArmPositionJacobian l₁ l₂ θ) ↔
      l₁ ^ 2 = 2 * l₂ ^ 2 ∧ Real.cos (θ 2) = -l₂ / l₁ ∧
        (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)) ^ 2 = l₂ ^ 2 := by
  rw [IsIsotropicMatrix, gram_elbowArm]
  constructor
  · rintro ⟨σ, -, hσ⟩
    have e00 := congrFun (congrFun hσ 0) 0
    have e12 := congrFun (congrFun hσ 1) 2
    have e11 := congrFun (congrFun hσ 1) 1
    have e22 := congrFun (congrFun hσ 2) 2
    simp at e00 e12 e11 e22
    have hc : l₁ * cos (θ 2) + l₂ = 0 := by
      rcases e12 with h | h
      · exact absurd h hl₂.ne'
      · exact h
    have hcos : cos (θ 2) = -l₂ / l₁ := by
      field_simp
      linarith
    refine ⟨?_, hcos, by rw [e00, e22]⟩
    have : l₁ * (l₁ * cos (θ 2)) = -(l₁ * l₂) := by
      rw [show l₁ * cos (θ 2) = -l₂ by linarith]; ring
    nlinarith [e11, e22, this]
  · rintro ⟨hl, hcos, hρ⟩
    refine ⟨l₂, hl₂.ne', ?_⟩
    have hc : l₁ * cos (θ 2) = -l₂ := by
      rw [hcos]; field_simp
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hρ]
    · nlinarith [hc]
    · right; linarith
    · right; linarith

/-- **MLS Exercise 13(b), p. 150: the isotropic points of the elbow manipulator without a wrist lie
on the horizontal circle of radius `l₂` about the shoulder `(0, 0, l₀)`**: at an isotropic
configuration the wrist centre has height `l₀` and horizontal distance `l₂` from the first axis. -/
theorem elbowArmPosition_of_isIsotropicMatrix {l₀ l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    {θ : Fin 3 → ℝ} (h : IsIsotropicMatrix (elbowArmPositionJacobian l₁ l₂ θ)) :
    elbowArmPosition l₀ l₁ l₂ θ 2 = l₀ ∧
      elbowArmPosition l₀ l₁ l₂ θ 0 ^ 2 + elbowArmPosition l₀ l₁ l₂ θ 1 ^ 2 = l₂ ^ 2 := by
  obtain ⟨hl, hcos, hρ⟩ := (isIsotropicMatrix_elbowArmPositionJacobian_iff hl₁ hl₂ θ).mp h
  have hc : l₁ * cos (θ 2) = -l₂ := by
    rw [hcos]; field_simp
  have hdiff := cos_diff_aux' (θ 1) (θ 2)
  have h1 := sin_sq_add_cos_sq (θ 1)
  have h2 := sin_sq_add_cos_sq (θ 1 + θ 2)
  have hsum : (l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2)) ^ 2 +
      (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) ^ 2 = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos (θ 2) := by
    linear_combination l₁ ^ 2 * h1 + l₂ ^ 2 * h2 + 2 * l₁ * l₂ * hdiff
  have hzero : (l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2)) ^ 2 = 0 := by
    nlinarith [hsum, hρ, hl, hc]
  have hz : l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hzero
  constructor
  · simp only [elbowArmPosition, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    linarith
  · simp only [elbowArmPosition, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 := sin_sq_add_cos_sq (θ 0)
    linear_combination (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) ^ 2 * h0 + hρ

/-- **MLS Exercise 13(c), p. 150, the force reading: at an isotropic configuration every end-effector
force is transmitted to the joints with the same gain.** If `JᵀJ = σ²I`, `σ ≠ 0`, for a square `J`,
then the joint torques `τ = Jᵀf` (the statics `τ = Jᵀf` of MLS p. 121) satisfy
`τ · τ = σ² (f · f)` for every force `f`. -/
theorem dotProduct_transpose_mulVec_of_isIsotropicMatrix {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ}
    (h : IsIsotropicMatrix J) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ f : Fin n → ℝ, (Jᵀ *ᵥ f) ⬝ᵥ (Jᵀ *ᵥ f) = σ ^ 2 * (f ⬝ᵥ f) := by
  obtain ⟨σ, hσ, hJ⟩ := h
  refine ⟨σ, hσ, fun f => ?_⟩
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hleft : ((σ ^ 2)⁻¹ • Jᵀ) * J = 1 := by
    rw [Matrix.smul_mul, hJ, smul_smul, inv_mul_cancel₀ hσ2, one_smul]
  have hright : J * ((σ ^ 2)⁻¹ • Jᵀ) = 1 := mul_eq_one_comm.mp hleft
  have hJJ : J * Jᵀ = (σ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.mul_smul] at hright
    rw [← hright, smul_smul, mul_inv_cancel₀ hσ2, one_smul]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJJ,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul]

end RoboLean.Examples
