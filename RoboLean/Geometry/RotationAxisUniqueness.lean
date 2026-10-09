import RoboLean.Geometry.RotationParameters

/-!
# Axis ambiguity on the principal interval

These are derived support statements for the ambiguity discussion in MLS
printed pp. 30–31 after equations (2.17)–(2.18) and Theorem 2.6. On `(0, π)`,
the checked generic-axis formula determines the signed unit axis. At `π`, only
the rank-one axis projector is determined, and two unit axes give the same
rotation exactly when they differ by sign. At zero angle, distinct unit axes
represent the identity. No global smooth choice is asserted.
-/

namespace RoboLean.Rotation

open Matrix

/-- The explicit generic-axis expression recovers a unit axis strictly inside
the principal interval, where the sine denominator is nonzero. -/
theorem genericAxis_exp_of_mem_Ioo (ω : Vec3) (hω : ‖ω‖ = 1)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) :
    genericAxis (exp ω θ) = ω := by
  have hangle : principalAngle (exp ω θ) = θ :=
    arccos_trace_exp_of_mem_Icc ω hω θ hθ₀.le hθπ.le
  rw [genericAxis, hangle]
  exact axis_recovery_of_sin_ne_zero ω hω θ
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ))

/-- Equal nondegenerate principal-angle exponentials have the same signed axis. -/
theorem axis_eq_of_exp_eq_of_mem_Ioo (ω η : Vec3) (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (h : exp ω θ = exp η θ) : ω = η := by
  have hω' := genericAxis_exp_of_mem_Ioo ω hω θ hθ₀ hθπ
  have hη' := genericAxis_exp_of_mem_Ioo η hη θ hθ₀ hθπ
  rw [h] at hω'
  exact hω'.symm.trans hη'

/-- Both the angle and the signed axis are unique strictly inside `(0, π)`. -/
theorem axis_angle_eq_of_exp_eq_of_mem_Ioo (ω η : Vec3) (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1)
    (θ φ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (hφ₀ : 0 < φ) (hφπ : φ < Real.pi) (h : exp ω θ = exp η φ) :
    ω = η ∧ θ = φ := by
  have ha := angle_eq_of_exp_eq_of_mem_Icc ω η hω hη θ φ
    hθ₀.le hθπ.le hφ₀.le hφπ.le h
  subst φ
  exact ⟨axis_eq_of_exp_eq_of_mem_Ioo ω η hω hη θ hθ₀ hθπ h, rfl⟩

private theorem outer_eq_imp_eq_or_neg (ω η : Vec3) (hω : ω ≠ 0)
    (h : Vec3.outer ω ω = Vec3.outer η η) : η = ω ∨ η = -ω := by
  classical
  have hex : ∃ i : Fin 3, ω i ≠ 0 := by
    by_contra hn
    apply hω
    ext i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hdiag := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i i) h
  simp only [Vec3.outer_apply] at hdiag
  have hp : (η i - ω i) * (η i + ω i) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with hminus | hplus
  · have heq : η i = ω i := sub_eq_zero.mp hminus
    left
    ext j
    apply mul_left_cancel₀ hi
    have hij := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) h
    simpa only [Vec3.outer_apply, heq] using hij.symm
  · have heq : η i = -ω i := add_eq_zero_iff_eq_neg.mp hplus
    right
    ext j
    change η j = -ω j
    apply mul_left_cancel₀ hi
    have hij := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) h
    simp only [Vec3.outer_apply, heq] at hij
    nlinarith

/-- At a half-turn, equal rotations determine a unit axis only up to sign. -/
theorem exp_pi_eq_iff_axis_eq_or_neg (ω η : Vec3) (hω : ‖ω‖ = 1) (hη : ‖η‖ = 1) :
    exp ω Real.pi = exp η Real.pi ↔ η = ω ∨ η = -ω := by
  constructor
  · intro h
    have hs : (2 : ℝ) • Vec3.outer ω ω = (2 : ℝ) • Vec3.outer η η := by
      rw [← exp_pi_add_one_of_norm_eq_one ω hω,
        ← exp_pi_add_one_of_norm_eq_one η hη, h]
    have ho : Vec3.outer ω ω = Vec3.outer η η := by
      ext i j
      have hij := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hs
      simp only [Matrix.smul_apply, smul_eq_mul] at hij
      linarith
    apply outer_eq_imp_eq_or_neg ω η _ ho
    intro hz
    simp [hz] at hω
  · intro h
    rcases h with h | h
    · rw [h]
    · rw [h]
      have hp := exp_neg_axis_two_pi_sub ω hω Real.pi
      rw [show 2 * Real.pi - Real.pi = Real.pi by ring] at hp
      exact hp.symm

/-- Identity has distinct unit-axis representations; zero-angle axis uniqueness
cannot be inferred from generic principal-angle uniqueness. -/
theorem identity_has_distinct_unit_axes :
    ∃ ω η : Vec3, ‖ω‖ = 1 ∧ ‖η‖ = 1 ∧ ω ≠ η ∧ exp ω 0 = exp η 0 := by
  obtain ⟨ω, hω, _⟩ := exists_unit_axis (1 : Rotation)
  refine ⟨ω, -ω, hω, by simpa using hω, ?_, by simp⟩
  intro h
  have hz : ω = 0 := by
    ext i
    change ω i = 0
    have hi := congrArg (fun v : Vec3 => v i) h
    simp only [PiLp.neg_apply] at hi
    linarith
  simp [hz] at hω

end RoboLean.Rotation
