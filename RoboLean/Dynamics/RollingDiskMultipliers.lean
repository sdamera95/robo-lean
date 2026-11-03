import RoboLean.Examples.ConstrainedDynamics

/-!
# The constraint forces of the rolling penny: Chapter 6 Exercise 3

MLS Chapter 6, Exercise 3, printed p. 314: "Calculate the constraint forces for the rolling penny
described in Example 6.2." Example 6.2 (pp. 272–274) is the disk `q = (x, y, θ, φ)` rolling without
slipping, with the constraints (6.10) `ẋ − ρ cos θ φ̇ = 0`, `ẏ − ρ sin θ φ̇ = 0`, the Lagrangian
`½ m (ẋ² + ẏ²) + ½ I₁ θ̇² + ½ I₂ φ̇²` and the wheel torques `(τ_θ, τ_φ)`.

**Formalized.** In the multiplier form (6.4) with the library's sign (`Constrained.MultiplierEquationsAt`:
`d/dt ∂L/∂q̇ − ∂L/∂q = Υ − Aᵀ λ`), along a motion that satisfies the rolling constraint near `t`:
the multiplier equations hold with `λ` exactly when the reduced equations (6.14) hold and
`λ₁ = −m ρ (cos θ φ̈ − sin θ θ̇ φ̇)`, `λ₂ = −m ρ (sin θ φ̈ + cos θ θ̇ φ̇)`, minus the mass times the
acceleration of the center (`rollingDisk_multiplierEquationsAt_iff`); with `I₂ + m ρ² ≠ 0` the
constraint forces in terms of the torques and the state are
`λ₁ = −m ρ (cos θ τ_φ / (I₂ + m ρ²) − sin θ θ̇ φ̇)`, `λ₂ = −m ρ (sin θ τ_φ / (I₂ + m ρ²) + cos θ θ̇ φ̇)`
(`rollingDisk_constraintForce`). The constraint force on the generalized coordinates is `−Aᵀ λ`: on
`(x, y)` it is `(m ẍ, m ÿ)`, the force the ground exerts on the disk.

Lean indices `0, 1, 2, 3` are the book's `x, y, θ, φ`. Nothing here concerns a physical coin.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Examples

private theorem coriolisMatrix_partials_zero' (v : Fin 4 → ℝ) :
    Christoffel.coriolisMatrix
        (Christoffel.partials fun _ _ => (0 : (Fin 4 → ℝ) →L[ℝ] ℝ)) v = 0 := by
  ext i j
  simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials]

/-- **MLS Chapter 6, Exercise 3, p. 314, with Example 6.2, pp. 272–274: the constraint forces of the
rolling penny.** Along a motion `q` with velocity `q'` near `t` and acceleration `q''` at `t` that
satisfies the rolling constraint (6.10) near `t`, the multiplier equations (6.4) (library sign:
`d/dt ∂L/∂q̇ − ∂L/∂q = Υ − Aᵀ λ`) hold with `λ` exactly when `I₁ θ̈ = τ_θ`, `(I₂ + m ρ²) φ̈ = τ_φ`
and `λ = (−m ρ (cos θ φ̈ − sin θ θ̇ φ̇), −m ρ (sin θ φ̈ + cos θ θ̇ φ̇))`. -/
theorem rollingDisk_multiplierEquationsAt_iff {m I₁ I₂ ρ τθ τφ : ℝ} {q q' : ℝ → Fin 4 → ℝ}
    {q'' : Fin 4 → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, Constrained.PfaffianAt (rollingDiskConstraint ρ) (q s) (q' s))
    (μ : Fin 2 → ℝ) :
    Constrained.MultiplierEquationsAt (rollingDiskLagrangian m I₁ I₂) (rollingDiskConstraint ρ) q
        (rollingDiskForce τθ τφ) μ t ↔
      I₁ * q'' 2 = τθ ∧ (I₂ + m * ρ ^ 2) * q'' 3 = τφ ∧
        μ 0 = -(m * ρ * (Real.cos (q t 2) * q'' 3 - Real.sin (q t 2) * q' t 2 * q' t 3)) ∧
        μ 1 = -(m * ρ * (Real.sin (q t 2) * q'' 3 + Real.cos (q t 2) * q' t 2 * q' t 3)) := by
  obtain ⟨a0, a1⟩ := rollingDisk_acceleration hq hq' hc
  have hM : ∀ i j, HasFDerivAt (fun x => rollingDiskInertia m I₁ I₂ x i j)
      (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) (q t) := fun _ _ => hasFDerivAt_const _ _
  have hV : HasFDerivAt (fun _ : Fin 4 → ℝ => (0 : ℝ)) (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) (q t) :=
    hasFDerivAt_const _ _
  have hsymm : ∀ x, (rollingDiskInertia m I₁ I₂ x).IsSymm := fun _ => Matrix.isSymm_diagonal _
  have hMq : rollingDiskInertia m I₁ I₂ (q t) *ᵥ q'' =
      ![m * q'' 0, m * q'' 1, I₁ * q'' 2, I₂ * q'' 3] := by
    funext i
    fin_cases i <;> simp [rollingDiskInertia, Matrix.mulVec_diagonal]
  have hA : (rollingDiskConstraint ρ (q t))ᵀ *ᵥ μ =
      ![μ 0, μ 1, 0, -(ρ * Real.cos (q t 2)) * μ 0 + -(ρ * Real.sin (q t 2)) * μ 1] := by
    funext i
    fin_cases i <;> simp [rollingDiskConstraint, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hG : Lagrangian.gradient (0 : (Fin 4 → ℝ) →L[ℝ] ℝ) = 0 := by
    funext i
    simp [Lagrangian.gradient]
  rw [Constrained.MultiplierEquationsAt, rollingDiskLagrangian,
    Lagrangian.lagrangeEquationsAt_mechanical_iff hsymm hM hV hq hq',
    coriolisMatrix_partials_zero', Matrix.zero_mulVec, add_zero, hMq, hA, hG, add_zero]
  simp only [funext_iff, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
  simp [rollingDiskForce]
  rw [a0, a1]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨by linarith, ?_, by linarith, by linarith⟩
    have e0 : μ 0 = -(m * (ρ * Real.cos (q t 2) * q'' 3 - ρ * Real.sin (q t 2) * q' t 2 * q' t 3)) := by
      linarith
    have e1 : μ 1 = -(m * (ρ * Real.sin (q t 2) * q'' 3 + ρ * Real.cos (q t 2) * q' t 2 * q' t 3)) := by
      linarith
    rw [e0, e1] at h3
    linear_combination h3 - m * ρ ^ 2 * q'' 3 * Real.sin_sq_add_cos_sq (q t 2)
  · rintro ⟨h2, h3, h0, h1⟩
    refine ⟨by rw [h0]; ring, by rw [h1]; ring, by linarith, ?_⟩
    rw [h0, h1]
    linear_combination h3 + m * ρ ^ 2 * q'' 3 * Real.sin_sq_add_cos_sq (q t 2)

/-- **MLS Chapter 6, Exercise 3, p. 314: the constraint forces in terms of the torques.** Under the
hypotheses of `rollingDisk_multiplierEquationsAt_iff` and `I₂ + m ρ² ≠ 0`, the multiplier equations
hold with `λ` exactly when `I₁ θ̈ = τ_θ`, `φ̈ = τ_φ / (I₂ + m ρ²)` and
`λ₁ = −m ρ (cos θ τ_φ / (I₂ + m ρ²) − sin θ θ̇ φ̇)`, `λ₂ = −m ρ (sin θ τ_φ / (I₂ + m ρ²) + cos θ θ̇ φ̇)`. -/
theorem rollingDisk_constraintForce {m I₁ I₂ ρ τθ τφ : ℝ} {q q' : ℝ → Fin 4 → ℝ}
    {q'' : Fin 4 → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, Constrained.PfaffianAt (rollingDiskConstraint ρ) (q s) (q' s))
    (hI : I₂ + m * ρ ^ 2 ≠ 0) (μ : Fin 2 → ℝ) :
    Constrained.MultiplierEquationsAt (rollingDiskLagrangian m I₁ I₂) (rollingDiskConstraint ρ) q
        (rollingDiskForce τθ τφ) μ t ↔
      I₁ * q'' 2 = τθ ∧ q'' 3 = τφ / (I₂ + m * ρ ^ 2) ∧
        μ 0 = -(m * ρ * (Real.cos (q t 2) * (τφ / (I₂ + m * ρ ^ 2)) -
          Real.sin (q t 2) * q' t 2 * q' t 3)) ∧
        μ 1 = -(m * ρ * (Real.sin (q t 2) * (τφ / (I₂ + m * ρ ^ 2)) +
          Real.cos (q t 2) * q' t 2 * q' t 3)) := by
  rw [rollingDisk_multiplierEquationsAt_iff hq hq' hc]
  have e : (I₂ + m * ρ ^ 2) * q'' 3 = τφ ↔ q'' 3 = τφ / (I₂ + m * ρ ^ 2) := by
    rw [eq_div_iff hI, mul_comm]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h2' := e.mp h2
    exact ⟨h1, h2', by rw [h3, h2'], by rw [h4, h2']⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, e.mpr h2, by rw [h3, h2], by rw [h4, h2]⟩

end Examples
end RoboLean
