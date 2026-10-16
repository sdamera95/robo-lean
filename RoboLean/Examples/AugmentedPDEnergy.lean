import RoboLean.Examples.PlanarTwoLinkControl

/-!
# No single `ε` makes the skewed energy of Proposition 4.10 a global Lyapunov function (MLS p. 195)

**What MLS states.** Proposition 4.10 (p. 194): "The control law (4.53) applied to the system (4.47)
results in exponential trajectory tracking if `K_v, K_p > 0`." The proof takes
`V = ½ ėᵀ M(θ) ė + ½ eᵀ K_p e + ε eᵀ M(θ) ė` and states (p. 195): "Choosing `ε > 0` sufficiently
small insures that `V̇` is negative definite (see Exercise 11) and hence the system is exponentially
stable using Theorem 4.5." Exercise 11 (p. 209) is the matrix fact that `[[εA, εB], [εBᵀ, C + εD]]`
is positive definite for `A`, `C` symmetric positive definite and `ε` small, for fixed matrices
`A, B, C, D`. In `V̇` the cross term `ε eᵀ(−K_v + Ṁ − C)ė` (corrected from the printed `½Ṁ`)
contains `C(θ, θ̇)`, which grows linearly with `θ̇`, so the off-diagonal block is not fixed.

**Formalized here, an instance (a check on one model, not a general theorem).** For the planar
two-link arm of MLS Figure 4.4 (p. 164) with `m₂ l₁ r₂ > 0`, the set point `θ_d ≡ 0` and
`K_p = K_v = I`, for every `ε > 0` there is a state `(e, ė)` at which the derivative of `V` along
the closed loop (`ManipulatorModel.augmentedEnergyRate`, the corrected `V̇`, which is the actual
derivative along every motion satisfying (4.54) by `ManipulatorModel.hasDerivAt_augmentedEnergy`) is
positive (`planarTwoLinkModel_exists_augmentedEnergyRate_pos`). So no single `ε` makes `V̇` negative
definite on the whole state space: the `ε` of MLS's argument must shrink as the region of initial
errors grows, which is the semiglobal form proved in `Control/AugmentedPD`. The state used has
`e = (0, E)`, `ė = ((1 + ε)E, 0)` with `sin E = −1`, `cos E = 0` and `E ≥ (2 + ε|a|)/(εβ)`, where
`β = m₂ l₁ r₂` and `a` is the constant of `M₁₁` in (4.10). Whether the augmented PD law gives global
exponential tracking by another Lyapunov function is not decided here.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean.Examples

/-- **For every `ε > 0` the skewed energy of MLS Proposition 4.10 (p. 195) increases somewhere along
the closed loop (4.54) of the planar two-link arm (MLS Figure 4.4, p. 164).** With `m₂ l₁ r₂ > 0`,
any inertia data, gravity data and joint forces, the set point `θ_d ≡ 0` (so `θ = e`, `θ̇ = ė`) and
`K_p = K_v = I`, for every `ε > 0` there are `e`, `ė` with
`−ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε eᵀ(−K_v + Ṁ − C)ė > 0` at `θ = e`, `θ̇ = ė`
(`ManipulatorModel.augmentedEnergyRate`). A counterexample instance: one `ε` does not serve every
initial error. -/
theorem planarTwoLinkModel_exists_augmentedEnergyRate_pos {m₁ m₂ r₁ r₂ l₁ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (hβ : 0 < m₂ * l₁ * r₂) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e w : Fin 2 → ℝ,
      0 < (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).augmentedEnergyRate 1 1 ε e w e w := by
  set β := m₂ * l₁ * r₂ with hβdef
  set a := I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2) with hadef
  obtain ⟨k, hk⟩ := exists_nat_gt ((2 + ε * |a|) / (ε * β) + Real.pi / 2)
  set E : ℝ := -(Real.pi / 2) + k * (2 * Real.pi) with hEdef
  have hsin : Real.sin E = -1 := by
    rw [hEdef, Real.sin_add_nat_mul_two_pi, Real.sin_neg, Real.sin_pi_div_two]
  have hcos : Real.cos E = 0 := by
    rw [hEdef, Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_pi_div_two]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hk1 : (1 : ℝ) ≤ k := by
    have h0 : 0 < (2 + ε * |a|) / (ε * β) := by positivity
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at this)
  have hEbig : (2 + ε * |a|) / (ε * β) < E := by
    have h3 := Real.two_le_pi
    have h4 : (2 * Real.pi - 1) * 1 ≤ (2 * Real.pi - 1) * k :=
      mul_le_mul_of_nonneg_left hk1 (by linarith)
    rw [hEdef]
    linarith
  have hE0 : 0 < E := lt_of_le_of_lt (by positivity) hEbig
  have hεβE : 2 + ε * |a| ≤ ε * β * E := by
    rw [div_lt_iff₀ (by positivity)] at hEbig
    linarith
  set S : ℝ := (1 + ε) * E with hSdef
  refine ⟨![0, E], ![S, 0], ?_⟩
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hrate : (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).augmentedEnergyRate 1 1 ε
      ![0, E] ![S, 0] ![0, E] ![S, 0] = -S ^ 2 + ε * a * S ^ 2 - ε * E ^ 2 + ε * β * E * S ^ 2 := by
    simp only [ManipulatorModel.augmentedEnergyRate]
    rw [add_sub_assoc (-1 : Matrix (Fin 2) (Fin 2) ℝ), ManipulatorModel.Mdot_sub_C _ hsymm,
      planarTwoLinkModel_C, planarTwoLinkModel_M, planarTwoLinkArm_massMatrix]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hsin, hcos]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.transpose_apply]
    ring
  rw [hrate]
  have hεa : -(ε * |a|) ≤ ε * a := by
    have := neg_abs_le a
    nlinarith
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hcoef : 1 ≤ -1 + ε * a + ε * β * E := by linarith
  have h1 : S ^ 2 ≤ -S ^ 2 + ε * a * S ^ 2 + ε * β * E * S ^ 2 := by nlinarith
  have h2 : ε * E ^ 2 < S ^ 2 := by
    have h5 : S ^ 2 - ε * E ^ 2 = (1 + ε + ε ^ 2) * E ^ 2 := by
      rw [hSdef]
      ring
    have h6 : 0 < (1 + ε + ε ^ 2) * E ^ 2 := by positivity
    linarith
  linarith

end RoboLean.Examples
