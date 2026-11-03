import RoboLean.Control.ConverseLyapunovC1

/-!
# A nonlinear instance of the converse of the exponential stability theorem (MLS Theorem 4.5,
p. 183)

**The field.** On `ℝⁿ` with the sup norm, `f(t, x)ᵢ = −2xᵢ + sin xᵢ` (time first, time-invariant),
written `sineDecayField n`. Its derivative is the diagonal map `h ↦ ((−2 + cos yᵢ) hᵢ)ᵢ`
(`sineDecayDeriv n`), continuous and bounded by `3` in operator norm, so every hypothesis of
`exists_lyapunov_of_exponentiallyStable_of_fderiv` other than exponential stability is met; the
origin is exponentially stable (Definition 4.3, pp. 180–181), by the local form of Theorem 4.5
with `V(x) = x ⬝ x`, since `x ⬝ f(x) ≤ −x ⬝ x` (`|sin σ| ≤ |σ|`). Hence the converse Lyapunov
function with all four bounds exists for this nonlinear field (`exists_lyapunov_sineDecayField`).

**Carrier.** `Fin n → ℝ` with the sup norm, as in `Control/ConverseLyapunovGeneral`. This is an
instance of a general theorem; it is not a claim about a physical system.
-/

noncomputable section

open Set Filter Topology Matrix

namespace RoboLean.Examples

/-- **A nonlinear field on `ℝⁿ` (for MLS Theorem 4.5, p. 183):** `f(t, x)ᵢ = −2xᵢ + sin xᵢ`, time
first and ignored. -/
def sineDecayField (n : ℕ) : ℝ → (Fin n → ℝ) → Fin n → ℝ :=
  fun _ x i => -2 * x i + Real.sin (x i)

/-- **The derivative of `sineDecayField` (for MLS Theorem 4.5, p. 183):** at `y` the diagonal map
`h ↦ ((−2 + cos yᵢ) hᵢ)ᵢ`, time first and ignored. -/
def sineDecayDeriv (n : ℕ) : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  fun _ y => ContinuousLinearMap.pi fun i =>
    (-2 + Real.cos (y i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

/-- **`sineDecayField` is differentiable in the state (for MLS Theorem 4.5, p. 183)** with the
derivative `sineDecayDeriv n t y` at every `y`, for every time `t`. -/
theorem hasFDerivAt_sineDecayField (n : ℕ) (t : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (sineDecayField n t) (sineDecayDeriv n t y) y := by
  refine hasFDerivAt_pi.mpr fun i => ?_
  have hp := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i y
  have h := (hp.const_mul (-2)).add ((Real.hasDerivAt_sin (y i)).comp_hasFDerivAt y hp)
  convert h using 1
  · funext v
    simp [sineDecayField]
  · rw [add_smul]

/-- **The derivative of `sineDecayField` is continuous in `(t, y)` on `[0, ∞) × ℝⁿ` (for MLS
Theorem 4.5, p. 183).** -/
theorem continuousOn_sineDecayDeriv (n : ℕ) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) => sineDecayDeriv n p.1 p.2) (Ici 0 ×ˢ univ) := by
  refine Continuous.continuousOn (continuous_clm_apply.mpr fun v => ?_)
  refine continuous_pi fun i => ?_
  simp only [sineDecayDeriv, ContinuousLinearMap.pi_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  fun_prop

/-- **The derivative of `sineDecayField` is bounded (for MLS Theorem 4.5, p. 183, and the
Lipschitz condition of p. 179):** `‖sineDecayDeriv n t y‖ ≤ 3` in operator norm for the sup norm. -/
theorem norm_sineDecayDeriv_le (n : ℕ) (t : ℝ) (y : Fin n → ℝ) : ‖sineDecayDeriv n t y‖ ≤ 3 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [sineDecayDeriv, ContinuousLinearMap.pi_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
  have hc : |-2 + Real.cos (y i)| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (y i), Real.cos_le_one (y i)]
  have hv : |v i| ≤ ‖v‖ := by simpa using norm_le_pi_norm v i
  exact mul_le_mul hc hv (abs_nonneg _) (by norm_num)

/-- The state times the field is at most minus the squared Euclidean norm (for MLS Theorem 4.5,
p. 183): `y ⬝ f(t, y) ≤ −y ⬝ y`, from `|sin σ| ≤ |σ|`. -/
private lemma dotProduct_sineDecayField_le (n : ℕ) (t : ℝ) (y : Fin n → ℝ) :
    y ⬝ᵥ sineDecayField n t y ≤ -(y ⬝ᵥ y) := by
  simp only [dotProduct, sineDecayField, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : y i * Real.sin (y i) ≤ |y i| * |y i| := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _)
  have h2 : |y i| * |y i| = y i * y i := abs_mul_abs_self _
  nlinarith

/-- **The origin of `ẋ = −2x + sin x` (componentwise) is exponentially stable (MLS Definition 4.3,
pp. 180–181),** by the local form of MLS Theorem 4.5 (p. 183) with `V(x) = x ⬝ x`. Sup norm on
`ℝⁿ`. -/
theorem exponentiallyStable_sineDecayField (n : ℕ) :
    Stability.ExponentiallyStable (sineDecayField n) 0 := by
  refine Stability.exponentiallyStable_of_quadratic_lyapunov_local (V := fun _ y => y ⬝ᵥ y)
    (Vdot := fun t y => sineDecayField n t y ⬝ᵥ y + y ⬝ᵥ sineDecayField n t y)
    (a₁ := 1) (a₂ := n + 1) (a₃ := 2) (ε := 1) one_pos (by positivity) two_pos one_pos
    ?_ ?_ ?_ ?_ ?_
  · refine Continuous.continuousOn ?_
    simp only [dotProduct]
    fun_prop
  · intro t _ y _
    simpa using Control.sq_norm_le_dotProduct_self y
  · intro t _ y _
    have h := Control.dotProduct_self_le_mul_sq_norm y
    nlinarith [sq_nonneg ‖y‖]
  · intro t₀ _ x hx t ht _
    exact Control.hasDerivAt_dotProduct (hx.2 t ht) (hx.2 t ht)
  · intro t _ y _
    have h1 := dotProduct_sineDecayField_le n t y
    have h2 := Control.sq_norm_le_dotProduct_self y
    rw [dotProduct_comm (sineDecayField n t y)]
    linarith

/-- **The converse of MLS Theorem 4.5 (p. 183) on a nonlinear field, every hypothesis met:** for
`sineDecayField n` there are `V`, `V̇`, `∂V/∂x` and constants with the four bounds of the theorem
on `‖x‖ ≤ ε`, from `exists_lyapunov_of_exponentiallyStable_of_fderiv` with `K = 3`. Sup norm on
`ℝⁿ`; time first. -/
theorem exists_lyapunov_sineDecayField (n : ℕ) :
    ∃ V Vdot : ℝ → (Fin n → ℝ) → ℝ, ∃ DV : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ,
      ∃ a₁ > 0, ∃ a₂ > 0, ∃ a₃ > 0, ∃ a₄ > 0, ∃ ε > 0,
        ContinuousOn (fun p : ℝ × (Fin n → ℝ) => V p.1 p.2) (Ici 0 ×ˢ univ) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → a₁ * ‖y‖ ^ 2 ≤ V t y ∧ V t y ≤ a₂ * ‖y‖ ^ 2) ∧
        Stability.HasDerivAlongSolutions (sineDecayField n) V Vdot univ ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → Vdot t y ≤ -(a₃ * ‖y‖ ^ 2)) ∧
        (∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → HasFDerivAt (V t) (DV t y) y) ∧
        ∀ t, 0 ≤ t → ∀ y : Fin n → ℝ, ‖y‖ ≤ ε → ‖DV t y‖ ≤ a₄ * ‖y‖ := by
  exact Stability.exists_lyapunov_of_exponentiallyStable_of_fderiv (K := 3)
    (fun _ => continuousOn_const) (fun t _ y => hasFDerivAt_sineDecayField n t y)
    (continuousOn_sineDecayDeriv n) (fun t _ y => by exact_mod_cast norm_sineDecayDeriv_le n t y)
    (exponentiallyStable_sineDecayField n)

end RoboLean.Examples
