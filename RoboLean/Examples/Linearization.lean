import RoboLean.Control.Linearization
import RoboLean.Examples.NonlinearSpring

/-!
# The damped pendulum by linearization (MLS Theorem 4.6 and p. 185 on the system of Example 4.6)

**The system.** MLS Example 4.6 (printed p. 187) writes the spring–mass–damper field (4.45),
`ẋ₁ = x₂`, `ẋ₂ = −f(x₂) − g(x₁)` (`springField f g` of `RoboLean.Examples.NonlinearSpring`, state
`(x₁, x₂) ∈ ℝ × ℝ`). With linear damping `f(v) = b v` and the pendulum restoring force
`g(θ) = k sin θ`, `b, k > 0`, its Jacobian at the origin is `A = [[0, 1], [−k, −b]]`
(`pendulumMatrix`), whose eigenvalues solve `μ² + bμ + k = 0` and have real part `−b/2` or are
real and negative (`isHurwitz_pendulumMatrix`).

**What is proved here.**

* the field in coordinates `Fin 2 → ℝ` (`pendulumField`) has the Fréchet derivative `x ↦ Ax` at
  the origin (`hasFDerivAt_pendulumField`), so by the time-invariant indirect method of p. 185 its
  origin is exponentially stable (`exponentiallyStable_pendulumField`); the linearization `ż = Az`
  is globally exponentially stable (`globallyExponentiallyStable_pendulumLinearization`);
* moving back to `ℝ × ℝ` (`ExponentiallyStable.of_continuousLinearEquiv`), the origin of
  `springField (b ·) (k sin ·)` is exponentially stable
  (`exponentiallyStable_springField_pendulum`), in particular for E023's damped pendulum `springField id sin`
  (`exponentiallyStable_dampedPendulum`). E023 proved only asymptotic stability, by Lasalle's
  principle (`asymptoticallyStableAt_dampedPendulum`, MLS Example 4.7);
* the conclusion concerns actual trajectories: the flow of `springField id sin` exists and decays
  exponentially from every initial state within some `ε` (`exists_hasFlow_decay_dampedPendulum`).

**Conventions.** Sup norms on `Fin 2 → ℝ` and `ℝ × ℝ`; the coordinate change is Mathlib's
`ContinuousLinearEquiv.finTwoArrow` (`y ↦ (y 0, y 1)`); the transfer lemma uses only that it is a
continuous linear equivalence. These are statements about the model equations, not about a
physical pendulum.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

open Stability Control

/-- **The Jacobian at the origin of the damped pendulum** `ẋ₁ = x₂`, `ẋ₂ = −b x₂ − k sin x₁` (MLS
eq. (4.38), p. 184, for the field (4.45) of p. 187 with `f(v) = b v`, `g(θ) = k sin θ`):
`A = [[0, 1], [−k, −b]]`. -/
def pendulumMatrix (k b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -k, -b]

/-- **The eigenvalue condition of MLS p. 185 for the damped pendulum:** for `k, b > 0` every complex
eigenvalue `μ` of `[[0, 1], [−k, −b]]` has negative real part. An eigenvector `v` has `v₀ ≠ 0`,
`v₁ = μ v₀` and `μ² + bμ + k = 0`; then either `Im μ = 0` and `μ² + bμ + k > 0` for `μ ≥ 0`, or
`Re μ = −b/2`. -/
theorem isHurwitz_pendulumMatrix {k b : ℝ} (hk : 0 < k) (hb : 0 < b) :
    IsHurwitz (pendulumMatrix k b) := by
  intro μ v hv0 hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [pendulumMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hv00 : v 0 ≠ 0 := by
    intro hz
    apply hv0
    funext i
    fin_cases i
    · exact hz
    · simpa [hz] using h0
  have hchar : (μ ^ 2 + b * μ + k) * v 0 = 0 := by
    rw [h0] at h1
    linear_combination -h1
  have hq : μ ^ 2 + b * μ + k = 0 := (mul_eq_zero.mp hchar).resolve_right hv00
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  by_contra hcon
  have hcon : 0 ≤ μ.re := not_lt.mp hcon
  have him0 : μ.im = 0 := by
    have : μ.im * (2 * μ.re + b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  rw [him0] at hre
  nlinarith

/-- **The damped pendulum field in coordinates `ℝ²`** (MLS eq. (4.45), p. 187, with `f(v) = b v`,
`g(θ) = k sin θ`): `y ↦ (y₁, −b y₁ − k sin y₀)`, where `y₀` is the angle and `y₁` the angular
velocity. -/
def pendulumField (k b : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![y 1, -(b * y 1) - k * Real.sin (y 0)]

/-- **The Jacobian of the pendulum field at the origin** (MLS eq. (4.38), p. 184): the field has
the Fréchet derivative `x ↦ A x` at `0`, `A = [[0, 1], [−k, −b]]`. -/
theorem hasFDerivAt_pendulumField (k b : ℝ) :
    HasFDerivAt (pendulumField k b)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (pendulumMatrix k b))) 0 := by
  rw [hasFDerivAt_pi']
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · have h := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)
    convert h using 1
    · funext y
      simp [pendulumField]
    · ext y
      simp [pendulumMatrix, dotProduct, Fin.sum_univ_two]
  · have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ)
    have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)
    have h := ((h1.const_mul b).neg).sub (h0.sin.const_mul k)
    convert h using 1
    · funext y
      simp [pendulumField]
    · ext y
      simp [pendulumMatrix, dotProduct, Fin.sum_univ_two]
      ring

/-- **The linearized damped pendulum is globally exponentially stable** (MLS eq. (4.40), p. 184,
and Definition 4.3, p. 181): `ż = Az` with `A = [[0, 1], [−k, −b]]`, `k, b > 0`. -/
theorem globallyExponentiallyStable_pendulumLinearization {k b : ℝ} (hk : 0 < k) (hb : 0 < b) :
    GloballyExponentiallyStable (fun _ z => pendulumMatrix k b *ᵥ z) 0 :=
  (isHurwitz_pendulumMatrix hk hb).globallyExponentiallyStable

/-- **The damped pendulum by the indirect method (MLS p. 185), in coordinates `ℝ²`:** for
`k, b > 0` the origin of `ẏ = (y₁, −b y₁ − k sin y₀)` is exponentially stable (Definition 4.3). -/
theorem exponentiallyStable_pendulumField {k b : ℝ} (hk : 0 < k) (hb : 0 < b) :
    ExponentiallyStable (fun _ => pendulumField k b) 0 :=
  (isHurwitz_pendulumMatrix hk hb).exponentiallyStable_of_hasFDerivAt (by simp [pendulumField])
    (hasFDerivAt_pendulumField k b)

/-- **The damped pendulum of MLS Example 4.6's system (4.45), p. 187, is exponentially stable**
(Definition 4.3), for linear damping `f(v) = b v` and restoring force `g(θ) = k sin θ` with
`k, b > 0`, on the state `(x₁, x₂) ∈ ℝ × ℝ` with the sup norm; by MLS Theorem 4.6 and p. 185 through
the coordinates `ℝ²`. -/
theorem exponentiallyStable_springField_pendulum {k b : ℝ} (hk : 0 < k) (hb : 0 < b) :
    ExponentiallyStable (fun _ => springField (fun v => b * v) (fun θ => k * Real.sin θ)) 0 := by
  refine ExponentiallyStable.of_continuousLinearEquiv
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm ?_
  have hconj : (fun (_ : ℝ) (y : Fin 2 → ℝ) => (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
      (springField (fun v => b * v) (fun θ => k * Real.sin θ)
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.symm y))) = fun _ => pendulumField k b := by
    funext t y i
    fin_cases i <;> simp [springField, pendulumField]
  rw [hconj]
  exact exponentiallyStable_pendulumField hk hb

/-- **E023's damped pendulum `ẋ₁ = x₂`, `ẋ₂ = −x₂ − sin x₁` is exponentially stable** (MLS
Definition 4.3, p. 181), by the indirect method (MLS Theorem 4.6, p. 184, and p. 185). E023 proved
asymptotic stability by Lasalle's principle (`asymptoticallyStableAt_dampedPendulum`). -/
theorem exponentiallyStable_dampedPendulum :
    ExponentiallyStable (fun _ => springField id Real.sin) 0 := by
  have h := exponentiallyStable_springField_pendulum one_pos one_pos
  have hf : springField id Real.sin = springField (fun v => 1 * v) (fun θ => 1 * Real.sin θ) := by
    funext x
    simp [springField]
  rw [hf]
  exact h

/-- **The trajectories of E023's damped pendulum decay exponentially** (MLS Definition 4.3, p. 181,
applied to the flow): the field `springField id sin` is Lipschitz, so its flow `φ` exists
(`exists_hasFlow_of_lipschitzWith`), and for some `m, α, ε > 0` every trajectory from
`‖x₀‖ ≤ ε` satisfies `‖φ(t, x₀)‖ ≤ m e^{−αt} ‖x₀‖` for `t ≥ 0`. This shows that the stability
statements above are not about an empty set of solutions. -/
theorem exists_hasFlow_decay_dampedPendulum :
    ∃ φ : ℝ → ℝ × ℝ → ℝ × ℝ, HasFlow (springField id Real.sin) φ ∧ ∃ m > 0, ∃ α > 0, ∃ ε > 0,
      ∀ x₀ : ℝ × ℝ, ‖x₀‖ ≤ ε → ∀ t, 0 ≤ t → ‖φ t x₀‖ ≤ m * Real.exp (-α * t) * ‖x₀‖ := by
  obtain ⟨φ, hφ⟩ := exists_hasFlow_of_lipschitzWith
    (lipschitzWith_springField LipschitzWith.id Real.lipschitzWith_sin)
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := exponentiallyStable_dampedPendulum
  refine ⟨φ, hφ, m, hm, α, hα, ε, hε, fun x₀ hx₀ t ht => ?_⟩
  have := h 0 le_rfl (fun t => φ t x₀) (hφ.isSolution x₀) (by simpa [hφ.map_zero] using hx₀) t ht
  simpa [hφ.map_zero] using this

end RoboLean.Examples
