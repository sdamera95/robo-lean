import RoboLean.Control.ExponentialArrival
import RoboLean.Examples.PlanarTwoLinkControl
import RoboLean.Examples.WorkspaceControl

/-!
# Set-point regulation of the planar two-link arm: an exponential bound and the end-effector error

The arm of MLS Figure 4.4 (printed p. 164, `planarTwoLinkModel`) under the PD law (4.51) of p. 193
with compensation of `N` and the gains `K_p = K_v = I`, at a fixed set point `θ_d`.

* **Exponential bound, uniform in the set point.** With positive masses and principal moments and
  any gravity data and joint forces, there is `C > 0` and, for every radius `ρ > 0`, a rate `α > 0`
  such that for every set point `θ_d` the closed loop has the exponential bound with constants
  `(C, α)` at `(θ_d, 0)` on the initial errors smaller than `ρ`
  (`planarTwoLinkArm_exponentialBoundOn_pdCompensatedTorque`). It is
  `ManipulatorModel.exponentialBoundOn_pdCompensatedTorque` (Proposition 4.10 of p. 194 as
  formalized, at a constant set point) with the bounds on `M` and `C` proved for this arm in
  `Examples/PlanarTwoLinkControl`. The constants are not computed numerically here.
* **End-effector error.** The end-effector map `planarArmXY l₁ l₂` of p. 97,
  `(l₁ cos θ₁ + l₂ cos(θ₁ + θ₂), l₁ sin θ₁ + l₂ sin(θ₁ + θ₂))`, is Lipschitz from the joint space
  with the sup norm to the plane with the Euclidean distance (`planarDist`), with constant
  `l₁ + 2 l₂` (`planarDist_planarArmXY_le`): the angle of the second link is `θ₁ + θ₂`, which moves
  by at most twice the sup norm of the joint change.

Statements about the ideal continuous model with exact model cancellation; nothing here concerns
sampling, numerical integration or a physical arm.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean.Examples

/-- **The Euclidean distance of the plane**, `√((u₁ − w₁)² + (u₂ − w₂)²)` for points written as
`Fin 2 → ℝ` (index `0` is `x`, index `1` is `y`, as in `planarArmXY`, MLS p. 97). The distance the
planar arm demo's arrival test uses; `Fin 2 → ℝ` itself carries Mathlib's sup norm. -/
def planarDist (u w : Fin 2 → ℝ) : ℝ :=
  √((u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2)

/-- Two points of the unit circle are no farther apart than their angles:
`‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
private theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have h : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

/-- **The end-effector map of the planar two-link arm is Lipschitz (MLS p. 97, the map
`(l₁ cos θ₁ + l₂ cos(θ₁ + θ₂), l₁ sin θ₁ + l₂ sin(θ₁ + θ₂))`).** For nonnegative link lengths and
all joint vectors `q, q'`, the Euclidean distance between the end-effector points is at most
`(l₁ + 2 l₂) ‖q − q'‖`, with the sup norm on the joint space. A derived bound, not printed in
MLS. -/
theorem planarDist_planarArmXY_le {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (q q' : Fin 2 → ℝ) :
    planarDist (planarArmXY l₁ l₂ q) (planarArmXY l₁ l₂ q') ≤ (l₁ + 2 * l₂) * ‖q - q'‖ := by
  set Z : ℂ := (l₁ : ℂ) * (Complex.exp ((q 0 : ℝ) * Complex.I) -
      Complex.exp ((q' 0 : ℝ) * Complex.I)) +
    (l₂ : ℂ) * (Complex.exp ((q 0 + q 1 : ℝ) * Complex.I) -
      Complex.exp ((q' 0 + q' 1 : ℝ) * Complex.I)) with hZ
  have hre : Z.re = planarArmXY l₁ l₂ q 0 - planarArmXY l₁ l₂ q' 0 := by
    simp only [hZ, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sub_im,
      planarArmXY, Matrix.cons_val_zero]
    ring
  have him : Z.im = planarArmXY l₁ l₂ q 1 - planarArmXY l₁ l₂ q' 1 := by
    simp only [hZ, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.sub_re,
      planarArmXY, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  have hd : planarDist (planarArmXY l₁ l₂ q) (planarArmXY l₁ l₂ q') = ‖Z‖ := by
    rw [planarDist, Complex.norm_def, Complex.normSq_apply, hre, him]
    ring_nf
  have h0 : |q 0 - q' 0| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 0
  have h1 : |q 1 - q' 1| ≤ ‖q - q'‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (q - q') 1
  have h01 : |(q 0 + q 1) - (q' 0 + q' 1)| ≤ 2 * ‖q - q'‖ := by
    have := abs_add_le (q 0 - q' 0) (q 1 - q' 1)
    rw [show q 0 - q' 0 + (q 1 - q' 1) = (q 0 + q 1) - (q' 0 + q' 1) by ring] at this
    linarith
  rw [hd]
  calc ‖Z‖ ≤ ‖(l₁ : ℂ) * (Complex.exp ((q 0 : ℝ) * Complex.I) -
          Complex.exp ((q' 0 : ℝ) * Complex.I))‖ +
        ‖(l₂ : ℂ) * (Complex.exp ((q 0 + q 1 : ℝ) * Complex.I) -
          Complex.exp ((q' 0 + q' 1 : ℝ) * Complex.I))‖ := norm_add_le _ _
    _ ≤ l₁ * |q 0 - q' 0| + l₂ * |(q 0 + q 1) - (q' 0 + q' 1)| := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hl₁,
          Real.norm_of_nonneg hl₂]
        gcongr
        · exact norm_exp_mul_I_sub_le _ _
        · exact norm_exp_mul_I_sub_le _ _
    _ ≤ l₁ * ‖q - q'‖ + l₂ * (2 * ‖q - q'‖) := by gcongr
    _ = (l₁ + 2 * l₂) * ‖q - q'‖ := by ring

variable (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)

/-- **PD set-point regulation of the planar two-link arm is exponential on bounded sets (MLS
Proposition 4.10, p. 194, at a constant set point; compare Proposition 4.9, p. 193).** With positive
masses and principal moments, any gravity data and joint forces, and `K_p = K_v = I`, there is
`C > 0` and, for every `ρ > 0`, a rate `α > 0` such that for every set point `θ_d` the PD law with
compensation of `N` has the exponential bound with constants `(C, α)` at `(θ_d, 0)` on the
initial errors smaller than `ρ` (state `(θ, θ̇)`, sup norm). The constants do not depend on the set
point; they are not computed numerically here. -/
theorem planarTwoLinkArm_exponentialBoundOn_pdCompensatedTorque (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ C > 0, ∀ ρ > 0, ∃ α > 0, ∀ θd : Fin 2 → ℝ,
      Stability.ExponentialBoundOn
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
          ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdCompensatedTorque 1 1 θd))
        (θd, 0) C α ρ := by
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMu : ∃ lam > 0, ∀ q v : Fin 2 → ℝ,
      lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q *ᵥ v) := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_uniformlyPosDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMb : ∃ μ, ∀ q v w : Fin 2 → ℝ,
      |v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂
  exact ManipulatorModel.exponentialBoundOn_pdCompensatedTorque _ hsymm hM hMu hMb
    (planarTwoLinkModel_C_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne) Matrix.PosDef.one Matrix.PosDef.one

end RoboLean.Examples
