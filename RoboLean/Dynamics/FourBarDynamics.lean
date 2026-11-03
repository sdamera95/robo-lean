import RoboLean.Control.ConstrainedManipulator
import RoboLean.Dynamics.Lagrangian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The four-bar linkage of MLS Chapter 6, Exercise 5 (printed pp. 314–315)

MLS Chapter 6, Exercise 5, printed pp. 314–315: "Derive the dynamics of the four-bar linkage shown
below in terms of the crank angle `θ₁ ∈ S¹`." No masses, gravity or input are printed.

**Reading of the figure (a convention of this file).** The rail through the base joint `B` is the
`x`-axis, `y` up in the plane of the figure. Link 1 (length `l₁`, the crank) turns about `B` at the
angle `θ₁` from the rail; link 2 (length `l₂`, the coupler) is at the relative angle `θ₂`; its end
`C` is a revolute joint on the slider `T`, which moves along the rail; `θ₃` is the relative angle of
the slider (link 3, rigid with `T`, of length `l₃` along the rail) to link 2. All angles are
counterclockwise. The joint space of the open chain is `q = (θ₁, θ₂, θ₃) ∈ ℝ³` (angles not reduced
mod `2π`), and closing the loop imposes two constraints (`loopConstraint`):
`l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) = 0` (`C` on the rail) and `θ₁ + θ₂ + θ₃ = 0` (the slider does not
turn). The masses are symbolic point masses: `m₁` at the joint between links 1 and 2, `m₂` at `C`
and `m₃` at the slider `T`, at distance `l₃` from `C` along the rail; the links are massless, and
gravity `g` acts along `−y` (take `g = 0` for a horizontal mechanism). The crank torque `τ` acts at
`B`.

**Parametrization by the crank angle.** For `0 < l₁ < l₂` the coupler stays on the side of the
slider shown (`cos(θ₁ + θ₂) > 0`), and the absolute coupler angle is
`θ₁ + θ₂ = −arcsin((l₁/l₂) sin θ₁)` (`couplerAngle`). The map
`f(θ₁) = (θ₁, θ₁₂ − θ₁, −θ₁₂)` (`joints`) is defined, smooth and injective on all of `ℝ`, and it is a
surface parametrization of the loop in the sense of MLS (4.56)–(4.57)
(`isSurfaceParametrization_joints`); the crank angle `θ₁ ∈ S¹` is represented by its real lift, and
`f(θ₁ + 2π) = f(θ₁) + (2π, −2π, 0)` (`joints_add_two_pi`), the same physical configuration. A chart
on the circle itself is not formalized. The other branch (`cos(θ₁ + θ₂) < 0`, the coupler folded
back) and the case `l₁ ≥ l₂` are not treated.

**Dynamics.** Along the loop the elbow mass moves on the circle of radius `l₁` and the masses at `C`
and `T` move along the rail with the slider rate `ẋ_C = s(θ₁) θ̇₁` (`sliderRate`), so the kinetic
energy is `½ m̃(θ₁) θ̇₁²` with `m̃ = m₁ l₁² + (m₂ + m₃) s(θ₁)²` (`kineticEnergy_loop`), and the
potential energy is `m₁ g l₁ sin θ₁`. Lagrange's equation for the reduced Lagrangian
`L̃ = ½ m̃(θ₁) θ̇₁² − m₁ g l₁ sin θ₁` with the crank torque is
`m̃(θ₁) θ̈₁ + ½ m̃′(θ₁) θ̇₁² + m₁ g l₁ cos θ₁ = τ` (`lagrangeEquationsAt_crank_iff`). That the
dynamics of the closed chain are Lagrange's equations of the Lagrangian restricted to the loop (the
holonomic substitution) is the modeling step, not derived here.

Nothing here concerns friction, joint clearances or a physical mechanism.
-/

noncomputable section

open Matrix Real Filter Topology

namespace RoboLean
namespace FourBar

open MapJacobian Control

/-! ### The loop and its parametrization by the crank angle -/

/-- **The absolute coupler angle `θ₁ + θ₂` of the four-bar linkage of MLS Chapter 6, Exercise 5
(p. 315)** as a function of the crank angle: `−arcsin((l₁/l₂) sin θ₁)`, the branch with the coupler
pointing towards the slider (`cos(θ₁ + θ₂) > 0`). -/
def couplerAngle (l₁ l₂ x : ℝ) : ℝ := -arcsin (l₁ / l₂ * sin x)

/-- **The loop-closure constraints of MLS Chapter 6, Exercise 5 (p. 315)** on the joint angles
`q = (θ₁, θ₂, θ₃)`: `h(q) = (l₁ sin θ₁ + l₂ sin(θ₁ + θ₂), θ₁ + θ₂ + θ₃)`; `h = 0` puts the end of
the coupler on the rail and keeps the slider from turning. -/
def loopConstraint (l₁ l₂ : ℝ) (q : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![l₁ * sin (q 0) + l₂ * sin (q 0 + q 1), q 0 + q 1 + q 2]

/-- **The joint angles as functions of the crank angle (MLS Chapter 6, Exercise 5, p. 315):**
`f(θ₁) = (θ₁, θ₁₂ − θ₁, −θ₁₂)` with `θ₁₂ = couplerAngle l₁ l₂ θ₁`, the parametrization
`f : ℝ¹ → ℝ³` of the loop in the form of MLS eq. (4.57), p. 200. -/
def joints (l₁ l₂ : ℝ) (φ : Fin 1 → ℝ) : Fin 3 → ℝ :=
  ![φ 0, couplerAngle l₁ l₂ (φ 0) - φ 0, -couplerAngle l₁ l₂ (φ 0)]

/-- `cos(θ₁ + θ₂)` on the loop, `√(1 − (l₁/l₂)² sin² θ₁)` (MLS Chapter 6, Exercise 5, p. 315). -/
def couplerCos (l₁ l₂ x : ℝ) : ℝ := √(1 - (l₁ / l₂ * sin x) ^ 2)

/-- **The position of the slider joint `C` along the rail (MLS Chapter 6, Exercise 5, p. 315):**
`x_C(θ₁) = l₁ cos θ₁ + l₂ √(1 − (l₁/l₂)² sin² θ₁)`; the slider `T` is at `x_C + l₃`. -/
def sliderPosition (l₁ l₂ x : ℝ) : ℝ := l₁ * cos x + l₂ * couplerCos l₁ l₂ x

/-- **The slider rate per unit crank rate (MLS Chapter 6, Exercise 5, p. 315):**
`s(θ₁) = dx_C/dθ₁ = −l₁ sin θ₁ − (l₁²/l₂) sin θ₁ cos θ₁ / √(1 − (l₁/l₂)² sin² θ₁)`. -/
def sliderRate (l₁ l₂ x : ℝ) : ℝ :=
  -(l₁ * sin x) - l₁ ^ 2 / l₂ * sin x * cos x / couplerCos l₁ l₂ x

variable {l₁ l₂ : ℝ}

private theorem ratio_bounds (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) :
    -1 < l₁ / l₂ * sin x ∧ l₁ / l₂ * sin x < 1 := by
  have hl₂ : 0 < l₂ := hl₁.trans hl
  have hr : 0 < l₁ / l₂ := div_pos hl₁ hl₂
  have hr1 : l₁ / l₂ < 1 := (div_lt_one hl₂).mpr hl
  have hs := neg_one_le_sin x
  have hs' := sin_le_one x
  constructor <;> nlinarith

private theorem one_sub_sq_pos (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) :
    0 < 1 - (l₁ / l₂ * sin x) ^ 2 := by
  obtain ⟨h1, h2⟩ := ratio_bounds hl₁ hl x
  nlinarith

/-- On the loop, `cos(θ₁ + θ₂) = √(1 − (l₁/l₂)² sin² θ₁) > 0` for `0 < l₁ < l₂` (MLS Chapter 6,
Exercise 5, p. 315): the coupler points towards the slider. -/
theorem couplerCos_pos (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) : 0 < couplerCos l₁ l₂ x :=
  Real.sqrt_pos.mpr (one_sub_sq_pos hl₁ hl x)

/-- `sin(θ₁ + θ₂) = −(l₁/l₂) sin θ₁` on the loop (MLS Chapter 6, Exercise 5, p. 315). -/
theorem sin_couplerAngle (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) :
    sin (couplerAngle l₁ l₂ x) = -(l₁ / l₂ * sin x) := by
  obtain ⟨h1, h2⟩ := ratio_bounds hl₁ hl x
  rw [couplerAngle, sin_neg, sin_arcsin h1.le h2.le]

/-- `cos(θ₁ + θ₂) = couplerCos` on the loop (MLS Chapter 6, Exercise 5, p. 315). -/
theorem cos_couplerAngle (x : ℝ) : cos (couplerAngle l₁ l₂ x) = couplerCos l₁ l₂ x := by
  rw [couplerAngle, cos_neg, cos_arcsin, couplerCos]

/-- **The parametrization closes the loop (MLS Chapter 6, Exercise 5, p. 315; eq. (4.57),
p. 200):** `h(f(θ₁)) = 0` for every crank angle, for `0 < l₁ < l₂`. -/
theorem loopConstraint_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) (φ : Fin 1 → ℝ) :
    loopConstraint l₁ l₂ (joints l₁ l₂ φ) = 0 := by
  have hl₂ : l₂ ≠ 0 := (hl₁.trans hl).ne'
  funext i
  fin_cases i
  · simp [loopConstraint, joints, sin_couplerAngle hl₁ hl]
    field_simp
    ring
  · simp [loopConstraint, joints]

/-- The parametrization by the crank angle is injective on all of `ℝ` (MLS p. 200's hypothesis on
`f`, for the loop of Exercise 5, p. 315): its first coordinate is the crank angle. -/
theorem joints_injective : Function.Injective (joints l₁ l₂) := by
  intro φ ψ h
  funext i
  fin_cases i
  simpa [joints] using congrFun h 0

/-- **The crank angle lives on `S¹` (MLS Chapter 6, Exercise 5, p. 315):** a full turn of the crank
returns the linkage to the same physical configuration, `f(θ₁ + 2π) = f(θ₁) + (2π, −2π, 0)`
(each joint angle changes by a multiple of `2π`). -/
theorem joints_add_two_pi (φ : Fin 1 → ℝ) :
    joints l₁ l₂ (φ + fun _ => 2 * π) = joints l₁ l₂ φ + ![2 * π, -(2 * π), 0] := by
  have hc : couplerAngle l₁ l₂ (φ 0 + 2 * π) = couplerAngle l₁ l₂ (φ 0) := by
    rw [couplerAngle, couplerAngle, sin_add_two_pi]
  funext i
  fin_cases i
  · simp [joints]
  · simp [joints, hc]
    ring
  · simp [joints, hc]

/-- **The derivative of the coupler angle (MLS Chapter 6, Exercise 5, p. 315):**
`d(θ₁ + θ₂)/dθ₁ = −(l₁/l₂) cos θ₁ / √(1 − (l₁/l₂)² sin² θ₁)` on the loop, for `0 < l₁ < l₂`. -/
theorem hasDerivAt_couplerAngle (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) :
    HasDerivAt (couplerAngle l₁ l₂) (-(l₁ / l₂ * cos x) / couplerCos l₁ l₂ x) x := by
  obtain ⟨h1, h2⟩ := ratio_bounds hl₁ hl x
  have h := ((Real.hasDerivAt_arcsin h1.ne' h2.ne).comp x
    ((hasDerivAt_sin x).const_mul (l₁ / l₂))).neg
  convert h using 1
  · rfl
  · unfold couplerCos
    ring

private theorem contDiff_couplerAngle (hl₁ : 0 < l₁) (hl : l₁ < l₂) :
    ContDiff ℝ 2 (couplerAngle l₁ l₂) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨h1, h2⟩ := ratio_bounds hl₁ hl x
  have hs : ContDiff ℝ 2 fun y : ℝ => l₁ / l₂ * sin y := contDiff_const.mul contDiff_sin
  exact ((Real.contDiffAt_arcsin h1.ne' h2.ne).comp x hs.contDiffAt).neg

/-- **The Jacobian `∂h/∂q` of the loop constraints (MLS Chapter 6, Exercise 5, p. 315; the matrix
of (4.56), p. 200):** `[[l₁ cos θ₁ + l₂ cos(θ₁ + θ₂), l₂ cos(θ₁ + θ₂), 0], [1, 1, 1]]`. -/
theorem jac_loopConstraint (q : Fin 3 → ℝ) :
    jac (loopConstraint l₁ l₂) q =
      !![l₁ * cos (q 0) + l₂ * cos (q 0 + q 1), l₂ * cos (q 0 + q 1), 0; 1, 1, 1] := by
  let P : Fin 3 → ((Fin 3 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  have hp : ∀ i, HasFDerivAt (fun x : Fin 3 → ℝ => x i) (P i) q := fun i => hasFDerivAt_apply i q
  have ha : HasFDerivAt (fun x : Fin 3 → ℝ => x 0 + x 1) (P 0 + P 1) q := (hp 0).add (hp 1)
  have h0 : HasFDerivAt (fun x : Fin 3 → ℝ => l₁ * sin (x 0) + l₂ * sin (x 0 + x 1))
      (l₁ • (cos (q 0) • P 0) + l₂ • (cos (q 0 + q 1) • (P 0 + P 1))) q :=
    ((hp 0).sin.const_mul l₁).add (ha.sin.const_mul l₂)
  have h1 : HasFDerivAt (fun x : Fin 3 → ℝ => x 0 + x 1 + x 2) (P 0 + P 1 + P 2) q :=
    ha.add (hp 2)
  have hL : ∀ k, HasFDerivAt (fun x => loopConstraint l₁ l₂ x k)
      (![l₁ • (cos (q 0) • P 0) + l₂ • (cos (q 0 + q 1) • (P 0 + P 1)), P 0 + P 1 + P 2] k) q := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
  ext i j
  rw [jac_apply_of_hasFDerivAt hL]
  fin_cases i <;> fin_cases j <;> simp [P]

/-- **The Jacobian `∂f/∂θ₁` of the crank-angle parametrization (MLS Chapter 6, Exercise 5,
p. 315):** the column `(1, c′ − 1, −c′)` with `c′` the derivative of the coupler angle. -/
theorem jac_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) (φ : Fin 1 → ℝ) :
    jac (joints l₁ l₂) φ =
      !![1; -(l₁ / l₂ * cos (φ 0)) / couplerCos l₁ l₂ (φ 0) - 1;
        -(-(l₁ / l₂ * cos (φ 0)) / couplerCos l₁ l₂ (φ 0))] := by
  set c' := -(l₁ / l₂ * cos (φ 0)) / couplerCos l₁ l₂ (φ 0)
  let P : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hp : HasFDerivAt (fun x : Fin 1 → ℝ => x 0) P φ := hasFDerivAt_apply 0 φ
  have hc : HasFDerivAt (fun x : Fin 1 → ℝ => couplerAngle l₁ l₂ (x 0)) (c' • P) φ :=
    (hasDerivAt_couplerAngle hl₁ hl (φ 0)).comp_hasFDerivAt (f := fun x : Fin 1 → ℝ => x 0) φ hp
  have hL : ∀ k, HasFDerivAt (fun x => joints l₁ l₂ x k) (![P, c' • P - P, -(c' • P)] k) φ := by
    intro k
    fin_cases k
    · exact hp
    · exact hc.sub hp
    · exact hc.neg
  ext i j
  rw [jac_apply_of_hasFDerivAt hL]
  fin_cases i <;> fin_cases j <;> simp [P]

/-- **The loop of MLS Chapter 6, Exercise 5 (p. 315) with its crank-angle parametrization is a
constraint surface in the sense of MLS (4.56)–(4.57), p. 200**, for `0 < l₁ < l₂`: two independent
smooth constraints on `ℝ³` and the smooth injective `f : ℝ → ℝ³` with `h(f(θ₁)) = 0`, whose
derivative spans the tangent line of the loop. The crank angle is the real lift of `θ₁ ∈ S¹`. -/
theorem isSurfaceParametrization_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) :
    IsSurfaceParametrization (loopConstraint l₁ l₂) (joints l₁ l₂) := by
  have hl₂ : 0 < l₂ := hl₁.trans hl
  have hcd := contDiff_couplerAngle hl₁ hl
  have hjl : ∀ φ : Fin 1 → ℝ, jac (loopConstraint l₁ l₂) (joints l₁ l₂ φ) =
      !![l₁ * cos (φ 0) + l₂ * couplerCos l₁ l₂ (φ 0), l₂ * couplerCos l₁ l₂ (φ 0), 0;
        1, 1, 1] := by
    intro φ
    rw [jac_loopConstraint]
    have e : joints l₁ l₂ φ 0 + joints l₁ l₂ φ 1 = couplerAngle l₁ l₂ (φ 0) := by
      simp [joints]
    rw [e, cos_couplerAngle]
    simp [joints]
  refine ⟨?_, ?_, joints_injective, loopConstraint_joints hl₁ hl, ?_, rfl, ?_⟩
  · unfold loopConstraint
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      fun_prop
  · have hp : ContDiff ℝ 2 fun φ : Fin 1 → ℝ => φ 0 := contDiff_apply ℝ ℝ 0
    have hc : ContDiff ℝ 2 fun φ : Fin 1 → ℝ => couplerAngle l₁ l₂ (φ 0) := hcd.comp hp
    unfold joints
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simpa using hp
    · simpa using hc.sub hp
    · simpa using hc.neg
  · intro φ
    rw [hjl]
    change LinearIndependent ℝ ![![l₁ * cos (φ 0) + l₂ * couplerCos l₁ l₂ (φ 0),
      l₂ * couplerCos l₁ l₂ (φ 0), 0], ![1, 1, 1]]
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrFun hst 1
    have e2 := congrFun hst 2
    simp at e1 e2
    rw [e2, add_zero] at e1
    have hb : l₂ * couplerCos l₁ l₂ (φ 0) ≠ 0 :=
      mul_ne_zero hl₂.ne' (couplerCos_pos hl₁ hl (φ 0)).ne'
    exact ⟨(mul_eq_zero.mp e1).resolve_right hb, e2⟩
  · intro φ v hv
    rw [hjl] at hv
    have e0 := congrFun hv 0
    have e1 := congrFun hv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1
    have hC := (couplerCos_pos hl₁ hl (φ 0)).ne'
    refine ⟨![v 0], ?_⟩
    rw [jac_joints hl₁ hl]
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct]
    · simp [Matrix.mulVec, dotProduct]
      field_simp
      linear_combination -e0
    · simp [Matrix.mulVec, dotProduct]
      field_simp
      linear_combination e0 - l₂ * couplerCos l₁ l₂ (φ 0) * e1

/-! ### Positions and velocities of the point masses along the loop -/

/-- The elbow of MLS Chapter 6, Exercise 5 (p. 315), the joint between links 1 and 2, in the plane
of the figure: `l₁ (cos θ₁, sin θ₁)`, where the point mass `m₁` sits. -/
def elbow (l₁ : ℝ) (q : Fin 3 → ℝ) : Fin 2 → ℝ := ![l₁ * cos (q 0), l₁ * sin (q 0)]

/-- The joint `C` at the end of the coupler in MLS Chapter 6, Exercise 5 (p. 315), for the open
chain: `l₁ (cos θ₁, sin θ₁) + l₂ (cos(θ₁ + θ₂), sin(θ₁ + θ₂))`, where the point mass `m₂` sits. -/
def jointC (l₁ l₂ : ℝ) (q : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![l₁ * cos (q 0) + l₂ * cos (q 0 + q 1), l₁ * sin (q 0) + l₂ * sin (q 0 + q 1)]

/-- The slider `T` of MLS Chapter 6, Exercise 5 (p. 315), at distance `l₃` from `C` along link 3,
for the open chain, where the point mass `m₃` sits. -/
def slider (l₁ l₂ l₃ : ℝ) (q : Fin 3 → ℝ) : Fin 2 → ℝ :=
  jointC l₁ l₂ q + ![l₃ * cos (q 0 + q 1 + q 2), l₃ * sin (q 0 + q 1 + q 2)]

/-- On the loop of MLS Chapter 6, Exercise 5 (p. 315), the joint `C` is on the rail at
`x_C(θ₁)`. -/
theorem jointC_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) (φ : Fin 1 → ℝ) :
    jointC l₁ l₂ (joints l₁ l₂ φ) = ![sliderPosition l₁ l₂ (φ 0), 0] := by
  have e : joints l₁ l₂ φ 0 + joints l₁ l₂ φ 1 = couplerAngle l₁ l₂ (φ 0) := by simp [joints]
  have hl₂ : l₂ ≠ 0 := (hl₁.trans hl).ne'
  funext i
  fin_cases i
  · simp only [jointC, Fin.zero_eta, Matrix.cons_val_zero]
    rw [e, cos_couplerAngle]
    simp [joints, sliderPosition]
  · simp only [jointC, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [e, sin_couplerAngle hl₁ hl]
    simp [joints]
    field_simp
    ring

/-- On the loop of MLS Chapter 6, Exercise 5 (p. 315), the slider is on the rail at `x_C(θ₁) + l₃`
(link 3 stays along the rail). -/
theorem slider_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) (l₃ : ℝ) (φ : Fin 1 → ℝ) :
    slider l₁ l₂ l₃ (joints l₁ l₂ φ) = ![sliderPosition l₁ l₂ (φ 0) + l₃, 0] := by
  have e : joints l₁ l₂ φ 0 + joints l₁ l₂ φ 1 + joints l₁ l₂ φ 2 = 0 := by simp [joints]
  rw [slider, jointC_joints hl₁ hl, e]
  funext i
  fin_cases i <;> simp

/-- **The slider rate (MLS Chapter 6, Exercise 5, p. 315):** `dx_C/dθ₁ = s(θ₁)`, for
`0 < l₁ < l₂`. -/
theorem hasDerivAt_sliderPosition (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) :
    HasDerivAt (sliderPosition l₁ l₂) (sliderRate l₁ l₂ x) x := by
  have hl₂ : l₂ ≠ 0 := (hl₁.trans hl).ne'
  have hu : HasDerivAt (fun y => 1 - (l₁ / l₂ * sin y) ^ 2)
      (-(2 * (l₁ / l₂ * sin x) * (l₁ / l₂ * cos x))) x := by
    have := (((hasDerivAt_sin x).const_mul (l₁ / l₂)).pow 2).const_sub 1
    convert this using 1
    ring
  have hC := hu.sqrt (one_sub_sq_pos hl₁ hl x).ne'
  have h := ((hasDerivAt_cos x).const_mul l₁).add (hC.const_mul l₂)
  have hC0 := (couplerCos_pos hl₁ hl x).ne'
  refine h.congr_deriv ?_
  unfold sliderRate
  rw [show √(1 - (l₁ / l₂ * sin x) ^ 2) = couplerCos l₁ l₂ x from rfl]
  field_simp
  ring

/-- **The elbow velocity along a crank motion (MLS Chapter 6, Exercise 5, p. 315):**
`θ̇₁ l₁ (−sin θ₁, cos θ₁)`. -/
theorem hasDerivAt_elbow_joints {θ : ℝ → ℝ} {v t : ℝ} (hθ : HasDerivAt θ v t) :
    HasDerivAt (fun s => elbow l₁ (joints l₁ l₂ fun _ => θ s))
      (v • ![-(l₁ * sin (θ t)), l₁ * cos (θ t)]) t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · have := (hθ.cos).const_mul l₁
    simp only [elbow, joints, Matrix.cons_val_zero, Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    convert this using 1
    ring
  · have := (hθ.sin).const_mul l₁
    simp only [elbow, joints, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one,
      Pi.smul_apply, smul_eq_mul]
    convert this using 1
    ring

/-- **The velocity of `C` along a crank motion (MLS Chapter 6, Exercise 5, p. 315):**
`θ̇₁ (s(θ₁), 0)`, along the rail. -/
theorem hasDerivAt_jointC_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) {θ : ℝ → ℝ} {v t : ℝ}
    (hθ : HasDerivAt θ v t) :
    HasDerivAt (fun s => jointC l₁ l₂ (joints l₁ l₂ fun _ => θ s))
      (v • ![sliderRate l₁ l₂ (θ t), 0]) t := by
  simp_rw [jointC_joints hl₁ hl]
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    exact ((hasDerivAt_sliderPosition hl₁ hl (θ t)).comp t hθ).congr_deriv (by ring)
  · simpa using hasDerivAt_const t (0 : ℝ)

/-- **The velocity of the slider along a crank motion (MLS Chapter 6, Exercise 5, p. 315):**
`θ̇₁ (s(θ₁), 0)`, the same as that of `C`. -/
theorem hasDerivAt_slider_joints (hl₁ : 0 < l₁) (hl : l₁ < l₂) (l₃ : ℝ) {θ : ℝ → ℝ} {v t : ℝ}
    (hθ : HasDerivAt θ v t) :
    HasDerivAt (fun s => slider l₁ l₂ l₃ (joints l₁ l₂ fun _ => θ s))
      (v • ![sliderRate l₁ l₂ (θ t), 0]) t := by
  simp_rw [slider_joints hl₁ hl]
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    exact (((hasDerivAt_sliderPosition hl₁ hl (θ t)).comp t hθ).add_const l₃).congr_deriv
      (by ring)
  · simpa using hasDerivAt_const t (0 : ℝ)

/-! ### The dynamics in the crank angle -/

/-- **The reduced inertia of MLS Chapter 6, Exercise 5 (p. 315):**
`m̃(θ₁) = m₁ l₁² + (m₂ + m₃) s(θ₁)²` for point masses `m₁` at the elbow, `m₂` at `C` and `m₃` at the
slider. -/
def reducedInertia (m₁ m₂ m₃ l₁ l₂ x : ℝ) : ℝ := m₁ * l₁ ^ 2 + (m₂ + m₃) * sliderRate l₁ l₂ x ^ 2

/-- **The kinetic energy of the four-bar linkage along the loop (MLS Chapter 6, Exercise 5,
p. 315):** with the velocities of the elbow, of `C` and of the slider along a crank motion
(`hasDerivAt_elbow_joints`, `hasDerivAt_jointC_joints`, `hasDerivAt_slider_joints`),
`½ (m₁ ‖v₁‖² + m₂ ‖v_C‖² + m₃ ‖v_T‖²) = ½ m̃(θ₁) θ̇₁²`. -/
theorem kineticEnergy_loop (m₁ m₂ m₃ l₁ l₂ x v : ℝ) :
    (1 / 2 : ℝ) * (m₁ * ((v • ![-(l₁ * sin x), l₁ * cos x]) ⬝ᵥ
          (v • ![-(l₁ * sin x), l₁ * cos x])) +
        m₂ * ((v • ![sliderRate l₁ l₂ x, 0]) ⬝ᵥ (v • ![sliderRate l₁ l₂ x, 0])) +
        m₃ * ((v • ![sliderRate l₁ l₂ x, 0]) ⬝ᵥ (v • ![sliderRate l₁ l₂ x, 0]))) =
      (1 / 2 : ℝ) * reducedInertia m₁ m₂ m₃ l₁ l₂ x * v ^ 2 := by
  have pyth := sin_sq_add_cos_sq x
  simp [dotProduct, Fin.sum_univ_two, reducedInertia]
  linear_combination (1 / 2 * m₁ * l₁ ^ 2 * v ^ 2) * pyth

/-- **The potential energy of MLS Chapter 6, Exercise 5 (p. 315)** in this file's reading: gravity
`g` along `−y`, so only the elbow mass changes height: `V(θ₁) = m₁ g l₁ sin θ₁`. -/
def crankPotential (m₁ g l₁ : ℝ) (q : Fin 1 → ℝ) : ℝ := m₁ * g * l₁ * sin (q 0)

/-- The `1 × 1` inertia `m̃(θ₁)` of the crank coordinate (MLS Chapter 6, Exercise 5, p. 315), as the
inertia matrix field of the reduced mechanical Lagrangian `½ m̃ θ̇₁² − V(θ₁)` (eq. (4.20) form). -/
def crankInertia (m₁ m₂ m₃ l₁ l₂ : ℝ) (q : Fin 1 → ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  !![reducedInertia m₁ m₂ m₃ l₁ l₂ (q 0)]

private theorem differentiableAt_couplerCos (hl₁ : 0 < l₁) (hl : l₁ < l₂) (x : ℝ) :
    DifferentiableAt ℝ (couplerCos l₁ l₂) x := by
  have hu : DifferentiableAt ℝ (fun y => 1 - (l₁ / l₂ * sin y) ^ 2) x := by fun_prop
  exact hu.sqrt (one_sub_sq_pos hl₁ hl x).ne'

/-- The reduced inertia of MLS Chapter 6, Exercise 5 (p. 315) is differentiable in the crank angle,
for `0 < l₁ < l₂`. -/
theorem differentiableAt_reducedInertia (hl₁ : 0 < l₁) (hl : l₁ < l₂) (m₁ m₂ m₃ x : ℝ) :
    DifferentiableAt ℝ (reducedInertia m₁ m₂ m₃ l₁ l₂) x := by
  have hC := differentiableAt_couplerCos hl₁ hl x
  have hC0 := (couplerCos_pos hl₁ hl x).ne'
  have hs : DifferentiableAt ℝ (sliderRate l₁ l₂) x := by
    unfold sliderRate
    exact (differentiableAt_sin.const_mul l₁).neg.sub
      (((differentiableAt_sin.const_mul (l₁ ^ 2 / l₂)).mul differentiableAt_cos).div hC hC0)
  unfold reducedInertia
  exact (hs.pow 2).const_mul (m₂ + m₃) |>.const_add (m₁ * l₁ ^ 2)

/-- **MLS Chapter 6, Exercise 5, p. 315: the dynamics of the four-bar linkage in the crank angle.**
For `0 < l₁ < l₂`, Lagrange's equation (MLS eq. (4.5), p. 158) for the reduced Lagrangian
`½ m̃(θ₁) θ̇₁² − m₁ g l₁ sin θ₁` with the crank torque `τ` holds at `t` exactly when
`m̃(θ₁) θ̈₁ + ½ m̃′(θ₁) θ̇₁² + m₁ g l₁ cos θ₁ = τ`, with `m̃ = m₁ l₁² + (m₂ + m₃) s(θ₁)²` and
`m̃′ = deriv m̃`. Hypotheses: near `t` the crank motion has velocity `θ'(s)`, and `θ'` has
derivative `θ''` at `t`. -/
theorem lagrangeEquationsAt_crank_iff (hl₁ : 0 < l₁) (hl : l₁ < l₂) (m₁ m₂ m₃ g : ℝ)
    {θ θ' : ℝ → Fin 1 → ℝ} {θ'' : Fin 1 → ℝ} {t : ℝ} (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (τ : ℝ) :
    Lagrangian.LagrangeEquationsAt
        (Lagrangian.mechanical (crankInertia m₁ m₂ m₃ l₁ l₂) (crankPotential m₁ g l₁)) θ ![τ] t ↔
      reducedInertia m₁ m₂ m₃ l₁ l₂ (θ t 0) * θ'' 0 +
          (1 / 2 : ℝ) * deriv (reducedInertia m₁ m₂ m₃ l₁ l₂) (θ t 0) * θ' t 0 ^ 2 +
        m₁ * g * l₁ * cos (θ t 0) = τ := by
  let P : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hp : HasFDerivAt (fun x : Fin 1 → ℝ => x 0) P (θ t) := hasFDerivAt_apply 0 (θ t)
  set d := deriv (reducedInertia m₁ m₂ m₃ l₁ l₂) (θ t 0)
  have hm : HasFDerivAt (fun q : Fin 1 → ℝ => reducedInertia m₁ m₂ m₃ l₁ l₂ (q 0)) (d • P) (θ t) :=
    (differentiableAt_reducedInertia hl₁ hl m₁ m₂ m₃ (θ t 0)).hasDerivAt.comp_hasFDerivAt
      (f := fun x : Fin 1 → ℝ => x 0) (θ t) hp
  have hM : ∀ i j, HasFDerivAt (fun q => crankInertia m₁ m₂ m₃ l₁ l₂ q i j)
      ((fun _ _ => d • P : Fin 1 → Fin 1 → ((Fin 1 → ℝ) →L[ℝ] ℝ)) i j) (θ t) := by
    intro i j
    fin_cases i
    fin_cases j
    exact hm
  have hV : HasFDerivAt (crankPotential m₁ g l₁) ((m₁ * g * l₁) • (cos (θ t 0) • P)) (θ t) :=
    hp.sin.const_mul (m₁ * g * l₁)
  have hsymm : ∀ q, (crankInertia m₁ m₂ m₃ l₁ l₂ q).IsSymm := by
    intro q
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [Lagrangian.lagrangeEquationsAt_mechanical_iff hsymm hM hV hθ hθ' ![τ]]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [crankInertia, Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials,
      Lagrangian.gradient, Matrix.vecHead, Matrix.mulVec, dotProduct, P] at h0
    linear_combination h0
  · intro h
    funext i
    fin_cases i
    simp [crankInertia, Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials,
      Lagrangian.gradient, Matrix.vecHead, Matrix.mulVec, dotProduct, P]
    linear_combination h

end FourBar
end RoboLean
