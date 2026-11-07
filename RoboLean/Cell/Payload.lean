import RoboLean.Cell.AssuredTorque

/-!
# The cell arm carrying a payload, with joint friction: the plant and its disturbance

The controller of the assured cell computes its torque from the model of the unloaded arm,
`cellArm` (MLS Example 4.3 with the cell's parameters). The plant here is the same arm with a
point mass `m` (kg) at the tool point, unknown to the controller, and a joint friction torque `τ_f`
with `|τ_f,i| ≤ f_c + f_v |θ̇ᵢ|` for every joint (Coulomb level `f_c` in N m, viscous coefficient
`f_v` in N m s), entering the equations of motion as a force acting on the joints, as friction does
in MLS p. 170.

**The plant.** A point mass at the tool point, which lies on the forearm's axis at distance
`l₂ = 49/125` m from the elbow, is rigidly attached to the forearm. The forearm and the point mass
together are one rigid body (MLS pp. 161–162: mass, mass centre and inertia tensor of a mass
distribution): mass `m₃ + m`, mass centre on the axis at `(m₃ r₂ + m l₂)/(m₃ + m)` from the elbow,
and principal moments about it `I_x3 + μ d²`, `I_y3`, `I_z3 + μ d²` with
`μ = m₃ m/(m₃ + m)` and `d = l₂ − r₂ = 23/250` m (the moment about the forearm's own axis does not
change). `cellPayloadArm m` is the library's three-link arm `Examples.threeLinkModel` with these
forearm parameters, so its inertia matrix, Coriolis matrix and gravity term are those of the
library's Lagrangian development (MLS eqs. (4.19)–(4.25), pp. 168–175). That it is the unloaded
arm plus a point mass at the tool point is checked here:

* `cellPayloadArm_M`: `M_m(θ) = M(θ) + m Jᵀ J`, with `J` the Jacobian of the tool point
  `Examples.elbowArmPosition (2/5) (17/40) (49/125)` (`toolInertia_eq_jacobian`, from
  `Examples.jac_elbowArmPosition`); so the kinetic energy is the arm's plus `½ m ‖J θ̇‖²`
  (`cellPayloadArm_kineticEnergy`);
* `cellPayloadArm_potentialEnergy`: the potential energy is the arm's plus `m g` times the tool
  point's height;
* `cellPayloadArm_C_mulVec`, `cellPayloadArm_N`: the Coriolis and centrifugal term and the
  gravity term are the arm's plus `m` times explicit terms `toolCoriolis`, `toolGravity`.

**The disturbance.** `payloadDisturbance m θ θ̇ θ̈ τ_f` is what the plant's equations add to the
controller's model: if the loaded arm obeys `M_m θ̈ + C_m θ̇ + N_m = τ − τ_f`, the unloaded model
obeys `M θ̈ + C θ̇ + N = τ + d` with this `d` (`payloadDisturbance_spec`), and
`d = −m (toolInertia θ̈ + toolCoriolis + toolGravity) − τ_f` (`payloadDisturbance_eq`).

**The bound.** `cellArm_payload_accel_abs_le`: under computed torque with the unloaded model, the
actual acceleration is `θ̈ = u + w` with `u` the commanded acceleration and `w = M⁻¹ d`, and `d`
depends on `θ̈`; eliminating `θ̈` exactly (`(M + m Jᵀ J) w = −m (Jᵀ J u + …) − τ_f`, with
`M + m Jᵀ J` positive definite, so no small-gain condition is needed) and bounding by Cramer's rule
on the block-diagonal loaded inertia gives `|wᵢ| ≤ 192` rad/s² for every joint, whenever the
commanded acceleration is at most `(583, 580, 580)` rad/s², the joint speeds at most
`(15/2, 29/5, 29/5)` rad/s, the forearm's mass centre at horizontal reach at least `29/80` m, and
`1080 m + (27/2) (f_c + (29/5) f_v) ≤ 192` (kg, N m, N m s).

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); lengths in m, masses in kg, torques in N m, speeds in rad/s, accelerations in rad/s².
The arm's numbers, the payload's location, the friction model and the bounds are design
statements, not from MLS. A checked statement here concerns the stated model only, not a physical
arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- **The cell arm with a point mass `m` (kg) at the tool point (MLS Example 4.3, p. 172, as
`Examples.threeLinkModel`; the forearm and the point mass as one rigid body, MLS pp. 161–162).**
The forearm's mass `49/10 + m` kg, its mass centre at `(49/10 · 3/10 + m · 49/125)/(49/10 + m)` m
from the elbow on the forearm's axis, and its principal moments about that point
`39/500 + μ (23/250)²`, `9/1000`, `39/500 + μ (23/250)²` kg m² with `μ = (49/10) m/(49/10 + m)`
(the parallel-axis shift of the forearm and of the point mass to the common mass centre); every
other parameter is that of `cellArm` (SI units, gravity `981/100` m/s² along `−z`). At `m = 0` it
is `cellArm` (`cellPayloadArm_zero`). A design definition, not from MLS. -/
def cellPayloadArm (m : ℝ) : ManipulatorModel 3 :=
  Examples.threeLinkModel (37 / 10) (8393 / 1000) (49 / 10 + m) (1 / 5) (17 / 80)
    ((49 / 10 * (3 / 10) + m * (49 / 125)) / (49 / 10 + m)) (2 / 5) (17 / 40)
    ![103 / 10000, 103 / 10000, 67 / 10000] ![67 / 500, 3 / 200, 67 / 500]
    ![39 / 500 + 49 / 10 * m / (49 / 10 + m) * (23 / 250) ^ 2, 9 / 1000,
      39 / 500 + 49 / 10 * m / (49 / 10 + m) * (23 / 250) ^ 2] (981 / 100)

/-- **The loaded cell arm as a robot `(M, C, N)` (MLS p. 303).** -/
def cellPayloadRobot (m : ℝ) : Control.RobotSystem 3 :=
  (cellPayloadArm m).toRobotSystem

/-- **Without a payload the loaded arm is the cell arm.** -/
theorem cellPayloadArm_zero : cellPayloadArm 0 = cellArm := by
  simp only [cellPayloadArm, cellArm]
  norm_num

/-- **The payload's inertia per unit mass (a design statement, not from MLS):** the matrix
`Jᵀ J` of the tool point's Jacobian, written out (`toolInertia_eq_jacobian`): the yaw entry
`R²` with `R = (17/40) cos θ₁ + (49/125) cos(θ₁ + θ₂)` the tool's horizontal reach (m), and the
shoulder–elbow block of a point at distance `49/125` m along a forearm of a planar two-link arm with
upper arm `17/40` m, depending only on `cos θ₂` (m²). -/
def toolInertia (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) ^ 2, 0, 0;
    0, 334289 / 1000000 + 833 / 2500 * Real.cos (θ 2), 2401 / 15625 + 833 / 5000 * Real.cos (θ 2);
    0, 2401 / 15625 + 833 / 5000 * Real.cos (θ 2), 2401 / 15625]

/-- **The payload's Coriolis and centrifugal term per unit mass (MLS eqs. (4.22)–(4.23),
pp. 170–171, for the inertia `Jᵀ J`; a design statement, not from MLS)**, at the configuration
`θ` (rad) and joint speeds `v` (rad/s), with `R` the tool's horizontal reach and
`Z = (17/40) sin θ₁ + (49/125) sin(θ₁ + θ₂)` its drop below the shoulder (m). -/
def toolCoriolis (θ v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-2 * (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) * v 0 *
      ((17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) * v 1 +
        49 / 125 * Real.sin (θ 1 + θ 2) * v 2),
    (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) *
        (17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) * v 0 ^ 2 -
      833 / 5000 * Real.sin (θ 2) * (2 * v 1 * v 2 + v 2 ^ 2),
    49 / 125 * Real.sin (θ 1 + θ 2) *
        (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) * v 0 ^ 2 +
      833 / 5000 * Real.sin (θ 2) * v 1 ^ 2]

/-- **The payload's gravity term per unit mass (MLS p. 169 and eq. (4.25), p. 175, for a point at
the tool; a design statement, not from MLS):** `g` times the gradient of the tool point's height,
`(0, −g R, −g (49/125) cos(θ₁ + θ₂))` (m/s² · m), with `g = 981/100` m/s². -/
def toolGravity (θ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0, -(981 / 100) * (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)),
    -(981 / 100) * (49 / 125 * Real.cos (θ 1 + θ 2))]

/-- **The payload's inertia per unit mass is `Jᵀ J` for the Jacobian of the tool point (MLS
eq. (4.19), p. 168, for a point mass; the tool point of the cell arm, MLS Example 3.2 with
`Examples.jac_elbowArmPosition`).** -/
theorem toolInertia_eq_jacobian (θ : Fin 3 → ℝ) :
    toolInertia θ =
      (MapJacobian.jac (Examples.elbowArmPosition (2 / 5) (17 / 40) (49 / 125)) θ)ᵀ *
        MapJacobian.jac (Examples.elbowArmPosition (2 / 5) (17 / 40) (49 / 125)) θ := by
  rw [Examples.jac_elbowArmPosition]
  have h0 := Real.sin_sq_add_cos_sq (θ 0)
  have hs1 := Real.sin_sq_add_cos_sq (θ 1)
  have hs12 := Real.sin_sq_add_cos_sq (θ 1 + θ 2)
  have hc2 : Real.cos (θ 2) = Real.cos (θ 1 + θ 2) * Real.cos (θ 1) +
      Real.sin (θ 1 + θ 2) * Real.sin (θ 1) := by
    rw [← Real.cos_sub]
    ring_nf
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toolInertia, Examples.elbowArmPositionJacobian, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination
      (-(17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) ^ 2) * h0
  · ring
  · ring
  · ring
  · linear_combination
      (-(17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) ^ 2) * h0 -
        (17 / 40) ^ 2 * hs1 - (49 / 125) ^ 2 * hs12 + 2 * (17 / 40) * (49 / 125) * hc2
  · linear_combination
      (-(17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) * (49 / 125) *
          Real.sin (θ 1 + θ 2)) * h0 - (49 / 125) ^ 2 * hs12 + (17 / 40) * (49 / 125) * hc2
  · ring
  · linear_combination
      (-(17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) * (49 / 125) *
          Real.sin (θ 1 + θ 2)) * h0 - (49 / 125) ^ 2 * hs12 + (17 / 40) * (49 / 125) * hc2
  · linear_combination (-(49 / 125) ^ 2 * Real.sin (θ 1 + θ 2) ^ 2) * h0 -
      (49 / 125) ^ 2 * hs12

/-- **The loaded arm's inertia matrix is the arm's plus `m Jᵀ J` (MLS eq. (4.19), p. 168, and
p. 173 for the arm's matrix, `Examples.threeLinkArm_massMatrix`), for `m ≥ 0` (kg).** -/
theorem cellPayloadArm_M {m : ℝ} (hm : 0 ≤ m) (θ : Fin 3 → ℝ) :
    (cellPayloadArm m).M θ = cellArm.M θ + m • toolInertia θ := by
  have hm' : (49 / 10 + m) ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [cellPayloadArm, cellArm, ManipulatorModel.M, Examples.threeLinkModel,
      Examples.threeLinkArm_massMatrix, toolInertia]
  all_goals try field_simp
  all_goals try ring_nf

/-- **The kinetic energy of the loaded arm is the arm's plus that of the point mass (MLS
eq. (4.18), p. 168, and eq. (4.8), p. 161):** `T_m(θ, θ̇) = T(θ, θ̇) + ½ m ‖J θ̇‖²`, with `J` the
Jacobian of the tool point, so `J θ̇` is the tool point's velocity (m/s), for `m ≥ 0` (kg). -/
theorem cellPayloadArm_kineticEnergy {m : ℝ} (hm : 0 ≤ m) (θ θ' : Fin 3 → ℝ) :
    (cellPayloadArm m).chain.kineticEnergy θ θ' =
      cellArm.chain.kineticEnergy θ θ' + 1 / 2 * m *
        ((MapJacobian.jac (Examples.elbowArmPosition (2 / 5) (17 / 40) (49 / 125)) θ *ᵥ θ') ⬝ᵥ
          (MapJacobian.jac (Examples.elbowArmPosition (2 / 5) (17 / 40) (49 / 125)) θ *ᵥ θ')) := by
  have h := cellPayloadArm_M hm θ
  simp only [ManipulatorModel.M] at h
  set J := MapJacobian.jac (Examples.elbowArmPosition (2 / 5) (17 / 40) (49 / 125)) θ
  have key : θ' ⬝ᵥ ((Jᵀ * J) *ᵥ θ') = (J *ᵥ θ') ⬝ᵥ (J *ᵥ θ') := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [InertialChain.kineticEnergy, InertialChain.kineticEnergy, h, toolInertia_eq_jacobian,
    Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, key, smul_eq_mul]
  ring

/-- **The potential energy of the loaded arm is the arm's plus `m g` times the tool point's height
(MLS p. 169 and p. 174 for the arm's heights, `Examples.threeLinkArm_potentialEnergy`)**, for
`m ≥ 0` (kg), `g = 981/100` m/s², heights in m. -/
theorem cellPayloadArm_potentialEnergy {m : ℝ} (hm : 0 ≤ m) (θ : Fin 3 → ℝ) :
    (cellPayloadArm m).chain.potentialEnergy (cellPayloadArm m).mass (cellPayloadArm m).gravity
        (cellPayloadArm m).up θ =
      cellArm.chain.potentialEnergy cellArm.mass cellArm.gravity cellArm.up θ +
        m * (981 / 100) * Examples.elbowArmPosition (2 / 5) (17 / 40) (49 / 125) θ 2 := by
  have hm' : (49 / 10 + m) ≠ 0 := by positivity
  simp only [cellPayloadArm, cellArm, Examples.threeLinkModel,
    Examples.threeLinkArm_potentialEnergy, Examples.elbowArmPosition]
  simp
  field_simp
  ring

/-- The Coriolis term of the library's three-link arm, `(C(θ, v) v)ᵢ = ∑ⱼ ∑ₖ Γᵢⱼₖ vₖ vⱼ`, with
the Christoffel symbols of MLS p. 174 (`Examples.threeLinkArm_christoffel`). -/
private theorem threeLinkModel_C_mulVec (m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ : ℝ) (I₁ I₂ I₃ : Fin 3 → ℝ)
    (g : ℝ) (θ v : Fin 3 → ℝ) (i : Fin 3) :
    ((Examples.threeLinkModel m₁ m₂ m₃ r₀ r₁ r₂ l₀ l₁ I₁ I₂ I₃ g).C θ v *ᵥ v) i =
      ∑ j, (∑ k, Examples.threeLinkArmChristoffel m₂ m₃ r₁ r₂ l₁ I₂ I₃ θ i j k * v k) * v j := by
  simp only [ManipulatorModel.C, Examples.threeLinkModel, Christoffel.coriolisMatrix, mulVec,
    dotProduct, Matrix.of_apply, Examples.threeLinkArm_christoffel]

/-- **The loaded arm's Coriolis and centrifugal term is the arm's plus `m` times
`toolCoriolis` (MLS eqs. (4.22)–(4.23), pp. 170–171, and p. 174 for the arm's Christoffel
symbols)**, for `m ≥ 0` (kg). -/
theorem cellPayloadArm_C_mulVec {m : ℝ} (hm : 0 ≤ m) (θ v : Fin 3 → ℝ) :
    (cellPayloadArm m).C θ v *ᵥ v = cellArm.C θ v *ᵥ v + m • toolCoriolis θ v := by
  have hm' : (49 / 10 + m) ≠ 0 := by positivity
  ext i
  rw [Pi.add_apply, cellPayloadArm, threeLinkModel_C_mulVec, cellArm, threeLinkModel_C_mulVec]
  fin_cases i <;>
    simp [Examples.threeLinkArmChristoffel, Fin.sum_univ_three, toolCoriolis] <;>
    field_simp <;>
    ring

/-- **The loaded arm's gravity term is the arm's plus `m` times `toolGravity` (MLS eq. (4.25),
p. 175, `Examples.threeLinkArm_gravityTerm`)**, for `m ≥ 0` (kg), with no further joint forces
in either model. -/
theorem cellPayloadArm_N {m : ℝ} (hm : 0 ≤ m) (θ v : Fin 3 → ℝ) :
    (cellPayloadArm m).N θ v = cellArm.N θ v + m • toolGravity θ := by
  have hm' : (49 / 10 + m) ≠ 0 := by positivity
  ext i
  fin_cases i <;>
    simp [cellPayloadArm, cellArm, ManipulatorModel.N, Examples.threeLinkModel,
      Examples.threeLinkArm_gravityTerm, toolGravity] <;>
    field_simp <;>
    ring

/-- **The disturbance that the payload and the friction add to the controller's model (a design
definition, not from MLS; MLS p. 170 for friction as a joint force).** At the configuration `θ`,
the joint speeds `v` and the joint accelerations `a` (rad, rad/s, rad/s²) with the friction torque
`τf` (N m): the unloaded model's left side `M a + C v + N` minus the loaded arm's left side
`M_m a + C_m v + N_m`, minus `τf` (N m). -/
def payloadDisturbance (m : ℝ) (θ v a τf : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cellRobot.M θ *ᵥ a + cellRobot.C θ v *ᵥ v + cellRobot.N θ v -
    ((cellPayloadRobot m).M θ *ᵥ a + (cellPayloadRobot m).C θ v *ᵥ v +
      (cellPayloadRobot m).N θ v) - τf

/-- **The disturbance is what the plant adds to the controller's model (a design statement, not
from MLS).** If the loaded arm obeys `M_m a + C_m v + N_m = τ − τf` (MLS eq. (4.47), p. 190, with
the friction as a joint force, p. 170), the unloaded model obeys `M a + C v + N = τ + d` with
`d = payloadDisturbance m θ v a τf` (N m). -/
theorem payloadDisturbance_spec {m : ℝ} {θ v a τ τf : Fin 3 → ℝ}
    (h : (cellPayloadRobot m).M θ *ᵥ a + (cellPayloadRobot m).C θ v *ᵥ v +
      (cellPayloadRobot m).N θ v = τ - τf) :
    cellRobot.M θ *ᵥ a + cellRobot.C θ v *ᵥ v + cellRobot.N θ v =
      τ + payloadDisturbance m θ v a τf := by
  rw [payloadDisturbance, h]
  abel

/-- **The disturbance written out (a design statement, not from MLS):**
`d = −m (Jᵀ J a + toolCoriolis θ v + toolGravity θ) − τf` (N m), for `m ≥ 0` (kg). -/
theorem payloadDisturbance_eq {m : ℝ} (hm : 0 ≤ m) (θ v a τf : Fin 3 → ℝ) :
    payloadDisturbance m θ v a τf =
      -(m • (toolInertia θ *ᵥ a + toolCoriolis θ v + toolGravity θ)) - τf := by
  have hM := cellPayloadArm_M hm θ
  have hC := cellPayloadArm_C_mulVec hm θ v
  have hN := cellPayloadArm_N hm θ v
  simp only [payloadDisturbance, cellPayloadRobot, cellRobot, ManipulatorModel.toRobotSystem]
  rw [hM, hC, hN, Matrix.add_mulVec, Matrix.smul_mulVec, smul_add, smul_add]
  abel

/-! ### The acceleration the payload and the friction produce -/

/-- The cell arm's inertia matrix applied to a joint vector, written out (MLS p. 173,
`Examples.threeLinkArm_massMatrix`, with the cell's parameters). -/
private theorem cellArm_M_mulVec' (θ w : Fin 3 → ℝ) :
    cellArm.M θ *ᵥ w =
      ![(3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 + 67 / 10000 +
          67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
          8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
          49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2) * w 0,
        (12269177 / 6400000 + 2499 / 2000 * Real.cos (θ 2)) * w 1 +
          (519 / 1000 + 2499 / 4000 * Real.cos (θ 2)) * w 2,
        (519 / 1000 + 2499 / 4000 * Real.cos (θ 2)) * w 1 + 519 / 1000 * w 2] := by
  ext i
  fin_cases i <;>
    simp [cellArm, ManipulatorModel.M, Examples.threeLinkModel, Examples.threeLinkArm_massMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- The yaw entry of the cell arm's inertia matrix is at least `307/10000` kg m² plus the forearm
mass times the square of its mass centre's horizontal reach (from `sin² + cos² = 1`). -/
private theorem cellArm_yaw_lower' (θ : Fin 3 → ℝ) :
    307 / 10000 + 49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 ≤
      3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 + 67 / 10000 +
        67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
        8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
        49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq (θ 1), Real.sin_sq_add_cos_sq (θ 1 + θ 2),
    sq_nonneg (Real.cos (θ 1)), sq_nonneg (Real.cos (θ 1 + θ 2))]

/-- `|a b| ≤ A B` from `|a| ≤ A` and `|b| ≤ B`. -/
private theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- One row of a linear system solved by Cramer's rule with four terms: if `D w = ∑ pₖ xₖ` with
`D > 0`, `|pₖ| ≤ Pₖ`, `|xₖ| ≤ Xₖ` and `∑ Pₖ Xₖ ≤ A D`, then `|w| ≤ A`. -/
private theorem abs_le_of_cramer4 {D w p₁ p₂ p₃ p₄ x₁ x₂ x₃ x₄ P₁ P₂ P₃ P₄ X₁ X₂ X₃ X₄ A : ℝ}
    (hD : 0 < D) (hw : D * w = p₁ * x₁ + p₂ * x₂ + p₃ * x₃ + p₄ * x₄)
    (h₁ : |p₁| ≤ P₁) (h₂ : |p₂| ≤ P₂) (h₃ : |p₃| ≤ P₃) (h₄ : |p₄| ≤ P₄)
    (k₁ : |x₁| ≤ X₁) (k₂ : |x₂| ≤ X₂) (k₃ : |x₃| ≤ X₃) (k₄ : |x₄| ≤ X₄)
    (hsum : P₁ * X₁ + P₂ * X₂ + P₃ * X₃ + P₄ * X₄ ≤ A * D) : |w| ≤ A := by
  have e : |D * w| ≤ P₁ * X₁ + P₂ * X₂ + P₃ * X₃ + P₄ * X₄ := by
    rw [hw]
    calc |p₁ * x₁ + p₂ * x₂ + p₃ * x₃ + p₄ * x₄|
        ≤ |p₁ * x₁| + |p₂ * x₂| + |p₃ * x₃| + |p₄ * x₄| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ P₁ * X₁ + P₂ * X₂ + P₃ * X₃ + P₄ * X₄ := by
          gcongr
          · exact abs_mul_le_of h₁ k₁
          · exact abs_mul_le_of h₂ k₂
          · exact abs_mul_le_of h₃ k₃
          · exact abs_mul_le_of h₄ k₄
  rw [abs_mul, abs_of_pos hD] at e
  exact le_of_mul_le_mul_left (by linarith) hD

/-- `|α + β c| ≤ β + α c` on `c ∈ [−1, 1]` when `|α| ≤ β` (a linear function lies below the chord
of its absolute value). -/
private theorem abs_linear_le_chord {α β c : ℝ} (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) (hab : |α| ≤ β) :
    |α + β * c| ≤ β + α * c := by
  obtain ⟨h1, h2⟩ := abs_le.mp hab
  rw [abs_le]
  constructor <;> nlinarith

/-- The determinant of the shoulder–elbow block of the loaded arm is at least that of the unloaded
arm, `D₀(c) = 4643792463/6400000000 − (6245001/16000000) c²`, for `m ≥ 0` and `c ∈ [−1, 1]`. -/
private theorem block_det_ge {m c : ℝ} (hm : 0 ≤ m) (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    4643792463 / 6400000000 - 6245001 / 16000000 * c ^ 2 ≤
      (12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c)) *
          (519 / 1000 + m * (2401 / 15625)) -
        (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) ^ 2 := by
  have hcc : c ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hm (sub_nonneg.2 hcc), mul_nonneg (mul_nonneg hm hm) (sub_nonneg.2 hcc)]

/-- The elbow row's payload coefficient at the stretched elbow is the binding one: on
`c ∈ [−1, 1]`, the sum of the per-unit-payload terms of the elbow row is at most `1080 D₀(c)`. -/
private theorem elbow_payload_poly {c : ℝ} (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    580 * (4147434529 / 32000000000 + 12108694877 / 100000000000 * c) +
        580 * (21483132377 / 100000000000 + 1192023 / 125000000 * c - 2081667 / 20000000 * c ^ 2) +
        28 * (12269177 / 6400000 + 2499 / 2000 * c) + 44 * (2499 / 4000 + 519 / 1000 * c) +
        1 / 5 * (580 * (693889 / 25000000 * (1 - c ^ 2)) +
          28 * (334289 / 1000000 + 833 / 2500 * c) + 44 * (833 / 5000 + 2401 / 15625 * c)) ≤
      1080 * (4643792463 / 6400000000 - 6245001 / 16000000 * c ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ 1 + c)]

/-- On `c ∈ [−1, 1]` the friction terms of the elbow row are at most `(27/2) D₀(c)`. -/
private theorem elbow_friction_poly {c : ℝ} (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    12269177 / 6400000 + 2499 / 2000 * c + (2499 / 4000 + 519 / 1000 * c) +
        1 / 5 * (334289 / 1000000 + 833 / 2500 * c + (833 / 5000 + 2401 / 15625 * c)) ≤
      27 / 2 * (4643792463 / 6400000000 - 6245001 / 16000000 * c ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ 1 + c)]


/-- `|R Z| ≤ K/2` from `R² + Z² ≤ K`. -/
private theorem abs_mul_le_of_sq_add_sq {R Z K : ℝ} (h : R ^ 2 + Z ^ 2 ≤ K) : |R * Z| ≤ K / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (R - Z), sq_nonneg (R + Z)]

/-- The square of a speed bounded by `V` is bounded by `V²`. -/
private theorem abs_sq_le_of {x X : ℝ} (h : |x| ≤ X) : |x ^ 2| ≤ X ^ 2 := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) h 2

/-- The yaw row's Coriolis term per unit payload mass is at most `57` N m/kg in the speed box. -/
private theorem payload_q0_bound {R Z s v₀ v₁ v₂ : ℝ} (hR : |R| ≤ 817 / 1000)
    (hRZ : |R * Z| ≤ 667489 / 2000000) (hs : |s| ≤ 1) (hv₀ : |v₀| ≤ 15 / 2) (hv₁ : |v₁| ≤ 29 / 5)
    (hv₂ : |v₂| ≤ 29 / 5) : |-2 * R * v₀ * (Z * v₁ + 49 / 125 * s * v₂)| ≤ 57 := by
  have e : -2 * R * v₀ * (Z * v₁ + 49 / 125 * s * v₂) =
      -2 * (v₀ * (R * Z * v₁ + 49 / 125 * (R * s * v₂))) := by ring
  have a1 := abs_mul_le_of hRZ hv₁
  have a2 := abs_mul_le_of (abs_mul_le_of hR hs) hv₂
  have a3 : |R * Z * v₁ + 49 / 125 * (R * s * v₂)| ≤
      667489 / 2000000 * (29 / 5) + 49 / 125 * (817 / 1000 * 1 * (29 / 5)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (49 / 125 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 49 / 125)]
    linarith
  have a4 := abs_mul_le_of hv₀ a3
  rw [e, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  linarith

/-- The shoulder row's Coriolis, centrifugal and gravity terms per unit payload mass are at most
`44` N m/kg in the speed box. -/
private theorem payload_q1_bound {R Z s v₀ v₁ v₂ : ℝ} (hR : |R| ≤ 817 / 1000)
    (hRZ : |R * Z| ≤ 667489 / 2000000) (hs : |s| ≤ 1) (hv₀ : |v₀| ≤ 15 / 2) (hv₁ : |v₁| ≤ 29 / 5)
    (hv₂ : |v₂| ≤ 29 / 5) :
    |R * Z * v₀ ^ 2 - 833 / 5000 * s * (2 * v₁ * v₂ + v₂ ^ 2) - 981 / 100 * R| ≤ 44 := by
  have b0 := abs_sq_le_of hv₀
  have b12 : |2 * v₁ * v₂ + v₂ ^ 2| ≤ 2 * (29 / 5) * (29 / 5) + (29 / 5) ^ 2 := by
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_mul_le_of (abs_mul_le_of (le_of_eq (abs_two (α := ℝ))) hv₁) hv₂
    have h2 := abs_sq_le_of hv₂
    linarith
  have a1 := abs_mul_le_of hRZ b0
  have a2 := abs_mul_le_of hs b12
  have e : R * Z * v₀ ^ 2 - 833 / 5000 * s * (2 * v₁ * v₂ + v₂ ^ 2) - 981 / 100 * R =
      R * Z * v₀ ^ 2 + (-(833 / 5000) * (s * (2 * v₁ * v₂ + v₂ ^ 2)) + (-(981 / 100)) * R) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have a3 : |-(833 / 5000) * (s * (2 * v₁ * v₂ + v₂ ^ 2)) + (-(981 / 100)) * R| ≤
      833 / 5000 * (1 * (2 * (29 / 5) * (29 / 5) + (29 / 5) ^ 2)) + 981 / 100 * (817 / 1000) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (-(833 / 5000) : ℝ), abs_mul (-(981 / 100) : ℝ)]
    rw [abs_of_neg (by norm_num : (-(833 / 5000) : ℝ) < 0),
      abs_of_neg (by norm_num : (-(981 / 100) : ℝ) < 0)]
    nlinarith
  linarith

/-- The elbow row's Coriolis, centrifugal and gravity terms per unit payload mass are at most `28`
N m/kg in the speed box. -/
private theorem payload_q2_bound {R s s' c' v₀ v₁ : ℝ} (hR : |R| ≤ 817 / 1000) (hs : |s| ≤ 1)
    (hs' : |s'| ≤ 1) (hc' : |c'| ≤ 1) (hv₀ : |v₀| ≤ 15 / 2) (hv₁ : |v₁| ≤ 29 / 5) :
    |49 / 125 * s * R * v₀ ^ 2 + 833 / 5000 * s' * v₁ ^ 2 - 981 / 100 * (49 / 125 * c')| ≤ 28 := by
  have a1 := abs_mul_le_of (abs_mul_le_of hs hR) (abs_sq_le_of hv₀)
  have a2 := abs_mul_le_of hs' (abs_sq_le_of hv₁)
  have e : 49 / 125 * s * R * v₀ ^ 2 + 833 / 5000 * s' * v₁ ^ 2 - 981 / 100 * (49 / 125 * c') =
      49 / 125 * (s * R * v₀ ^ 2) + (833 / 5000 * (s' * v₁ ^ 2) +
        (-(981 / 100 * (49 / 125))) * c') := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have a3 : |833 / 5000 * (s' * v₁ ^ 2) + (-(981 / 100 * (49 / 125))) * c'| ≤
      833 / 5000 * (1 * (29 / 5) ^ 2) + 981 / 100 * (49 / 125) * 1 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (833 / 5000 : ℝ), abs_mul (-(981 / 100 * (49 / 125)) : ℝ),
      abs_of_pos (by norm_num : (0 : ℝ) < 833 / 5000),
      abs_of_neg (by norm_num : (-(981 / 100 * (49 / 125)) : ℝ) < 0)]
    nlinarith
  rw [abs_mul (49 / 125 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 49 / 125)]
  nlinarith

/-- The yaw row: with `(M₀₀ + m R²) w₀ = −(m R² u₀ + m q₀ + f₀)`, the yaw entry at least
`307/10000 + (49/10) ρ²` for a forearm reach `ρ ≥ 29/80` m, `R = ρ + (23/250) c` with `|c| ≤ 1`,
and the bounds of the data, `|w₀| ≤ 192`. -/
private theorem yaw_row_bound {m fc fv M₀₀ R ρ c w₀ u₀ q₀ f₀ : ℝ} (hm : 0 ≤ m) (hfc : 0 ≤ fc)
    (hfv : 0 ≤ fv) (hcond : 1080 * m + 27 / 2 * (fc + 29 / 5 * fv) ≤ 192) (hρ : 29 / 80 ≤ ρ)
    (hM : 307 / 10000 + 49 / 10 * ρ ^ 2 ≤ M₀₀) (hRρ : R = ρ + 23 / 250 * c) (hc : |c| ≤ 1)
    (hu : |u₀| ≤ 583) (hq : |q₀| ≤ 57) (hf : |f₀| ≤ fc + 15 / 2 * fv)
    (e : M₀₀ * w₀ = -(m * (R ^ 2 * (u₀ + w₀) + q₀)) - f₀) : |w₀| ≤ 192 := by
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hR2 : R ^ 2 ≤ (ρ + 23 / 250) ^ 2 := by
    rw [hRρ]
    nlinarith
  have hR2' : 0 ≤ R ^ 2 := sq_nonneg R
  have hK : 0 < M₀₀ + m * R ^ 2 := by nlinarith
  have e' : (M₀₀ + m * R ^ 2) * w₀ = -(m * R ^ 2) * u₀ + (-m) * q₀ + (-1) * f₀ := by
    linear_combination e
  have b1 : |(-(m * R ^ 2)) * u₀| ≤ m * R ^ 2 * 583 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hm hR2')]
    exact mul_le_mul_of_nonneg_left hu (mul_nonneg hm hR2')
  have b2 : |(-m) * q₀| ≤ m * 57 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_left hq hm
  have b3 : |(-1) * f₀| ≤ fc + 15 / 2 * fv := by rw [abs_mul]; simpa using hf
  have hsum : |(M₀₀ + m * R ^ 2) * w₀| ≤ m * R ^ 2 * 583 + m * 57 + (fc + 15 / 2 * fv) := by
    rw [e']
    refine (abs_add_le _ _).trans ?_
    have := abs_add_le ((-(m * R ^ 2)) * u₀) ((-m) * q₀)
    linarith
  -- the budget: `m (391 (ρ + 23/250)² + 57) + f_c + (15/2) f_v ≤ 192 (307/10000 + (49/10) ρ²)`
  have hp : 391 * (ρ + 23 / 250) ^ 2 + 57 ≤ 1080 * (307 / 10000 + 49 / 10 * ρ ^ 2) := by nlinarith
  have hq' : (75 : ℝ) / 58 ≤ 27 / 2 * (307 / 10000 + 49 / 10 * ρ ^ 2) := by nlinarith
  have hF : fc + 15 / 2 * fv ≤ 75 / 58 * (fc + 29 / 5 * fv) := by nlinarith
  have k1 := mul_le_mul_of_nonneg_left hp hm
  have k2 := mul_le_mul_of_nonneg_left hq' (by positivity : (0 : ℝ) ≤ fc + 29 / 5 * fv)
  have k3 := mul_le_mul_of_nonneg_left hR2 hm
  have k4 := mul_le_mul_of_nonneg_right hcond
    (by positivity : (0 : ℝ) ≤ 307 / 10000 + 49 / 10 * ρ ^ 2)
  have hbudget : m * R ^ 2 * 583 + m * 57 + (fc + 15 / 2 * fv) ≤ 192 * (M₀₀ + m * R ^ 2) := by
    nlinarith
  rw [abs_mul, abs_of_pos hK] at hsum
  exact le_of_mul_le_mul_left (by linarith) hK

/-- On `c ∈ [−1, 1]` the shoulder row's payload coefficient at zero payload,
`B₂₂ P₁₁ − B₁₂ P₁₂`, is at most `19/200` in magnitude. -/
private theorem shoulder_coeff_bound {c : ℝ} (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    |519 / 1000 * (334289 / 1000000 + 833 / 2500 * c) -
      (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)| ≤ 19 / 200 := by
  have h := mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ 1 + c)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (c + 1 / 20)]

/-- The elbow row's payload coefficient `B₁₁ P₂₂ − B₁₂ P₁₂ + m det P` is nonnegative on
`c ∈ [−1, 1]` for `m ≥ 0`. -/
private theorem elbow_coeff_nonneg {m c : ℝ} (hm : 0 ≤ m) (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ 21483132377 / 100000000000 + 1192023 / 125000000 * c - 2081667 / 20000000 * c ^ 2 +
      m * (693889 / 25000000 * (1 - c ^ 2)) := by
  have h := mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ 1 + c)
  have h' := mul_nonneg hm h
  nlinarith

/-- The shoulder–elbow block: with the loaded block `B + m P` (entries in `c = cos θ₂`), the two
rows `(B + m P) (w₁, w₂) = −(m P (u₁, u₂) + (h₁, h₂))`, `|uᵢ| ≤ 580`, `|h₁| ≤ 44 m + F`,
`|h₂| ≤ 28 m + F` and `1080 m + (27/2) F ≤ 192`, both `|w₁| ≤ 192` and `|w₂| ≤ 192`, by Cramer's
rule. -/
private theorem block_rows_bound {m F c w₁ w₂ u₁ u₂ h₁ h₂ : ℝ} (hm : 0 ≤ m) (hF : 0 ≤ F)
    (hcond : 1080 * m + 27 / 2 * F ≤ 192) (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1)
    (hu₁ : |u₁| ≤ 580) (hu₂ : |u₂| ≤ 580) (hh₁ : |h₁| ≤ 44 * m + F) (hh₂ : |h₂| ≤ 28 * m + F)
    (E₁ : (12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c)) * w₁ +
      (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) * w₂ =
      -(m * ((334289 / 1000000 + 833 / 2500 * c) * u₁ + (2401 / 15625 + 833 / 5000 * c) * u₂) +
        h₁))
    (E₂ : (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) * w₁ +
      (519 / 1000 + m * (2401 / 15625)) * w₂ =
      -(m * ((2401 / 15625 + 833 / 5000 * c) * u₁ + 2401 / 15625 * u₂) + h₂)) :
    |w₁| ≤ 192 ∧ |w₂| ≤ 192 := by
  -- the two Cramer identities
  have hw₁ : ((12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c)) *
        (519 / 1000 + m * (2401 / 15625)) -
        (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) ^ 2) * w₁ =
      (-(m * (519 / 1000 * (334289 / 1000000 + 833 / 2500 * c) -
          (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) +
          m * (693889 / 25000000 * (1 - c ^ 2))))) * u₁ +
        (-(m * (-(1192023 / 125000000) * c))) * u₂ +
        (-(519 / 1000 + m * (2401 / 15625))) * h₁ +
        (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) * h₂ := by
    linear_combination (519 / 1000 + m * (2401 / 15625)) * E₁ -
      (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) * E₂
  have hw₂ : ((12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c)) *
        (519 / 1000 + m * (2401 / 15625)) -
        (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) ^ 2) * w₂ =
      (-(m * (12108694877 / 100000000000 + 4147434529 / 32000000000 * c))) * u₁ +
        (-(m * (21483132377 / 100000000000 + 1192023 / 125000000 * c -
          2081667 / 20000000 * c ^ 2 + m * (693889 / 25000000 * (1 - c ^ 2))))) * u₂ +
        (-(12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c))) * h₂ +
        (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) * h₁ := by
    linear_combination
      (12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c)) * E₂ -
      (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) * E₁
  clear E₁ E₂
  -- the determinant
  have hm5 : m ≤ 1 / 5 := by linarith
  have h1c := mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ 1 + c)
  have hcc : c ^ 2 ≤ 1 := by linarith only [h1c]
  have hDD := block_det_ge hm hc₁ hc₂
  have hD₀ : 2145792063 / 6400000000 ≤ 4643792463 / 6400000000 - 6245001 / 16000000 * c ^ 2 := by
    linarith only [hcc]
  have hD : 0 < (12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c)) *
        (519 / 1000 + m * (2401 / 15625)) -
        (519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)) ^ 2 := by
    linarith only [hDD, hD₀]
  -- the off-diagonal entry
  have hP₁₂ : |2401 / 15625 + 833 / 5000 * c| ≤ 833 / 5000 + 2401 / 15625 * c :=
    abs_linear_le_chord hc₁ hc₂ (by norm_num [abs_of_pos])
  have hB₁₂0 : |519 / 1000 + 2499 / 4000 * c| ≤ 2499 / 4000 + 519 / 1000 * c :=
    abs_linear_le_chord hc₁ hc₂ (by norm_num [abs_of_pos])
  have hB₁₂b : |519 / 1000 + 2499 / 4000 * c + m * (2401 / 15625 + 833 / 5000 * c)| ≤
      2499 / 4000 + 519 / 1000 * c + m * (833 / 5000 + 2401 / 15625 * c) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hm]
    have := mul_le_mul_of_nonneg_left hP₁₂ hm
    linarith only [this, hB₁₂0]
  have hP₁₁ : 0 ≤ 334289 / 1000000 + 833 / 2500 * c := by linarith only [hc₁]
  have hmP₁₁ := mul_nonneg hm hP₁₁
  have hP₁₂c : 0 ≤ 833 / 5000 + 2401 / 15625 * c := by linarith only [hc₁]
  have hdP0 : 0 ≤ 693889 / 25000000 * (1 - c ^ 2) := by linarith only [hcc]
  have k1 : m * m ≤ m * (1 / 5) := mul_le_mul_of_nonneg_left hm5 hm
  have k2 : m * F ≤ 1 / 5 * F := mul_le_mul_of_nonneg_right hm5 hF
  constructor
  · -- the shoulder
    have ha₁₁ := shoulder_coeff_bound hc₁ hc₂
    have hdP : 693889 / 25000000 * (1 - c ^ 2) ≤ 693889 / 25000000 := by
      nlinarith only [sq_nonneg c]
    refine abs_le_of_cramer4 hD hw₁ (P₁ := m * (19 / 200 + m * (693889 / 25000000)))
      (P₂ := m * (1 / 100)) (P₃ := 519 / 1000 + m * (2401 / 15625))
      (P₄ := 183 / 160 + m * (33 / 100))
      (X₁ := 580) (X₂ := 580) (X₃ := 44 * m + F) (X₄ := 28 * m + F) ?_ ?_ ?_ ?_ hu₁ hu₂ hh₁ hh₂ ?_
    · rw [abs_neg, abs_mul, abs_of_nonneg hm]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hm
      rw [abs_mul, abs_of_nonneg hm, abs_of_nonneg hdP0]
      have := mul_le_mul_of_nonneg_left hdP hm
      linarith only [this, ha₁₁]
    · rw [abs_neg, abs_mul, abs_of_nonneg hm]
      refine mul_le_mul_of_nonneg_left ?_ hm
      rw [abs_le]
      constructor <;> linarith only [hc₁, hc₂]
    · rw [abs_neg, abs_of_nonneg (by positivity)]
    · refine hB₁₂b.trans ?_
      have : m * (833 / 5000 + 2401 / 15625 * c) ≤ m * (33 / 100) :=
        mul_le_mul_of_nonneg_left (by linarith only [hc₂]) hm
      linarith only [this, hc₂]
    · have k3 := mul_le_mul_of_nonneg_left (hD₀.trans hDD) (by norm_num : (0 : ℝ) ≤ 192)
      linarith only [k1, k2, k3, hcond, hm, hF]
  · -- the elbow
    have ha₂₁ : |12108694877 / 100000000000 + 4147434529 / 32000000000 * c| ≤
        4147434529 / 32000000000 + 12108694877 / 100000000000 * c :=
      abs_linear_le_chord hc₁ hc₂ (by norm_num [abs_of_pos])
    have ha₂₂ := elbow_coeff_nonneg hm hc₁ hc₂
    refine abs_le_of_cramer4 hD hw₂
      (P₁ := m * (4147434529 / 32000000000 + 12108694877 / 100000000000 * c))
      (P₂ := m * (21483132377 / 100000000000 + 1192023 / 125000000 * c -
          2081667 / 20000000 * c ^ 2 + m * (693889 / 25000000 * (1 - c ^ 2))))
      (P₃ := 12269177 / 6400000 + 2499 / 2000 * c + m * (334289 / 1000000 + 833 / 2500 * c))
      (P₄ := 2499 / 4000 + 519 / 1000 * c + m * (833 / 5000 + 2401 / 15625 * c))
      (X₁ := 580) (X₂ := 580) (X₃ := 28 * m + F) (X₄ := 44 * m + F) ?_ ?_ ?_ ?_ hu₁ hu₂ hh₂ hh₁ ?_
    · rw [abs_neg, abs_mul, abs_of_nonneg hm]
      exact mul_le_mul_of_nonneg_left ha₂₁ hm
    · rw [abs_neg, abs_of_nonneg (mul_nonneg hm ha₂₂)]
    · rw [abs_neg, abs_of_nonneg (by linarith only [hmP₁₁, hc₁])]
    · exact hB₁₂b
    · have pm := elbow_payload_poly hc₁ hc₂
      have pf := elbow_friction_poly hc₁ hc₂
      have k3 := mul_le_mul_of_nonneg_left pm hm
      have k4 := mul_le_mul_of_nonneg_left pf hF
      have hQ : 0 ≤ 580 * (693889 / 25000000 * (1 - c ^ 2)) +
          28 * (334289 / 1000000 + 833 / 2500 * c) + 44 * (833 / 5000 + 2401 / 15625 * c) := by
        linarith only [hdP0, hP₁₁, hP₁₂c]
      have hQ' : 0 ≤ 334289 / 1000000 + 833 / 2500 * c + (833 / 5000 + 2401 / 15625 * c) := by
        linarith only [hP₁₁, hP₁₂c]
      have k5 := mul_le_mul_of_nonneg_right k1 hQ
      have k6 := mul_le_mul_of_nonneg_right k2 hQ'
      have k7 := mul_le_mul_of_nonneg_left hcond
        (by linarith only [hD₀] : (0 : ℝ) ≤ 4643792463 / 6400000000 - 6245001 / 16000000 * c ^ 2)
      have k8 := mul_le_mul_of_nonneg_left hDD (by norm_num : (0 : ℝ) ≤ 192)
      linarith only [k3, k4, k5, k6, k7, k8]

/-- **The acceleration that the payload and the friction produce, for the cell arm under computed
torque with the unloaded model (MLS eq. (4.19), p. 168, eqs. (4.22)–(4.23), pp. 170–171, and
p. 173 for the inertia matrix; the bound is a design statement, not from MLS).** Let `m ≥ 0` (kg),
`f_c, f_v ≥ 0` (N m, N m s) with `1080 m + (27/2) (f_c + (29/5) f_v) ≤ 192`. Let the configuration
`θ` (rad) keep the forearm's mass centre at horizontal distance at least `29/80` m from the base
axis, the commanded acceleration `u` be at most `583`, `580`, `580` rad/s² and the joint speeds `v`
at most `15/2`, `29/5`, `29/5` rad/s in the base, the shoulder and the elbow, and the friction
torque satisfy `|fᵢ| ≤ f_c + f_v |vᵢ|` (N m). If the actual acceleration is `u + w` and
`M(θ) w` equals the disturbance `payloadDisturbance m θ v (u + w) f` (which is the case for the
loaded arm under computed torque with the unloaded model, `w = M⁻¹ d`), then `|wᵢ| ≤ 192` rad/s²
for every joint. The actual acceleration is eliminated exactly (the loaded inertia
`M + m Jᵀ J` is invertible), so no small-gain condition on `m` enters. -/
theorem cellArm_payload_accel_abs_le {m fc fv : ℝ} (hm : 0 ≤ m) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : 1080 * m + 27 / 2 * (fc + 29 / 5 * fv) ≤ 192) {θ v u w f : Fin 3 → ℝ}
    (hθ : 29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))
    (hu : ∀ i, |u i| ≤ ![583, 580, 580] i) (hv : ∀ i, |v i| ≤ ![15 / 2, 29 / 5, 29 / 5] i)
    (hf : ∀ i, |f i| ≤ fc + fv * |v i|)
    (hw : cellRobot.M θ *ᵥ w = payloadDisturbance m θ v (u + w) f) (i : Fin 3) : |w i| ≤ 192 := by
  rw [payloadDisturbance_eq hm] at hw
  change cellArm.M θ *ᵥ w = _ at hw
  rw [cellArm_M_mulVec'] at hw
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  have hw2 := congrFun hw 2
  simp [toolInertia, toolCoriolis, toolGravity, dotProduct, Fin.sum_univ_three] at hw0 hw1 hw2
  have hu0 : |u 0| ≤ 583 := by simpa using hu 0
  have hu1 : |u 1| ≤ 580 := by simpa using hu 1
  have hu2 : |u 2| ≤ 580 := by simpa using hu 2
  have hv0 : |v 0| ≤ 15 / 2 := by simpa using hv 0
  have hv1 : |v 1| ≤ 29 / 5 := by simpa using hv 1
  have hv2 : |v 2| ≤ 29 / 5 := by simpa using hv 2
  have hf0 : |f 0| ≤ fc + 15 / 2 * fv := by
    linarith [hf 0, mul_le_mul_of_nonneg_left hv0 hfv]
  have hf1 : |f 1| ≤ fc + 29 / 5 * fv := by
    linarith [hf 1, mul_le_mul_of_nonneg_left hv1 hfv]
  have hf2 : |f 2| ≤ fc + 29 / 5 * fv := by
    linarith [hf 2, mul_le_mul_of_nonneg_left hv2 hfv]
  -- the tool's reach `R` and drop `Z`
  have hRb : |17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)| ≤ 817 / 1000 := by
    have := Real.neg_one_le_cos (θ 1)
    have := Real.cos_le_one (θ 1)
    have := Real.neg_one_le_cos (θ 1 + θ 2)
    have := Real.cos_le_one (θ 1 + θ 2)
    rw [abs_le]; constructor <;> linarith
  have hRZ : |(17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) *
      (17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2))| ≤ 667489 / 2000000 := by
    have e1 := Real.sin_sq_add_cos_sq (θ 1)
    have e2 := Real.sin_sq_add_cos_sq (θ 1 + θ 2)
    have e3 : Real.cos (θ 2) = Real.cos (θ 1 + θ 2) * Real.cos (θ 1) +
        Real.sin (θ 1 + θ 2) * Real.sin (θ 1) := by
      rw [← Real.cos_sub]; ring_nf
    have hc := Real.cos_le_one (θ 2)
    have hsq : (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) ^ 2 +
        (17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) ^ 2 ≤ 667489 / 1000000 := by
      have e : (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) ^ 2 +
          (17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) ^ 2 =
          334289 / 1000000 + 833 / 2500 * Real.cos (θ 2) := by
        rw [e3]
        linear_combination (17 / 40) ^ 2 * e1 + (49 / 125) ^ 2 * e2
      rw [e]
      linarith only [hc]
    have := abs_mul_le_of_sq_add_sq hsq
    linarith only [this]
  have hq0 := payload_q0_bound hRb hRZ (Real.abs_sin_le_one (θ 1 + θ 2)) hv0 hv1 hv2
  have hq1 := payload_q1_bound hRb hRZ (Real.abs_sin_le_one (θ 2)) hv0 hv1 hv2
  have hq2 := payload_q2_bound hRb (Real.abs_sin_le_one (θ 1 + θ 2))
    (Real.abs_sin_le_one (θ 2)) (Real.abs_cos_le_one (θ 1 + θ 2)) hv0 hv1
  have r0 : |w 0| ≤ 192 :=
    yaw_row_bound hm hfc hfv hcond hθ (cellArm_yaw_lower' θ) (c := Real.cos (θ 1 + θ 2))
      (R := 17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) (by ring)
      (Real.abs_cos_le_one _) hu0 hq0 hf0 (by linear_combination hw0)
  have hblk := block_rows_bound hm (by positivity) hcond (Real.neg_one_le_cos (θ 2))
    (Real.cos_le_one (θ 2)) hu1 hu2 (w₁ := w 1) (w₂ := w 2)
    (h₁ := m * ((17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) *
        (17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) * v 0 ^ 2 -
      833 / 5000 * Real.sin (θ 2) * (2 * v 1 * v 2 + v 2 ^ 2) -
      981 / 100 * (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2))) + f 1)
    (h₂ := m * (49 / 125 * Real.sin (θ 1 + θ 2) *
        (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) * v 0 ^ 2 +
      833 / 5000 * Real.sin (θ 2) * v 1 ^ 2 - 981 / 100 * (49 / 125 * Real.cos (θ 1 + θ 2))) +
        f 2)
    ((abs_add_le _ _).trans (by
      rw [abs_mul, abs_of_nonneg hm]; linarith only [mul_le_mul_of_nonneg_left hq1 hm, hf1]))
    ((abs_add_le _ _).trans (by
      rw [abs_mul, abs_of_nonneg hm]; linarith only [mul_le_mul_of_nonneg_left hq2 hm, hf2]))
    (by linear_combination hw1) (by linear_combination hw2)
  fin_cases i
  · exact r0
  · exact hblk.1
  · exact hblk.2

end Cell
end RoboLean
