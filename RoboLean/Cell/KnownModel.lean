import RoboLean.Cell.Payload

/-!
# The cell arm with rotor inertia and a nominal payload in the controller's model

The controller of the assured cell computes its torque from a model of the arm. Here that model
carries what a deployed controller knows: the inertia of the motor rotors reflected through the
gears, `J` (kg m²) on every joint, and the nominal mass `mn` (kg) of the part held at the tool
point. The plant is the same rigid arm with its actual rotor inertia `J'` on every joint, carrying
the actual mass `m` at the tool point, under a joint friction torque `τ_f` of any form with
`|τ_f,i| ≤ f_c + f_v |θ̇ᵢ|`. What the controller does not know is the mass error `m − mn`, the
rotor-inertia error `J' − J` and the friction.

**The robot.** `cellLoadedRobot J m` is the robot `(M, C, N)` of MLS p. 303 with
`M(θ) = M_m(θ) + J I`, `C = C_m`, `N = N_m`, where `(M_m, C_m, N_m)` is the library's three-link
arm carrying the point mass `m` at the tool point (`cellPayloadArm m`: MLS Example 4.3, p. 172,
with the forearm and the point mass as one rigid body, MLS pp. 161–162). The rotor inertia enters
as a constant diagonal: a rotor turning at the joint rate through a reduction gear adds
`½ J θ̇ᵢ²` to the kinetic energy (MLS eq. (4.18), p. 168, for one more body; the gyroscopic
coupling of a rotor carried by a moving link is neglected, a modelling statement). So
`M(θ) = M₀(θ) + J I + m Jtᵀ Jt` with `M₀` the unloaded arm's inertia and `Jt` the Jacobian of the
tool point (`cellLoadedRobot_M`). The controller's model is `cellLoadedRobot J mn`, the plant
`cellLoadedRobot J' m`.

**The disturbance.** `nominalDisturbance J mn J' m θ θ̇ θ̈ τ_f` is what the plant's equations add
to the controller's model (`nominalDisturbance_spec`); written out (`nominalDisturbance_eq`) it is
`−(m − mn) (Jtᵀ Jt θ̈ + toolCoriolis + toolGravity) − (J' − J) θ̈ − τ_f`.

**The bound.** `cellLoaded_accel_abs_le`: under computed torque with the controller's model, the
actual acceleration is `u + w` with `u` the commanded acceleration, and `M̂ w = d`, where `d`
depends on the actual acceleration. Eliminating it exactly gives
`(M₀ + J' I + m Jtᵀ Jt) w = −(m − mn) (Jtᵀ Jt u + …) − (J' − J) u − τ_f`, with the plant's inertia on
the left. Cramer's rule on its block-diagonal form, expanded in the plant's rotor inertia above
`3/2` kg m² and in its mass, gives `|wᵢ| ≤ 192` rad/s² for every joint whenever the commanded
acceleration is at most `(583, 580, 580)` rad/s², the joint speeds at most `(15/2, 29/5, 29/5)`
rad/s, the forearm's mass centre at horizontal reach at least `29/80` m, the plant's rotor inertia
at least `3/2` kg m², and
`|m − mn| + (15/4) |J' − J| + (f_c + (29/5) f_v)/150 ≤ 8/5` (kg, kg m², N m, N m s).

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); lengths in m, masses in kg, inertias in kg m², torques in N m, speeds in rad/s,
accelerations in rad/s². The arm's numbers, the rotor model, the payload's location, the friction
model and the bounds are design statements, not from MLS. A checked statement here concerns the
stated rigid model only, not a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- **The cell arm with rotor inertia `J` (kg m²) on every joint and a point mass `m` (kg) at the
tool point, as a robot `(M, C, N)` (MLS p. 303; the arm of MLS Example 4.3, p. 172, as
`cellPayloadArm m`).** The inertia matrix is the loaded arm's plus `J I`, the rotors' inertia
reflected to the joints (a design definition, not from MLS: the kinetic energy of a rotor turning
at the joint rate, `½ J θ̇ᵢ²`, with the gyroscopic coupling of a rotor carried by a moving link
neglected); the Coriolis matrix and the gravity term are the loaded arm's (a constant diagonal adds
neither). The controller's model is `cellLoadedRobot J mn` with the nominal values, the plant
`cellLoadedRobot J' m` with the actual ones. SI units, gravity `981/100` m/s² along `−z`. -/
def cellLoadedRobot (J m : ℝ) : Control.RobotSystem 3 where
  M θ := (cellPayloadRobot m).M θ + J • (1 : Matrix (Fin 3) (Fin 3) ℝ)
  C θ v := (cellPayloadRobot m).C θ v
  N θ v := (cellPayloadRobot m).N θ v

/-- **The inertia matrix of the arm with rotor inertia and payload is the unloaded arm's plus `J I`
plus `m Jtᵀ Jt` (MLS eq. (4.19), p. 168; `cellPayloadArm_M`), for `m ≥ 0` (kg).** `Jt` is the
Jacobian of the tool point (`toolInertia_eq_jacobian`), `J` the rotor inertia (kg m²). -/
theorem cellLoadedRobot_M (J : ℝ) {m : ℝ} (hm : 0 ≤ m) (θ : Fin 3 → ℝ) :
    (cellLoadedRobot J m).M θ = cellArm.M θ + J • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
      m • toolInertia θ := by
  show (cellPayloadArm m).M θ + J • (1 : Matrix (Fin 3) (Fin 3) ℝ) = _
  rw [cellPayloadArm_M hm]
  abel

/-- **Without rotor inertia and payload the robot is the cell arm (a design statement, not from
MLS).** -/
theorem cellLoadedRobot_zero : cellLoadedRobot 0 0 = cellRobot := by
  have h : cellPayloadRobot 0 = cellRobot := by
    rw [cellPayloadRobot, cellPayloadArm_zero]
    rfl
  simp only [cellLoadedRobot, h, zero_smul, add_zero]

/-- **The inertia matrix of the arm with rotor inertia and payload is positive definite (MLS
Lemma 4.2(1), p. 171, for the cell arm, `cellArm_M_posDef`), for `J ≥ 0` (kg m²) and `m ≥ 0`
(kg):** the unloaded arm's inertia is positive definite, `J I` and `m Jtᵀ Jt` are positive
semidefinite. -/
theorem cellLoadedRobot_M_posDef {J m : ℝ} (hJ : 0 ≤ J) (hm : 0 ≤ m) (θ : Fin 3 → ℝ) :
    ((cellLoadedRobot J m).M θ).PosDef := by
  rw [cellLoadedRobot_M J hm]
  have h2 : (J • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hJ
  have h3 : (m • toolInertia θ).PosSemidef := by
    rw [toolInertia_eq_jacobian, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).smul hm
  exact ((cellArm_M_posDef θ).add_posSemidef h2).add_posSemidef h3

/-- **The disturbance that the mass error, the rotor-inertia error and the friction add to the
controller's model (a design definition, not from MLS; MLS p. 170 for friction as a joint
force).** At the configuration `θ`, the joint speeds `v` and the joint accelerations `a` (rad,
rad/s, rad/s²) with the friction torque `τf` (N m): the left side `M̂ a + Ĉ v + N̂` of the
controller's model `cellLoadedRobot J mn` minus the left side of the plant `cellLoadedRobot J' m`,
minus `τf` (N m). -/
def nominalDisturbance (J mn J' m : ℝ) (θ v a τf : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (cellLoadedRobot J mn).M θ *ᵥ a + (cellLoadedRobot J mn).C θ v *ᵥ v +
      (cellLoadedRobot J mn).N θ v -
    ((cellLoadedRobot J' m).M θ *ᵥ a + (cellLoadedRobot J' m).C θ v *ᵥ v +
      (cellLoadedRobot J' m).N θ v) - τf

/-- **The disturbance is what the plant adds to the controller's model (a design statement, not
from MLS).** If the plant `cellLoadedRobot J' m` obeys `M a + C v + N = τ − τf` (MLS eq. (4.47),
p. 190, with the friction as a joint force, p. 170), the controller's model `cellLoadedRobot J mn`
obeys `M̂ a + Ĉ v + N̂ = τ + d` with `d = nominalDisturbance J mn J' m θ v a τf` (N m). -/
theorem nominalDisturbance_spec {J mn J' m : ℝ} {θ v a τ τf : Fin 3 → ℝ}
    (h : (cellLoadedRobot J' m).M θ *ᵥ a + (cellLoadedRobot J' m).C θ v *ᵥ v +
      (cellLoadedRobot J' m).N θ v = τ - τf) :
    (cellLoadedRobot J mn).M θ *ᵥ a + (cellLoadedRobot J mn).C θ v *ᵥ v +
      (cellLoadedRobot J mn).N θ v = τ + nominalDisturbance J mn J' m θ v a τf := by
  rw [nominalDisturbance, h]
  abel

/-- **The disturbance written out (a design statement, not from MLS):**
`d = −(m − mn) (Jtᵀ Jt a + toolCoriolis θ v + toolGravity θ) − (J' − J) a − τf` (N m), for
`mn ≥ 0` and `m ≥ 0` (kg). -/
theorem nominalDisturbance_eq (J J' : ℝ) {mn m : ℝ} (hmn : 0 ≤ mn) (hm : 0 ≤ m)
    (θ v a τf : Fin 3 → ℝ) :
    nominalDisturbance J mn J' m θ v a τf =
      -((m - mn) • (toolInertia θ *ᵥ a + toolCoriolis θ v + toolGravity θ)) - (J' - J) • a - τf := by
  have hC : ∀ {μ : ℝ}, 0 ≤ μ → (cellLoadedRobot J μ).C θ v *ᵥ v =
      cellArm.C θ v *ᵥ v + μ • toolCoriolis θ v := fun hμ => cellPayloadArm_C_mulVec hμ θ v
  have hN : ∀ {μ : ℝ}, 0 ≤ μ → (cellLoadedRobot J μ).N θ v = cellArm.N θ v + μ • toolGravity θ :=
    fun hμ => cellPayloadArm_N hμ θ v
  have hC' : (cellLoadedRobot J' m).C θ v *ᵥ v = cellArm.C θ v *ᵥ v + m • toolCoriolis θ v :=
    cellPayloadArm_C_mulVec hm θ v
  have hN' : (cellLoadedRobot J' m).N θ v = cellArm.N θ v + m • toolGravity θ :=
    cellPayloadArm_N hm θ v
  rw [nominalDisturbance, cellLoadedRobot_M J hmn, cellLoadedRobot_M J' hm, hC hmn, hN hmn, hC', hN']
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  module

/-! ### The acceleration the errors produce -/

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



/-- The numerator of one row of Cramer's rule, bounded term by term: with `α, β, γ, δ ≥ 0`,
`|−d (α u₁ + β u₂) − γ g₁ + δ g₂| ≤ dm (α U + β U) + γ G₁ + δ G₂`. -/
private theorem abs_cramer_num_le {d α β γ δ u₁ u₂ g₁ g₂ dm U G₁ G₂ : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hd : |d| ≤ dm) (hu₁ : |u₁| ≤ U) (hu₂ : |u₂| ≤ U)
    (hg₁ : |g₁| ≤ G₁) (hg₂ : |g₂| ≤ G₂) :
    |-d * (α * u₁ + β * u₂) - γ * g₁ + δ * g₂| ≤ dm * (α * U + β * U) + γ * G₁ + δ * G₂ := by
  have hdm0 : 0 ≤ dm := (abs_nonneg d).trans hd
  have e1 : |α * u₁ + β * u₂| ≤ α * U + β * U := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
    exact add_le_add (mul_le_mul_of_nonneg_left hu₁ hα) (mul_le_mul_of_nonneg_left hu₂ hβ)
  have e3 : |-d * (α * u₁ + β * u₂)| ≤ dm * (α * U + β * U) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hd e1 (abs_nonneg _) hdm0
  have e4 : |γ * g₁| ≤ γ * G₁ := by
    rw [abs_mul, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left hg₁ hγ
  have e5 : |δ * g₂| ≤ δ * G₂ := by
    rw [abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hg₂ hδ
  have e6 := abs_add_le (-d * (α * u₁ + β * u₂) - γ * g₁) (δ * g₂)
  have e7 := abs_sub (-d * (α * u₁ + β * u₂)) (γ * g₁)
  linarith

/-- One row of Cramer's rule for the plant's shoulder–elbow block, expanded in the plant's extra
rotor inertia `j ≥ 0` and its mass `m ≥ 0`: the orders `1`, `j` and `m` of the determinant bound
the orders of the numerator, the orders `j²`, `j m` and `m²` of the determinant are nonnegative. -/
private theorem cramer_row {K₁₁ K₁₂ K₂₂ P₁₁ P₁₂ P₂₂ j m d w₁ w₂ u₁ u₂ g₁ g₂ dm U G₁ G₂ A : ℝ}
    (hj : 0 ≤ j) (hm : 0 ≤ m) (hd : |d| ≤ dm) (hu₁ : |u₁| ≤ U) (hu₂ : |u₂| ≤ U)
    (hg₁ : |g₁| ≤ G₁) (hg₂ : |g₂| ≤ G₂) (hA : 0 ≤ A)
    (hK₁₂ : 0 ≤ K₁₂) (hK₂₂ : 0 ≤ K₂₂) (hP₁₁ : 0 ≤ P₁₁) (hP₁₂ : 0 ≤ P₁₂) (hP₂₂ : 0 ≤ P₂₂)
    (hdP : 0 ≤ P₁₁ * P₂₂ - P₁₂ ^ 2)
    (ha₁ : 0 ≤ K₂₂ * P₁₁ - K₁₂ * P₁₂) (ha₂ : 0 ≤ K₂₂ * P₁₂ - K₁₂ * P₂₂)
    (hdet : 0 < K₁₁ * K₂₂ - K₁₂ ^ 2) (htr : 0 ≤ K₁₁ + K₂₂)
    (hX : 0 ≤ K₁₁ * P₂₂ + K₂₂ * P₁₁ - 2 * K₁₂ * P₁₂)
    (h0 : dm * U * ((K₂₂ * P₁₁ - K₁₂ * P₁₂) + (K₂₂ * P₁₂ - K₁₂ * P₂₂)) + K₂₂ * G₁ + K₁₂ * G₂ ≤
      A * (K₁₁ * K₂₂ - K₁₂ ^ 2))
    (hjc : dm * U * (P₁₁ + P₁₂) + G₁ ≤ A * (K₁₁ + K₂₂))
    (hmc : dm * U * (P₁₁ * P₂₂ - P₁₂ ^ 2) + P₂₂ * G₁ + P₁₂ * G₂ ≤
      A * (K₁₁ * P₂₂ + K₂₂ * P₁₁ - 2 * K₁₂ * P₁₂))
    (E₁ : (K₁₁ + j + m * P₁₁) * w₁ + (K₁₂ + m * P₁₂) * w₂ = -(d * (P₁₁ * u₁ + P₁₂ * u₂) + g₁))
    (E₂ : (K₁₂ + m * P₁₂) * w₁ + (K₂₂ + j + m * P₂₂) * w₂ = -(d * (P₁₂ * u₁ + P₂₂ * u₂) + g₂)) :
    |w₁| ≤ A := by
  have hcr : ((K₁₁ + j + m * P₁₁) * (K₂₂ + j + m * P₂₂) - (K₁₂ + m * P₁₂) ^ 2) * w₁ =
      -d * ((K₂₂ * P₁₁ - K₁₂ * P₁₂ + j * P₁₁ + m * (P₁₁ * P₂₂ - P₁₂ ^ 2)) * u₁ +
        (K₂₂ * P₁₂ - K₁₂ * P₂₂ + j * P₁₂) * u₂) - (K₂₂ + j + m * P₂₂) * g₁ +
        (K₁₂ + m * P₁₂) * g₂ := by
    linear_combination (K₂₂ + j + m * P₂₂) * E₁ - (K₁₂ + m * P₁₂) * E₂
  have hD : (K₁₁ + j + m * P₁₁) * (K₂₂ + j + m * P₂₂) - (K₁₂ + m * P₁₂) ^ 2 =
      (K₁₁ * K₂₂ - K₁₂ ^ 2) + j * (K₁₁ + K₂₂) + j ^ 2 +
        m * (K₁₁ * P₂₂ + K₂₂ * P₁₁ - 2 * K₁₂ * P₁₂) + j * m * (P₁₁ + P₂₂) +
        m ^ 2 * (P₁₁ * P₂₂ - P₁₂ ^ 2) := by ring
  have t1 : 0 ≤ j * (K₁₁ + K₂₂) := mul_nonneg hj htr
  have t2 : 0 ≤ m * (K₁₁ * P₂₂ + K₂₂ * P₁₁ - 2 * K₁₂ * P₁₂) := mul_nonneg hm hX
  have t3 : 0 ≤ j * m * (P₁₁ + P₂₂) := mul_nonneg (mul_nonneg hj hm) (add_nonneg hP₁₁ hP₂₂)
  have t4 : 0 ≤ m ^ 2 * (P₁₁ * P₂₂ - P₁₂ ^ 2) := mul_nonneg (sq_nonneg m) hdP
  have t5 := sq_nonneg j
  have hDpos : 0 < (K₁₁ + j + m * P₁₁) * (K₂₂ + j + m * P₂₂) - (K₁₂ + m * P₁₂) ^ 2 := by
    rw [hD]
    linarith
  have c1 : 0 ≤ K₂₂ * P₁₁ - K₁₂ * P₁₂ + j * P₁₁ + m * (P₁₁ * P₂₂ - P₁₂ ^ 2) := by
    have := mul_nonneg hj hP₁₁
    have := mul_nonneg hm hdP
    linarith
  have c2 : 0 ≤ K₂₂ * P₁₂ - K₁₂ * P₂₂ + j * P₁₂ := by
    have := mul_nonneg hj hP₁₂
    linarith
  have c3 : 0 ≤ K₂₂ + j + m * P₂₂ := by
    have := mul_nonneg hm hP₂₂
    linarith
  have c4 : 0 ≤ K₁₂ + m * P₁₂ := by
    have := mul_nonneg hm hP₁₂
    linarith
  have hN := abs_cramer_num_le c1 c2 c3 c4 hd hu₁ hu₂ hg₁ hg₂
  rw [← hcr, abs_mul, abs_of_pos hDpos] at hN
  have k1 := mul_le_mul_of_nonneg_left hjc hj
  have k2 := mul_le_mul_of_nonneg_left hmc hm
  have k3 := mul_nonneg hA t5
  have k4 := mul_nonneg hA t3
  have k5 := mul_nonneg hA t4
  have hfin : dm * ((K₂₂ * P₁₁ - K₁₂ * P₁₂ + j * P₁₁ + m * (P₁₁ * P₂₂ - P₁₂ ^ 2)) * U +
        (K₂₂ * P₁₂ - K₁₂ * P₂₂ + j * P₁₂) * U) + (K₂₂ + j + m * P₂₂) * G₁ +
        (K₁₂ + m * P₁₂) * G₂ ≤
      A * ((K₁₁ + j + m * P₁₁) * (K₂₂ + j + m * P₂₂) - (K₁₂ + m * P₁₂) ^ 2) := by
    rw [hD]
    linarith
  exact le_of_mul_le_mul_left (hN.trans (hfin.trans_eq (mul_comm _ _))) hDpos

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the off-diagonal entry. -/
private theorem blk_pK12 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (519 / 1000 + 2499 / 4000 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a payload entry. -/
private theorem blk_pP11 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (334289 / 1000000 + 833 / 2500 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a payload entry. -/
private theorem blk_pP12 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the payload block's determinant. -/
private theorem blk_pdP {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (334289 / 1000000 + 833 / 2500 * c) * (2401 / 15625 : ℝ) - (2401 / 15625 + 833 / 5000 * c) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a shoulder-row coefficient. -/
private theorem blk_pa1 {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a shoulder-row coefficient. -/
private theorem blk_pa2 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (2019 / 1000 : ℝ) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 : ℝ) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: an elbow-row coefficient. -/
private theorem blk_pb1 {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: an elbow-row coefficient. -/
private theorem blk_pb2 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (334289 / 1000000 + 833 / 2500 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the block's determinant. -/
private theorem blk_pdet {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 < (21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the block's trace. -/
private theorem blk_ptr {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the first-order coefficient of the determinant in the mass. -/
private theorem blk_pX {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, zeroth order, mass error. -/
private theorem blk_fS0m {c : ℝ} (hc₂ : c ≤ 1) :
    580 * (((2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) + ((2019 / 1000 : ℝ) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 : ℝ))) + 44 * (2019 / 1000 : ℝ) + 28 * (519 / 1000 + 2499 / 4000 * c) ≤ 120 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [sq_nonneg (c - 1), hc₂]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, zeroth order, rotor error. -/
private theorem blk_fS0J {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    580 * ((2019 / 1000 : ℝ) + (519 / 1000 + 2499 / 4000 * c)) ≤ 450 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, zeroth order, friction. -/
private theorem blk_fS0F {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (2019 / 1000 : ℝ) + (519 / 1000 + 2499 / 4000 * c) ≤ 4 / 5 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, order in the rotor inertia, mass error. -/
private theorem blk_fSjM {c : ℝ} (hc₂ : c ≤ 1) :
    580 * ((334289 / 1000000 + 833 / 2500 * c) + (2401 / 15625 + 833 / 5000 * c)) + 44 ≤ 120 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [sq_nonneg (c - 1), hc₂]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: both rows, order in the rotor inertia, rotor error. -/
private theorem blk_fSjJ {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    (580 : ℝ) ≤ 450 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: both rows, order in the rotor inertia, friction. -/
private theorem blk_fSjF {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    (1 : ℝ) ≤ 4 / 5 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, order in the mass, mass error. -/
private theorem blk_fSmM {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    580 * ((334289 / 1000000 + 833 / 2500 * c) * (2401 / 15625 : ℝ) - (2401 / 15625 + 833 / 5000 * c) ^ 2) + 44 * (2401 / 15625 : ℝ) + 28 * (2401 / 15625 + 833 / 5000 * c) ≤ 120 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, order in the mass, rotor error. -/
private theorem blk_fSmJ {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    580 * ((2401 / 15625 : ℝ) + (2401 / 15625 + 833 / 5000 * c)) ≤ 450 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the shoulder row, order in the mass, friction. -/
private theorem blk_fSmF {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (2401 / 15625 : ℝ) + (2401 / 15625 + 833 / 5000 * c) ≤ 4 / 5 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, zeroth order, mass error. -/
private theorem blk_fT0m {c : ℝ} (hc₂ : c ≤ 1) :
    580 * (((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) + ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (334289 / 1000000 + 833 / 2500 * c))) + 28 * (21869177 / 6400000 + 2499 / 2000 * c) + 44 * (519 / 1000 + 2499 / 4000 * c) ≤ 120 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [sq_nonneg (c - 1), hc₂]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, zeroth order, rotor error. -/
private theorem blk_fT0J {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    580 * ((21869177 / 6400000 + 2499 / 2000 * c) + (519 / 1000 + 2499 / 4000 * c)) ≤ 450 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, zeroth order, friction. -/
private theorem blk_fT0F {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (21869177 / 6400000 + 2499 / 2000 * c) + (519 / 1000 + 2499 / 4000 * c) ≤ 4 / 5 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, order in the rotor inertia, mass error. -/
private theorem blk_fTjM {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    580 * ((2401 / 15625 : ℝ) + (2401 / 15625 + 833 / 5000 * c)) + 28 ≤ 120 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, order in the mass, mass error. -/
private theorem blk_fTmM {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    580 * ((334289 / 1000000 + 833 / 2500 * c) * (2401 / 15625 : ℝ) - (2401 / 15625 + 833 / 5000 * c) ^ 2) + 28 * (334289 / 1000000 + 833 / 2500 * c) + 44 * (2401 / 15625 + 833 / 5000 * c) ≤ 120 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, order in the mass, rotor error. -/
private theorem blk_fTmJ {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    580 * ((334289 / 1000000 + 833 / 2500 * c) + (2401 / 15625 + 833 / 5000 * c)) ≤ 450 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the elbow row, order in the mass, friction. -/
private theorem blk_fTmF {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (334289 / 1000000 + 833 / 2500 * c) + (2401 / 15625 + 833 / 5000 * c) ≤ 4 / 5 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- The plant's shoulder–elbow block: with the block of the unloaded arm plus `3/2` kg m² on the
diagonal (entries in `c = cos θ₂ ∈ [−11/20, 1]`), the plant's extra rotor inertia `j ≥ 0`, its mass
`m ≥ 0`, the mass error `d` with `|d| ≤ dm`, `|uᵢ| ≤ 580`, `|g₁| ≤ 44 dm + 580 dJ + F`,
`|g₂| ≤ 28 dm + 580 dJ + F` and `120 dm + 450 dJ + (4/5) F ≤ 192`, both rows of
`(K + j I + m P) w = −(d P u + g)` give `|wᵢ| ≤ 192`. -/
private theorem block_bound {c j m d w₁ w₂ u₁ u₂ g₁ g₂ dm dJ F : ℝ} (hc₁ : -11 / 20 ≤ c)
    (hc₂ : c ≤ 1) (hj : 0 ≤ j) (hm : 0 ≤ m) (hd : |d| ≤ dm) (hdJ : 0 ≤ dJ) (hF : 0 ≤ F)
    (hcond : 120 * dm + 450 * dJ + 4 / 5 * F ≤ 192) (hu₁ : |u₁| ≤ 580) (hu₂ : |u₂| ≤ 580)
    (hg₁ : |g₁| ≤ 44 * dm + 580 * dJ + F) (hg₂ : |g₂| ≤ 28 * dm + 580 * dJ + F)
    (E₁ : ((21869177 / 6400000 + 2499 / 2000 * c) + j + m * (334289 / 1000000 + 833 / 2500 * c)) * w₁ + ((519 / 1000 + 2499 / 4000 * c) + m * (2401 / 15625 + 833 / 5000 * c)) * w₂ =
      -(d * ((334289 / 1000000 + 833 / 2500 * c) * u₁ + (2401 / 15625 + 833 / 5000 * c) * u₂) + g₁))
    (E₂ : ((519 / 1000 + 2499 / 4000 * c) + m * (2401 / 15625 + 833 / 5000 * c)) * w₁ + ((2019 / 1000 : ℝ) + j + m * (2401 / 15625 : ℝ)) * w₂ =
      -(d * ((2401 / 15625 + 833 / 5000 * c) * u₁ + (2401 / 15625 : ℝ) * u₂) + g₂)) :
    |w₁| ≤ 192 ∧ |w₂| ≤ 192 := by
  have hdm0 : 0 ≤ dm := (abs_nonneg d).trans hd
  have pK12 := blk_pK12 hc₁
  have pP11 := blk_pP11 hc₁
  have pP12 := blk_pP12 hc₁
  have pdP := blk_pdP hc₁ hc₂
  have pa1 := blk_pa1 hc₁ hc₂
  have pa2 := blk_pa2 hc₁
  have pb1 := blk_pb1 hc₁ hc₂
  have pb2 := blk_pb2 hc₁
  have pdet := blk_pdet hc₁ hc₂
  have ptr := blk_ptr hc₁
  have pX := blk_pX hc₁ hc₂
  have fS0m := blk_fS0m hc₂
  have fS0J := blk_fS0J hc₁ hc₂
  have fS0F := blk_fS0F hc₁ hc₂
  have fSjM := blk_fSjM hc₂
  have fSjJ := blk_fSjJ hc₁
  have fSjF := blk_fSjF hc₁
  have fSmM := blk_fSmM hc₁ hc₂
  have fSmJ := blk_fSmJ hc₁ hc₂
  have fSmF := blk_fSmF hc₁ hc₂
  have fT0m := blk_fT0m hc₂
  have fT0J := blk_fT0J hc₁ hc₂
  have fT0F := blk_fT0F hc₁ hc₂
  have fTjM := blk_fTjM hc₁
  have fTmM := blk_fTmM hc₁ hc₂
  have fTmJ := blk_fTmJ hc₁ hc₂
  have fTmF := blk_fTmF hc₁ hc₂
  have hD := mul_le_mul_of_nonneg_right hcond pdet.le
  have hT := mul_le_mul_of_nonneg_right hcond ptr
  have hXc := mul_le_mul_of_nonneg_right hcond pX
  constructor
  · refine cramer_row (K₁₁ := (21869177 / 6400000 + 2499 / 2000 * c)) (K₁₂ := (519 / 1000 + 2499 / 4000 * c)) (K₂₂ := (2019 / 1000 : ℝ))
      (P₁₁ := (334289 / 1000000 + 833 / 2500 * c)) (P₁₂ := (2401 / 15625 + 833 / 5000 * c)) (P₂₂ := (2401 / 15625 : ℝ)) (A := 192)
      hj hm hd hu₁ hu₂ hg₁ hg₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ E₁ E₂
    · norm_num
    · exact pK12
    · norm_num
    · exact pP11
    · exact pP12
    · norm_num
    · exact pdP
    · exact pa1
    · exact pa2
    · exact pdet
    · exact ptr
    · exact pX
    · linarith only [mul_le_mul_of_nonneg_left fS0m hdm0, mul_le_mul_of_nonneg_left fS0J hdJ,
        mul_le_mul_of_nonneg_left fS0F hF, hD]
    · linarith only [mul_le_mul_of_nonneg_left fSjM hdm0, mul_le_mul_of_nonneg_left fSjJ hdJ,
        mul_le_mul_of_nonneg_left fSjF hF, hT]
    · linarith only [mul_le_mul_of_nonneg_left fSmM hdm0, mul_le_mul_of_nonneg_left fSmJ hdJ,
        mul_le_mul_of_nonneg_left fSmF hF, hXc]
  · refine cramer_row (K₁₁ := (2019 / 1000 : ℝ)) (K₁₂ := (519 / 1000 + 2499 / 4000 * c)) (K₂₂ := (21869177 / 6400000 + 2499 / 2000 * c))
      (P₁₁ := (2401 / 15625 : ℝ)) (P₁₂ := (2401 / 15625 + 833 / 5000 * c)) (P₂₂ := (334289 / 1000000 + 833 / 2500 * c)) (A := 192)
      (w₁ := w₂) (w₂ := w₁) (u₁ := u₂) (u₂ := u₁) (g₁ := g₂) (g₂ := g₁)
      hj hm hd hu₂ hu₁ hg₂ hg₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · norm_num
    · exact pK12
    · linarith only [hc₁]
    · norm_num
    · exact pP12
    · exact pP11
    · linarith only [pdP]
    · exact pb1
    · exact pb2
    · linarith only [pdet]
    · linarith only [ptr]
    · linarith only [pX]
    · linarith only [mul_le_mul_of_nonneg_left fT0m hdm0, mul_le_mul_of_nonneg_left fT0J hdJ,
        mul_le_mul_of_nonneg_left fT0F hF, hD]
    · linarith only [mul_le_mul_of_nonneg_left fTjM hdm0, mul_le_mul_of_nonneg_left fSjJ hdJ,
        mul_le_mul_of_nonneg_left fSjF hF, hT]
    · linarith only [mul_le_mul_of_nonneg_left fTmM hdm0, mul_le_mul_of_nonneg_left fTmJ hdJ,
        mul_le_mul_of_nonneg_left fTmF hF, hXc]
    · linear_combination E₂
    · linear_combination E₁

/-- If the forearm's mass centre is at horizontal reach at least `29/80` m, the elbow angle has
`cos θ₂ ≥ −11/20`: the reach is at most the distance `√(l₁² + r₂² + 2 l₁ r₂ cos θ₂)` from the
shoulder to that mass centre. -/
private theorem cos_two_ge_of_reach {θ : Fin 3 → ℝ}
    (hθ : 29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) :
    -11 / 20 ≤ Real.cos (θ 2) := by
  have e1 := Real.sin_sq_add_cos_sq (θ 1)
  have e2 := Real.sin_sq_add_cos_sq (θ 1 + θ 2)
  have e3 : Real.cos (θ 2) = Real.cos (θ 1 + θ 2) * Real.cos (θ 1) +
      Real.sin (θ 1 + θ 2) * Real.sin (θ 1) := by
    rw [← Real.cos_sub]
    ring_nf
  have key : (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 +
      (17 / 40 * Real.sin (θ 1) + 3 / 10 * Real.sin (θ 1 + θ 2)) ^ 2 =
      (17 / 40) ^ 2 + (3 / 10) ^ 2 + 2 * (17 / 40) * (3 / 10) * Real.cos (θ 2) := by
    rw [e3]
    linear_combination (17 / 40) ^ 2 * e1 + (3 / 10) ^ 2 * e2
  have hsq := mul_self_le_mul_self (by norm_num) hθ
  nlinarith [sq_nonneg (17 / 40 * Real.sin (θ 1) + 3 / 10 * Real.sin (θ 1 + θ 2))]

/-- The yaw row: with `(M₀₀ + J' + m R²) w₀ = −(d (R² u₀ + q₀) + e u₀ + f₀)`, the yaw entry at
least `307/10000 + (49/10) ρ²` for a forearm reach `ρ ∈ [29/80, 29/40]` m, `R = ρ + (23/250) c`
with `|c| ≤ 1`, `J' ≥ 3/2`, `m ≥ 0` and the bounds of the data, `|w₀| ≤ 192`. -/
private theorem yaw_row {m J' d e dm dJ F M₀₀ R ρ c w₀ u₀ q₀ f₀ : ℝ} (hm : 0 ≤ m)
    (hJ' : 3 / 2 ≤ J') (hd : |d| ≤ dm) (he : |e| ≤ dJ) (hF : 0 ≤ F) (hf₀ : |f₀| ≤ 75 / 58 * F)
    (hcond : 120 * dm + 450 * dJ + 4 / 5 * F ≤ 192) (hρ : 29 / 80 ≤ ρ) (hρ' : ρ ≤ 29 / 40)
    (hM : 307 / 10000 + 49 / 10 * ρ ^ 2 ≤ M₀₀) (hRρ : R = ρ + 23 / 250 * c) (hc : |c| ≤ 1)
    (hu : |u₀| ≤ 583) (hq : |q₀| ≤ 57)
    (E : (M₀₀ + J' + m * R ^ 2) * w₀ = -(d * (R ^ 2 * u₀ + q₀) + e * u₀ + f₀)) : |w₀| ≤ 192 := by
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hdm0 : 0 ≤ dm := (abs_nonneg d).trans hd
  have hdJ0 : 0 ≤ dJ := (abs_nonneg e).trans he
  have hR2 : R ^ 2 ≤ (ρ + 23 / 250) ^ 2 := by
    rw [hRρ]
    nlinarith
  have hR2' : 0 ≤ R ^ 2 := sq_nonneg R
  have hmR := mul_nonneg hm hR2'
  have hY : 0 < 307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2 := by positivity
  have hpos : 0 < M₀₀ + J' + m * R ^ 2 := by linarith
  have hrhs : |-(d * (R ^ 2 * u₀ + q₀) + e * u₀ + f₀)| ≤
      dm * (583 * R ^ 2 + 57) + dJ * 583 + 75 / 58 * F := by
    rw [abs_neg]
    have a1 : |R ^ 2 * u₀ + q₀| ≤ 583 * R ^ 2 + 57 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hR2']
      nlinarith [mul_le_mul_of_nonneg_left hu hR2']
    have a2 : |d * (R ^ 2 * u₀ + q₀)| ≤ dm * (583 * R ^ 2 + 57) := by
      rw [abs_mul]
      exact mul_le_mul hd a1 (abs_nonneg _) hdm0
    have a3 : |e * u₀| ≤ dJ * 583 := by
      rw [abs_mul]
      exact mul_le_mul he hu (abs_nonneg _) hdJ0
    have a4 := abs_add_le (d * (R ^ 2 * u₀ + q₀) + e * u₀) f₀
    have a5 := abs_add_le (d * (R ^ 2 * u₀ + q₀)) (e * u₀)
    linarith
  have p1 : 583 * R ^ 2 + 57 ≤ 120 * (307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2) := by
    nlinarith [sq_nonneg ρ]
  have p2 : (583 : ℝ) ≤ 450 * (307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2) := by nlinarith [sq_nonneg ρ]
  have p3 : (75 / 58 : ℝ) ≤ 4 / 5 * (307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2) := by
    nlinarith [sq_nonneg ρ]
  have hb : dm * (583 * R ^ 2 + 57) + dJ * 583 + 75 / 58 * F ≤ 192 * (M₀₀ + J' + m * R ^ 2) := by
    have k1 := mul_le_mul_of_nonneg_left p1 hdm0
    have k2 := mul_le_mul_of_nonneg_left p2 hdJ0
    have k3 := mul_le_mul_of_nonneg_left p3 hF
    have k4 := mul_le_mul_of_nonneg_right hcond hY.le
    nlinarith
  rw [← E, abs_mul, abs_of_pos hpos] at hrhs
  exact le_of_mul_le_mul_left (by linarith) hpos

/-- `|d h + e u + f| ≤ dm H + dJ U + F` from the bounds of the three terms. -/
private theorem abs_three_le {d h e u f dm H dJ U F : ℝ} (hd : |d| ≤ dm) (hh : |h| ≤ H)
    (he : |e| ≤ dJ) (hu : |u| ≤ U) (hf : |f| ≤ F) : |d * h + e * u + f| ≤ dm * H + dJ * U + F := by
  have h1 : |d * h| ≤ dm * H := by
    rw [abs_mul]
    exact mul_le_mul hd hh (abs_nonneg _) ((abs_nonneg _).trans hd)
  have h2 : |e * u| ≤ dJ * U := by
    rw [abs_mul]
    exact mul_le_mul he hu (abs_nonneg _) ((abs_nonneg _).trans he)
  have h3 := abs_add_le (d * h + e * u) f
  have h4 := abs_add_le (d * h) (e * u)
  linarith

/-- **The acceleration that the mass error, the rotor-inertia error and the friction produce, for
the cell arm under computed torque with the controller's model (MLS eq. (4.19), p. 168,
eqs. (4.22)–(4.23), pp. 170–171, and p. 173 for the inertia matrix; the bound is a design
statement, not from MLS).** Let the nominal and the actual mass satisfy `mn, m ≥ 0` (kg), the
plant's rotor inertia `J' ≥ 3/2` (kg m²), `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0`
(N m, N m s) and `dm + (15/4) dJ + (f_c + (29/5) f_v)/150 ≤ 8/5`. Let the configuration `θ` (rad)
keep the forearm's mass centre at horizontal distance at least `29/80` m from the base axis, the
commanded acceleration `u` be at most `583`, `580`, `580` rad/s² and the joint speeds `v` at most
`15/2`, `29/5`, `29/5` rad/s in the base, the shoulder and the elbow, and the friction torque
satisfy `|fᵢ| ≤ f_c + f_v |vᵢ|` (N m). If the actual acceleration is `u + w` and `M̂(θ) w` equals
the disturbance `nominalDisturbance J mn J' m θ v (u + w) f` (which is the case for the plant
under computed torque with the controller's model `cellLoadedRobot J mn`), then `|wᵢ| ≤ 192`
rad/s² for every joint. The actual acceleration is eliminated exactly (the plant's inertia is
invertible), so no small-gain condition enters. -/
theorem cellLoaded_accel_abs_le {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn) (hm : 0 ≤ m)
    (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 15 / 4 * dJ + (fc + 29 / 5 * fv) / 150 ≤ 8 / 5) {θ v u w f : Fin 3 → ℝ}
    (hθ : 29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))
    (hu : ∀ i, |u i| ≤ ![583, 580, 580] i) (hv : ∀ i, |v i| ≤ ![15 / 2, 29 / 5, 29 / 5] i)
    (hf : ∀ i, |f i| ≤ fc + fv * |v i|)
    (hw : (cellLoadedRobot J mn).M θ *ᵥ w = nominalDisturbance J mn J' m θ v (u + w) f)
    (i : Fin 3) : |w i| ≤ 192 := by
  have hdJ0 : 0 ≤ dJ := (abs_nonneg _).trans hdJ
  have hF : 0 ≤ fc + 29 / 5 * fv := by positivity
  have hcond' : 120 * dm + 450 * dJ + 4 / 5 * (fc + 29 / 5 * fv) ≤ 192 := by linarith
  have hj : 0 ≤ J' - 3 / 2 := by linarith
  rw [nominalDisturbance_eq J J' hmn hm, cellLoadedRobot_M J hmn] at hw
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
  rw [cellArm_M_mulVec'] at hw
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  have hw2 := congrFun hw 2
  simp [toolInertia, toolCoriolis, toolGravity, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
    Matrix.vecTail, Pi.smul_apply, smul_eq_mul] at hw0 hw1 hw2
  have hu0 : |u 0| ≤ 583 := by simpa using hu 0
  have hu1 : |u 1| ≤ 580 := by simpa using hu 1
  have hu2 : |u 2| ≤ 580 := by simpa using hu 2
  have hv0 : |v 0| ≤ 15 / 2 := by simpa using hv 0
  have hv1 : |v 1| ≤ 29 / 5 := by simpa using hv 1
  have hv2 : |v 2| ≤ 29 / 5 := by simpa using hv 2
  have hf0 : |f 0| ≤ 75 / 58 * (fc + 29 / 5 * fv) := by
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
  have hρ' : 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) ≤ 29 / 40 := by
    linarith [Real.cos_le_one (θ 1), Real.cos_le_one (θ 1 + θ 2)]
  have r0 : |w 0| ≤ 192 :=
    yaw_row hm hJ' hdm hdJ hF hf0 hcond' hθ hρ' (cellArm_yaw_lower' θ) (c := Real.cos (θ 1 + θ 2))
      (R := 17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) (by ring)
      (Real.abs_cos_le_one _) hu0 hq0 (by linear_combination hw0)
  have hblk := block_bound (cos_two_ge_of_reach hθ) (Real.cos_le_one (θ 2)) hj hm hdm hdJ0 hF
    hcond' hu1 hu2 (w₁ := w 1) (w₂ := w 2)
    (g₁ := (m - mn) * ((17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) *
        (17 / 40 * Real.sin (θ 1) + 49 / 125 * Real.sin (θ 1 + θ 2)) * v 0 ^ 2 -
      833 / 5000 * Real.sin (θ 2) * (2 * v 1 * v 2 + v 2 ^ 2) -
      981 / 100 * (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2))) +
      (J' - J) * u 1 + f 1)
    (g₂ := (m - mn) * (49 / 125 * Real.sin (θ 1 + θ 2) *
        (17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) * v 0 ^ 2 +
      833 / 5000 * Real.sin (θ 2) * v 1 ^ 2 - 981 / 100 * (49 / 125 * Real.cos (θ 1 + θ 2))) +
      (J' - J) * u 2 + f 2)
    (by linarith [abs_three_le hdm hq1 hdJ hu1 hf1])
    (by linarith [abs_three_le hdm hq2 hdJ hu2 hf2])
    (by linear_combination hw1) (by linear_combination hw2)
  fin_cases i
  · exact r0
  · exact hblk.1
  · exact hblk.2

end Cell
end RoboLean
