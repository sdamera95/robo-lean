import RoboLean.Cell.KnownModel
import RoboLean.Cell.PayloadTube

/-!
# The bound of the nominal-model disturbance at the gain 50

The bound of `RoboLean.Cell.KnownModel` (`cellLoaded_accel_abs_le`, at the gain `ω = 80` rad/s)
at a second design point: the gain `ω = 50` rad/s with the same tube radius `δ = 3/100` rad, so
that the acceleration budget is `ω² δ = 75` rad/s². The controller's model carries the rotor
inertia `J` (kg m²) on every joint and the nominal mass `mn` (kg) at the tool point
(`cellLoadedRobot J mn`); the plant has the rotor inertia `J' ≥ 3/2` kg m² on every joint and the
actual mass `m` (kg) at the tool point, under a joint friction torque `f` with
`|fᵢ| ≤ f_c + f_v |θ̇ᵢ|`. Inside the first-exit tube of radius `301/10000` rad around a linked
move the commanded acceleration is at most `(230, 228, 228)` rad/s² and the joint speeds at most
`(57/10, 4, 4)` rad/s (`Loop.nominal_tube_bounds_gain50`), and the exact elimination of the
actual acceleration with Cramer's rule, expanded in the plant's rotor inertia above `3/2` kg m²
and in its mass, gives `|wᵢ| ≤ 75` rad/s² whenever
`|m − mn| + (7/2) |J' − J| + (f_c + 4 f_v)/60 ≤ 3/2` (kg, kg m², N m, N m s)
(`cellLoaded_accel_abs_le_gain50`). The friction enters with the speed `4` rad/s of the shoulder
and the elbow at this gain (`29/5` rad/s at the gain 80).

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); masses in kg, inertias in kg m², torques in N m, speeds in rad/s, accelerations in
rad/s², time in seconds. The arm's numbers, the rotor model, the payload's location, the friction
model, the scene and the bounds are design statements, not from MLS (the arm is MLS Example 4.3,
p. 172; the computed torque law MLS eq. (4.49), p. 191). A checked statement here concerns the
stated rigid model only, not a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

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

/-- The yaw row's Coriolis term per unit payload mass is at most `30` N m/kg in the speed box
`(57/10, 4, 4)` rad/s. -/
private theorem q0_bound_gain50 {R Z s v₀ v₁ v₂ : ℝ} (hR : |R| ≤ 817 / 1000)
    (hRZ : |R * Z| ≤ 667489 / 2000000) (hs : |s| ≤ 1) (hv₀ : |v₀| ≤ 57 / 10) (hv₁ : |v₁| ≤ 4)
    (hv₂ : |v₂| ≤ 4) : |-2 * R * v₀ * (Z * v₁ + 49 / 125 * s * v₂)| ≤ 30 := by
  have e : -2 * R * v₀ * (Z * v₁ + 49 / 125 * s * v₂) =
      -2 * (v₀ * (R * Z * v₁ + 49 / 125 * (R * s * v₂))) := by ring
  have a1 := abs_mul_le_of hRZ hv₁
  have a2 := abs_mul_le_of (abs_mul_le_of hR hs) hv₂
  have a3 : |R * Z * v₁ + 49 / 125 * (R * s * v₂)| ≤
      667489 / 2000000 * (4) + 49 / 125 * (817 / 1000 * 1 * (4)) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (49 / 125 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 49 / 125)]
    linarith
  have a4 := abs_mul_le_of hv₀ a3
  rw [e, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  linarith

/-- The shoulder row's Coriolis, centrifugal and gravity terms per unit payload mass are at most
`27` N m/kg in the speed box
`(57/10, 4, 4)` rad/s. -/
private theorem q1_bound_gain50 {R Z s v₀ v₁ v₂ : ℝ} (hR : |R| ≤ 817 / 1000)
    (hRZ : |R * Z| ≤ 667489 / 2000000) (hs : |s| ≤ 1) (hv₀ : |v₀| ≤ 57 / 10) (hv₁ : |v₁| ≤ 4)
    (hv₂ : |v₂| ≤ 4) :
    |R * Z * v₀ ^ 2 - 833 / 5000 * s * (2 * v₁ * v₂ + v₂ ^ 2) - 981 / 100 * R| ≤ 27 := by
  have b0 := abs_sq_le_of hv₀
  have b12 : |2 * v₁ * v₂ + v₂ ^ 2| ≤ 2 * (4) * (4) + (4) ^ 2 := by
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
      833 / 5000 * (1 * (2 * (4) * (4) + (4) ^ 2)) + 981 / 100 * (817 / 1000) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (-(833 / 5000) : ℝ), abs_mul (-(981 / 100) : ℝ)]
    rw [abs_of_neg (by norm_num : (-(833 / 5000) : ℝ) < 0),
      abs_of_neg (by norm_num : (-(981 / 100) : ℝ) < 0)]
    nlinarith
  linarith

/-- The elbow row's Coriolis, centrifugal and gravity terms per unit payload mass are at most `17`
N m/kg in the speed box `(57/10, 4, 4)` rad/s. -/
private theorem q2_bound_gain50 {R s s' c' v₀ v₁ : ℝ} (hR : |R| ≤ 817 / 1000) (hs : |s| ≤ 1)
    (hs' : |s'| ≤ 1) (hc' : |c'| ≤ 1) (hv₀ : |v₀| ≤ 57 / 10) (hv₁ : |v₁| ≤ 4) :
    |49 / 125 * s * R * v₀ ^ 2 + 833 / 5000 * s' * v₁ ^ 2 - 981 / 100 * (49 / 125 * c')| ≤ 17 := by
  have a1 := abs_mul_le_of (abs_mul_le_of hs hR) (abs_sq_le_of hv₀)
  have a2 := abs_mul_le_of hs' (abs_sq_le_of hv₁)
  have e : 49 / 125 * s * R * v₀ ^ 2 + 833 / 5000 * s' * v₁ ^ 2 - 981 / 100 * (49 / 125 * c') =
      49 / 125 * (s * R * v₀ ^ 2) + (833 / 5000 * (s' * v₁ ^ 2) +
        (-(981 / 100 * (49 / 125))) * c') := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have a3 : |833 / 5000 * (s' * v₁ ^ 2) + (-(981 / 100 * (49 / 125))) * c'| ≤
      833 / 5000 * (1 * (4) ^ 2) + 981 / 100 * (49 / 125) * 1 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (833 / 5000 : ℝ), abs_mul (-(981 / 100 * (49 / 125)) : ℝ),
      abs_of_pos (by norm_num : (0 : ℝ) < 833 / 5000),
      abs_of_neg (by norm_num : (-(981 / 100 * (49 / 125)) : ℝ) < 0)]
    nlinarith
  rw [abs_mul (49 / 125 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 49 / 125)]
  nlinarith

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the off-diagonal entry. -/
private theorem blk50_pK12 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (519 / 1000 + 2499 / 4000 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a payload entry. -/
private theorem blk50_pP11 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (334289 / 1000000 + 833 / 2500 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a payload entry. -/
private theorem blk50_pP12 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the payload block's determinant. -/
private theorem blk50_pdP {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (334289 / 1000000 + 833 / 2500 * c) * (2401 / 15625 : ℝ) - (2401 / 15625 + 833 / 5000 * c) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a shoulder-row coefficient. -/
private theorem blk50_pa1 {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: a shoulder-row coefficient. -/
private theorem blk50_pa2 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (2019 / 1000 : ℝ) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 : ℝ) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: an elbow-row coefficient. -/
private theorem blk50_pb1 {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: an elbow-row coefficient. -/
private theorem blk50_pb2 {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (334289 / 1000000 + 833 / 2500 * c) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the block's determinant. -/
private theorem blk50_pdet {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 < (21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the block's trace. -/
private theorem blk50_ptr {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block: the first-order coefficient of the determinant in the mass. -/
private theorem blk50_pX {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    0 ≤ (21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, zeroth order, mass error. -/
private theorem blk50_fS0m {c : ℝ} (hc₂ : c ≤ 1) :
    228 * (((2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) + ((2019 / 1000 : ℝ) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 : ℝ))) + 27 * (2019 / 1000 : ℝ) + 17 * (519 / 1000 + 2499 / 4000 * c) ≤ 50 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [sq_nonneg (c - 1), hc₂]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, zeroth order, rotor error. -/
private theorem blk50_fS0J {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    228 * ((2019 / 1000 : ℝ) + (519 / 1000 + 2499 / 4000 * c)) ≤ 175 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, zeroth order, friction. -/
private theorem blk50_fS0F {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (2019 / 1000 : ℝ) + (519 / 1000 + 2499 / 4000 * c) ≤ 5 / 6 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, order in the rotor inertia, mass error. -/
private theorem blk50_fSjM {c : ℝ} (hc₂ : c ≤ 1) :
    228 * ((334289 / 1000000 + 833 / 2500 * c) + (2401 / 15625 + 833 / 5000 * c)) + 27 ≤ 50 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [sq_nonneg (c - 1), hc₂]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: both rows, order in the rotor inertia, rotor error. -/
private theorem blk50_fSjJ {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    (228 : ℝ) ≤ 175 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: both rows, order in the rotor inertia, friction. -/
private theorem blk50_fSjF {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    (1 : ℝ) ≤ 5 / 6 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, order in the mass, mass error. -/
private theorem blk50_fSmM {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    228 * ((334289 / 1000000 + 833 / 2500 * c) * (2401 / 15625 : ℝ) - (2401 / 15625 + 833 / 5000 * c) ^ 2) + 27 * (2401 / 15625 : ℝ) + 17 * (2401 / 15625 + 833 / 5000 * c) ≤ 50 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, order in the mass, rotor error. -/
private theorem blk50_fSmJ {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    228 * ((2401 / 15625 : ℝ) + (2401 / 15625 + 833 / 5000 * c)) ≤ 175 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the shoulder row, order in the mass, friction. -/
private theorem blk50_fSmF {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (2401 / 15625 : ℝ) + (2401 / 15625 + 833 / 5000 * c) ≤ 5 / 6 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, zeroth order, mass error. -/
private theorem blk50_fT0m {c : ℝ} (hc₂ : c ≤ 1) :
    228 * (((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) - (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) + ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 + 833 / 5000 * c) - (519 / 1000 + 2499 / 4000 * c) * (334289 / 1000000 + 833 / 2500 * c))) + 17 * (21869177 / 6400000 + 2499 / 2000 * c) + 27 * (519 / 1000 + 2499 / 4000 * c) ≤ 50 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [sq_nonneg (c - 1), hc₂]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, zeroth order, rotor error. -/
private theorem blk50_fT0J {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    228 * ((21869177 / 6400000 + 2499 / 2000 * c) + (519 / 1000 + 2499 / 4000 * c)) ≤ 175 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, zeroth order, friction. -/
private theorem blk50_fT0F {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (21869177 / 6400000 + 2499 / 2000 * c) + (519 / 1000 + 2499 / 4000 * c) ≤ 5 / 6 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2019 / 1000 : ℝ) - (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, order in the rotor inertia, mass error. -/
private theorem blk50_fTjM {c : ℝ} (hc₁ : -11 / 20 ≤ c) :
    228 * ((2401 / 15625 : ℝ) + (2401 / 15625 + 833 / 5000 * c)) + 17 ≤ 50 * ((21869177 / 6400000 + 2499 / 2000 * c) + (2019 / 1000 : ℝ)) := by
  nlinarith [hc₁]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, order in the mass, mass error. -/
private theorem blk50_fTmM {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    228 * ((334289 / 1000000 + 833 / 2500 * c) * (2401 / 15625 : ℝ) - (2401 / 15625 + 833 / 5000 * c) ^ 2) + 17 * (334289 / 1000000 + 833 / 2500 * c) + 27 * (2401 / 15625 + 833 / 5000 * c) ≤ 50 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, order in the mass, rotor error. -/
private theorem blk50_fTmJ {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    228 * ((334289 / 1000000 + 833 / 2500 * c) + (2401 / 15625 + 833 / 5000 * c)) ≤ 175 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- A polynomial fact on `c ∈ [−11/20, 1]` for the plant's shoulder–elbow block at gain 50: the elbow row, order in the mass, friction. -/
private theorem blk50_fTmF {c : ℝ} (hc₁ : -11 / 20 ≤ c) (hc₂ : c ≤ 1) :
    (334289 / 1000000 + 833 / 2500 * c) + (2401 / 15625 + 833 / 5000 * c) ≤ 5 / 6 * ((21869177 / 6400000 + 2499 / 2000 * c) * (2401 / 15625 : ℝ) + (2019 / 1000 : ℝ) * (334289 / 1000000 + 833 / 2500 * c) - 2 * (519 / 1000 + 2499 / 4000 * c) * (2401 / 15625 + 833 / 5000 * c)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 11 / 20), sq_nonneg (c - 1)]

/-- The plant's shoulder–elbow block at gain 50: with the block of the unloaded arm plus `3/2` kg m²
on the diagonal (entries in `c = cos θ₂ ∈ [−11/20, 1]`), the plant's extra rotor inertia `j ≥ 0`,
its mass `m ≥ 0`, the mass error `d` with `|d| ≤ dm`, `|uᵢ| ≤ 228`, `|g₁| ≤ 27 dm + 228 dJ + F`,
`|g₂| ≤ 17 dm + 228 dJ + F` and `50 dm + 175 dJ + (5/6) F ≤ 75`, both rows of
`(K + j I + m P) w = −(d P u + g)` give `|wᵢ| ≤ 75`. -/
private theorem block_bound_gain50 {c j m d w₁ w₂ u₁ u₂ g₁ g₂ dm dJ F : ℝ} (hc₁ : -11 / 20 ≤ c)
    (hc₂ : c ≤ 1) (hj : 0 ≤ j) (hm : 0 ≤ m) (hd : |d| ≤ dm) (hdJ : 0 ≤ dJ) (hF : 0 ≤ F)
    (hcond : 50 * dm + 175 * dJ + 5 / 6 * F ≤ 75) (hu₁ : |u₁| ≤ 228) (hu₂ : |u₂| ≤ 228)
    (hg₁ : |g₁| ≤ 27 * dm + 228 * dJ + F) (hg₂ : |g₂| ≤ 17 * dm + 228 * dJ + F)
    (E₁ : ((21869177 / 6400000 + 2499 / 2000 * c) + j + m * (334289 / 1000000 + 833 / 2500 * c)) * w₁ + ((519 / 1000 + 2499 / 4000 * c) + m * (2401 / 15625 + 833 / 5000 * c)) * w₂ =
      -(d * ((334289 / 1000000 + 833 / 2500 * c) * u₁ + (2401 / 15625 + 833 / 5000 * c) * u₂) + g₁))
    (E₂ : ((519 / 1000 + 2499 / 4000 * c) + m * (2401 / 15625 + 833 / 5000 * c)) * w₁ + ((2019 / 1000 : ℝ) + j + m * (2401 / 15625 : ℝ)) * w₂ =
      -(d * ((2401 / 15625 + 833 / 5000 * c) * u₁ + (2401 / 15625 : ℝ) * u₂) + g₂)) :
    |w₁| ≤ 75 ∧ |w₂| ≤ 75 := by
  have hdm0 : 0 ≤ dm := (abs_nonneg d).trans hd
  have pK12 := blk50_pK12 hc₁
  have pP11 := blk50_pP11 hc₁
  have pP12 := blk50_pP12 hc₁
  have pdP := blk50_pdP hc₁ hc₂
  have pa1 := blk50_pa1 hc₁ hc₂
  have pa2 := blk50_pa2 hc₁
  have pb1 := blk50_pb1 hc₁ hc₂
  have pb2 := blk50_pb2 hc₁
  have pdet := blk50_pdet hc₁ hc₂
  have ptr := blk50_ptr hc₁
  have pX := blk50_pX hc₁ hc₂
  have fS0m := blk50_fS0m hc₂
  have fS0J := blk50_fS0J hc₁ hc₂
  have fS0F := blk50_fS0F hc₁ hc₂
  have fSjM := blk50_fSjM hc₂
  have fSjJ := blk50_fSjJ hc₁
  have fSjF := blk50_fSjF hc₁
  have fSmM := blk50_fSmM hc₁ hc₂
  have fSmJ := blk50_fSmJ hc₁ hc₂
  have fSmF := blk50_fSmF hc₁ hc₂
  have fT0m := blk50_fT0m hc₂
  have fT0J := blk50_fT0J hc₁ hc₂
  have fT0F := blk50_fT0F hc₁ hc₂
  have fTjM := blk50_fTjM hc₁
  have fTmM := blk50_fTmM hc₁ hc₂
  have fTmJ := blk50_fTmJ hc₁ hc₂
  have fTmF := blk50_fTmF hc₁ hc₂
  have hD := mul_le_mul_of_nonneg_right hcond pdet.le
  have hT := mul_le_mul_of_nonneg_right hcond ptr
  have hXc := mul_le_mul_of_nonneg_right hcond pX
  constructor
  · refine cramer_row (K₁₁ := (21869177 / 6400000 + 2499 / 2000 * c)) (K₁₂ := (519 / 1000 + 2499 / 4000 * c)) (K₂₂ := (2019 / 1000 : ℝ))
      (P₁₁ := (334289 / 1000000 + 833 / 2500 * c)) (P₁₂ := (2401 / 15625 + 833 / 5000 * c)) (P₂₂ := (2401 / 15625 : ℝ)) (A := 75)
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
      (P₁₁ := (2401 / 15625 : ℝ)) (P₁₂ := (2401 / 15625 + 833 / 5000 * c)) (P₂₂ := (334289 / 1000000 + 833 / 2500 * c)) (A := 75)
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

/-- The yaw row at gain 50: with `(M₀₀ + J' + m R²) w₀ = −(d (R² u₀ + q₀) + e u₀ + f₀)`, the yaw entry at
least `307/10000 + (49/10) ρ²` for a forearm reach `ρ ∈ [29/80, 29/40]` m, `R = ρ + (23/250) c`
with `|c| ≤ 1`, `J' ≥ 3/2`, `m ≥ 0` and the bounds of the data, `|w₀| ≤ 75`. -/
private theorem yaw_row_gain50 {m J' d e dm dJ F M₀₀ R ρ c w₀ u₀ q₀ f₀ : ℝ} (hm : 0 ≤ m)
    (hJ' : 3 / 2 ≤ J') (hd : |d| ≤ dm) (he : |e| ≤ dJ) (hF : 0 ≤ F) (hf₀ : |f₀| ≤ 57 / 40 * F)
    (hcond : 50 * dm + 175 * dJ + 5 / 6 * F ≤ 75) (hρ : 29 / 80 ≤ ρ) (hρ' : ρ ≤ 29 / 40)
    (hM : 307 / 10000 + 49 / 10 * ρ ^ 2 ≤ M₀₀) (hRρ : R = ρ + 23 / 250 * c) (hc : |c| ≤ 1)
    (hu : |u₀| ≤ 230) (hq : |q₀| ≤ 30)
    (E : (M₀₀ + J' + m * R ^ 2) * w₀ = -(d * (R ^ 2 * u₀ + q₀) + e * u₀ + f₀)) : |w₀| ≤ 75 := by
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
      dm * (230 * R ^ 2 + 30) + dJ * 230 + 57 / 40 * F := by
    rw [abs_neg]
    have a1 : |R ^ 2 * u₀ + q₀| ≤ 230 * R ^ 2 + 30 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hR2']
      nlinarith [mul_le_mul_of_nonneg_left hu hR2']
    have a2 : |d * (R ^ 2 * u₀ + q₀)| ≤ dm * (230 * R ^ 2 + 30) := by
      rw [abs_mul]
      exact mul_le_mul hd a1 (abs_nonneg _) hdm0
    have a3 : |e * u₀| ≤ dJ * 230 := by
      rw [abs_mul]
      exact mul_le_mul he hu (abs_nonneg _) hdJ0
    have a4 := abs_add_le (d * (R ^ 2 * u₀ + q₀) + e * u₀) f₀
    have a5 := abs_add_le (d * (R ^ 2 * u₀ + q₀)) (e * u₀)
    linarith
  have p1 : 230 * R ^ 2 + 30 ≤ 50 * (307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2) := by
    nlinarith [sq_nonneg ρ]
  have p2 : (230 : ℝ) ≤ 175 * (307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2) := by nlinarith [sq_nonneg ρ]
  have p3 : (57 / 40 : ℝ) ≤ 5 / 6 * (307 / 10000 + 49 / 10 * ρ ^ 2 + 3 / 2) := by
    nlinarith [sq_nonneg ρ]
  have hb : dm * (230 * R ^ 2 + 30) + dJ * 230 + 57 / 40 * F ≤ 75 * (M₀₀ + J' + m * R ^ 2) := by
    have k1 := mul_le_mul_of_nonneg_left p1 hdm0
    have k2 := mul_le_mul_of_nonneg_left p2 hdJ0
    have k3 := mul_le_mul_of_nonneg_left p3 hF
    have k4 := mul_le_mul_of_nonneg_right hcond hY.le
    nlinarith
  rw [← E, abs_mul, abs_of_pos hpos] at hrhs
  exact le_of_mul_le_mul_left (by linarith) hpos

/-- **The acceleration that the mass error, the rotor-inertia error and the friction produce at
the gain 50, for the cell arm under computed torque with the controller's model (MLS eq. (4.19),
p. 168, eqs. (4.22)–(4.23), pp. 170–171, and p. 173 for the inertia matrix; the bound is a design
statement, not from MLS).** Let the nominal and the actual mass satisfy `mn, m ≥ 0` (kg), the
plant's rotor inertia `J' ≥ 3/2` (kg m²), `|m − mn| ≤ dm`, `|J' − J| ≤ dJ`, `f_c, f_v ≥ 0`
(N m, N m s) and `dm + (7/2) dJ + (f_c + 4 f_v)/60 ≤ 3/2`. Let the configuration `θ` (rad) keep
the forearm's mass centre at horizontal distance at least `29/80` m from the base axis, the
commanded acceleration `u` be at most `230`, `228`, `228` rad/s² and the joint speeds `v` at most
`57/10`, `4`, `4` rad/s in the base, the shoulder and the elbow, and the friction torque satisfy
`|fᵢ| ≤ f_c + f_v |vᵢ|` (N m). If the actual acceleration is `u + w` and `M̂(θ) w` equals the
disturbance `nominalDisturbance J mn J' m θ v (u + w) f`, then `|wᵢ| ≤ 75` rad/s² for every
joint. -/
theorem cellLoaded_accel_abs_le_gain50 {J mn J' m dm dJ fc fv : ℝ} (hmn : 0 ≤ mn) (hm : 0 ≤ m)
    (hJ' : 3 / 2 ≤ J') (hdm : |m - mn| ≤ dm) (hdJ : |J' - J| ≤ dJ) (hfc : 0 ≤ fc) (hfv : 0 ≤ fv)
    (hcond : dm + 7 / 2 * dJ + (fc + 4 * fv) / 60 ≤ 3 / 2) {θ v u w f : Fin 3 → ℝ}
    (hθ : 29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))
    (hu : ∀ i, |u i| ≤ ![230, 228, 228] i) (hv : ∀ i, |v i| ≤ ![57 / 10, 4, 4] i)
    (hf : ∀ i, |f i| ≤ fc + fv * |v i|)
    (hw : (cellLoadedRobot J mn).M θ *ᵥ w = nominalDisturbance J mn J' m θ v (u + w) f)
    (i : Fin 3) : |w i| ≤ 75 := by
  have hdJ0 : 0 ≤ dJ := (abs_nonneg _).trans hdJ
  have hF : 0 ≤ fc + 4 * fv := by positivity
  have hcond' : 50 * dm + 175 * dJ + 5 / 6 * (fc + 4 * fv) ≤ 75 := by linarith
  have hj : 0 ≤ J' - 3 / 2 := by linarith
  rw [nominalDisturbance_eq J J' hmn hm, cellLoadedRobot_M J hmn] at hw
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
  rw [cellArm_M_mulVec'] at hw
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  have hw2 := congrFun hw 2
  simp [toolInertia, toolCoriolis, toolGravity, dotProduct, Fin.sum_univ_three, Matrix.vecHead,
    Matrix.vecTail, Pi.smul_apply, smul_eq_mul] at hw0 hw1 hw2
  have hu0 : |u 0| ≤ 230 := by simpa using hu 0
  have hu1 : |u 1| ≤ 228 := by simpa using hu 1
  have hu2 : |u 2| ≤ 228 := by simpa using hu 2
  have hv0 : |v 0| ≤ 57 / 10 := by simpa using hv 0
  have hv1 : |v 1| ≤ 4 := by simpa using hv 1
  have hv2 : |v 2| ≤ 4 := by simpa using hv 2
  have hf0 : |f 0| ≤ 57 / 40 * (fc + 4 * fv) := by
    linarith [hf 0, mul_le_mul_of_nonneg_left hv0 hfv]
  have hf1 : |f 1| ≤ fc + 4 * fv := by
    linarith [hf 1, mul_le_mul_of_nonneg_left hv1 hfv]
  have hf2 : |f 2| ≤ fc + 4 * fv := by
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
  have hq0 := q0_bound_gain50 hRb hRZ (Real.abs_sin_le_one (θ 1 + θ 2)) hv0 hv1 hv2
  have hq1 := q1_bound_gain50 hRb hRZ (Real.abs_sin_le_one (θ 2)) hv0 hv1 hv2
  have hq2 := q2_bound_gain50 hRb (Real.abs_sin_le_one (θ 1 + θ 2))
    (Real.abs_sin_le_one (θ 2)) (Real.abs_cos_le_one (θ 1 + θ 2)) hv0 hv1
  have hρ' : 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) ≤ 29 / 40 := by
    linarith [Real.cos_le_one (θ 1), Real.cos_le_one (θ 1 + θ 2)]
  have r0 : |w 0| ≤ 75 :=
    yaw_row_gain50 hm hJ' hdm hdJ hF hf0 hcond' hθ hρ' (cellArm_yaw_lower' θ) (c := Real.cos (θ 1 + θ 2))
      (R := 17 / 40 * Real.cos (θ 1) + 49 / 125 * Real.cos (θ 1 + θ 2)) (by ring)
      (Real.abs_cos_le_one _) hu0 hq0 (by linear_combination hw0)
  have hblk := block_bound_gain50 (cos_two_ge_of_reach hθ) (Real.cos_le_one (θ 2)) hj hm hdm hdJ0 hF
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

/-- If the shoulder and the forearm are both within `π/3` of the horizontal,
`|θ₁| ≤ π/3` and `|θ₁ + θ₂| ≤ π/3` (radians), the forearm's mass centre is at horizontal
distance at least `29/80` m from the base axis. -/
private theorem reach_of_abs_le_pi_div_three {θ : Fin 3 → ℝ}
    (h₁ : |θ 1| ≤ Real.pi / 3) (h₁₂ : |θ 1 + θ 2| ≤ Real.pi / 3) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  have hc : ∀ y : ℝ, |y| ≤ Real.pi / 3 → 1 / 2 ≤ Real.cos y := fun y hy => by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hy
  linarith [hc _ h₁, hc _ h₁₂]

end Cell

namespace Cell.Loop

open Set Supervisor

/-- Every configuration within `1/10` rad (each joint) of a point of the segment between two
waypoints linked by the supervisor's link test keeps the forearm's mass centre at horizontal
distance at least `29/80` m from the base axis: such a configuration lies in a cell inflated by
`1/10`, hence in the joint envelope (shoulder at most `51°` in magnitude, shoulder plus elbow at
most `57°` in magnitude). -/
private theorem reach_linked {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) {p : Fin 3 → ℝ}
    (hp : p ∈ segment ℝ (DegPoint.toRad a) (DegPoint.toRad g)) {θ : Fin 3 → ℝ}
    (hθ : ∀ i, |θ i - p i| ≤ 1 / 10) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  obtain ⟨B, hB, ha, hb⟩ := sceneLinked_of_linked_eq_true hag
  have hpB : p ∈ B.radSet 0 :=
    (B.convex_radSet 0).segment_subset (DegBox.toRad_mem_radSet ha) (DegBox.toRad_mem_radSet hb) hp
  have hθE := radSet_subset_jointEnvelope B hB (DegBox.mem_radSet_of_abs_sub_le hpB hθ)
  have hπ := Real.pi_pos
  obtain ⟨h11, h12⟩ := hθE 1
  obtain ⟨h21, h22⟩ := hθE 2
  simp [DegPoint.toRad, degToRad, jointEnvelope] at h11 h12 h21 h22
  apply reach_of_abs_le_pi_div_three
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- The travel of a linked move in each joint: two waypoints linked by the supervisor's link test
lie in one cell, hence in the joint envelope, so they differ by at most `162°` (`9π/10` rad) on
the base and `57°` (`19π/60` rad) on the shoulder and the elbow. -/
private theorem abs_toRad_sub_le_of_linked {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) (i : Fin 3) :
    |DegPoint.toRad g i - DegPoint.toRad a i| ≤ ![9 / 10, 19 / 60, 19 / 60] i * Real.pi := by
  obtain ⟨B, hB, ha, hb⟩ := sceneLinked_of_linked_eq_true hag
  have hE : ∀ w : Waypoint, B.Contains w → DegPoint.toRad w ∈ jointEnvelope.radSet 0 :=
    fun w hw => radSet_subset_jointEnvelope B hB
      (B.radSet_mono (by norm_num) (DegBox.toRad_mem_radSet hw))
  have hπ := Real.pi_pos
  obtain ⟨h1, h2⟩ := hE a ha i
  obtain ⟨h3, h4⟩ := hE g hb i
  rw [abs_le]
  fin_cases i <;> simp [DegPoint.toRad, degToRad, jointEnvelope] at h1 h2 h3 h4 ⊢ <;>
    constructor <;> linarith

/-- **The tube bounds along a linked move at the gain `ω = 50` rad/s (a design statement, not from
MLS; the commanded acceleration is that of the computed torque law, MLS eq. (4.49), p. 191, with
`K_p = ω² I` and `K_v = 2ω I`).** Let `a, g` be waypoints linked by the supervisor's link test
for the loop data `openCellParams h T δa va`, `r` the quintic reference from `a` to `g` admitted
at `t₀` with duration `2` s, and `(θ, θ̇)` (rad, rad/s) in the tube `InTube 50 (301/10000)`
around `(r(s), ṙ(s))` at some time `s`. Then the forearm's mass centre is at horizontal distance
at least `29/80` m from the base axis; the commanded acceleration
`r̈ᵢ(s) − 100 (θ̇ᵢ − ṙᵢ(s)) − 2500 (θᵢ − rᵢ(s))` is at most `230` rad/s² in magnitude on the base
and `228` rad/s² on the shoulder and the elbow; and the joint speed `|θ̇ᵢ|` is at most `57/10`
rad/s on the base and `4` rad/s on the shoulder and the elbow. -/
theorem nominal_tube_bounds_gain50 {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) {t₀ s : ℝ} {θ θ' : Fin 3 → ℝ}
    (hin : Cell.InTube 50 (301 / 10000) θ θ'
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s)) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) ∧
    (∀ i, |moveRefDeriv2 (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s i -
        2 * 50 * (θ' i - moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s i) -
        50 ^ 2 * (θ i - moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ 2 s i)| ≤
      ![230, 228, 228] i) ∧
    ∀ i, |θ' i| ≤ ![57 / 10, 4, 4] i := by
  have hπ := Real.pi_pos
  have hπ' := Real.pi_lt_d4
  refine ⟨reach_linked hag (moveRef_mem_segment _ _ _ _ _)
    (fun i => (hin i).1.trans (by norm_num)), fun i => ?_, fun i => ?_⟩
  · have h2 := abs_moveRefDeriv2_apply_le (a := DegPoint.toRad a) (b := DegPoint.toRad g)
      (t₀ := t₀) (by norm_num : (0 : ℝ) < 2) s i
    have hg := abs_toRad_sub_le_of_linked hag i
    have hk : 6 * (![9 / 10, 19 / 60, 19 / 60] i * Real.pi) / 2 ^ 2 + 7500 * (301 / 10000) ≤
        ![230, 228, 228] i := by
      fin_cases i <;> norm_num <;> linarith
    obtain ⟨he, hz⟩ := hin i
    rw [abs_le] at he hz h2 ⊢
    constructor <;> linarith
  · have h1 := abs_moveRefDeriv_apply_le (a := DegPoint.toRad a) (b := DegPoint.toRad g)
      (t₀ := t₀) (by norm_num : (0 : ℝ) < 2) s i
    have hg := abs_toRad_sub_le_of_linked hag i
    have hk : 15 / 8 * (![9 / 10, 19 / 60, 19 / 60] i * Real.pi) / 2 + 100 * (301 / 10000) ≤
        ![57 / 10, 4, 4] i := by
      fin_cases i <;> norm_num <;> linarith
    obtain ⟨he, hz⟩ := hin i
    rw [abs_le] at he hz h1 ⊢
    constructor <;> linarith

end Cell.Loop
end RoboLean
