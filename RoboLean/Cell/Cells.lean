import RoboLean.Cell.Scene
import RoboLean.Cell.GeometryLipschitz

/-!
# Clearance certificates of the scene's cells

For each of the three cells of the scene (`pickCell`, `crossCell`, `placeCell`) and each of the four
obstacles (`table`, `divider`, `shelf`, `rearWall`), a separating plane `(n, β)` with `n ⬝ᵥ n ≤ 1`
certifies that at every configuration of the cell inflated by `1/20` rad in each joint the shoulder,
the elbow point and the tool point satisfy `n ⬝ᵥ p ≥ β + ρ + c`, `ρ = 3/50` the link radius and
`c = 3/100` the clearance, while the obstacle lies in `n ⬝ᵥ p ≤ β`. Hence every point of both links
is at Euclidean distance at least `ρ + c` from every obstacle, and every point of the two link
capsules of radius `ρ` at distance at least `c` (`cell_clear`, `cell_capsule_clear`). The
trigonometric bounds use monotonicity of `sin` and `cos`, `|sin x − sin y| ≤ |x − y|`, the exact
values of `sin` and `cos` at `π/6` and `π/4`, `sin x ≤ x` for `x ≥ 0`, and `3 < π < 3.15`. The arm
is that of MLS Example 3.2 (pp. 89–91); the scene, the cells and the certificates are design
statements, not from MLS.
-/

noncomputable section

open Real

namespace RoboLean.Cell

open RoboLean.Examples

/-! ### Trigonometric steps and the two shapes of certificate -/

/-- `sin (x + d) ≤ sin x + d` for `d ≥ 0` (sine is `1`-Lipschitz). -/
private theorem sin_add_le_add (x d : ℝ) (hd : 0 ≤ d) : sin (x + d) ≤ sin x + d := by
  have h := Real.abs_sin_sub_sin_le (x + d) x
  rw [add_sub_cancel_left, abs_of_nonneg hd] at h
  linarith [le_abs_self (sin (x + d) - sin x)]

/-- `sin x − d ≤ sin (x − d)` for `d ≥ 0` (sine is `1`-Lipschitz). -/
private theorem sub_le_sin_sub (x d : ℝ) (hd : 0 ≤ d) : sin x - d ≤ sin (x - d) := by
  have h := Real.abs_sin_sub_sin_le x (x - d)
  rw [sub_sub_cancel, abs_of_nonneg hd] at h
  linarith [le_abs_self (sin x - sin (x - d))]

/-- `cos (x − d) ≤ cos x + d` for `d ≥ 0` (cosine is `1`-Lipschitz). -/
private theorem cos_sub_le_add (x d : ℝ) (hd : 0 ≤ d) : cos (x - d) ≤ cos x + d := by
  have h := Real.abs_cos_sub_cos_le (x - d) x
  rw [show x - d - x = -d by ring, abs_neg, abs_of_nonneg hd] at h
  linarith [le_abs_self (cos (x - d) - cos x)]

/-- `1 ≤ √2`. -/
private theorem one_le_sqrt_two : (1 : ℝ) ≤ √2 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- A vertical plane through the base axis side: with `n = (u, v, 0)`, `β + r ≤ 0`, nonnegative
horizontal reaches and a nonnegative yaw factor `−u sin θ₀ + v cos θ₀`, the plane is a certificate.
-/
private theorem vertical_cert {l₀ l₁ l₂ r β u v : ℝ} {O S : Set (Fin 3 → ℝ)}
    (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (hn : u * u + v * v ≤ 1) (hβ : β + r ≤ 0)
    (hO : ∀ p ∈ O, u * p 0 + v * p 1 ≤ β)
    (hS : ∀ θ ∈ S, 0 ≤ cos (θ 1) ∧ 0 ≤ cos (θ 1 + θ 2) ∧
      0 ≤ -u * sin (θ 0) + v * cos (θ 0)) :
    IsArmPlaneCert l₀ l₁ l₂ O S r ![u, v, 0] β := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [dotProduct, Fin.sum_univ_three]
    linarith
  · intro p hp
    simp [dotProduct, Fin.sum_univ_three]
    linarith [hO p hp]
  · simp [dotProduct, Fin.sum_univ_three, shoulderPoint]
    linarith
  · intro θ hθ
    obtain ⟨hc1, hc12, hy⟩ := hS θ hθ
    have e1 : ![u, v, 0] ⬝ᵥ elbowPoint l₀ l₁ θ =
        (l₁ * cos (θ 1)) * (-u * sin (θ 0) + v * cos (θ 0)) := by
      simp [dotProduct, Fin.sum_univ_three, elbowPoint, elbowArmPosition]
      ring
    have e2 : ![u, v, 0] ⬝ᵥ elbowArmPosition l₀ l₁ l₂ θ =
        (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) * (-u * sin (θ 0) + v * cos (θ 0)) := by
      simp [dotProduct, Fin.sum_univ_three, elbowArmPosition]
      ring
    rw [e1, e2]
    constructor
    · have := mul_nonneg (mul_nonneg h₁ hc1) hy
      linarith
    · have := mul_nonneg (add_nonneg (mul_nonneg h₁ hc1) (mul_nonneg h₂ hc12)) hy
      linarith

/-- A horizontal plane `z = β`: the obstacle below it and the shoulder, elbow and tool heights at
least `β + r` give a certificate. -/
private theorem horizontal_cert {l₀ l₁ l₂ r β : ℝ} {O S : Set (Fin 3 → ℝ)}
    (hO : ∀ p ∈ O, p 2 ≤ β) (hs : β + r ≤ l₀)
    (hS : ∀ θ ∈ S, β + r ≤ l₀ - l₁ * sin (θ 1) ∧
      β + r ≤ l₀ - l₁ * sin (θ 1) - l₂ * sin (θ 1 + θ 2)) :
    IsArmPlaneCert l₀ l₁ l₂ O S r ![0, 0, 1] β := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [dotProduct, Fin.sum_univ_three]
  · intro p hp
    simpa [dotProduct, Fin.sum_univ_three] using hO p hp
  · simpa [dotProduct, Fin.sum_univ_three, shoulderPoint] using hs
  · intro θ hθ
    obtain ⟨he, ht⟩ := hS θ hθ
    constructor
    · simpa [dotProduct, Fin.sum_univ_three, elbowPoint, elbowArmPosition] using he
    · simpa [dotProduct, Fin.sum_univ_three, elbowArmPosition] using ht

/-! ### Joint and trigonometric bounds on the three inflated cells -/

/-- Bounds on the inflated pick cell. -/
private theorem pick_bounds {θ : Fin 3 → ℝ} (hθ : θ ∈ pickCell.radSet cellInflation) :
    sin (θ 1) ≤ 1 / 20 ∧ sin (θ 1 + θ 2) ≤ 3 / 5 ∧ 0 ≤ cos (θ 1) ∧ 0 ≤ cos (θ 1 + θ 2) ∧
      0 ≤ 4 / 5 * sin (θ 0) - 3 / 5 * cos (θ 0) ∧ 0 ≤ sin (θ 0) ∧ 0 ≤ cos (θ 0) := by
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have h0 := hθ 0
  have h1 := hθ 1
  have h2 := hθ 2
  simp [pickCell, DegPoint.toRad, degToRad, cellInflation] at h0 h1 h2
  obtain ⟨a0, b0⟩ := h0
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  have s1 : sin (θ 1) ≤ 1 / 20 :=
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)).trans
      (Real.sin_le (by norm_num))
  have s12 : sin (θ 1 + θ 2) ≤ 3 / 5 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ 1 + θ 2) (y := π / 6 + 1 / 10)
      (by linarith) (by linarith) (by linarith)
    have h' := sin_add_le_add (π / 6) (1 / 10) (by norm_num)
    rw [Real.sin_pi_div_six] at h'
    linarith
  have c1 : 0 ≤ cos (θ 1) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have c12 : 0 ≤ cos (θ 1 + θ 2) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have s0 : √2 / 2 - 1 / 20 ≤ sin (θ 0) := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := π / 4 - 1 / 20) (y := θ 0)
      (by linarith) (by linarith) (by linarith)
    have h' := sub_le_sin_sub (π / 4) (1 / 20) (by norm_num)
    rw [Real.sin_pi_div_four] at h'
    linarith
  have c0 : cos (θ 0) ≤ √2 / 2 + 1 / 20 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := π / 4 - 1 / 20) (y := θ 0)
      (by linarith) (by linarith) (by linarith)
    have h' := cos_sub_le_add (π / 4) (1 / 20) (by norm_num)
    rw [Real.cos_pi_div_four] at h'
    linarith
  have hs2 := one_le_sqrt_two
  refine ⟨s1, s12, c1, c12, by linarith, Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
    (by linarith), Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)⟩

/-- Bounds on the inflated crossing cell. -/
private theorem cross_bounds {θ : Fin 3 → ℝ} (hθ : θ ∈ crossCell.radSet cellInflation) :
    sin (θ 1) ≤ -9 / 20 ∧ sin (θ 1 + θ 2) ≤ π / 12 + 1 / 10 ∧ 0 ≤ cos (θ 1) ∧
      0 ≤ cos (θ 1 + θ 2) ∧ 0 ≤ cos (θ 0) := by
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have h0 := hθ 0
  have h1 := hθ 1
  have h2 := hθ 2
  simp [crossCell, DegPoint.toRad, degToRad, cellInflation] at h0 h1 h2
  obtain ⟨a0, b0⟩ := h0
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  have s1 : sin (θ 1) ≤ -9 / 20 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ 1) (y := -(π / 6) + 1 / 20)
      (by linarith) (by linarith) (by linarith)
    have h' := sin_add_le_add (-(π / 6)) (1 / 20) (by norm_num)
    rw [Real.sin_neg, Real.sin_pi_div_six] at h'
    linarith
  have s12 : sin (θ 1 + θ 2) ≤ π / 12 + 1 / 10 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ 1 + θ 2) (y := π / 12 + 1 / 10)
      (by linarith) (by linarith) (by linarith)
    have h' := sin_add_le_add (π / 12) (1 / 10) (by norm_num)
    have h'' := Real.sin_le (x := π / 12) (by linarith)
    linarith
  exact ⟨s1, s12, Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith),
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith),
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)⟩

/-- Bounds on the inflated place cell. -/
private theorem place_bounds {θ : Fin 3 → ℝ} (hθ : θ ∈ placeCell.radSet cellInflation) :
    sin (θ 1) ≤ 1 / 20 ∧ sin (θ 1 + θ 2) ≤ π / 12 + 1 / 10 ∧ 0 ≤ cos (θ 1) ∧
      0 ≤ cos (θ 1 + θ 2) ∧ 0 ≤ -(4 / 5) * sin (θ 0) - 3 / 5 * cos (θ 0) ∧ 0 ≤ cos (θ 0) := by
  have hπ1 := Real.pi_gt_three
  have hπ2 := Real.pi_lt_d2
  have h0 := hθ 0
  have h1 := hθ 1
  have h2 := hθ 2
  simp [placeCell, DegPoint.toRad, degToRad, cellInflation] at h0 h1 h2
  obtain ⟨a0, b0⟩ := h0
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  have s1 : sin (θ 1) ≤ 1 / 20 :=
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)).trans
      (Real.sin_le (by norm_num))
  have s12 : sin (θ 1 + θ 2) ≤ π / 12 + 1 / 10 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ 1 + θ 2) (y := π / 12 + 1 / 10)
      (by linarith) (by linarith) (by linarith)
    have h' := sin_add_le_add (π / 12) (1 / 10) (by norm_num)
    have h'' := Real.sin_le (x := π / 12) (by linarith)
    linarith
  have s0 : sin (θ 0) ≤ -(√2 / 2) + 1 / 20 := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ 0) (y := -(π / 4) + 1 / 20)
      (by linarith) (by linarith) (by linarith)
    have h' := sin_add_le_add (-(π / 4)) (1 / 20) (by norm_num)
    rw [Real.sin_neg, Real.sin_pi_div_four] at h'
    linarith
  have c0 : cos (θ 0) ≤ √2 / 2 + 1 / 20 := by
    rw [← Real.cos_neg]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := π / 4 - 1 / 20) (y := -θ 0)
      (by linarith) (by linarith) (by linarith)
    have h' := cos_sub_le_add (π / 4) (1 / 20) (by norm_num)
    rw [Real.cos_pi_div_four] at h'
    linarith
  have hs2 := one_le_sqrt_two
  exact ⟨s1, s12, Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith),
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith), by linarith,
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)⟩

/-- The certificate radius `ρ + c = 9/100` m (link radius plus clearance) of the scene (a design
value, not from MLS). -/
theorem linkRadius_add_clearance : linkRadius + clearance = 9 / 100 := by
  norm_num [linkRadius, clearance]

/-- Pick cell against the table: the plane `z = 0`, `n = (0, 0, 1)`, `β = 0` (a design statement,
not from MLS). -/
theorem pick_table_cert : IsArmPlaneCert armL0 armL1 armL2 table (pickCell.radSet cellInflation)
    (linkRadius + clearance) ![0, 0, 1] 0 := by
  rw [linkRadius_add_clearance]
  refine horizontal_cert ?_ (by norm_num [armL0]) ?_
  · intro p hp
    simpa [table] using hp
  · intro θ hθ
    obtain ⟨s1, s12, -⟩ := pick_bounds hθ
    simp only [armL0, armL1, armL2]
    constructor <;> linarith [Real.pi_lt_d2]

/-- Pick cell against the divider: the vertical plane `n = (−4/5, −3/5, 0)`, `β = −9/100` (a design
statement, not from MLS). -/
theorem pick_divider_cert : IsArmPlaneCert armL0 armL1 armL2 divider
    (pickCell.radSet cellInflation) (linkRadius + clearance) ![-4 / 5, -3 / 5, 0] (-9 / 100) := by
  rw [linkRadius_add_clearance]
  refine vertical_cert (by norm_num [armL1]) (by norm_num [armL2]) (by norm_num) (by norm_num) ?_ ?_
  · intro p hp
    have h0 := (hp 0).1
    have h1 := (hp 1).1
    simp at h0 h1
    linarith
  · intro θ hθ
    obtain ⟨-, -, c1, c12, hy, hs, hc⟩ := pick_bounds hθ
    exact ⟨c1, c12, by linarith⟩

/-- Pick cell against the shelf: the plane `x = 2/5`, `n = (−1, 0, 0)`, `β = −2/5` (a design
statement, not from MLS). -/
theorem pick_shelf_cert : IsArmPlaneCert armL0 armL1 armL2 shelf (pickCell.radSet cellInflation)
    (linkRadius + clearance) ![-1, 0, 0] (-2 / 5) := by
  rw [linkRadius_add_clearance]
  refine vertical_cert (by norm_num [armL1]) (by norm_num [armL2]) (by norm_num) (by norm_num) ?_ ?_
  · intro p hp
    have h0 := (hp 0).1
    simp at h0
    linarith
  · intro θ hθ
    obtain ⟨-, -, c1, c12, hy, hs, hc⟩ := pick_bounds hθ
    exact ⟨c1, c12, by linarith⟩

/-- Pick cell against the rear wall: the plane `y = −1/4`, `n = (0, 1, 0)`, `β = −1/4` (a design
statement, not from MLS). -/
theorem pick_rearWall_cert : IsArmPlaneCert armL0 armL1 armL2 rearWall
    (pickCell.radSet cellInflation) (linkRadius + clearance) ![0, 1, 0] (-1 / 4) := by
  rw [linkRadius_add_clearance]
  refine vertical_cert (by norm_num [armL1]) (by norm_num [armL2]) (by norm_num) (by norm_num) ?_ ?_
  · intro p hp
    simp only [rearWall, Set.mem_ofPred_eq] at hp
    linarith
  · intro θ hθ
    obtain ⟨-, -, c1, c12, hy, hs, hc⟩ := pick_bounds hθ
    exact ⟨c1, c12, by linarith⟩

/-- Crossing cell against the table: `n = (0, 0, 1)`, `β = 0` (a design statement, not from MLS). -/
theorem cross_table_cert : IsArmPlaneCert armL0 armL1 armL2 table (crossCell.radSet cellInflation)
    (linkRadius + clearance) ![0, 0, 1] 0 := by
  rw [linkRadius_add_clearance]
  refine horizontal_cert ?_ (by norm_num [armL0]) ?_
  · intro p hp
    simpa [table] using hp
  · intro θ hθ
    obtain ⟨s1, s12, -⟩ := cross_bounds hθ
    simp only [armL0, armL1, armL2]
    constructor <;> linarith [Real.pi_lt_d2]

/-- Crossing cell against the divider: the horizontal plane at the divider's top, `n = (0, 0, 1)`,
`β = 3/10` (a design statement, not from MLS). -/
theorem cross_divider_cert : IsArmPlaneCert armL0 armL1 armL2 divider
    (crossCell.radSet cellInflation) (linkRadius + clearance) ![0, 0, 1] (3 / 10) := by
  rw [linkRadius_add_clearance]
  refine horizontal_cert ?_ (by norm_num [armL0]) ?_
  · intro p hp
    have := (hp 2).2
    simpa using this
  · intro θ hθ
    obtain ⟨s1, s12, -⟩ := cross_bounds hθ
    simp only [armL0, armL1, armL2]
    constructor <;> linarith [Real.pi_lt_d2]

/-- Crossing cell against the shelf: the horizontal plane at the shelf's top, `n = (0, 0, 1)`,
`β = 3/25` (a design statement, not from MLS). -/
theorem cross_shelf_cert : IsArmPlaneCert armL0 armL1 armL2 shelf (crossCell.radSet cellInflation)
    (linkRadius + clearance) ![0, 0, 1] (3 / 25) := by
  rw [linkRadius_add_clearance]
  refine horizontal_cert ?_ (by norm_num [armL0]) ?_
  · intro p hp
    have := (hp 2).2
    simpa using this
  · intro θ hθ
    obtain ⟨s1, s12, -⟩ := cross_bounds hθ
    simp only [armL0, armL1, armL2]
    constructor <;> linarith [Real.pi_lt_d2]

/-- Crossing cell against the rear wall: `n = (0, 1, 0)`, `β = −1/4` (a design statement, not from
MLS). -/
theorem cross_rearWall_cert : IsArmPlaneCert armL0 armL1 armL2 rearWall
    (crossCell.radSet cellInflation) (linkRadius + clearance) ![0, 1, 0] (-1 / 4) := by
  rw [linkRadius_add_clearance]
  refine vertical_cert (by norm_num [armL1]) (by norm_num [armL2]) (by norm_num) (by norm_num) ?_ ?_
  · intro p hp
    simp only [rearWall, Set.mem_ofPred_eq] at hp
    linarith
  · intro θ hθ
    obtain ⟨-, -, c1, c12, hc⟩ := cross_bounds hθ
    exact ⟨c1, c12, by linarith⟩

/-- Place cell against the table: `n = (0, 0, 1)`, `β = 0` (a design statement, not from MLS). -/
theorem place_table_cert : IsArmPlaneCert armL0 armL1 armL2 table (placeCell.radSet cellInflation)
    (linkRadius + clearance) ![0, 0, 1] 0 := by
  rw [linkRadius_add_clearance]
  refine horizontal_cert ?_ (by norm_num [armL0]) ?_
  · intro p hp
    simpa [table] using hp
  · intro θ hθ
    obtain ⟨s1, s12, -⟩ := place_bounds hθ
    simp only [armL0, armL1, armL2]
    constructor <;> linarith [Real.pi_lt_d2]

/-- Place cell against the divider: the vertical plane `n = (4/5, −3/5, 0)`, `β = −9/100` (a design
statement, not from MLS). -/
theorem place_divider_cert : IsArmPlaneCert armL0 armL1 armL2 divider
    (placeCell.radSet cellInflation) (linkRadius + clearance) ![4 / 5, -3 / 5, 0] (-9 / 100) := by
  rw [linkRadius_add_clearance]
  refine vertical_cert (by norm_num [armL1]) (by norm_num [armL2]) (by norm_num) (by norm_num) ?_ ?_
  · intro p hp
    have h0 := (hp 0).2
    have h1 := (hp 1).1
    simp at h0 h1
    linarith
  · intro θ hθ
    obtain ⟨-, -, c1, c12, hy, hc⟩ := place_bounds hθ
    exact ⟨c1, c12, by linarith⟩

/-- Place cell against the shelf: the horizontal plane at the shelf's top, `n = (0, 0, 1)`,
`β = 3/25` (a design statement, not from MLS). -/
theorem place_shelf_cert : IsArmPlaneCert armL0 armL1 armL2 shelf (placeCell.radSet cellInflation)
    (linkRadius + clearance) ![0, 0, 1] (3 / 25) := by
  rw [linkRadius_add_clearance]
  refine horizontal_cert ?_ (by norm_num [armL0]) ?_
  · intro p hp
    have := (hp 2).2
    simpa using this
  · intro θ hθ
    obtain ⟨s1, s12, -⟩ := place_bounds hθ
    simp only [armL0, armL1, armL2]
    constructor <;> linarith [Real.pi_lt_d2]

/-- Place cell against the rear wall: `n = (0, 1, 0)`, `β = −1/4` (a design statement, not from
MLS). -/
theorem place_rearWall_cert : IsArmPlaneCert armL0 armL1 armL2 rearWall
    (placeCell.radSet cellInflation) (linkRadius + clearance) ![0, 1, 0] (-1 / 4) := by
  rw [linkRadius_add_clearance]
  refine vertical_cert (by norm_num [armL1]) (by norm_num [armL2]) (by norm_num) (by norm_num) ?_ ?_
  · intro p hp
    simp only [rearWall, Set.mem_ofPred_eq] at hp
    linarith
  · intro θ hθ
    obtain ⟨-, -, c1, c12, hy, hc⟩ := place_bounds hθ
    exact ⟨c1, c12, by linarith⟩

/-- **Clearance of the scene's cells.** For every cell of the scene, every configuration `θ` of the
cell inflated by `1/20` rad in each joint and every obstacle of the scene, every point of both link
segments of the arm is at Euclidean distance at least `ρ + c = 9/100` m from every point of the
obstacle (the arm of MLS Example 3.2, pp. 89–91; a design statement, not from MLS). -/
theorem cell_clear : ∀ B ∈ sceneCells, ∀ θ ∈ B.radSet cellInflation, ∀ O ∈ sceneObstacles,
    KeepsClearance (armLinks armL0 armL1 armL2 θ) O (linkRadius + clearance) := by
  intro B hB θ hθ O hO
  simp only [sceneCells, List.mem_cons, List.not_mem_nil, or_false] at hB
  simp only [sceneObstacles, List.mem_cons, List.not_mem_nil, or_false] at hO
  rcases hB with rfl | rfl | rfl <;> rcases hO with rfl | rfl | rfl | rfl
  · exact pick_table_cert.keepsClearance θ hθ
  · exact pick_divider_cert.keepsClearance θ hθ
  · exact pick_shelf_cert.keepsClearance θ hθ
  · exact pick_rearWall_cert.keepsClearance θ hθ
  · exact cross_table_cert.keepsClearance θ hθ
  · exact cross_divider_cert.keepsClearance θ hθ
  · exact cross_shelf_cert.keepsClearance θ hθ
  · exact cross_rearWall_cert.keepsClearance θ hθ
  · exact place_table_cert.keepsClearance θ hθ
  · exact place_divider_cert.keepsClearance θ hθ
  · exact place_shelf_cert.keepsClearance θ hθ
  · exact place_rearWall_cert.keepsClearance θ hθ

/-- **Clearance of the link capsules.** For every cell of the scene, every configuration of the cell
inflated by `1/20` rad in each joint and every obstacle, every point of the capsules of radius
`ρ = 3/50` m around the two links is at Euclidean distance at least `c = 3/100` m from every point
of the obstacle (a design statement, not from MLS). -/
theorem cell_capsule_clear : ∀ B ∈ sceneCells, ∀ θ ∈ B.radSet cellInflation, ∀ O ∈ sceneObstacles,
    KeepsClearance (capsule (armLinks armL0 armL1 armL2 θ) linkRadius) O clearance := by
  intro B hB θ hθ O hO
  exact (cell_clear B hB θ hθ O hO).capsule

/-- The Lipschitz constant `73/50` of the scene's tool map (a design value, not from MLS). -/
def toolLipschitz : ℝ := 73 / 50

/-- **Lipschitz bound of the scene's tool map.** For joint vectors `θ`, `θ'` with `|θ i − θ' i| ≤ m`
for every joint, the tool points of the scene's arm are at Euclidean distance at most
`73/50 · m` (MLS Example 3.2, p. 90; `(73/50)² ≥ (l₁ + 2 l₂)² + (l₁ + l₂)²`; a design statement, not
from MLS). -/
theorem tool_lipschitz {θ θ' : Fin 3 → ℝ} {m : ℝ} (hm : ∀ i, |θ i - θ' i| ≤ m) :
    euclidDist (elbowArmPosition armL0 armL1 armL2 θ) (elbowArmPosition armL0 armL1 armL2 θ') ≤
      toolLipschitz * m := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0)
  refine (euclidDist_elbowArmPosition_le armL0 armL1 armL2 (by norm_num [armL1])
    (by norm_num [armL2]) hm).trans ?_
  apply mul_le_mul_of_nonneg_right _ hm0
  unfold toolLipschitzConst toolLipschitz armL1 armL2
  rw [Real.sqrt_le_iff]
  norm_num

/-- The tool point of the scene's arm as a point of `EuclideanSpace ℝ (Fin 3)`, so that `dist` is
the Euclidean distance in metres (MLS Example 3.2, p. 90; a design definition, not from MLS). -/
def sceneTool (θ : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (elbowArmPosition armL0 armL1 armL2 θ)

/-- The Lipschitz bound of the scene's tool map in the form `dist (tool θ) (tool θ') ≤ L r`
whenever `|θ i − θ' i| ≤ r` for every joint, with `L = 73/50` and the Euclidean distance (a design
statement, not from MLS; radians and metres). -/
theorem sceneTool_lipschitz : ∀ θ θ' : Fin 3 → ℝ, ∀ r : ℝ, (∀ i, |θ i - θ' i| ≤ r) →
    dist (sceneTool θ) (sceneTool θ') ≤ toolLipschitz * r :=
  fun _ _ _ h => tool_lipschitz h

/-- **The straight joint-space move from a pick slot to a place slot collides with the divider.**
Halfway along the straight joint-space segment from the pick slot `(60, 0, 30)` to the place slot
`(-60, 0, 15)` degrees the tool point of the arm lies in the divider, so no clearance holds there (a
design statement, not from MLS). -/
theorem straight_pick_place_hits_divider :
    elbowArmPosition armL0 armL1 armL2
        (fun i => DegPoint.toRad (60, 0, 30) i +
          (1 / 2 : ℝ) * (DegPoint.toRad (-60, 0, 15) i - DegPoint.toRad (60, 0, 30) i)) ∈
      divider := by
  have hθ : (fun i => DegPoint.toRad (60, 0, 30) i +
      (1 / 2 : ℝ) * (DegPoint.toRad (-60, 0, 15) i - DegPoint.toRad (60, 0, 30) i)) =
      ![0, 0, π / 8] := by
    funext i
    fin_cases i <;> simp [DegPoint.toRad, degToRad] <;> ring
  rw [hθ]
  have hs2 : (7 / 5 : ℝ) ≤ √2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hπ1 := Real.pi_gt_three
  have hs0 : 0 ≤ sin (π / 8) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc0 : 0 ≤ cos (π / 8) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hc1 : cos (π / 8) ≤ 1 := Real.cos_le_one _
  have hs1 : sin (π / 8) ≤ 1 := Real.sin_le_one _
  have hdouble : √2 / 2 = 2 * sin (π / 8) * cos (π / 8) := by
    rw [← Real.sin_two_mul, show 2 * (π / 8) = π / 4 by ring, Real.sin_pi_div_four]
  have hs : √2 / 4 ≤ sin (π / 8) := by nlinarith
  simp only [divider, realBox, Set.mem_ofPred_eq]
  intro i
  fin_cases i <;>
    simp [elbowArmPosition, armL0, armL1, armL2, -Real.sin_pi_div_eight, -Real.cos_pi_div_eight] <;>
    first
    | (constructor <;> nlinarith)
    | norm_num

/-- At the halfway configuration of the straight joint-space move from the pick slot `(60, 0, 30)`
to the place slot `(-60, 0, 15)` degrees, the links of the arm keep no positive clearance from the
divider: the move is not certifiable by any cell (a design statement, not from MLS). -/
theorem straight_pick_place_not_clear {r : ℝ} (hr : 0 < r) :
    ¬ KeepsClearance
      (armLinks armL0 armL1 armL2
        (fun i => DegPoint.toRad (60, 0, 30) i +
          (1 / 2 : ℝ) * (DegPoint.toRad (-60, 0, 15) i - DegPoint.toRad (60, 0, 30) i)))
      divider r := by
  intro h
  have := h _ (Or.inr (right_mem_segment ℝ _ _)) _ straight_pick_place_hits_divider
  rw [euclidDist, dist_self] at this
  linarith

end RoboLean.Cell
