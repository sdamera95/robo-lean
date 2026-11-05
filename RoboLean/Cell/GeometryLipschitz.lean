import RoboLean.Cell.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A Lipschitz bound for the tool map of the three-link arm

For the tool map `elbowArmPosition l₀ l₁ l₂` of MLS Example 3.2 (p. 90) with `0 ≤ l₁`, `0 ≤ l₂`, the
Euclidean distance between the tool points of two configurations whose joint angles differ by at
most `m` radians in each joint is at most `√((l₁ + 2 l₂)² + (l₁ + l₂)²) · m`. The horizontal reach
`R = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂)` and the height drop `Z = l₁ sin θ₁ + l₂ sin(θ₁ + θ₂)` move by at
most `(l₁ + 2 l₂) m` together, and the yaw moves the horizontal point by at most `|R| · |Δθ₀|` with
`|R| ≤ l₁ + l₂`. A design statement, not from MLS.
-/

noncomputable section

open Real

namespace RoboLean.Cell

open RoboLean.Examples

/-- The Lipschitz constant `√((l₁ + 2 l₂)² + (l₁ + l₂)²)` of the tool map of the three-link arm with
respect to the largest joint difference (radians) and the Euclidean distance (metres) (a design
definition, not from MLS). -/
def toolLipschitzConst (l₁ l₂ : ℝ) : ℝ := √((l₁ + 2 * l₂) ^ 2 + (l₁ + l₂) ^ 2)

/-- The squared chord between two points of the unit circle is at most the squared angle:
`(cos x − cos y)² + (sin x − sin y)² ≤ (x − y)²`. -/
private theorem chord_sq_le (x y : ℝ) :
    (cos x - cos y) ^ 2 + (sin x - sin y) ^ 2 ≤ (x - y) ^ 2 := by
  have e : (cos x - cos y) ^ 2 + (sin x - sin y) ^ 2 = 2 - 2 * cos (x - y) := by
    rw [Real.cos_sub]
    linear_combination sin_sq_add_cos_sq x + sin_sq_add_cos_sq y
  have h := Real.one_sub_sq_div_two_le_cos (x := x - y)
  rw [e]
  linarith

/-- **Lipschitz bound of the tool map.** For `0 ≤ l₁`, `0 ≤ l₂` and joint vectors `θ`, `θ'` with
`|θ i − θ' i| ≤ m` for every joint, the Euclidean distance between the tool points
`elbowArmPosition l₀ l₁ l₂ θ` and `elbowArmPosition l₀ l₁ l₂ θ'` (MLS Example 3.2, p. 90) is at most
`toolLipschitzConst l₁ l₂ * m` (a design statement, not from MLS; radians and metres). -/
theorem euclidDist_elbowArmPosition_le (l₀ l₁ l₂ : ℝ) (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    {θ θ' : Fin 3 → ℝ} {m : ℝ} (hm : ∀ i, |θ i - θ' i| ≤ m) :
    euclidDist (elbowArmPosition l₀ l₁ l₂ θ) (elbowArmPosition l₀ l₁ l₂ θ') ≤
      toolLipschitzConst l₁ l₂ * m := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0)
  obtain ⟨d0, e0⟩ := abs_le.mp (hm 0)
  obtain ⟨d1, e1⟩ := abs_le.mp (hm 1)
  obtain ⟨d2, e2⟩ := abs_le.mp (hm 2)
  set R := l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2) with hR
  set R' := l₁ * cos (θ' 1) + l₂ * cos (θ' 1 + θ' 2) with hR'
  set Z := l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2) with hZ
  set Z' := l₁ * sin (θ' 1) + l₂ * sin (θ' 1 + θ' 2) with hZ'
  have key : ∑ i, (elbowArmPosition l₀ l₁ l₂ θ i - elbowArmPosition l₀ l₁ l₂ θ' i) ^ 2 =
      (R - R') ^ 2 + 2 * (R * R') * (1 - cos (θ 0 - θ' 0)) + (Z - Z') ^ 2 := by
    simp only [Fin.sum_univ_three, elbowArmPosition, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [Real.cos_sub]
    linear_combination R ^ 2 * sin_sq_add_cos_sq (θ 0) + R' ^ 2 * sin_sq_add_cos_sq (θ' 0)
  -- the shoulder–elbow and the forearm directions
  have hA := chord_sq_le (θ 1) (θ' 1)
  have hB := chord_sq_le (θ 1 + θ 2) (θ' 1 + θ' 2)
  have hA' : (θ 1 - θ' 1) ^ 2 ≤ m ^ 2 := sq_le_sq' d1 e1
  have hB' : (θ 1 + θ 2 - (θ' 1 + θ' 2)) ^ 2 ≤ (2 * m) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  set A := (cos (θ 1) - cos (θ' 1)) ^ 2 + (sin (θ 1) - sin (θ' 1)) ^ 2 with hAdef
  set B := (cos (θ 1 + θ 2) - cos (θ' 1 + θ' 2)) ^ 2 +
    (sin (θ 1 + θ 2) - sin (θ' 1 + θ' 2)) ^ 2 with hBdef
  set X := (cos (θ 1) - cos (θ' 1)) * (cos (θ 1 + θ 2) - cos (θ' 1 + θ' 2)) +
    (sin (θ 1) - sin (θ' 1)) * (sin (θ 1 + θ 2) - sin (θ' 1 + θ' 2)) with hXdef
  have hX : X ≤ A + B / 4 := by
    nlinarith [sq_nonneg (cos (θ 1) - cos (θ' 1) - (cos (θ 1 + θ 2) - cos (θ' 1 + θ' 2)) / 2),
      sq_nonneg (sin (θ 1) - sin (θ' 1) - (sin (θ 1 + θ 2) - sin (θ' 1 + θ' 2)) / 2)]
  have hRZe : (R - R') ^ 2 + (Z - Z') ^ 2 = l₁ ^ 2 * A + l₂ ^ 2 * B + 2 * (l₁ * l₂) * X := by
    rw [hR, hR', hZ, hZ', hAdef, hBdef, hXdef]
    ring
  have h12 : 0 ≤ l₁ * l₂ := mul_nonneg h₁ h₂
  have hRZ : (R - R') ^ 2 + (Z - Z') ^ 2 ≤ (l₁ + 2 * l₂) ^ 2 * m ^ 2 := by
    rw [hRZe]
    have i1 := mul_le_mul_of_nonneg_left (hA.trans hA') (sq_nonneg l₁)
    have i2 := mul_le_mul_of_nonneg_left (hB.trans hB') (sq_nonneg l₂)
    have i3 : X ≤ 2 * m ^ 2 := by linarith [hA.trans hA', hB.trans hB']
    have i4 := mul_le_mul_of_nonneg_left i3 (by linarith : 0 ≤ 2 * (l₁ * l₂))
    linarith
  -- the yaw
  have habsR : |R| ≤ l₁ + l₂ := by
    rw [hR]
    calc |l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)|
        ≤ |l₁ * cos (θ 1)| + |l₂ * cos (θ 1 + θ 2)| := abs_add_le _ _
      _ = l₁ * |cos (θ 1)| + l₂ * |cos (θ 1 + θ 2)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h₁, abs_of_nonneg h₂]
      _ ≤ l₁ * 1 + l₂ * 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = l₁ + l₂ := by ring
  have habsR' : |R'| ≤ l₁ + l₂ := by
    rw [hR']
    calc |l₁ * cos (θ' 1) + l₂ * cos (θ' 1 + θ' 2)|
        ≤ |l₁ * cos (θ' 1)| + |l₂ * cos (θ' 1 + θ' 2)| := abs_add_le _ _
      _ = l₁ * |cos (θ' 1)| + l₂ * |cos (θ' 1 + θ' 2)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h₁, abs_of_nonneg h₂]
      _ ≤ l₁ * 1 + l₂ * 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = l₁ + l₂ := by ring
  have hRR : R * R' ≤ (l₁ + l₂) ^ 2 := by
    calc R * R' ≤ |R * R'| := le_abs_self _
      _ = |R| * |R'| := abs_mul _ _
      _ ≤ (l₁ + l₂) * (l₁ + l₂) := mul_le_mul habsR habsR' (abs_nonneg _) (by linarith)
      _ = (l₁ + l₂) ^ 2 := by ring
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ 0 - θ' 0)
  have hc1 : 0 ≤ 1 - cos (θ 0 - θ' 0) := by linarith [Real.cos_le_one (θ 0 - θ' 0)]
  have h0' : (θ 0 - θ' 0) ^ 2 ≤ m ^ 2 := sq_le_sq' d0 e0
  have hyaw : 2 * (R * R') * (1 - cos (θ 0 - θ' 0)) ≤ (l₁ + l₂) ^ 2 * m ^ 2 := by
    have j1 := mul_le_mul_of_nonneg_right hRR hc1
    have j2 : 2 * (1 - cos (θ 0 - θ' 0)) ≤ m ^ 2 := by linarith
    have j3 := mul_le_mul_of_nonneg_left j2 (sq_nonneg (l₁ + l₂))
    linarith
  have hsum : ∑ i, (elbowArmPosition l₀ l₁ l₂ θ i - elbowArmPosition l₀ l₁ l₂ θ' i) ^ 2 ≤
      ((l₁ + 2 * l₂) ^ 2 + (l₁ + l₂) ^ 2) * m ^ 2 := by
    rw [key]
    linarith
  rw [euclidDist_eq, toolLipschitzConst]
  calc √(∑ i, (elbowArmPosition l₀ l₁ l₂ θ i - elbowArmPosition l₀ l₁ l₂ θ' i) ^ 2)
      ≤ √(((l₁ + 2 * l₂) ^ 2 + (l₁ + l₂) ^ 2) * m ^ 2) := Real.sqrt_le_sqrt hsum
    _ = √((l₁ + 2 * l₂) ^ 2 + (l₁ + l₂) ^ 2) * m := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hm0]

end RoboLean.Cell
