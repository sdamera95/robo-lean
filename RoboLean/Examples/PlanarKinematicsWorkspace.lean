import RoboLean.Examples.PlanarTwoLinkInverseKinematics
import RoboLean.Examples.PlanarThreeLinkSelfMotion
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Workspace of the planar three-link robot: MLS Example 3.4

MLS printed pp. 96–97, Figure 3.6. The planar three-link arm has
`x = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) + l₃ cos(θ₁ + θ₂ + θ₃)`,
`y = l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) + l₃ sin(θ₁ + θ₂ + θ₃)`, `φ = θ₁ + θ₂ + θ₃` (eq. (3.14)), the
position map `planarThreeLinkPosition` of the library (angles from `+x`). The book takes
`l₁ > l₂ > l₃` and `l₁ > l₂ + l₃` and states:

* "`W_R` is an annulus with inner radius `l₁ - l₂ - l₃` and outer radius `l₁ + l₂ + l₃`";
* the dextrous workspace (positions reachable with every orientation `φ`) is smaller "by `2 l₃` on
  the inner and outer edges" (Figure 3.6(d)). Read here as the annulus with inner radius
  `l₁ - l₂ + l₃` and outer radius `l₁ + l₂ - l₃`: each edge moves by `2 l₃`.

Both are proved for `0 < l₃ < l₂` and `l₂ + l₃ < l₁` (the book's inequalities with positive
lengths, which the book leaves implicit), as conditions on `x² + y²`. Orientations are real
angles; `θ₁ + θ₂ + θ₃ = φ` is exact because `θ₃` is a free real number.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

private theorem twoLink_sq (a b α β : ℝ) :
    (a * cos α + b * cos (α + β)) ^ 2 + (a * sin α + b * sin (α + β)) ^ 2 =
      a ^ 2 + b ^ 2 + 2 * a * b * cos β := by
  have hα := sin_sq_add_cos_sq α
  have hβ := sin_sq_add_cos_sq β
  rw [cos_add, sin_add]
  linear_combination (a ^ 2 + 2 * a * b * cos β + b ^ 2 * (cos β ^ 2 + sin β ^ 2)) * hα + b ^ 2 * hβ

private theorem twoLink_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (α β : ℝ) :
    (a - b) ^ 2 ≤ (a * cos α + b * cos (α + β)) ^ 2 + (a * sin α + b * sin (α + β)) ^ 2 ∧
      (a * cos α + b * cos (α + β)) ^ 2 + (a * sin α + b * sin (α + β)) ^ 2 ≤ (a + b) ^ 2 := by
  rw [twoLink_sq]
  have h1 := neg_one_le_cos β
  have h2 := cos_le_one β
  have hab : 0 < a * b := mul_pos ha hb
  constructor <;> nlinarith

private theorem twoLink_exists {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : (a - b) ^ 2 ≤ u ^ 2 + v ^ 2) (h₂ : u ^ 2 + v ^ 2 ≤ (a + b) ^ 2) :
    ∃ α β : ℝ, a * cos α + b * cos (α + β) = u ∧ a * sin α + b * sin (α + β) = v := by
  have hn := norm_vec_neg u v
  have hx2 : (vec (-v) u 0) 2 = 0 := by simp [vec]
  have hlo : |a - b| ≤ ‖vec (-v) u 0‖ := by
    rw [hn]
    apply Real.le_sqrt_of_sq_le
    rwa [sq_abs]
  have hhi : ‖vec (-v) u 0‖ ≤ a + b := by
    rw [hn, ← Real.sqrt_sq (by positivity : 0 ≤ a + b)]
    exact Real.sqrt_le_sqrt h₂
  obtain ⟨q, hq⟩ := exists_planarTwoLinkPosition_eq ha hb hx2 hlo hhi
  obtain ⟨e₁, e₂⟩ := (planarTwoLinkPosition_eq_vec_iff a b u v q).mp hq
  exact ⟨q 0, q 1, e₁, e₂⟩

private theorem polar (x y : ℝ) :
    ∃ ψ : ℝ, √(x ^ 2 + y ^ 2) * cos ψ = x ∧ √(x ^ 2 + y ^ 2) * sin ψ = y := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨0, by simp [hx, hy], by simp [hx, hy]⟩
  · set z : ℂ := ⟨x, y⟩
    have hz : z ≠ 0 := by
      intro hz
      apply h
      have h1 : x = 0 := congrArg Complex.re hz
      have h2 : y = 0 := congrArg Complex.im hz
      simp [h1, h2]
    have hnorm : ‖z‖ = √(x ^ 2 + y ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp [z]
      ring
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    refine ⟨Complex.arg z, ?_, ?_⟩
    · rw [Complex.cos_arg hz, ← hnorm]
      field_simp
      rfl
    · rw [Complex.sin_arg, ← hnorm]
      field_simp
      rfl

private theorem pos_apply (l₁ l₂ l₃ x y : ℝ) (θ : Fin 3 → ℝ) :
    planarThreeLinkPosition l₁ l₂ l₃ θ = ![x, y] ↔
      l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) + l₃ * cos (θ 0 + θ 1 + θ 2) = x ∧
        l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1) + l₃ * sin (θ 0 + θ 1 + θ 2) = y := by
  constructor
  · intro h
    exact ⟨by simpa [planarThreeLinkPosition] using congrFun h 0,
      by simpa [planarThreeLinkPosition] using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa [planarThreeLinkPosition] using h0
    · simpa [planarThreeLinkPosition] using h1

/-- **MLS Example 3.4, p. 97: the reachable workspace of the planar three-link robot is the
annulus `l₁ - l₂ - l₃ ≤ r ≤ l₁ + l₂ + l₃`.** For `0 < l₃ < l₂` and `l₂ + l₃ < l₁`, a point `(x, y)`
is the position of some joint vector exactly when `(l₁ - l₂ - l₃)² ≤ x² + y² ≤ (l₁ + l₂ + l₃)²`. -/
theorem planarThreeLink_reachable_iff {l₁ l₂ l₃ : ℝ} (h₃ : 0 < l₃) (h₂₃ : l₃ < l₂)
    (h₁ : l₂ + l₃ < l₁) (x y : ℝ) :
    (∃ θ : Fin 3 → ℝ, planarThreeLinkPosition l₁ l₂ l₃ θ = ![x, y]) ↔
      (l₁ - l₂ - l₃) ^ 2 ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ (l₁ + l₂ + l₃) ^ 2 := by
  have hl₂ : 0 < l₂ := h₃.trans h₂₃
  have hl₁ : 0 < l₁ := by linarith
  constructor
  · rintro ⟨θ, hθ⟩
    obtain ⟨hx, hy⟩ := (pos_apply l₁ l₂ l₃ x y θ).mp hθ
    set wx := l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1)
    set wy := l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1)
    set c := cos (θ 0 + θ 1 + θ 2)
    set s := sin (θ 0 + θ 1 + θ 2)
    have hcs : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
    obtain ⟨hW₁, hW₂⟩ := twoLink_bounds hl₁ hl₂ (θ 0) (θ 1)
    set W2 := wx ^ 2 + wy ^ 2
    set W := √W2
    have hW0 : 0 ≤ W := Real.sqrt_nonneg _
    have hWsq : W ^ 2 = W2 := Real.sq_sqrt (by positivity)
    have hWlo : l₁ - l₂ ≤ W := Real.le_sqrt_of_sq_le hW₁
    have hWhi : W ≤ l₁ + l₂ := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ l₁ + l₂)]
      exact Real.sqrt_le_sqrt hW₂
    have hdot : (wx * c + wy * s) ^ 2 ≤ W ^ 2 := by
      rw [hWsq]
      nlinarith [sq_nonneg (wx * s - wy * c)]
    have habs : |wx * c + wy * s| ≤ W := abs_le_of_sq_le_sq' hdot hW0 |> fun h => abs_le.mpr h
    have hxy : x ^ 2 + y ^ 2 = W2 + l₃ ^ 2 + 2 * l₃ * (wx * c + wy * s) := by
      rw [← hx, ← hy]
      linear_combination l₃ ^ 2 * hcs
    obtain ⟨hd₁, hd₂⟩ := abs_le.mp habs
    rw [hxy, ← hWsq]
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hlo, hhi⟩
    set P := √(x ^ 2 + y ^ 2)
    have hP0 : l₁ - l₂ - l₃ ≤ P := Real.le_sqrt_of_sq_le hlo
    have hPhi : P ≤ l₁ + l₂ + l₃ := by
      rw [← Real.sqrt_sq (by linarith : 0 ≤ l₁ + l₂ + l₃)]
      exact Real.sqrt_le_sqrt hhi
    obtain ⟨ψ, hψx, hψy⟩ := polar x y
    have hcs := sin_sq_add_cos_sq ψ
    have hr : ∀ ρ : ℝ, (ρ * cos ψ) ^ 2 + (ρ * sin ψ) ^ 2 = ρ ^ 2 := fun ρ => by
      linear_combination ρ ^ 2 * hcs
    by_cases hcase : l₁ - l₂ + l₃ ≤ P
    · obtain ⟨α, β, hα, hβ⟩ := twoLink_exists (u := (P - l₃) * cos ψ) (v := (P - l₃) * sin ψ)
        hl₁ hl₂ (by rw [hr]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
        (by rw [hr]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
      refine ⟨![α, β, ψ - α - β], (pos_apply l₁ l₂ l₃ x y _).mpr ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, show α + β + (ψ - α - β) = ψ by ring]
      constructor
      · rw [hα, ← hψx]; ring
      · rw [hβ, ← hψy]; ring
    · obtain ⟨α, β, hα, hβ⟩ := twoLink_exists (u := (P + l₃) * cos ψ) (v := (P + l₃) * sin ψ)
        hl₁ hl₂ (by rw [hr]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
        (by rw [hr]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
      refine ⟨![α, β, ψ + π - α - β], (pos_apply l₁ l₂ l₃ x y _).mpr ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, show α + β + (ψ + π - α - β) = ψ + π by ring,
        cos_add_pi, sin_add_pi]
      constructor
      · rw [hα, ← hψx]; ring
      · rw [hβ, ← hψy]; ring

/-- **MLS Example 3.4, p. 97, Figure 3.6(d): the dextrous workspace of the planar three-link
robot.** For `0 < l₃ < l₂` and `l₂ + l₃ < l₁`, the position `(x, y)` is reached with every
orientation `φ` exactly when `(l₁ - l₂ + l₃)² ≤ x² + y² ≤ (l₁ + l₂ - l₃)²`: the reachable annulus
reduced by `2 l₃` on the inner and outer edges. -/
theorem planarThreeLink_dextrous_iff {l₁ l₂ l₃ : ℝ} (h₃ : 0 < l₃) (h₂₃ : l₃ < l₂)
    (h₁ : l₂ + l₃ < l₁) (x y : ℝ) :
    (∀ φ : ℝ, ∃ θ : Fin 3 → ℝ, planarThreeLinkPosition l₁ l₂ l₃ θ = ![x, y] ∧
        θ 0 + θ 1 + θ 2 = φ) ↔
      (l₁ - l₂ + l₃) ^ 2 ≤ x ^ 2 + y ^ 2 ∧ x ^ 2 + y ^ 2 ≤ (l₁ + l₂ - l₃) ^ 2 := by
  have hl₂ : 0 < l₂ := h₃.trans h₂₃
  have hl₁ : 0 < l₁ := by linarith
  obtain ⟨ψ, hψx, hψy⟩ := polar x y
  have hPsq : √(x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  set P := √(x ^ 2 + y ^ 2)
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hcs := sin_sq_add_cos_sq ψ
  -- the wrist point for orientation `φ` and its squared distance from the base
  have hwrist : ∀ φ : ℝ, (x - l₃ * cos φ) ^ 2 + (y - l₃ * sin φ) ^ 2 =
      P ^ 2 + l₃ ^ 2 - 2 * l₃ * P * cos (ψ - φ) := by
    intro φ
    rw [cos_sub]
    linear_combination (-1 : ℝ) * hPsq + 2 * l₃ * cos φ * hψx + 2 * l₃ * sin φ * hψy +
      l₃ ^ 2 * sin_sq_add_cos_sq φ
  constructor
  · intro h
    have hreach : ∀ φ : ℝ, (l₁ - l₂) ^ 2 ≤ P ^ 2 + l₃ ^ 2 - 2 * l₃ * P * cos (ψ - φ) ∧
        P ^ 2 + l₃ ^ 2 - 2 * l₃ * P * cos (ψ - φ) ≤ (l₁ + l₂) ^ 2 := by
      intro φ
      obtain ⟨θ, hθ, hφ⟩ := h φ
      obtain ⟨hx, hy⟩ := (pos_apply l₁ l₂ l₃ x y θ).mp hθ
      rw [hφ] at hx hy
      rw [← hwrist φ]
      have hu : x - l₃ * cos φ = l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) := by linarith
      have hv : y - l₃ * sin φ = l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1) := by linarith
      rw [hu, hv]
      exact twoLink_bounds hl₁ hl₂ (θ 0) (θ 1)
    obtain ⟨h₁, -⟩ := hreach ψ
    obtain ⟨-, h₂⟩ := hreach (ψ - π)
    simp only [sub_self, cos_zero, mul_one, sub_sub_cancel, cos_pi] at h₁ h₂
    have hlo : l₁ - l₂ + l₃ ≤ P := by nlinarith
    have hhi : P ≤ l₁ + l₂ - l₃ := by nlinarith
    rw [← hPsq]
    exact ⟨pow_le_pow_left₀ (by linarith) hlo 2, pow_le_pow_left₀ hP0 hhi 2⟩
  · rintro ⟨hlo, hhi⟩ φ
    have hPlo : l₁ - l₂ + l₃ ≤ P := Real.le_sqrt_of_sq_le hlo
    have hPhi : P ≤ l₁ + l₂ - l₃ := by
      rw [← Real.sqrt_sq (by linarith : 0 ≤ l₁ + l₂ - l₃)]
      exact Real.sqrt_le_sqrt hhi
    have hc₁ := neg_one_le_cos (ψ - φ)
    have hc₂ := cos_le_one (ψ - φ)
    have hl3P : 0 ≤ l₃ * P := by positivity
    obtain ⟨α, β, hα, hβ⟩ := twoLink_exists (u := x - l₃ * cos φ) (v := y - l₃ * sin φ) hl₁ hl₂
      (by rw [hwrist]; nlinarith) (by rw [hwrist]; nlinarith)
    refine ⟨![α, β, φ - α - β], (pos_apply l₁ l₂ l₃ x y _).mpr ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, show α + β + (φ - α - β) = φ by ring]
      constructor
      · rw [hα]; ring
      · rw [hβ]; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring

end Examples

end RoboLean
