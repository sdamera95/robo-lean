import RoboLean.Examples.PlanarTwoLinkWorkspace
import RoboLean.Kinematics.PadenKahan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Closed-form inverse kinematics of the planar two-link arm (MLS eq. (3.16))

MLS Chapter 3, §3.1, printed pp. 97–98. For the planar two-link manipulator of Figure 3.7a with
forward kinematics `x = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂)`, `y = l₁ sin θ₁ + l₂ sin(θ₁ + θ₂)` (p. 97),
the book solves for the joint angles in polar coordinates `(r, φ)`, `r = √(x² + y²)`: the law of
cosines gives
`θ₂ = π ± α`, `α = cos⁻¹((l₁² + l₂² - r²) / (2 l₁ l₂))` (eq. (3.16)), and then
`θ₁ = atan2(y, x) ± β`, `β = cos⁻¹((r² + l₁² - l₂²) / (2 l₁ r))`, "where the sign used for `β`
agrees with that used for `α`" (p. 98). Outside the workspace no solution exists ("consider what
happens if `r > l₁ + l₂`").

Frame. The book's arm points along `+x` at `θ = 0`; the library's arm `planarTwoLink a b`
(Example 3.1 specialized, ledger K06–K07) points along `+y`. The two frames differ by the
rotation `Rz(π/2)`: the book's point `(x, y)` is the library point `vec (-y) x 0`
(`planarTwoLinkPosition_eq_vec_iff`), so the book's equations are exactly the equations for the
library's tool position, with `l₁ = a`, `l₂ = b`, `θ₁ = q 0`, `θ₂ = q 1`. Joint angles are real
numbers and are determined modulo `2π` (ledger K01); `atan2` is the library's `Rotation.atan2`
(argument in `(-π, π]`) and `cos⁻¹` is `Real.arccos`.

Proved here (ledger K30):

* the frame bridge from the library position to the book's two equations;
* the elbow subproblem: `a² + b² + 2ab cos θ₂ = r²` holds exactly for `θ₂ = π ± α` modulo `2π`
  (`planarTwoLink_elbow_iff`), the two values are distinct modulo `2π` exactly in the interior of
  the annulus, `|a - b| < r < a + b` (`planarTwoLink_elbow_branches_ne_iff`);
* the complete solution: for positive lengths and `0 < r` with `|a - b| ≤ r ≤ a + b`, the joint
  vectors reaching the book's point `(x, y)` are exactly
  `θ₂ = π + α, θ₁ = atan2(y, x) + β` and `θ₂ = π - α, θ₁ = atan2(y, x) - β`, modulo `2π` in each
  angle (`planarTwoLink_inverseKinematics_iff`), and both branches do reach it
  (`planarTwoLink_inverseKinematics_plus`, `_minus`);
* the case `r = 0`, possible only for `a = b`: the solutions are `θ₂ = π` modulo `2π` with `θ₁`
  arbitrary (`planarTwoLink_inverseKinematics_origin`); the printed formula for `β` divides by
  `r` and does not cover it;
* no solution for `r > l₁ + l₂` (printed), and none for `r < |l₁ - l₂|` (not printed; from the
  annulus row C01): the elbow subproblem already fails (`planarTwoLink_elbow_no_solution`);
* the elbow angle `arccos((r² - a² - b²)/(2ab))` used by the existence construction of the
  workspace row C02 (`exists_planarTwoLinkPosition_eq`) is `π - α`, the minus branch
  (`arccos_elbow_eq_pi_sub_alpha`).

Hypotheses the book does not state: positive link lengths `0 < l₁, l₂` (the formulas divide by
`l₁ l₂`) and `r ≠ 0` for `θ₁` (the formula for `β` divides by `r`). Source observation: the book
says "if `α ≠ 0`, there are two distinct values of `θ₂`"; at `α = π` (the outer boundary
`r = l₁ + l₂`) the two values `0` and `2π` are distinct real numbers that name the same joint
angle (p. 84), so modulo `2π` the values are distinct exactly when `0 < α < π`. These are
statements about the coordinate model, not about a physical arm, joint limits or a numerical
solver.
-/

noncomputable section

namespace RoboLean.Examples

/-- The angle `α = cos⁻¹((l₁² + l₂² - r²) / (2 l₁ l₂))` of MLS eq. (3.16), p. 98: the interior
angle of the triangle with sides `l₁`, `l₂`, `r` opposite the side `r` (Figure 3.7b). `cos⁻¹` is
`Real.arccos`, which is total (it is `π` below `-1` and `0` above `1`). -/
def planarTwoLinkAlpha (l₁ l₂ r : ℝ) : ℝ :=
  Real.arccos ((l₁ ^ 2 + l₂ ^ 2 - r ^ 2) / (2 * l₁ * l₂))

/-- The angle `β = cos⁻¹((r² + l₁² - l₂²) / (2 l₁ r))` of MLS p. 98: the angle at the base
between the first link and the segment to the target (Figure 3.7b). `cos⁻¹` is `Real.arccos`;
for `r = 0` Lean's division gives `0`, a value the book's formula does not assign. -/
def planarTwoLinkBeta (l₁ l₂ r : ℝ) : ℝ :=
  Real.arccos ((r ^ 2 + l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * r))

/-! ### Frame bridge -/

/-- **The book's equations on MLS p. 97 are the library's tool position.** The planar two-link
arm (`planarTwoLinkPosition a b q`, MLS eq. (3.4) specialized, zero configuration along `+y`)
reaches the library point `vec (-y) x 0` exactly when
`a cos θ₁ + b cos(θ₁ + θ₂) = x` and `a sin θ₁ + b sin(θ₁ + θ₂) = y`, the forward kinematics of
MLS p. 97 (Figure 3.7a, zero configuration along `+x`) with `l₁ = a`, `l₂ = b`, `θ₁ = q 0`,
`θ₂ = q 1`. The book's point `(x, y)` and the library point differ by the rotation `Rz(π/2)`. -/
theorem planarTwoLinkPosition_eq_vec_iff (a b x y : ℝ) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q = vec (-y) x 0 ↔
      a * Real.cos (q 0) + b * Real.cos (q 0 + q 1) = x ∧
        a * Real.sin (q 0) + b * Real.sin (q 0 + q 1) = y := by
  rw [planarTwoLinkPosition_eq]
  constructor
  · intro h
    have h0 := congrArg (fun v : Vec3 => v 0) h
    have h1 := congrArg (fun v : Vec3 => v 1) h
    simp only [vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    ext i
    fin_cases i
    · simp [vec, ← h2]
      ring
    · simp [vec, ← h1]
    · simp [vec]

/-- The distance `r = √(x² + y²)` of the book's point `(x, y)` (MLS p. 98) is the norm of the
library point `vec (-y) x 0`. -/
theorem norm_vec_neg (x y : ℝ) : ‖vec (-y) x 0‖ = √(x ^ 2 + y ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  ring_nf

/-! ### The elbow subproblem: `θ₂ = π ± α` -/

/-- **MLS eq. (3.16), p. 98: the two elbow angles.** For nonzero link lengths `a, b` and a
distance `r` with `-1 ≤ (a² + b² - r²)/(2ab) ≤ 1`, the law of cosines
`a² + b² + 2ab cos θ₂ = r²` holds exactly for `θ₂ = π + α` or `θ₂ = π - α` modulo `2π`, with
`α = planarTwoLinkAlpha a b r`. -/
theorem planarTwoLink_elbow_iff {a b r : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hκ₁ : -1 ≤ (a ^ 2 + b ^ 2 - r ^ 2) / (2 * a * b))
    (hκ₂ : (a ^ 2 + b ^ 2 - r ^ 2) / (2 * a * b) ≤ 1) (θ₂ : ℝ) :
    a ^ 2 + b ^ 2 + 2 * a * b * Real.cos θ₂ = r ^ 2 ↔
      ∃ k : ℤ, θ₂ = Real.pi + planarTwoLinkAlpha a b r + k * (2 * Real.pi) ∨
        θ₂ = Real.pi - planarTwoLinkAlpha a b r + k * (2 * Real.pi) := by
  set κ := (a ^ 2 + b ^ 2 - r ^ 2) / (2 * a * b) with hκ
  have hab : 2 * a * b ≠ 0 := by positivity
  have hcosα : Real.cos (planarTwoLinkAlpha a b r) = κ := Real.cos_arccos hκ₁ hκ₂
  have h1 : a ^ 2 + b ^ 2 + 2 * a * b * Real.cos θ₂ = r ^ 2 ↔
      Real.cos θ₂ = Real.cos (Real.pi - planarTwoLinkAlpha a b r) := by
    rw [Real.cos_pi_sub, hcosα, hκ]
    constructor
    · intro h
      field_simp
      linarith
    · intro h
      field_simp at h
      linarith
  rw [h1, Real.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨-k, Or.inr (by push_cast; linarith)⟩
    · exact ⟨k - 1, Or.inl (by push_cast; linarith)⟩
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k + 1, Or.inr (by push_cast; linarith)⟩
    · exact ⟨-k, Or.inl (by push_cast; linarith)⟩

private theorem alpha_cos_bounds {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r)
    (h₁ : |a - b| ≤ r) (h₂ : r ≤ a + b) :
    -1 ≤ (a ^ 2 + b ^ 2 - r ^ 2) / (2 * a * b) ∧ (a ^ 2 + b ^ 2 - r ^ 2) / (2 * a * b) ≤ 1 := by
  have hab : 0 < 2 * a * b := by positivity
  have hlo : (a - b) ^ 2 ≤ r ^ 2 := by
    have := abs_le.mp (h₁.trans (le_abs_self r))
    nlinarith [abs_nonneg (a - b), sq_abs (a - b), abs_le.mp h₁]
  have hhi : r ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hr h₂ 2
  constructor
  · rw [le_div_iff₀ hab]; nlinarith
  · rw [div_le_iff₀ hab]; nlinarith

/-- **MLS p. 98: when the two elbow angles differ.** For positive link lengths and a distance
`r` in the annulus, `|a - b| ≤ r ≤ a + b`, the two values `π + α` and `π - α` of eq. (3.16) are
distinct modulo `2π` exactly when `|a - b| < r < a + b`. On the boundary circles (`α = 0` at
`r = |a - b|`, `α = π` at `r = a + b`) they name one joint angle. The book's condition
"`α ≠ 0`" does not exclude `α = π`, where the two real values `0` and `2π` are the same angle
(p. 84). -/
theorem planarTwoLink_elbow_branches_ne_iff {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r)
    (h₁ : |a - b| ≤ r) (h₂ : r ≤ a + b) :
    (¬ ∃ k : ℤ, Real.pi + planarTwoLinkAlpha a b r =
        Real.pi - planarTwoLinkAlpha a b r + k * (2 * Real.pi)) ↔
      |a - b| < r ∧ r < a + b := by
  obtain ⟨hκ₁, hκ₂⟩ := alpha_cos_bounds ha hb hr h₁ h₂
  have hab : 0 < 2 * a * b := by positivity
  constructor
  · intro hne
    refine ⟨lt_of_le_of_ne h₁ fun heq => hne ?_, lt_of_le_of_ne h₂ fun heq => hne ?_⟩
    · apply PadenKahan.subproblemThree_branches_eq_of_abs_eq_one
      left
      rw [← heq, sq_abs, div_eq_one_iff_eq hab.ne']
      ring
    · apply PadenKahan.subproblemThree_branches_eq_of_abs_eq_one
      right
      rw [heq, div_eq_iff hab.ne']
      ring
  · rintro ⟨hlt₁, hlt₂⟩
    apply PadenKahan.subproblemThree_branches_ne_of_abs_lt_one
    · rw [lt_div_iff₀ hab]
      have : r ^ 2 < (a + b) ^ 2 := by
        have := abs_nonneg (a - b)
        nlinarith
      nlinarith
    · rw [div_lt_iff₀ hab]
      have : (a - b) ^ 2 < r ^ 2 := by
        have h := abs_nonneg (a - b)
        nlinarith [sq_abs (a - b)]
      nlinarith

/-- **MLS p. 98: no elbow angle outside the workspace.** For nonnegative link lengths, if the
target distance exceeds the reach, `r > l₁ + l₂` (the case the book asks the reader to consider),
or is below the inner radius, `0 ≤ r < |l₁ - l₂|` (not printed; the inner circle of the annulus,
ledger C01), then no `θ₂` satisfies the law of cosines `a² + b² + 2ab cos θ₂ = r²`: the
subproblem for `θ₂` has no solution. -/
theorem planarTwoLink_elbow_no_solution {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : a + b < r ∨ r < |a - b|) (θ₂ : ℝ) :
    a ^ 2 + b ^ 2 + 2 * a * b * Real.cos θ₂ ≠ r ^ 2 := by
  intro heq
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hc₁ := Real.neg_one_le_cos θ₂
  have hc₂ := Real.cos_le_one θ₂
  rcases h with h | h
  · have : (a + b) ^ 2 < r ^ 2 := by nlinarith
    nlinarith [mul_nonneg hab (by linarith : (0 : ℝ) ≤ 1 - Real.cos θ₂)]
  · have : r ^ 2 < (a - b) ^ 2 := by
      have := sq_abs (a - b)
      nlinarith
    nlinarith [mul_nonneg hab (by linarith : (0 : ℝ) ≤ 1 + Real.cos θ₂)]

/-- **MLS p. 98: no solution for `r > l₁ + l₂`.** For nonnegative link lengths, no joint vector
puts the tool of the planar two-link arm at the book's point `(x, y)` when
`√(x² + y²) > a + b`, nor when `√(x² + y²) < |a - b|` (the inner bound is not printed; it is
the inner circle of the annulus, ledger C01). -/
theorem planarTwoLink_inverseKinematics_no_solution {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b < √(x ^ 2 + y ^ 2) ∨ √(x ^ 2 + y ^ 2) < |a - b|) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q ≠ vec (-y) x 0 := by
  intro heq
  have hn := planarTwoLinkPosition_norm_sq a b q
  rw [heq, norm_vec_neg] at hn
  exact planarTwoLink_elbow_no_solution ha hb (Real.sqrt_nonneg _) h (q 1) hn.symm

/-! ### The complete solution -/

private theorem rotate_form {a b r x y θ₁ θ₂ ψ : ℝ}
    (hc : a + b * Real.cos θ₂ = r * Real.cos ψ) (hs : b * Real.sin θ₂ = r * Real.sin ψ) :
    (a * Real.cos θ₁ + b * Real.cos (θ₁ + θ₂) = x ∧ a * Real.sin θ₁ + b * Real.sin (θ₁ + θ₂) = y)
      ↔ (r * Real.cos (θ₁ + ψ) = x ∧ r * Real.sin (θ₁ + ψ) = y) := by
  have e1 : a * Real.cos θ₁ + b * Real.cos (θ₁ + θ₂) = r * Real.cos (θ₁ + ψ) := by
    rw [Real.cos_add, Real.cos_add]
    linear_combination Real.cos θ₁ * hc - Real.sin θ₁ * hs
  have e2 : a * Real.sin θ₁ + b * Real.sin (θ₁ + θ₂) = r * Real.sin (θ₁ + ψ) := by
    rw [Real.sin_add, Real.sin_add]
    linear_combination Real.sin θ₁ * hc + Real.cos θ₁ * hs
  rw [e1, e2]

private theorem polar_iff {r x y u : ℝ} (hr : 0 < r) (hxy : r = √(x ^ 2 + y ^ 2)) :
    (r * Real.cos u = x ∧ r * Real.sin u = y) ↔
      ∃ m : ℤ, u = Rotation.atan2 y x + m * (2 * Real.pi) := by
  have hc := Rotation.sqrt_mul_cos_atan2 y x
  have hs := Rotation.sqrt_mul_sin_atan2 y x
  rw [← hxy] at hc hs
  constructor
  · rintro ⟨h1, h2⟩
    have hcos : Real.cos u = Real.cos (Rotation.atan2 y x) := by
      apply mul_left_cancel₀ hr.ne'
      rw [h1, hc]
    have hsin : Real.sin u = Real.sin (Rotation.atan2 y x) := by
      apply mul_left_cancel₀ hr.ne'
      rw [h2, hs]
    obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hcos hsin)
    exact ⟨m, by linarith⟩
  · rintro ⟨m, rfl⟩
    have e1 : Real.cos (Rotation.atan2 y x + m * (2 * Real.pi)) = Real.cos (Rotation.atan2 y x) :=
      by rw [Real.cos_add_int_mul_two_pi]
    have e2 : Real.sin (Rotation.atan2 y x + m * (2 * Real.pi)) = Real.sin (Rotation.atan2 y x) :=
      by rw [Real.sin_add_int_mul_two_pi]
    rw [e1, e2]
    exact ⟨hc, hs⟩

/-- The two triangle identities behind the printed solution (MLS p. 98, Figure 3.7b), for
positive lengths and `0 < r` in the annulus: `a - b cos α = r cos β` and `b sin α = r sin β`. -/
private theorem triangle_identities {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (h₁ : |a - b| ≤ r) (h₂ : r ≤ a + b) :
    a - b * Real.cos (planarTwoLinkAlpha a b r) = r * Real.cos (planarTwoLinkBeta a b r) ∧
      b * Real.sin (planarTwoLinkAlpha a b r) = r * Real.sin (planarTwoLinkBeta a b r) := by
  obtain ⟨hκ₁, hκ₂⟩ := alpha_cos_bounds ha hb hr.le h₁ h₂
  have har : 0 < 2 * a * r := by positivity
  have hab : 0 < 2 * a * b := by positivity
  have hb₀ := abs_le.mp h₁
  have hβ₁ : -1 ≤ (r ^ 2 + a ^ 2 - b ^ 2) / (2 * a * r) := by
    rw [le_div_iff₀ har]
    nlinarith
  have hβ₂ : (r ^ 2 + a ^ 2 - b ^ 2) / (2 * a * r) ≤ 1 := by
    rw [div_le_iff₀ har]
    nlinarith
  have hcα : Real.cos (planarTwoLinkAlpha a b r) = (a ^ 2 + b ^ 2 - r ^ 2) / (2 * a * b) :=
    Real.cos_arccos hκ₁ hκ₂
  have hcβ : Real.cos (planarTwoLinkBeta a b r) = (r ^ 2 + a ^ 2 - b ^ 2) / (2 * a * r) :=
    Real.cos_arccos hβ₁ hβ₂
  refine ⟨?_, ?_⟩
  · rw [hcα, hcβ]
    field_simp
    ring
  · have hsα : 0 ≤ Real.sin (planarTwoLinkAlpha a b r) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
    have hsβ : 0 ≤ Real.sin (planarTwoLinkBeta a b r) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
    have hsq : (b * Real.sin (planarTwoLinkAlpha a b r)) ^ 2 =
        (r * Real.sin (planarTwoLinkBeta a b r)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sin_sq, Real.sin_sq, hcα, hcβ]
      field_simp
      ring
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- **MLS eq. (3.16) and p. 98: the complete inverse kinematics of the planar two-link arm.**
For positive link lengths `a = l₁`, `b = l₂` and a target `(x, y)` of the book's plane at distance
`r = √(x² + y²)` with `0 < r` and `|a - b| ≤ r ≤ a + b`, a joint vector `q` (`θ₁ = q 0`,
`θ₂ = q 1`) puts the tool at `(x, y)` (the library point `vec (-y) x 0`) exactly when, modulo
`2π` in each angle, either `θ₂ = π + α` and `θ₁ = atan2(y, x) + β`, or `θ₂ = π - α` and
`θ₁ = atan2(y, x) - β`, with `α = planarTwoLinkAlpha a b r` and `β = planarTwoLinkBeta a b r`:
"the sign used for `β` agrees with that used for `α`". The book does not state `0 < a, b` or
`r ≠ 0`; the case `r = 0` is `planarTwoLink_inverseKinematics_origin`. -/
theorem planarTwoLink_inverseKinematics_iff {a b x y r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : r = √(x ^ 2 + y ^ 2)) (hr₀ : 0 < r) (h₁ : |a - b| ≤ r) (h₂ : r ≤ a + b)
    (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q = vec (-y) x 0 ↔
      (∃ k m : ℤ, q 1 = Real.pi + planarTwoLinkAlpha a b r + k * (2 * Real.pi) ∧
          q 0 = Rotation.atan2 y x + planarTwoLinkBeta a b r + m * (2 * Real.pi)) ∨
        (∃ k m : ℤ, q 1 = Real.pi - planarTwoLinkAlpha a b r + k * (2 * Real.pi) ∧
          q 0 = Rotation.atan2 y x - planarTwoLinkBeta a b r + m * (2 * Real.pi)) := by
  obtain ⟨hκ₁, hκ₂⟩ := alpha_cos_bounds ha hb hr₀.le h₁ h₂
  obtain ⟨hcβ, hsβ⟩ := triangle_identities ha hb hr₀ h₁ h₂
  set α := planarTwoLinkAlpha a b r
  set β := planarTwoLinkBeta a b r
  -- the plus branch: `a + b cos θ₂ = r cos(-β)`, `b sin θ₂ = r sin(-β)`
  have plus : ∀ k : ℤ, q 1 = Real.pi + α + k * (2 * Real.pi) →
      (planarTwoLinkPosition a b q = vec (-y) x 0 ↔
        ∃ m : ℤ, q 0 = Rotation.atan2 y x + β + m * (2 * Real.pi)) := by
    intro k hk
    have ec : Real.cos (q 1) = -Real.cos α := by
      rw [hk, Real.cos_add_int_mul_two_pi, add_comm, Real.cos_add_pi]
    have es : Real.sin (q 1) = -Real.sin α := by
      rw [hk, Real.sin_add_int_mul_two_pi, add_comm, Real.sin_add_pi]
    rw [planarTwoLinkPosition_eq_vec_iff, rotate_form (ψ := -β) (r := r)
      (by rw [ec, Real.cos_neg]; linarith) (by rw [es, Real.sin_neg]; linarith),
      polar_iff hr₀ hr]
    exact exists_congr fun m => by constructor <;> intro h <;> linarith
  -- the minus branch: `a + b cos θ₂ = r cos β`, `b sin θ₂ = r sin β`
  have minus : ∀ k : ℤ, q 1 = Real.pi - α + k * (2 * Real.pi) →
      (planarTwoLinkPosition a b q = vec (-y) x 0 ↔
        ∃ m : ℤ, q 0 = Rotation.atan2 y x - β + m * (2 * Real.pi)) := by
    intro k hk
    have ec : Real.cos (q 1) = -Real.cos α := by
      rw [hk, Real.cos_add_int_mul_two_pi, Real.cos_pi_sub]
    have es : Real.sin (q 1) = Real.sin α := by
      rw [hk, Real.sin_add_int_mul_two_pi, Real.sin_pi_sub]
    rw [planarTwoLinkPosition_eq_vec_iff, rotate_form (ψ := β) (r := r)
      (by rw [ec]; linarith) (by rw [es]; linarith), polar_iff hr₀ hr]
    exact exists_congr fun m => by constructor <;> intro h <;> linarith
  constructor
  · intro h
    have hn := planarTwoLinkPosition_norm_sq a b q
    rw [h, norm_vec_neg, ← hr] at hn
    obtain ⟨k, hk | hk⟩ :=
      (planarTwoLink_elbow_iff ha.ne' hb.ne' hκ₁ hκ₂ (q 1)).mp hn.symm
    · exact Or.inl ⟨k, ((plus k hk).mp h).choose, hk, ((plus k hk).mp h).choose_spec⟩
    · exact Or.inr ⟨k, ((minus k hk).mp h).choose, hk, ((minus k hk).mp h).choose_spec⟩
  · rintro (⟨k, m, hk, hm⟩ | ⟨k, m, hk, hm⟩)
    · exact (plus k hk).mpr ⟨m, hm⟩
    · exact (minus k hk).mpr ⟨m, hm⟩

/-- **MLS p. 98, the plus branch reaches the target.** Under the hypotheses of
`planarTwoLink_inverseKinematics_iff`, the joint vector `θ₁ = atan2(y, x) + β`, `θ₂ = π + α`
puts the tool at the book's point `(x, y)`. -/
theorem planarTwoLink_inverseKinematics_plus {a b x y r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : r = √(x ^ 2 + y ^ 2)) (hr₀ : 0 < r) (h₁ : |a - b| ≤ r) (h₂ : r ≤ a + b) :
    planarTwoLinkPosition a b
        ![Rotation.atan2 y x + planarTwoLinkBeta a b r, Real.pi + planarTwoLinkAlpha a b r] =
      vec (-y) x 0 :=
  (planarTwoLink_inverseKinematics_iff ha hb hr hr₀ h₁ h₂ _).mpr
    (Or.inl ⟨0, 0, by simp, by simp⟩)

/-- **MLS p. 98, the minus branch (the "flip solution" of Figure 3.7b, or the original one: the
book does not fix which is which) reaches the target.** Under the hypotheses of
`planarTwoLink_inverseKinematics_iff`, `θ₁ = atan2(y, x) - β`, `θ₂ = π - α` puts the tool at the
book's point `(x, y)`. -/
theorem planarTwoLink_inverseKinematics_minus {a b x y r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : r = √(x ^ 2 + y ^ 2)) (hr₀ : 0 < r) (h₁ : |a - b| ≤ r) (h₂ : r ≤ a + b) :
    planarTwoLinkPosition a b
        ![Rotation.atan2 y x - planarTwoLinkBeta a b r, Real.pi - planarTwoLinkAlpha a b r] =
      vec (-y) x 0 :=
  (planarTwoLink_inverseKinematics_iff ha hb hr hr₀ h₁ h₂ _).mpr
    (Or.inr ⟨0, 0, by simp, by simp⟩)

/-- **The case `r = 0` (not covered by the formula of MLS p. 98).** For equal nonzero link
lengths `a = b`, the tool of the planar two-link arm is at the base origin (the book's point
`(0, 0)`, `r = 0`) exactly when `θ₂ = π` modulo `2π`, for every `θ₁`; the printed formula for `β`
divides by `r` and leaves this case out. For `a ≠ b` the origin is not reachable
(`planarTwoLink_inverseKinematics_no_solution` with `r = 0 < |a - b|`). -/
theorem planarTwoLink_inverseKinematics_origin {a : ℝ} (ha : a ≠ 0) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a a q = 0 ↔ ∃ k : ℤ, q 1 = Real.pi + k * (2 * Real.pi) := by
  rw [planarTwoLinkPosition_eq_zero_iff ha, ← Real.cos_pi, Real.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨-k, by push_cast; linarith⟩
    · exact ⟨k - 1, by push_cast; linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, Or.inl (by push_cast; linarith)⟩

/-- **Relation to the workspace row C02.** The elbow angle `arccos((r² - a² - b²)/(2ab))` of the
existence construction `exists_planarTwoLinkPosition_eq` is the minus branch `π - α` of
MLS eq. (3.16), p. 98, for all real `a, b, r` (`arccos(-t) = π - arccos t`). -/
theorem arccos_elbow_eq_pi_sub_alpha (a b r : ℝ) :
    Real.arccos ((r ^ 2 - a ^ 2 - b ^ 2) / (2 * a * b)) = Real.pi - planarTwoLinkAlpha a b r := by
  rw [planarTwoLinkAlpha, ← Real.arccos_neg]
  congr 1
  ring

end RoboLean.Examples
