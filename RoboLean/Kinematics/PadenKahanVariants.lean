import RoboLean.Kinematics.PadenKahan

/-!
# Variants of the Paden–Kahan subproblems (MLS Exercises 5–7)

MLS §3.8, printed pp. 147–148.

* Subproblem 5 (Exercise 7, translation to a given distance): for a unit prismatic twist
  `ξ = (v, 0)` (infinite pitch, unit magnitude), `‖q - e^{ξ̂θ} p‖ = δ` holds exactly for
  `θ = vᵀ(q - p) ± √D` with `D = (vᵀ(q - p))² - ‖q - p‖² + δ²` when `D ≥ 0`, and has no solution
  when `D < 0`; there are at most two solutions.
* Subproblem 4 (Exercise 6, rotation about two intersecting axes to given distances): the
  reduction of the printed hint, the image point `c = e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p` lies on the three
  spheres centred at `q₁`, `q₂` and the intersection point `r`, of radii `δ₁`, `δ₂` and
  `‖p - r‖`; conversely each such `c` reached by Subproblem 2 gives a solution.
* Subproblem 2′ (Exercise 5, rotation about two non-intersecting axes): the angles exist exactly
  when some intermediate point `c` is reachable from `p` about the second axis and reaches `q`
  about the first, i.e. satisfies the conditions (3.19) of Subproblem 1 for both.

The use of these subproblems for the SCARA robot (Exercise 7) is in the SCARA kinematics
example; the elbow with non-intersecting shoulder axes (Exercise 5) is not treated.
Conventions as in `RoboLean.Kinematics.PadenKahan`: unit axes as explicit hypotheses, points
acted on by `RigidTransform.applyPoint`, angles in the real lift.
-/

noncomputable section

namespace RoboLean

namespace PadenKahan

/-- The discriminant `D = (vᵀ(q - p))² - ‖q - p‖² + δ²` of Subproblem 5 (MLS Exercise 7,
p. 148): the solutions are `vᵀ(q - p) ± √D`. -/
def subproblemFiveDisc (v p q : Vec3) (δ : ℝ) : ℝ :=
  inner ℝ v (q - p) ^ 2 - ‖q - p‖ ^ 2 + δ ^ 2

/-- The squared distance of Subproblem 5 is `(θ - vᵀ(q - p))² - D + δ²`. -/
private theorem subproblemFive_norm_sq {v : Vec3} (hv : ‖v‖ = 1) (p q : Vec3) (δ θ : ℝ) :
    ‖q - (Twist.exp (Twist.prismatic v) θ).applyPoint p‖ ^ 2 =
      (θ - inner ℝ v (q - p)) ^ 2 - subproblemFiveDisc v p q δ + δ ^ 2 := by
  have hap : (Twist.exp (Twist.prismatic v) θ).applyPoint p = p + θ • v := by
    rw [Twist.exp_prismatic]
    simp [RigidTransform.applyPoint]
  rw [hap, show q - (p + θ • v) = (q - p) - θ • v by abel, norm_sub_sq_real, norm_smul, hv,
    inner_smul_right, real_inner_comm, subproblemFiveDisc]
  simp only [Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- **MLS Exercise 7, p. 148: Subproblem 5, translation to a given distance.** For a unit
prismatic twist `ξ = (v, 0)` and `δ ≥ 0` (the book takes `δ > 0`), if the discriminant `D` is
nonnegative then `‖q - e^{ξ̂θ} p‖ = δ` holds exactly for `θ = vᵀ(q - p) + √D` and
`θ = vᵀ(q - p) - √D`. -/
theorem subproblemFive_iff {v : Vec3} (hv : ‖v‖ = 1) (p q : Vec3) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 0 ≤ subproblemFiveDisc v p q δ) (θ : ℝ) :
    ‖q - (Twist.exp (Twist.prismatic v) θ).applyPoint p‖ = δ ↔
      θ = inner ℝ v (q - p) + Real.sqrt (subproblemFiveDisc v p q δ) ∨
        θ = inner ℝ v (q - p) - Real.sqrt (subproblemFiveDisc v p q δ) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) hδ, subproblemFive_norm_sq hv,
    show ∀ x : ℝ, x - subproblemFiveDisc v p q δ + δ ^ 2 = δ ^ 2 ↔
      x = Real.sqrt (subproblemFiveDisc v p q δ) ^ 2 from fun x => by
        rw [Real.sq_sqrt hD]
        constructor <;> intro h <;> linarith,
    sq_eq_sq_iff_eq_or_eq_neg]
  constructor <;> rintro (h | h)
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith

/-- **MLS Exercise 7, p. 148: no solution of Subproblem 5 when `D < 0`** (the line through `p`
along `v` misses the sphere of radius `δ` about `q`), for every real `δ`. -/
theorem subproblemFive_no_solution {v : Vec3} (hv : ‖v‖ = 1) (p q : Vec3) {δ : ℝ}
    (hD : subproblemFiveDisc v p q δ < 0) (θ : ℝ) :
    ‖q - (Twist.exp (Twist.prismatic v) θ).applyPoint p‖ ≠ δ := by
  intro h
  have h2 := subproblemFive_norm_sq hv p q δ θ
  rw [h] at h2
  nlinarith [sq_nonneg (θ - inner ℝ v (q - p))]

/-- **MLS Exercise 6, pp. 147–148: Subproblem 4, the hint.** For unit revolute twists
`ξ₁ = (-ω₁ × r, ω₁)`, `ξ₂ = (-ω₂ × r, ω₂)` whose axes meet at `r`, the angles `θ₁, θ₂` solve
`‖e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p - q₁‖ = δ₁` and `‖e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p - q₂‖ = δ₂` exactly when the image
point `c = e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p` lies on the three spheres centred at `q₁`, `q₂` and `r` of radii
`δ₁`, `δ₂` and `‖p - r‖`; finding `θ₁, θ₂` from `c` is Subproblem 2. -/
theorem subproblemFour_iff {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (r p q₁ q₂ : Vec3) (δ₁ δ₂ θ₁ θ₂ : ℝ) :
    (‖(Twist.exp (Twist.revolute ω₁ r) θ₁ * Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p -
          q₁‖ = δ₁ ∧
        ‖(Twist.exp (Twist.revolute ω₁ r) θ₁ * Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p -
          q₂‖ = δ₂) ↔
      ∃ c : Vec3, ‖c - q₁‖ = δ₁ ∧ ‖c - q₂‖ = δ₂ ∧ ‖c - r‖ = ‖p - r‖ ∧
        (Twist.exp (Twist.revolute ω₁ r) θ₁ * Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p =
          c := by
  have hr : ‖(Twist.exp (Twist.revolute ω₁ r) θ₁ *
      Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p - r‖ = ‖p - r‖ := by
    rw [RigidTransform.mul_applyPoint, Twist.exp_revolute_applyPoint ω₂ r hω₂,
      Twist.exp_revolute_applyPoint ω₁ r hω₁, add_sub_cancel_right, add_sub_cancel_right,
      Rotation.norm_act, Rotation.norm_act]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, h₁, h₂, hr, rfl⟩
  · rintro ⟨c, h₁, h₂, -, rfl⟩
    exact ⟨h₁, h₂⟩

/-- **MLS Exercise 5, p. 147: Subproblem 2′, rotation about two non-intersecting axes.** For
unit revolute twists `ξ₁ = (-ω₁ × r₁, ω₁)` and `ξ₂ = (-ω₂ × r₂, ω₂)` with arbitrary axis points,
some angles give `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` exactly when some point `c` satisfies the conditions
(3.19) of Subproblem 1 (MLS p. 100) both for rotating `p` to `c` about the second axis and for
rotating `c` to `q` about the first: `ω₂ᵀ(p - r₂) = ω₂ᵀ(c - r₂)`, `‖(p - r₂)′‖ = ‖(c - r₂)′‖`,
`ω₁ᵀ(c - r₁) = ω₁ᵀ(q - r₁)` and `‖(c - r₁)′‖ = ‖(q - r₁)′‖` (projections `′` perpendicular to the
respective axis). -/
theorem subproblemTwoPrime_exists_iff {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (r₁ r₂ p q : Vec3) :
    (∃ θ₁ θ₂ : ℝ,
        (Twist.exp (Twist.revolute ω₁ r₁) θ₁ * Twist.exp (Twist.revolute ω₂ r₂) θ₂).applyPoint p =
          q) ↔
      ∃ c : Vec3, (inner ℝ ω₂ (p - r₂) = inner ℝ ω₂ (c - r₂) ∧
          ‖Vec3.perp ω₂ (p - r₂)‖ = ‖Vec3.perp ω₂ (c - r₂)‖) ∧
        (inner ℝ ω₁ (c - r₁) = inner ℝ ω₁ (q - r₁) ∧
          ‖Vec3.perp ω₁ (c - r₁)‖ = ‖Vec3.perp ω₁ (q - r₁)‖) := by
  constructor
  · rintro ⟨θ₁, θ₂, h⟩
    refine ⟨(Twist.exp (Twist.revolute ω₂ r₂) θ₂).applyPoint p,
      (subproblemOne_exists_iff hω₂ r₂ p _).mp ⟨θ₂, rfl⟩,
      (subproblemOne_exists_iff hω₁ r₁ _ q).mp ⟨θ₁, ?_⟩⟩
    rw [← h, RigidTransform.mul_applyPoint]
  · rintro ⟨c, h₂, h₁⟩
    obtain ⟨θ₂, hθ₂⟩ := (subproblemOne_exists_iff hω₂ r₂ p c).mpr h₂
    obtain ⟨θ₁, hθ₁⟩ := (subproblemOne_exists_iff hω₁ r₁ c q).mpr h₁
    exact ⟨θ₁, θ₂, by rw [RigidTransform.mul_applyPoint, hθ₂, hθ₁]⟩

end PadenKahan

end RoboLean
