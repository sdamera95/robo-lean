import RoboLean.Kinematics.SerialChain
import RoboLean.Geometry.RotationSurjectivity
import RoboLean.Geometry.RotationParameters
import RoboLean.Geometry.EulerAngles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Paden–Kahan subproblems

MLS Chapter 3, §3.2, printed pp. 99–103: the three geometric subproblems used to solve
inverse kinematics with the product of exponentials.

Conventions.

* A "zero-pitch twist with unit magnitude" (p. 99) is a revolute joint twist
  `Twist.revolute ω r = (-ω × r, ω)` with `‖ω‖ = 1`; `r` is a point on its axis (ledger K03).
  Unit axes are explicit hypotheses.
* Points and free vectors are both `Vec3`; the twist exponential acts on points by
  `RigidTransform.applyPoint`, so `e^{ξ̂θ} p` is `(Twist.exp ξ θ).applyPoint p`.
* Angles are real numbers; solutions are described up to integer multiples of `2π` (ledger
  K01). `atan2 y x` is the library's `Rotation.atan2` (Euler-angle module), the argument of
  `x + i y` in `(-π, π]`, with `atan2 0 0 = 0`.
* `Vec3.perp ω u` is the projection `u′ = u - ω ωᵀ u` onto the plane perpendicular to `ω`, and
  `planeAngle ω u v` is the angle `atan2(ωᵀ(u′ × v′), u′ᵀv′)` of eq. (3.28).

Contents.

* The law-of-cosines identity `norm_sub_exp_act_sq` behind Subproblems 1 and 3:
  `‖v - e^{ω̂θ} u‖² = (ωᵀ(v - u))² + ‖u′‖² + ‖v′‖² - 2‖u′‖‖v′‖ cos(θ₀ - θ)`.
* Subproblem 1 (rotation about a single axis, eqs. (3.17)–(3.19), pp. 99–100): the necessary
  conditions (3.19), existence exactly under them, the atan2 solution, uniqueness modulo `2π`
  when `u′ ≠ 0`, and the case `u′ = 0` (`p = q` on the axis, every angle a solution).
* Subproblem 2 (two subsequent rotations about intersecting axes, eqs. (3.20)–(3.25),
  pp. 100–102): the coincident-axes reduction, and for non-parallel axes the decomposition
  (3.24) of the intermediate vector, existence exactly when `‖p - r‖ = ‖q - r‖` and the value
  of `γ²` is nonnegative, and the zero/one/two branch structure of the intermediate point.
* Subproblem 3 (rotation to a given distance, eqs. (3.26)–(3.29), pp. 102–103): the projected
  distance and law of cosines, the solutions `θ₀ ± cos⁻¹ κ` modulo `2π`, and the zero/one/two
  branch structure.

Hypotheses the book does not state are explicit and named in the docstrings: the
nondegeneracy `u′ ≠ 0`, `v′ ≠ 0` of Subproblem 3; the equal-norm condition of Subproblem 2,
which the book lists as a consequence on p. 101 but which existence also requires; and, for
Subproblem 2, intersecting axes are modelled by a common axis point `r`. The branch count of
Subproblem 2 is a count of intermediate points `c` of eq. (3.21); the number of angle pairs
also depends on whether `p` or `q` lies on an axis (Subproblem 1 then has every angle as a
solution). These are statements about the coordinate model, not about a physical arm or a
numerical solver.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace PadenKahan

/-! ### Supporting vector identities -/

private theorem inner_eq_dot (x y : Vec3) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

private theorem cross_cross_right (a b c : Vec3) :
    Vec3.cross a (Vec3.cross b c) = inner ℝ a c • b - inner ℝ a b • c := by
  apply WithLp.ofLp_injective
  simp only [Vec3.cross_coordinates, WithLp.ofLp_sub, WithLp.ofLp_smul, inner_eq_dot]
  rw [cross_cross_eq_smul_sub_smul', dotProduct_comm (WithLp.ofLp b)]

private theorem inner_cross_eq (a b c : Vec3) :
    inner ℝ (Vec3.cross a b) c = inner ℝ a (Vec3.cross b c) := by
  simp only [inner_eq_dot, Vec3.cross_coordinates]
  rw [dotProduct_comm, triple_product_permutation]

private theorem eq_inner_smul_of_cross_eq_zero {ω z : Vec3} (hω : ‖ω‖ = 1)
    (h : Vec3.cross ω z = 0) : z = inner ℝ ω z • ω := by
  have h2 := cross_cross_right ω ω z
  rw [h, Vec3.cross_zero, real_inner_self_eq_norm_sq, hω] at h2
  simp only [one_pow, one_smul] at h2
  exact (sub_eq_zero.mp h2.symm).symm

/-! ### The two-argument arctangent

`Rotation.atan2 y x` (from `RoboLean.Geometry.EulerAngles`) is the argument of `x + i y`, in
`(-π, π]`; at the origin it is `0`, where the book leaves `atan2(0, 0)` undefined. Its polar-form
lemmas `Rotation.sqrt_mul_cos_atan2` and `Rotation.sqrt_mul_sin_atan2` live next to it. -/

/-! ### Projection onto the plane perpendicular to an axis -/

@[deprecated Vec3.perp (since := "2026-10-11")]
alias perp := Vec3.perp

@[deprecated Vec3.inner_perp (since := "2026-10-13")]
alias inner_perp := Vec3.inner_perp

@[deprecated Vec3.norm_perp_sq (since := "2026-10-13")]
alias norm_perp_sq := Vec3.norm_perp_sq

@[deprecated Vec3.inner_perp_perp (since := "2026-10-13")]
alias inner_perp_perp := Vec3.inner_perp_perp

@[deprecated Vec3.cross_perp (since := "2026-10-13")]
alias cross_perp := Vec3.cross_perp

@[deprecated Rotation.exp_act_eq (since := "2026-10-11")]
alias exp_act_eq := Rotation.exp_act_eq

/-- The angle `θ₀ = atan2(ωᵀ(u′ × v′), u′ᵀv′)` between the projections `u′` and `v′` of `u`
and `v` onto the plane perpendicular to `ω`, measured about `ω`: MLS eq. (3.28), p. 103, and
the solution formula of Subproblem 1, p. 100. -/
def planeAngle (ω u v : Vec3) : ℝ :=
  Rotation.atan2 (inner ℝ ω (Vec3.cross (Vec3.perp ω u) (Vec3.perp ω v)))
    (inner ℝ (Vec3.perp ω u) (Vec3.perp ω v))

/-- **The law-of-cosines identity behind Subproblems 1 and 3** (MLS eqs. (3.27)–(3.29),
pp. 102–103). For a unit axis `ω`, every pair of vectors `u, v` and every angle `θ`,
`‖v - e^{ω̂θ} u‖² = (ωᵀ(v - u))² + ‖u′‖² + ‖v′‖² - 2 ‖u′‖ ‖v′‖ cos(θ₀ - θ)`, with
`θ₀ = planeAngle ω u v`. The first term is the book's projection of `δ` along the axis and the
rest is the law of cosines in the perpendicular plane. No nondegeneracy is assumed: when
`u′ = 0` or `v′ = 0` the cosine term vanishes. -/
theorem norm_sub_exp_act_sq {ω : Vec3} (hω : ‖ω‖ = 1) (u v : Vec3) (θ : ℝ) :
    ‖v - (Rotation.exp ω θ).act u‖ ^ 2 =
      inner ℝ ω (v - u) ^ 2 + ‖Vec3.perp ω u‖ ^ 2 + ‖Vec3.perp ω v‖ ^ 2 -
        2 * ‖Vec3.perp ω u‖ * ‖Vec3.perp ω v‖ * Real.cos (planeAngle ω u v - θ) := by
  set x := inner ℝ (Vec3.perp ω u) (Vec3.perp ω v) with hx
  set y := inner ℝ ω (Vec3.cross (Vec3.perp ω u) (Vec3.perp ω v)) with hy
  -- the plane vectors are perpendicular to the axis, so `u′ × v′ = y ω`
  have hpar : Vec3.cross (Vec3.perp ω u) (Vec3.perp ω v) = y • ω := by
    apply eq_inner_smul_of_cross_eq_zero hω
    rw [cross_cross_right, Vec3.inner_perp hω, Vec3.inner_perp hω, zero_smul, zero_smul, sub_zero]
  have hxy : x ^ 2 + y ^ 2 = (‖Vec3.perp ω u‖ * ‖Vec3.perp ω v‖) ^ 2 := by
    have h := Vec3.norm_cross_sq (Vec3.perp ω u) (Vec3.perp ω v)
    rw [hpar, norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs, ← hx] at h
    rw [mul_pow]
    linarith
  have hm : √(x ^ 2 + y ^ 2) = ‖Vec3.perp ω u‖ * ‖Vec3.perp ω v‖ := by
    rw [hxy, Real.sqrt_sq (by positivity)]
  have hc := Rotation.sqrt_mul_cos_atan2 y x
  have hs := Rotation.sqrt_mul_sin_atan2 y x
  rw [hm] at hc hs
  -- the inner product of `v` with the rotated `u`
  have hv : v = inner ℝ ω v • ω + Vec3.perp ω v := by simp [Vec3.perp]
  have hwv : inner ℝ (Vec3.cross ω (Vec3.perp ω u)) v =
      inner ℝ (Vec3.cross ω (Vec3.perp ω u)) (Vec3.perp ω v) := by
    conv_lhs => rw [hv]
    rw [inner_add_right, inner_smul_right, real_inner_comm ω (Vec3.cross ω (Vec3.perp ω u)),
      Vec3.inner_cross_left, mul_zero, zero_add]
  have hy' : inner ℝ v (Vec3.cross ω (Vec3.perp ω u)) = y := by
    rw [real_inner_comm (Vec3.cross ω (Vec3.perp ω u)) v, hwv, inner_cross_eq]
  have hvu : inner ℝ v (Vec3.perp ω u) = inner ℝ u v - inner ℝ ω u * inner ℝ ω v := by
    simp only [Vec3.perp, inner_sub_right, inner_smul_right, real_inner_comm v ω,
      real_inner_comm v u]
  have hin : inner ℝ v ((Rotation.exp ω θ).act u) =
      inner ℝ ω u * inner ℝ ω v + Real.cos θ * x + Real.sin θ * y := by
    rw [Rotation.exp_act_eq hω, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, inner_smul_right, hy', hvu, real_inner_comm ω v, hx,
      Vec3.inner_perp_perp hω]
  have hu2 := Vec3.norm_perp_sq hω u
  have hv2 := Vec3.norm_perp_sq hω v
  rw [norm_sub_sq_real, Rotation.norm_act, hin, Real.cos_sub, inner_sub_right]
  unfold planeAngle
  rw [← hx, ← hy]
  linear_combination (-1) * hu2 + (-1) * hv2 + 2 * Real.cos θ * hc + 2 * Real.sin θ * hs

/-! ### Subproblem 1: rotation about a single axis (MLS pp. 99–100) -/

/-- **MLS eqs. (3.17)–(3.18), p. 99.** For the zero-pitch unit twist `ξ = (-ω × r, ω)` of a
revolute joint whose axis passes through `r`, `e^{ξ̂θ} p = q` holds exactly when the rotation
`e^{ω̂θ}` carries `u = p - r` to `v = q - r`. Points and vectors are both `Vec3`; the point
action is `RigidTransform.applyPoint`. -/
theorem applyPoint_exp_revolute_eq_iff {ω : Vec3} (hω : ‖ω‖ = 1) (r p q : Vec3) (θ : ℝ) :
    (Twist.exp (Twist.revolute ω r) θ).applyPoint p = q ↔
      (Rotation.exp ω θ).act (p - r) = q - r := by
  rw [Twist.exp_revolute_applyPoint ω r hω, eq_sub_iff_add_eq]

private theorem eq_iff_norm_sub_sq_eq_zero (a b : Vec3) : a = b ↔ ‖b - a‖ ^ 2 = 0 := by
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero, eq_comm]

/-- The distance form of Subproblem 1 (MLS p. 100): with `u = p - r`, `v = q - r`, the
equation `e^{ξ̂θ} p = q` of (3.17) holds exactly when
`(ωᵀ(v - u))² + (‖u′‖ - ‖v′‖)² + 2 ‖u′‖ ‖v′‖ (1 - cos(θ₀ - θ)) = 0`, a sum of three
nonnegative terms, with `θ₀ = planeAngle ω u v`. -/
theorem subproblemOne_iff_sum_eq_zero {ω : Vec3} (hω : ‖ω‖ = 1) (r p q : Vec3) (θ : ℝ) :
    (Twist.exp (Twist.revolute ω r) θ).applyPoint p = q ↔
      inner ℝ ω ((q - r) - (p - r)) ^ 2 + (‖Vec3.perp ω (p - r)‖ - ‖Vec3.perp ω (q - r)‖) ^ 2 +
        2 * ‖Vec3.perp ω (p - r)‖ * ‖Vec3.perp ω (q - r)‖ *
          (1 - Real.cos (planeAngle ω (p - r) (q - r) - θ)) = 0 := by
  rw [applyPoint_exp_revolute_eq_iff hω, eq_iff_norm_sub_sq_eq_zero, norm_sub_exp_act_sq hω]
  constructor <;> intro h <;> linear_combination h

/-- **MLS eq. (3.19), p. 100: the necessary conditions of Subproblem 1.** If `e^{ξ̂θ} p = q`
for the unit revolute twist through `r` with axis `ω`, then `u = p - r` and `v = q - r` have
equal projections onto the axis, `ωᵀu = ωᵀv`, and equal projections onto the perpendicular
plane, `‖u′‖ = ‖v′‖`. -/
theorem subproblemOne_necessary {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3} {θ : ℝ}
    (h : (Twist.exp (Twist.revolute ω r) θ).applyPoint p = q) :
    inner ℝ ω (p - r) = inner ℝ ω (q - r) ∧ ‖Vec3.perp ω (p - r)‖ = ‖Vec3.perp ω (q - r)‖ := by
  rw [subproblemOne_iff_sum_eq_zero hω] at h
  set A := inner ℝ ω ((q - r) - (p - r))
  set P := ‖Vec3.perp ω (p - r)‖
  set Q := ‖Vec3.perp ω (q - r)‖
  have hc : 0 ≤ 1 - Real.cos (planeAngle ω (p - r) (q - r) - θ) := by
    linarith [Real.cos_le_one (planeAngle ω (p - r) (q - r) - θ)]
  have h3 : 0 ≤ 2 * P * Q * (1 - Real.cos (planeAngle ω (p - r) (q - r) - θ)) := by
    positivity
  have hA : A ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg (P - Q)]
  have hPQ : (P - Q) ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg (P - Q)]
  refine ⟨?_, ?_⟩
  · have hA0 : A = 0 := pow_eq_zero_iff two_ne_zero |>.mp hA
    have : A = inner ℝ ω (q - r) - inner ℝ ω (p - r) := inner_sub_right _ _ _
    linarith
  · have := pow_eq_zero_iff two_ne_zero |>.mp hPQ
    linarith

/-- **MLS p. 100: the solution formula of Subproblem 1.** If the conditions (3.19) hold, the
angle `θ = atan2(ωᵀ(u′ × v′), u′ᵀv′)` (`planeAngle ω u v`, with `u = p - r`, `v = q - r`)
solves `e^{ξ̂θ} p = q`. This direction needs no nondegeneracy: when `u′ = 0` every angle is a
solution, this one included. -/
theorem subproblemOne_planeAngle {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3}
    (h₁ : inner ℝ ω (p - r) = inner ℝ ω (q - r))
    (h₂ : ‖Vec3.perp ω (p - r)‖ = ‖Vec3.perp ω (q - r)‖) :
    (Twist.exp (Twist.revolute ω r) (planeAngle ω (p - r) (q - r))).applyPoint p = q := by
  rw [subproblemOne_iff_sum_eq_zero hω, inner_sub_right, h₁, h₂]
  simp

/-- **MLS p. 100: existence for Subproblem 1.** For the unit revolute twist through `r` with
axis `ω`, some angle `θ` satisfies `e^{ξ̂θ} p = q` if and only if the conditions (3.19) hold:
`ωᵀu = ωᵀv` and `‖u′‖ = ‖v′‖`, with `u = p - r`, `v = q - r`. -/
theorem subproblemOne_exists_iff {ω : Vec3} (hω : ‖ω‖ = 1) (r p q : Vec3) :
    (∃ θ : ℝ, (Twist.exp (Twist.revolute ω r) θ).applyPoint p = q) ↔
      inner ℝ ω (p - r) = inner ℝ ω (q - r) ∧ ‖Vec3.perp ω (p - r)‖ = ‖Vec3.perp ω (q - r)‖ := by
  constructor
  · rintro ⟨θ, h⟩
    exact subproblemOne_necessary hω h
  · rintro ⟨h₁, h₂⟩
    exact ⟨_, subproblemOne_planeAngle hω h₁ h₂⟩

/-- **MLS p. 100: uniqueness for Subproblem 1 when `u′ ≠ 0`.** Under the conditions (3.19) and
`u′ ≠ 0` (the point `p` is not on the axis), the solutions of `e^{ξ̂θ} p = q` are exactly the
angles `θ₀ + 2πk`, `k ∈ ℤ`, with `θ₀ = atan2(ωᵀ(u′ × v′), u′ᵀv′)`. The book determines `θ` by
the atan2 formula and leaves the `2π` ambiguity implicit (real-lift convention, ledger K01). -/
theorem subproblemOne_iff {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3}
    (h₁ : inner ℝ ω (p - r) = inner ℝ ω (q - r))
    (h₂ : ‖Vec3.perp ω (p - r)‖ = ‖Vec3.perp ω (q - r)‖)
    (hu : Vec3.perp ω (p - r) ≠ 0) (θ : ℝ) :
    (Twist.exp (Twist.revolute ω r) θ).applyPoint p = q ↔
      ∃ k : ℤ, θ = planeAngle ω (p - r) (q - r) + k * (2 * Real.pi) := by
  rw [subproblemOne_iff_sum_eq_zero hω, inner_sub_right, h₁, ← h₂, sub_self, sub_self]
  have hP : 0 < ‖Vec3.perp ω (p - r)‖ := norm_pos_iff.mpr hu
  constructor
  · intro h
    have hcos : Real.cos (planeAngle ω (p - r) (q - r) - θ) = 1 := by
      have h' : 2 * ‖Vec3.perp ω (p - r)‖ ^ 2 *
          (1 - Real.cos (planeAngle ω (p - r) (q - r) - θ)) = 0 := by
        linear_combination h
      have hP2 : 2 * ‖Vec3.perp ω (p - r)‖ ^ 2 ≠ 0 := by positivity
      have := (mul_eq_zero.mp h').resolve_left hP2
      linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcos
    exact ⟨-n, by push_cast; linarith⟩
  · rintro ⟨k, rfl⟩
    have hcos : Real.cos (planeAngle ω (p - r) (q - r) -
        (planeAngle ω (p - r) (q - r) + k * (2 * Real.pi))) = 1 := by
      rw [sub_add_cancel_left, Real.cos_neg, Real.cos_int_mul_two_pi]
    rw [hcos]
    ring

/-- **MLS p. 100: the degenerate case of Subproblem 1.** If the conditions (3.19) hold and
`u′ = 0`, then `p = q`, the point `p` lies on the axis through `r` with direction `ω`, and every
angle `θ` solves `e^{ξ̂θ} p = q` ("an infinite number of solutions"). -/
theorem subproblemOne_of_perp_eq_zero {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3}
    (h₁ : inner ℝ ω (p - r) = inner ℝ ω (q - r))
    (h₂ : ‖Vec3.perp ω (p - r)‖ = ‖Vec3.perp ω (q - r)‖)
    (hu : Vec3.perp ω (p - r) = 0) :
    p = q ∧ p ∈ axisLine r ω ∧
      ∀ θ : ℝ, (Twist.exp (Twist.revolute ω r) θ).applyPoint p = q := by
  have hv : Vec3.perp ω (q - r) = 0 := by
    rw [← norm_eq_zero, ← h₂, hu, norm_zero]
  have hpu : p - r = inner ℝ ω (p - r) • ω := by
    simpa [Vec3.perp, sub_eq_zero] using hu
  have hqv : q - r = inner ℝ ω (q - r) • ω := by
    simpa [Vec3.perp, sub_eq_zero] using hv
  have hpq : p = q := by
    have : p - r = q - r := by rw [hpu, hqv, h₁]
    simpa using this
  refine ⟨hpq, ?_, ?_⟩
  · rw [mem_axisLine_iff]
    exact ⟨inner ℝ ω (p - r), by rw [← hpu]; abel⟩
  · intro θ
    rw [subproblemOne_iff_sum_eq_zero hω, inner_sub_right, h₁, hu, hv]
    simp

/-! ### Subproblem 3: rotation to a given distance (MLS pp. 102–103) -/

/-- **MLS eqs. (3.26)–(3.29), pp. 102–103: the squared distance of Subproblem 3.** For the unit
revolute twist through `r` with axis `ω`, every angle `θ` gives
`‖q - e^{ξ̂θ} p‖² = |ωᵀ(p - q)|² + ‖u′‖² + ‖v′‖² - 2 ‖u′‖ ‖v′‖ cos(θ₀ - θ)` with `u = p - r`,
`v = q - r` and `θ₀ = atan2(ωᵀ(u′ × v′), u′ᵀv′)` (eq. (3.28)). This is the book's projected
distance `δ′² = δ² - |ωᵀ(p - q)|²` and its law of cosines with `φ = θ₀ - θ`. -/
theorem subproblemThree_norm_sq {ω : Vec3} (hω : ‖ω‖ = 1) (r p q : Vec3) (θ : ℝ) :
    ‖q - (Twist.exp (Twist.revolute ω r) θ).applyPoint p‖ ^ 2 =
      inner ℝ ω (p - q) ^ 2 + ‖Vec3.perp ω (p - r)‖ ^ 2 + ‖Vec3.perp ω (q - r)‖ ^ 2 -
        2 * ‖Vec3.perp ω (p - r)‖ * ‖Vec3.perp ω (q - r)‖ *
          Real.cos (planeAngle ω (p - r) (q - r) - θ) := by
  have h : q - (Twist.exp (Twist.revolute ω r) θ).applyPoint p =
      (q - r) - (Rotation.exp ω θ).act (p - r) := by
    rw [Twist.exp_revolute_applyPoint ω r hω]
    abel
  have hA : inner ℝ ω ((q - r) - (p - r)) ^ 2 = inner ℝ ω (p - q) ^ 2 := by
    rw [show (q - r) - (p - r) = -(p - q) by abel, inner_neg_right, neg_sq]
  rw [h, norm_sub_exp_act_sq hω, hA]

/-- The argument of `cos⁻¹` in MLS eq. (3.29), p. 103:
`(‖u′‖² + ‖v′‖² - δ′²) / (2 ‖u′‖ ‖v′‖)` with `δ′² = δ² - |ωᵀ(p - q)|²`, `u = p - r` and
`v = q - r`. The book's `δ′²` may be negative; the formula uses it only through `δ′²`. -/
def subproblemThreeCos (ω r p q : Vec3) (δ : ℝ) : ℝ :=
  (‖Vec3.perp ω (p - r)‖ ^ 2 + ‖Vec3.perp ω (q - r)‖ ^ 2 - (δ ^ 2 - inner ℝ ω (p - q) ^ 2)) /
    (2 * ‖Vec3.perp ω (p - r)‖ * ‖Vec3.perp ω (q - r)‖)

/-- **MLS p. 103: Subproblem 3 reduced to one cosine equation.** For the unit revolute twist
through `r` with axis `ω` and `δ ≥ 0` (the book takes `δ > 0`), if neither `p` nor `q` lies on
the axis (`u′ ≠ 0`, `v′ ≠ 0`, nondegeneracy hypotheses the book does not state), then
`‖q - e^{ξ̂θ} p‖ = δ` holds exactly when `cos(θ - θ₀) = κ`, with `θ₀` of eq. (3.28) and `κ` the
argument of `cos⁻¹` in eq. (3.29) (`subproblemThreeCos`). -/
theorem subproblemThree_iff_cos {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3} {δ : ℝ}
    (hδ : 0 ≤ δ) (hu : Vec3.perp ω (p - r) ≠ 0) (hv : Vec3.perp ω (q - r) ≠ 0) (θ : ℝ) :
    ‖q - (Twist.exp (Twist.revolute ω r) θ).applyPoint p‖ = δ ↔
      Real.cos (θ - planeAngle ω (p - r) (q - r)) = subproblemThreeCos ω r p q δ := by
  have hP : 0 < ‖Vec3.perp ω (p - r)‖ := norm_pos_iff.mpr hu
  have hQ : 0 < ‖Vec3.perp ω (q - r)‖ := norm_pos_iff.mpr hv
  have hden : 2 * ‖Vec3.perp ω (p - r)‖ * ‖Vec3.perp ω (q - r)‖ ≠ 0 := by positivity
  rw [← sq_eq_sq₀ (norm_nonneg _) hδ, subproblemThree_norm_sq hω, subproblemThreeCos,
    eq_div_iff hden, ← Real.cos_neg, neg_sub]
  constructor <;> intro h <;> linear_combination -h

/-- **MLS eq. (3.29), p. 103: the solutions of Subproblem 3.** Under the hypotheses of
`subproblemThree_iff_cos` and `-1 ≤ κ ≤ 1` for the argument `κ` of `cos⁻¹`, the solutions of
`‖q - e^{ξ̂θ} p‖ = δ` are exactly `θ = θ₀ ± cos⁻¹ κ` up to integer multiples of `2π`. -/
theorem subproblemThree_iff {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3} {δ : ℝ}
    (hδ : 0 ≤ δ) (hu : Vec3.perp ω (p - r) ≠ 0) (hv : Vec3.perp ω (q - r) ≠ 0)
    (hκ₁ : -1 ≤ subproblemThreeCos ω r p q δ) (hκ₂ : subproblemThreeCos ω r p q δ ≤ 1)
    (θ : ℝ) :
    ‖q - (Twist.exp (Twist.revolute ω r) θ).applyPoint p‖ = δ ↔
      ∃ k : ℤ,
        θ = planeAngle ω (p - r) (q - r) + Real.arccos (subproblemThreeCos ω r p q δ) +
            k * (2 * Real.pi) ∨
          θ = planeAngle ω (p - r) (q - r) - Real.arccos (subproblemThreeCos ω r p q δ) +
            k * (2 * Real.pi) := by
  rw [subproblemThree_iff_cos hω hδ hu hv]
  conv_lhs => rw [← Real.cos_arccos hκ₁ hκ₂, eq_comm, Real.cos_eq_cos_iff]
  refine exists_congr fun k => or_congr ?_ ?_ <;>
    constructor <;> intro h <;> linarith

/-- **MLS p. 103: no solution of Subproblem 3 when `|κ| > 1`.** Under the hypotheses of
`subproblemThree_iff_cos`, if the argument `κ` of `cos⁻¹` in eq. (3.29) has `|κ| > 1` (the circle
of radius `‖u′‖` misses the circle of radius `δ′`), no angle gives `‖q - e^{ξ̂θ} p‖ = δ`. -/
theorem subproblemThree_no_solution {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3} {δ : ℝ}
    (hδ : 0 ≤ δ) (hu : Vec3.perp ω (p - r) ≠ 0) (hv : Vec3.perp ω (q - r) ≠ 0)
    (hκ : 1 < |subproblemThreeCos ω r p q δ|) (θ : ℝ) :
    ‖q - (Twist.exp (Twist.revolute ω r) θ).applyPoint p‖ ≠ δ := by
  rw [Ne, subproblemThree_iff_cos hω hδ hu hv]
  intro h
  have := Real.abs_cos_le_one (θ - planeAngle ω (p - r) (q - r))
  rw [h] at this
  linarith

/-- **MLS p. 103: one solution of Subproblem 3 when `|κ| = 1`.** If `κ = 1` or `κ = -1` (the
circles are tangent), the two angles `θ₀ + cos⁻¹ κ` and `θ₀ - cos⁻¹ κ` of eq. (3.29) agree up
to a multiple of `2π`, so `subproblemThree_iff` gives a single solution modulo `2π`. -/
theorem subproblemThree_branches_eq_of_abs_eq_one (θ₀ κ : ℝ) (hκ : κ = 1 ∨ κ = -1) :
    ∃ k : ℤ, θ₀ + Real.arccos κ = θ₀ - Real.arccos κ + k * (2 * Real.pi) := by
  rcases hκ with rfl | rfl
  · exact ⟨0, by simp [Real.arccos_one]⟩
  · exact ⟨1, by rw [Real.arccos_neg_one]; push_cast; ring⟩

/-- **MLS p. 103: two solutions of Subproblem 3 when `|κ| < 1`.** If `-1 < κ < 1` (the circles
cross at two points), the two angles `θ₀ + cos⁻¹ κ` and `θ₀ - cos⁻¹ κ` of eq. (3.29) are distinct
modulo `2π`, so `subproblemThree_iff` gives exactly two solutions modulo `2π`. -/
theorem subproblemThree_branches_ne_of_abs_lt_one (θ₀ κ : ℝ) (hκ₁ : -1 < κ) (hκ₂ : κ < 1) :
    ¬ ∃ k : ℤ, θ₀ + Real.arccos κ = θ₀ - Real.arccos κ + k * (2 * Real.pi) := by
  rintro ⟨k, hk⟩
  have h0 : 0 < Real.arccos κ := Real.arccos_pos.mpr hκ₂
  have hπ : Real.arccos κ < Real.pi := Real.arccos_lt_pi.mpr hκ₁
  have hpi := Real.pi_pos
  have hk0 : (0 : ℝ) < k := by nlinarith
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk0' : 0 < k := by exact_mod_cast hk0
  have hk1' : k < 1 := by exact_mod_cast hk1
  omega

/-- **Degenerate Subproblem 3 (not discussed in MLS).** If `p` or `q` lies on the axis
(`u′ = 0` or `v′ = 0`), the distance `‖q - e^{ξ̂θ} p‖` does not depend on `θ`, so every angle or
no angle is a solution; the formula (3.29) divides by zero in this case. -/
theorem subproblemThree_norm_eq_of_perp_eq_zero {ω : Vec3} (hω : ‖ω‖ = 1) {r p q : Vec3}
    (h : Vec3.perp ω (p - r) = 0 ∨ Vec3.perp ω (q - r) = 0) (θ θ' : ℝ) :
    ‖q - (Twist.exp (Twist.revolute ω r) θ).applyPoint p‖ =
      ‖q - (Twist.exp (Twist.revolute ω r) θ').applyPoint p‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), subproblemThree_norm_sq hω,
    subproblemThree_norm_sq hω]
  rcases h with h | h <;> simp [h]

/-! ### Subproblem 2: rotation about two subsequent axes (MLS pp. 100–102) -/

/-- **MLS p. 100, vector form of Subproblem 1.** For a unit axis `ω`, some rotation `e^{ω̂θ}`
carries `u` to `v` if and only if `ωᵀu = ωᵀv` and `‖u′‖ = ‖v′‖` (eq. (3.19)). This is
`subproblemOne_exists_iff` with the axis through the origin. -/
theorem exists_exp_act_eq_iff {ω : Vec3} (hω : ‖ω‖ = 1) (u v : Vec3) :
    (∃ θ : ℝ, (Rotation.exp ω θ).act u = v) ↔
      inner ℝ ω u = inner ℝ ω v ∧ ‖Vec3.perp ω u‖ = ‖Vec3.perp ω v‖ := by
  have h := subproblemOne_exists_iff hω 0 u v
  simp only [applyPoint_exp_revolute_eq_iff hω, sub_zero] at h
  exact h

/-- **MLS eq. (3.20), p. 100, reduced as in eq. (3.22), p. 101.** For unit revolute twists
`ξ₁ = (-ω₁ × r, ω₁)` and `ξ₂ = (-ω₂ × r, ω₂)` whose axes meet at the point `r`,
`e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` holds exactly when `e^{ω̂₁θ₁} e^{ω̂₂θ₂} u = v`, with `u = p - r`,
`v = q - r`. Intersecting axes are modelled by giving both twists the same axis point `r`. -/
theorem subproblemTwo_iff_act {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (r p q : Vec3) (θ₁ θ₂ : ℝ) :
    (Twist.exp (Twist.revolute ω₁ r) θ₁ * Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p = q ↔
      (Rotation.exp ω₁ θ₁).act ((Rotation.exp ω₂ θ₂).act (p - r)) = q - r := by
  rw [RigidTransform.mul_applyPoint, Twist.exp_revolute_applyPoint ω₂ r hω₂,
    applyPoint_exp_revolute_eq_iff hω₁, add_sub_cancel_right]

/-- **MLS p. 101: coincident axes.** If the two axes coincide (`ξ₁ = ξ₂`), Subproblem 2 reduces
to Subproblem 1: `(θ₁, θ₂)` solves eq. (3.20) exactly when `θ₁ + θ₂` solves eq. (3.17). -/
theorem subproblemTwo_coincident (ξ : Twist) (p q : Vec3) (θ₁ θ₂ : ℝ) :
    (Twist.exp ξ θ₁ * Twist.exp ξ θ₂).applyPoint p = q ↔
      (Twist.exp ξ (θ₁ + θ₂)).applyPoint p = q := by
  rw [Twist.exp_add]

/-- The coefficient `α` of MLS p. 102 in the decomposition (3.24) of the intermediate vector:
`α = ((ω₁ᵀω₂) ω₂ᵀu - ω₁ᵀv) / ((ω₁ᵀω₂)² - 1)`, with `u = p - r` and `v = q - r`. -/
def subproblemTwoAlpha (ω₁ ω₂ u v : Vec3) : ℝ :=
  (inner ℝ ω₁ ω₂ * inner ℝ ω₂ u - inner ℝ ω₁ v) / (inner ℝ ω₁ ω₂ ^ 2 - 1)

/-- The coefficient `β` of MLS p. 102 in the decomposition (3.24) of the intermediate vector:
`β = ((ω₁ᵀω₂) ω₁ᵀv - ω₂ᵀu) / ((ω₁ᵀω₂)² - 1)`, with `u = p - r` and `v = q - r`. -/
def subproblemTwoBeta (ω₁ ω₂ u v : Vec3) : ℝ :=
  (inner ℝ ω₁ ω₂ * inner ℝ ω₁ v - inner ℝ ω₂ u) / (inner ℝ ω₁ ω₂ ^ 2 - 1)

/-- The right-hand side of the equation for `γ²` on MLS p. 102:
`γ² = (‖u‖² - α² - β² - 2αβ ω₁ᵀω₂) / ‖ω₁ × ω₂‖²`. -/
def subproblemTwoGammaSq (ω₁ ω₂ u v : Vec3) : ℝ :=
  (‖u‖ ^ 2 - subproblemTwoAlpha ω₁ ω₂ u v ^ 2 - subproblemTwoBeta ω₁ ω₂ u v ^ 2 -
      2 * subproblemTwoAlpha ω₁ ω₂ u v * subproblemTwoBeta ω₁ ω₂ u v * inner ℝ ω₁ ω₂) /
    ‖Vec3.cross ω₁ ω₂‖ ^ 2

/-- The candidate intermediate vector `z = α ω₁ + β ω₂ + γ (ω₁ × ω₂)` of MLS eq. (3.24), p. 101;
the intermediate point of eq. (3.21) is `c = r + z`. -/
def subproblemTwoPoint (ω₁ ω₂ u v : Vec3) (γ : ℝ) : Vec3 :=
  subproblemTwoAlpha ω₁ ω₂ u v • ω₁ + subproblemTwoBeta ω₁ ω₂ u v • ω₂ +
    γ • Vec3.cross ω₁ ω₂

private theorem norm_cross_sq_unit {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1) :
    ‖Vec3.cross ω₁ ω₂‖ ^ 2 = 1 - inner ℝ ω₁ ω₂ ^ 2 := by
  rw [Vec3.norm_cross_sq, hω₁, hω₂]
  ring

private theorem inner_sq_sub_one_ne_zero {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) : inner ℝ ω₁ ω₂ ^ 2 - 1 ≠ 0 := by
  have h := norm_cross_sq_unit hω₁ hω₂
  have hpos : 0 < ‖Vec3.cross ω₁ ω₂‖ ^ 2 := by positivity
  intro h0
  linarith

/-- MLS eq. (3.23), p. 101, first half: every candidate `z` of (3.24) has `ω₁ᵀz = ω₁ᵀv`, for
unit axes that are not parallel (`ω₁ × ω₂ ≠ 0`) and every `γ`. -/
theorem inner_subproblemTwoPoint_left {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) (u v : Vec3) (γ : ℝ) :
    inner ℝ ω₁ (subproblemTwoPoint ω₁ ω₂ u v γ) = inner ℝ ω₁ v := by
  have hk := inner_sq_sub_one_ne_zero hω₁ hω₂ hn
  simp only [subproblemTwoPoint, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hω₁, Vec3.inner_cross_left, subproblemTwoAlpha, subproblemTwoBeta]
  field_simp
  ring

/-- MLS eq. (3.23), p. 101, second half: every candidate `z` of (3.24) has `ω₂ᵀz = ω₂ᵀu`, for
unit axes that are not parallel and every `γ`. -/
theorem inner_subproblemTwoPoint_right {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) (u v : Vec3) (γ : ℝ) :
    inner ℝ ω₂ (subproblemTwoPoint ω₁ ω₂ u v γ) = inner ℝ ω₂ u := by
  have hk := inner_sq_sub_one_ne_zero hω₁ hω₂ hn
  simp only [subproblemTwoPoint, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hω₂, Vec3.inner_cross_right, subproblemTwoAlpha, subproblemTwoBeta,
    real_inner_comm ω₁ ω₂]
  field_simp
  ring

/-- **MLS eq. (3.25), p. 102.** The squared norm of a candidate `z = αω₁ + βω₂ + γ(ω₁ × ω₂)` is
`α² + β² + 2αβ ω₁ᵀω₂ + γ² ‖ω₁ × ω₂‖²`, for unit axes. -/
theorem norm_subproblemTwoPoint_sq {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (u v : Vec3) (γ : ℝ) :
    ‖subproblemTwoPoint ω₁ ω₂ u v γ‖ ^ 2 =
      subproblemTwoAlpha ω₁ ω₂ u v ^ 2 + subproblemTwoBeta ω₁ ω₂ u v ^ 2 +
        2 * subproblemTwoAlpha ω₁ ω₂ u v * subproblemTwoBeta ω₁ ω₂ u v * inner ℝ ω₁ ω₂ +
        γ ^ 2 * ‖Vec3.cross ω₁ ω₂‖ ^ 2 := by
  have h1 : inner ℝ (Vec3.cross ω₁ ω₂) ω₁ = 0 := by
    rw [real_inner_comm]; exact Vec3.inner_cross_left ω₁ ω₂
  have h2 : inner ℝ (Vec3.cross ω₁ ω₂) ω₂ = 0 := by
    rw [real_inner_comm]; exact Vec3.inner_cross_right ω₁ ω₂
  rw [← real_inner_self_eq_norm_sq]
  simp only [subproblemTwoPoint, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, hω₁, hω₂, Vec3.inner_cross_left,
    Vec3.inner_cross_right, h1, h2, real_inner_comm ω₁ ω₂, RCLike.conj_to_real]
  ring

/-- **MLS eq. (3.24), p. 101.** For unit axes that are not parallel (`ω₁ × ω₂ ≠ 0`), every
vector `z` with `ω₁ᵀz = ω₁ᵀv` and `ω₂ᵀz = ω₂ᵀu` (eq. (3.23)) is the candidate
`αω₁ + βω₂ + γ(ω₁ × ω₂)` with `γ = (ω₁ × ω₂)ᵀz / ‖ω₁ × ω₂‖²`: the coefficients `α`, `β` are
forced by the two linear equations of p. 102. -/
theorem eq_subproblemTwoPoint {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) {u v z : Vec3} (h₁ : inner ℝ ω₁ z = inner ℝ ω₁ v)
    (h₂ : inner ℝ ω₂ z = inner ℝ ω₂ u) :
    z = subproblemTwoPoint ω₁ ω₂ u v
      (inner ℝ (Vec3.cross ω₁ ω₂) z / ‖Vec3.cross ω₁ ω₂‖ ^ 2) := by
  set n := Vec3.cross ω₁ ω₂ with hn_def
  set w := z - subproblemTwoPoint ω₁ ω₂ u v (inner ℝ n z / ‖n‖ ^ 2) with hw
  have hN : ‖n‖ ^ 2 ≠ 0 := by positivity
  have hw1 : inner ℝ ω₁ w = 0 := by
    rw [hw, inner_sub_right, inner_subproblemTwoPoint_left hω₁ hω₂ hn, h₁, sub_self]
  have hw2 : inner ℝ ω₂ w = 0 := by
    rw [hw, inner_sub_right, inner_subproblemTwoPoint_right hω₁ hω₂ hn, h₂, sub_self]
  have hwn : inner ℝ n w = 0 := by
    have h1 : inner ℝ n ω₁ = 0 := by
      rw [real_inner_comm]; exact Vec3.inner_cross_left ω₁ ω₂
    have h2 : inner ℝ n ω₂ = 0 := by
      rw [real_inner_comm]; exact Vec3.inner_cross_right ω₁ ω₂
    rw [hw, inner_sub_right]
    simp only [subproblemTwoPoint, inner_add_right, inner_smul_right, ← hn_def, h1, h2,
      real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hcw : Vec3.cross n w = 0 := by
    rw [Vec3.cross_anticomm, hn_def, cross_cross_right, real_inner_comm, hw2,
      real_inner_comm, hw1]
    simp
  have hnn := cross_cross_right n n w
  rw [hcw, Vec3.cross_zero, hwn, zero_smul, zero_sub, real_inner_self_eq_norm_sq] at hnn
  have hw0 : w = 0 := by
    have : ‖n‖ ^ 2 • w = 0 := by rw [← neg_eq_zero, ← hnn]
    exact (smul_eq_zero.mp this).resolve_left hN
  rw [hw, sub_eq_zero] at hw0
  exact hw0

@[deprecated Rotation.inner_exp_act_axis (since := "2026-10-11")]
alias inner_exp_act_axis := Rotation.inner_exp_act_axis

/-- **MLS pp. 101–102: every solution of Subproblem 2 passes through a candidate point.** For
unit revolute twists whose axes meet at `r` and are not parallel (`ω₁ × ω₂ ≠ 0`), `(θ₁, θ₂)`
solves `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` exactly when, for some real `γ` with `γ²` equal to the value
of p. 102 (`subproblemTwoGammaSq`), the rotation `e^{ω̂₂θ₂}` carries `u = p - r` to the
candidate `z = αω₁ + βω₂ + γ(ω₁ × ω₂)` of eq. (3.24) and `e^{ω̂₁θ₁}` carries `z` to `v = q - r`.
The two rotations are the two instances of Subproblem 1 of p. 102. -/
theorem subproblemTwo_iff {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) (r p q : Vec3) (θ₁ θ₂ : ℝ) :
    (Twist.exp (Twist.revolute ω₁ r) θ₁ * Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p = q ↔
      ∃ γ : ℝ, γ ^ 2 = subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r) ∧
        (Rotation.exp ω₂ θ₂).act (p - r) = subproblemTwoPoint ω₁ ω₂ (p - r) (q - r) γ ∧
        (Rotation.exp ω₁ θ₁).act (subproblemTwoPoint ω₁ ω₂ (p - r) (q - r) γ) = q - r := by
  rw [subproblemTwo_iff_act hω₁ hω₂]
  constructor
  · intro h
    set z := (Rotation.exp ω₂ θ₂).act (p - r) with hz
    have h₂ : inner ℝ ω₂ z = inner ℝ ω₂ (p - r) := Rotation.inner_exp_act_axis hω₂ θ₂ _
    have h₁ : inner ℝ ω₁ z = inner ℝ ω₁ (q - r) := by
      rw [← h, Rotation.inner_exp_act_axis hω₁]
    have hzeq := eq_subproblemTwoPoint hω₁ hω₂ hn h₁ h₂
    set γ := inner ℝ (Vec3.cross ω₁ ω₂) z / ‖Vec3.cross ω₁ ω₂‖ ^ 2
    refine ⟨γ, ?_, hzeq, hzeq ▸ h⟩
    have hN : ‖Vec3.cross ω₁ ω₂‖ ^ 2 ≠ 0 := by positivity
    have hnorm := norm_subproblemTwoPoint_sq hω₁ hω₂ (p - r) (q - r) γ
    rw [← hzeq, hz, Rotation.norm_act] at hnorm
    rw [subproblemTwoGammaSq, eq_div_iff hN]
    linarith
  · rintro ⟨γ, -, h₂, h₁⟩
    rw [h₂, h₁]

/-- **MLS p. 102: each admissible `γ` gives a solution of Subproblem 2.** For unit,
non-parallel axes meeting at `r`, if `‖p - r‖ = ‖q - r‖` and `γ² = subproblemTwoGammaSq`, the
two instances of Subproblem 1 through the candidate `z` of eq. (3.24) are solvable: some
`θ₂` carries `u = p - r` to `z` and some `θ₁` carries `z` to `v = q - r`. The condition
`‖u‖ = ‖v‖` is the book's `‖u‖² = ‖z‖² = ‖v‖²` of p. 101. -/
theorem subproblemTwo_exists_of_sq_eq {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) {r p q : Vec3} (hnorm : ‖p - r‖ = ‖q - r‖) {γ : ℝ}
    (hγ : γ ^ 2 = subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r)) :
    ∃ θ₁ θ₂ : ℝ,
      (Rotation.exp ω₂ θ₂).act (p - r) = subproblemTwoPoint ω₁ ω₂ (p - r) (q - r) γ ∧
      (Rotation.exp ω₁ θ₁).act (subproblemTwoPoint ω₁ ω₂ (p - r) (q - r) γ) = q - r := by
  set z := subproblemTwoPoint ω₁ ω₂ (p - r) (q - r) γ
  have hN : ‖Vec3.cross ω₁ ω₂‖ ^ 2 ≠ 0 := by positivity
  have hz : ‖z‖ ^ 2 = ‖p - r‖ ^ 2 := by
    rw [norm_subproblemTwoPoint_sq hω₁ hω₂, hγ, subproblemTwoGammaSq, div_mul_cancel₀ _ hN]
    ring
  have hz₁ := inner_subproblemTwoPoint_left hω₁ hω₂ hn (p - r) (q - r) γ
  have hz₂ := inner_subproblemTwoPoint_right hω₁ hω₂ hn (p - r) (q - r) γ
  obtain ⟨θ₂, h₂⟩ := (exists_exp_act_eq_iff hω₂ (p - r) z).mpr ⟨hz₂.symm, by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Vec3.norm_perp_sq hω₂,
      Vec3.norm_perp_sq hω₂, hz, hz₂]⟩
  obtain ⟨θ₁, h₁⟩ := (exists_exp_act_eq_iff hω₁ z (q - r)).mpr ⟨hz₁, by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Vec3.norm_perp_sq hω₁,
      Vec3.norm_perp_sq hω₁, hz, hz₁, hnorm]⟩
  exact ⟨θ₁, θ₂, h₂, h₁⟩

/-- **MLS pp. 101–102: existence for Subproblem 2 (non-parallel axes).** For unit revolute
twists whose axes meet at `r` and are not parallel, some `(θ₁, θ₂)` solves
`e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` if and only if `‖p - r‖ = ‖q - r‖` and the value of `γ²` on p. 102
is nonnegative. The book lists `‖u‖ = ‖v‖` among the consequences of a solution (p. 101) and
says the equation for `γ` "may have zero, one, or two real solutions"; the iff combines both. -/
theorem subproblemTwo_exists_iff {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) (r p q : Vec3) :
    (∃ θ₁ θ₂ : ℝ, (Twist.exp (Twist.revolute ω₁ r) θ₁ *
        Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p = q) ↔
      ‖p - r‖ = ‖q - r‖ ∧ 0 ≤ subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r) := by
  constructor
  · rintro ⟨θ₁, θ₂, h⟩
    refine ⟨?_, ?_⟩
    · rw [subproblemTwo_iff_act hω₁ hω₂] at h
      rw [← h, Rotation.norm_act, Rotation.norm_act]
    · obtain ⟨γ, hγ, -⟩ := (subproblemTwo_iff hω₁ hω₂ hn r p q θ₁ θ₂).mp h
      rw [← hγ]
      positivity
  · rintro ⟨hnorm, hΓ⟩
    have hγ : √(subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r)) ^ 2 =
        subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r) := Real.sq_sqrt hΓ
    obtain ⟨θ₁, θ₂, h₂, h₁⟩ := subproblemTwo_exists_of_sq_eq hω₁ hω₂ hn hnorm hγ
    exact ⟨θ₁, θ₂, (subproblemTwo_iff hω₁ hω₂ hn r p q θ₁ θ₂).mpr ⟨_, hγ, h₂, h₁⟩⟩

/-- Distinct values of `γ` give distinct candidates `z` of eq. (3.24), MLS p. 101, when the axes
are not parallel. -/
theorem subproblemTwoPoint_injective {ω₁ ω₂ : Vec3} (hn : Vec3.cross ω₁ ω₂ ≠ 0) (u v : Vec3) :
    Function.Injective (subproblemTwoPoint ω₁ ω₂ u v) := by
  intro γ γ' h
  simp only [subproblemTwoPoint, add_right_inj] at h
  exact smul_left_injective ℝ hn h

/-- **MLS p. 102: at most two intermediate points.** For unit, non-parallel axes meeting at
`r`, every solution `(θ₁, θ₂)` of eq. (3.20) moves `p` about the second axis to the point
`c = r + z` of eq. (3.21) with `z` the candidate for `γ = √Γ` or for `γ = -√Γ`, where `Γ` is the
value of `γ²` on p. 102. -/
theorem subproblemTwo_intermediate {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) {r p q : Vec3} {θ₁ θ₂ : ℝ}
    (h : (Twist.exp (Twist.revolute ω₁ r) θ₁ *
      Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p = q) :
    (Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p =
        r + subproblemTwoPoint ω₁ ω₂ (p - r) (q - r)
          (√(subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r))) ∨
      (Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p =
        r + subproblemTwoPoint ω₁ ω₂ (p - r) (q - r)
          (-√(subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r))) := by
  obtain ⟨γ, hγ, h₂, -⟩ := (subproblemTwo_iff hω₁ hω₂ hn r p q θ₁ θ₂).mp h
  have hΓ : 0 ≤ subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r) := by
    rw [← hγ]
    positivity
  have hsq : γ ^ 2 = √(subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r)) ^ 2 := by
    rw [Real.sq_sqrt hΓ, hγ]
  rw [Twist.exp_revolute_applyPoint ω₂ r hω₂, h₂, add_comm]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hg | hg
  · exact Or.inl (by rw [hg])
  · exact Or.inr (by rw [hg])

/-- **MLS p. 102: two solutions when `Γ > 0`.** For unit, non-parallel axes meeting at `r`, if
`‖p - r‖ = ‖q - r‖` and the value `Γ` of `γ²` is positive ("the circles in Figure 3.9 intersect
at two points"), there are solutions `(θ₁, θ₂)` and `(θ₁', θ₂')` of eq. (3.20) whose
intermediate points `c` of eq. (3.21) differ. -/
theorem subproblemTwo_two_solutions {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) {r p q : Vec3} (hnorm : ‖p - r‖ = ‖q - r‖)
    (hΓ : 0 < subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r)) :
    ∃ θ₁ θ₂ θ₁' θ₂' : ℝ,
      (Twist.exp (Twist.revolute ω₁ r) θ₁ *
        Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p = q ∧
      (Twist.exp (Twist.revolute ω₁ r) θ₁' *
        Twist.exp (Twist.revolute ω₂ r) θ₂').applyPoint p = q ∧
      (Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p ≠
        (Twist.exp (Twist.revolute ω₂ r) θ₂').applyPoint p := by
  set Γ := subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r)
  have hγp : √Γ ^ 2 = Γ := Real.sq_sqrt hΓ.le
  have hγm : (-√Γ) ^ 2 = Γ := by rw [neg_sq, hγp]
  obtain ⟨θ₁, θ₂, h₂, h₁⟩ := subproblemTwo_exists_of_sq_eq hω₁ hω₂ hn hnorm hγp
  obtain ⟨θ₁', θ₂', h₂', h₁'⟩ := subproblemTwo_exists_of_sq_eq hω₁ hω₂ hn hnorm hγm
  refine ⟨θ₁, θ₂, θ₁', θ₂', (subproblemTwo_iff hω₁ hω₂ hn r p q θ₁ θ₂).mpr ⟨_, hγp, h₂, h₁⟩,
    (subproblemTwo_iff hω₁ hω₂ hn r p q θ₁' θ₂').mpr ⟨_, hγm, h₂', h₁'⟩, ?_⟩
  rw [Twist.exp_revolute_applyPoint ω₂ r hω₂, Twist.exp_revolute_applyPoint ω₂ r hω₂, h₂, h₂']
  intro h
  have := subproblemTwoPoint_injective hn (p - r) (q - r) (add_right_cancel h)
  have hs : 0 < √Γ := Real.sqrt_pos.mpr hΓ
  linarith

/-- **MLS p. 102: one intermediate point when `Γ = 0`** ("one solution when the circles are
tangential"). For unit, non-parallel axes meeting at `r`, if the value of `γ²` is zero, every
solution of eq. (3.20) passes through the single point `c = r + αω₁ + βω₂`. -/
theorem subproblemTwo_intermediate_of_eq_zero {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1)
    (hω₂ : ‖ω₂‖ = 1) (hn : Vec3.cross ω₁ ω₂ ≠ 0) {r p q : Vec3} {θ₁ θ₂ : ℝ}
    (hΓ : subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r) = 0)
    (h : (Twist.exp (Twist.revolute ω₁ r) θ₁ *
      Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p = q) :
    (Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p =
      r + subproblemTwoPoint ω₁ ω₂ (p - r) (q - r) 0 := by
  have := subproblemTwo_intermediate hω₁ hω₂ hn h
  rw [hΓ, Real.sqrt_zero, neg_zero, or_self] at this
  exact this

/-- **MLS p. 102: no solution when `Γ < 0`** ("none when the circles fail to intersect"). For
unit, non-parallel axes meeting at `r`, a negative value of `γ²` leaves eq. (3.20) without a
solution. -/
theorem subproblemTwo_no_solution {ω₁ ω₂ : Vec3} (hω₁ : ‖ω₁‖ = 1) (hω₂ : ‖ω₂‖ = 1)
    (hn : Vec3.cross ω₁ ω₂ ≠ 0) {r p q : Vec3}
    (hΓ : subproblemTwoGammaSq ω₁ ω₂ (p - r) (q - r) < 0) (θ₁ θ₂ : ℝ) :
    (Twist.exp (Twist.revolute ω₁ r) θ₁ *
      Twist.exp (Twist.revolute ω₂ r) θ₂).applyPoint p ≠ q := by
  intro h
  have := ((subproblemTwo_exists_iff hω₁ hω₂ hn r p q).mp ⟨θ₁, θ₂, h⟩).2
  linarith

end PadenKahan
end RoboLean
