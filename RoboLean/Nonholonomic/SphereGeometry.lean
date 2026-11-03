import RoboLean.Nonholonomic.SphereRolling
import RoboLean.Geometry.Rodrigues
import RoboLean.Geometry.CrossProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Rolling the unit sphere around a closed path of the plane: MLS Proposition 8.7

MLS Chapter 8, §4.3, printed pp. 386–387, Proposition 8.7 ("Sphere rolling on a plane"): two
points `α_f`, `α̃f` of the sphere a distance `l < π/2` apart; rolling the sphere on the plane along
the closed curve ABCDA of Figure 8.5 takes `α_f` to `α̃f`, provided AB and DA have length `x`, BC
and CD length `π/2`, and `2(x − tan⁻¹(x/(π/2))) = l`. The proof develops the planar path on the
sphere: AB and BC become great-circle arcs from `α_f` through `B′` to the pole `C′`, CD an arc
down to `D′` on the equator with `d(B′, D′) = θ`, and DA an arc of the equator of length `x`, so
that `d(α_f, α̃f) = 2x − θ` with `θ = 2 tan⁻¹(x/(π/2))`.

**What is formalized.**

* Spherical geometry on `Vec3`: the great-circle arc `s ↦ cos s · p + sin s · d` from a unit
  point `p` in a unit tangent direction `d ⊥ p` stays on the unit sphere, has unit speed, and is
  at spherical distance `arccos ⟨p, q⟩` exactly `s` from `p` for `s ∈ [0, π]`.
* Rolling along a straight segment of the plane: for the unit sphere on the plane `z = 0` with
  centre `c(t) = c₀ + t d`, `d = (cos β, sin β, 0)`, the orientation `R(t) = exp(t â) R₀` with
  `a = e₃ × d` has spatial angular velocity `a` (`Ṙ = â R`), zero velocity of the contact point
  `ċ + a × (−e₃) = 0` and zero spin `⟨a, e₃⟩ = 0`, the pure rolling of MLS p. 249. The body
  coordinates of the contact point are `Rᵀ(−e₃)`.
* Figure 8.5 placed with `B` at the origin and `A = (x, 0)`: the kite with sides `x, π/2, π/2, x`,
  right angles at `B` and `D` and angle `θ = 2 tan⁻¹(x/(π/2))` at `C` closes. Rolling around it
  from any orientation `R₀` moves the contact point from `α_f = R₀ᵀ(−e₃)` to
  `cos(2x − θ) α_f + sin(2x − θ) w`, `w = R₀ᵀ(−e₁)` the body direction of the first leg: a point of
  the great circle through `α_f` in direction `w` at distance `2x − θ`. With `x` the solution of
  the equation (`prop87_existsUnique`), this is Proposition 8.7: the contact point moves to the
  point at distance `l` along the great circle the first leg starts on.

**Hypotheses the book does not state.** The right angle at `B` (drawn in Figure 8.5 and used in
the proof, `∠(α_f B′ C′) = π/2`); the unit radius (the lengths `π/2` are distances on the sphere of
radius one); the starting orientation `R₀` orthogonal; the first leg of the path starting along
the great circle from `α_f` to `α̃f` (the proof's "connect `α_f` and `α̃f` by an arc of a great
circle, and denote by `A` the starting point").

**Conventions.** Vectors of space are the library's `Vec3` (Euclidean), coordinates read through
`WithLp.ofLp`, matrices act on coordinates by `*ᵥ`; `e₁, e₃` are the first and third basis
vectors; the plane is `z = 0` with the sphere above it; the spherical distance of unit vectors is
`arccos ⟨p, q⟩`; Figure 8.5 is traversed A → B → C → D → A as drawn (clockwise in the plane).
-/

noncomputable section

open Set Real Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Nonholonomic

open RoboLean.Vec3

/-- **The distance on the unit sphere** (MLS Proposition 8.7, p. 386, "a distance `l` apart on
the sphere"): `d(p, q) = arccos ⟨p, q⟩` for unit vectors `p, q` of `Vec3`. -/
def sphereDist (p q : Vec3) : ℝ := arccos (inner ℝ p q)

/-- **The great-circle arc** from a unit point `p` in a unit tangent direction `d ⊥ p` (MLS proof of
Proposition 8.7, p. 387, "an arc of a great circle"): `s ↦ cos s · p + sin s · d`. -/
def greatCircle (p d : Vec3) (s : ℝ) : Vec3 := cos s • p + sin s • d

/-- **A great-circle arc stays on the unit sphere** (MLS proof of Proposition 8.7, p. 387):
`‖cos s · p + sin s · d‖ = 1` for unit `p, d` with `⟨p, d⟩ = 0`. -/
theorem norm_greatCircle {p d : Vec3} (hp : ‖p‖ = 1) (hd : ‖d‖ = 1) (hpd : inner ℝ p d = 0)
    (s : ℝ) : ‖greatCircle p d s‖ = 1 := by
  have h : ‖greatCircle p d s‖ ^ 2 = 1 := by
    rw [greatCircle, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, hpd, hp, hd, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs]
    nlinarith [sin_sq_add_cos_sq s]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h, one_pow])

/-- **A great-circle arc has unit speed** (MLS proof of Proposition 8.7, p. 387: the distance
traversed equals the arc length): its velocity is `−sin s · p + cos s · d`, of norm `1` for unit
`p, d` with `⟨p, d⟩ = 0`. -/
theorem hasDerivAt_greatCircle (p d : Vec3) (s : ℝ) :
    HasDerivAt (greatCircle p d) (-sin s • p + cos s • d) s := by
  have h := ((hasDerivAt_cos s).smul_const p).add ((hasDerivAt_sin s).smul_const d)
  exact h

/-- **The velocity of a great-circle arc has norm `1`** (MLS proof of Proposition 8.7, p. 387),
for unit `p, d` with `⟨p, d⟩ = 0`. -/
theorem norm_deriv_greatCircle {p d : Vec3} (hp : ‖p‖ = 1) (hd : ‖d‖ = 1)
    (hpd : inner ℝ p d = 0) (s : ℝ) : ‖-sin s • p + cos s • d‖ = 1 := by
  have h := norm_greatCircle hp hd hpd (s + π / 2)
  rwa [greatCircle, cos_add_pi_div_two, sin_add_pi_div_two] at h

/-- **Along a great-circle arc the spherical distance is the arc length** (MLS proof of
Proposition 8.7, p. 387): `d(p, cos s · p + sin s · d) = s` for `s ∈ [0, π]`, unit `p, d` with
`⟨p, d⟩ = 0`. -/
theorem sphereDist_greatCircle {p d : Vec3} (hp : ‖p‖ = 1) (hpd : inner ℝ p d = 0) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs : s ≤ π) : sphereDist p (greatCircle p d s) = s := by
  rw [sphereDist, greatCircle, inner_add_right, real_inner_smul_right, real_inner_smul_right, hpd,
    real_inner_self_eq_norm_sq, hp, one_pow, mul_one, mul_zero, add_zero, arccos_cos hs₀ hs]

/-- **The vertical `e₃`,** normal to the plane `z = 0` on which the sphere rolls (MLS §4.3,
p. 385, the plane of the object). -/
def vertical : Vec3 := WithLp.toLp 2 ![0, 0, 1]

/-- **The horizontal unit direction `(cos β, sin β, 0)`** of a straight segment of the plane (MLS
Figure 8.5, p. 387). -/
def planarDir (β : ℝ) : Vec3 := WithLp.toLp 2 ![cos β, sin β, 0]

/-- **The rolling axis `e₃ × d = (−sin β, cos β, 0)`** for rolling along `d = (cos β, sin β, 0)`
(for MLS Proposition 8.7, p. 387). -/
def rollAxis (β : ℝ) : Vec3 := WithLp.toLp 2 ![-sin β, cos β, 0]

/-- **The rolling axis is `e₃ × d`** (MLS p. 26 cross product; for Proposition 8.7, p. 387). -/
theorem rollAxis_eq_cross (β : ℝ) : rollAxis β = cross vertical (planarDir β) := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [cross_coordinates, rollAxis, vertical, planarDir, cross_apply]

/-- **No slip** (pure rolling, MLS p. 249; for Proposition 8.7, p. 387): with centre velocity
`d = (cos β, sin β, 0)` and spatial angular velocity `a = e₃ × d`, the contact point `c − e₃` of
the unit sphere has velocity `d + a × (−e₃) = 0`. -/
theorem planarDir_add_cross_rollAxis (β : ℝ) :
    planarDir β + cross (rollAxis β) (-vertical) = 0 := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [cross_coordinates, rollAxis, vertical, planarDir, cross_apply]

/-- **No spin about the normal** (pure rolling, MLS p. 249; for Proposition 8.7, p. 387):
`⟨e₃ × d, e₃⟩ = 0`. -/
theorem inner_rollAxis_vertical (β : ℝ) : inner ℝ (rollAxis β) vertical = 0 := by
  simp [rollAxis, vertical, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three]

/-- **The orientation change of the unit sphere rolling a distance `s` along `(cos β, sin β, 0)`**
(for MLS Proposition 8.7, p. 387): `exp(s â)`, `a = e₃ × d` (the rotation about `a` by `s`, MLS
eq. (2.14)). -/
def rollSegment (β s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := NormedSpace.exp (s • hat (rollAxis β))

/-- **The rolling orientation solves `Ṙ = â R`** (for MLS Proposition 8.7, p. 387):
`t ↦ exp(t â) R₀` has derivative `â exp(t â) R₀`, so its spatial angular velocity is the constant
`a = e₃ × d` of `planarDir_add_cross_rollAxis` and `inner_rollAxis_vertical`. -/
theorem hasDerivAt_rollSegment (β : ℝ) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    HasDerivAt (fun s => rollSegment β s * R₀) (hat (rollAxis β) * (rollSegment β t * R₀))
      t := by
  rw [← mul_assoc]
  exact (hasDerivAt_exp_smul_const' (hat (rollAxis β)) t).mul_const R₀

/-- **Rolling along a segment determines the orientation** (for MLS Proposition 8.7, p. 387): a
differentiable orientation curve with `Ṙ = â R` for the rolling axis `a = e₃ × d` (no slip and no
spin, `planarDir_add_cross_rollAxis`, `inner_rollAxis_vertical`) is `R(t) = exp(t â) R(0)`. -/
theorem eq_rollSegment_of_hasDerivAt (β : ℝ) {R : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hR : ∀ t, HasDerivAt R (hat (rollAxis β) * R t) t) (t : ℝ) :
    R t = rollSegment β t * R 0 := by
  set A := hat (rollAxis β)
  have hF : ∀ s, HasDerivAt (fun r => NormedSpace.exp (r • (-A)) * R r) 0 s := by
    intro s
    have h := (hasDerivAt_exp_smul_const (-A) s).mul (hR s)
    convert! h using 1
    simp [mul_assoc]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hconst
  have hcancel : NormedSpace.exp (t • A) * NormedSpace.exp (t • (-A)) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • A)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  calc R t = NormedSpace.exp (t • A) * (NormedSpace.exp (t • (-A)) * R t) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ = rollSegment β t * R 0 := by rw [hconst, rollSegment]

/-- **The body motion of rolling along a segment** (for MLS Proposition 8.7, p. 387):
`exp(s â)ᵀ w` in coordinates, with `h = cos β w₀ + sin β w₁` the component along `d`:
`(w₀ − cos β (sin s w₂ + (1 − cos s) h), w₁ − sin β (sin s w₂ + (1 − cos s) h), cos s w₂ + sin s h)`
(Rodrigues' formula, MLS eq. (2.14)). -/
theorem rollSegment_transpose_mulVec (β s : ℝ) (w : Fin 3 → ℝ) :
    (rollSegment β s)ᵀ *ᵥ w =
      ![w 0 - cos β * (sin s * w 2 + (1 - cos s) * (cos β * w 0 + sin β * w 1)),
        w 1 - sin β * (sin s * w 2 + (1 - cos s) * (cos β * w 0 + sin β * w 1)),
        cos s * w 2 + sin s * (cos β * w 0 + sin β * w 1)] := by
  have hn : ‖rollAxis β‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [rollAxis, Fin.sum_univ_three]
  rw [rollSegment, exp_hat_of_norm_eq_one _ hn]
  ext i
  fin_cases i <;>
    simp [hat, rollAxis, mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
      pow_two] <;>
    first | ring1 | linear_combination (cos s - 1) * w 2 * sin_sq_add_cos_sq β

/-- **The contact point in body coordinates** (MLS §4.3, p. 385; for Proposition 8.7, p. 387):
`Rᵀ(−e₃)` for the unit sphere with orientation `R` resting on the plane `z = 0`. -/
def contactPoint (R : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 := WithLp.toLp 2 (Rᵀ *ᵥ ![0, 0, -1])

/-- **MLS Figure 8.5, p. 387: the angle `θ = 2 tan⁻¹(x/(π/2))` at `C`.** -/
def kiteAngle (x : ℝ) : ℝ := 2 * arctan (x / (π / 2))

/-- `sin θ` and `cos θ` for `θ = 2 tan⁻¹ y`. -/
private theorem sin_cos_two_arctan (y : ℝ) :
    sin (2 * arctan y) = 2 * y / (1 + y ^ 2) ∧ cos (2 * arctan y) = (1 - y ^ 2) / (1 + y ^ 2) := by
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hs : √(1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt h1.le
  have hs0 : √(1 + y ^ 2) ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  constructor
  · rw [sin_two_mul, sin_arctan, cos_arctan]
    field_simp
    rw [hs]
  · rw [cos_two_mul, cos_arctan]
    field_simp
    rw [hs]
    ring

/-- **MLS Figure 8.5, p. 387: the kite ABCDA closes** with `B` at the origin, `A = (x, 0)`, the
legs `A → B` along `(cos π, sin π)` of length `x`, `B → C` along `(cos(π/2), sin(π/2))` of length
`π/2`, `C → D` along `(cos(θ − π/2), sin(θ − π/2))` of length `π/2` and `D → A` along
`(cos(θ + π), sin(θ + π))` of length `x`, `θ = kiteAngle x`; the angles at `B` and `D` are right
angles. -/
theorem kite_closes (x : ℝ) :
    x * cos π + π / 2 * cos (π / 2) + π / 2 * cos (kiteAngle x - π / 2) +
        x * cos (kiteAngle x + π) = 0 ∧
      x * sin π + π / 2 * sin (π / 2) + π / 2 * sin (kiteAngle x - π / 2) +
        x * sin (kiteAngle x + π) = 0 ∧
      cos π * cos (π / 2) + sin π * sin (π / 2) = 0 ∧
      cos (kiteAngle x - π / 2) * cos (kiteAngle x + π) +
        sin (kiteAngle x - π / 2) * sin (kiteAngle x + π) = 0 := by
  obtain ⟨hsin, hcos⟩ := sin_cos_two_arctan (x / (π / 2))
  have hπ : π ≠ 0 := pi_ne_zero
  have h1 : (0 : ℝ) < 1 + (x / (π / 2)) ^ 2 := by positivity
  simp only [kiteAngle, cos_sub_pi_div_two, sin_sub_pi_div_two, cos_add_pi, sin_add_pi, cos_pi,
    sin_pi, cos_pi_div_two, sin_pi_div_two, hsin, hcos]
  refine ⟨?_, ?_, by ring, by ring⟩
  · field_simp
    ring
  · field_simp
    ring

/-- **MLS Figure 8.5, p. 387: the orientation change of rolling around ABCDA,**
`E₄ E₃ E₂ E₁` with `E₁ = rollSegment π x` (A → B), `E₂ = rollSegment (π/2) (π/2)` (B → C),
`E₃ = rollSegment (θ − π/2) (π/2)` (C → D), `E₄ = rollSegment (θ + π) x` (D → A),
`θ = kiteAngle x`. -/
def kiteRoll (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rollSegment (kiteAngle x + π) x * rollSegment (kiteAngle x - π / 2) (π / 2) *
    rollSegment (π / 2) (π / 2) * rollSegment π x

/-- **MLS proof of Proposition 8.7, p. 387: rolling around ABCDA moves the contact point along a
great circle by `2x − θ`.** From any orientation `R₀`, the contact point moves from
`α_f = R₀ᵀ(−e₃)` to `cos(2x − θ) α_f + sin(2x − θ) w`, `w = R₀ᵀ(−e₁)`, `θ = kiteAngle x` (a point
of the great circle through `α_f` in direction `w` when `R₀` is orthogonal). -/
theorem contactPoint_kiteRoll (x : ℝ) (R₀ : Matrix (Fin 3) (Fin 3) ℝ) :
    contactPoint (kiteRoll x * R₀) =
      greatCircle (contactPoint R₀) (WithLp.toLp 2 (R₀ᵀ *ᵥ ![-1, 0, 0]))
        (2 * x - kiteAngle x) := by
  set θ := kiteAngle x
  have s4 : (rollSegment (θ + π) x)ᵀ *ᵥ ![0, 0, -1] =
      ![-(sin x * cos θ), -(sin x * sin θ), -cos x] := by
    rw [rollSegment_transpose_mulVec]
    ext i
    fin_cases i <;> simp [cos_add_pi, sin_add_pi] <;> ring
  have s3 : (rollSegment (θ - π / 2) (π / 2))ᵀ *ᵥ ![-(sin x * cos θ), -(sin x * sin θ), -cos x] =
      ![sin (θ - x), -cos (θ - x), 0] := by
    rw [rollSegment_transpose_mulVec]
    ext i
    fin_cases i <;> simp [sin_sub, cos_sub] <;> ring
  have s2 : (rollSegment (π / 2) (π / 2))ᵀ *ᵥ ![sin (θ - x), -cos (θ - x), 0] =
      ![sin (θ - x), 0, -cos (θ - x)] := by
    rw [rollSegment_transpose_mulVec]
    ext i
    fin_cases i <;> simp
  have s1 : (rollSegment π x)ᵀ *ᵥ ![sin (θ - x), 0, -cos (θ - x)] =
      ![-sin (2 * x - θ), 0, -cos (2 * x - θ)] := by
    rw [rollSegment_transpose_mulVec, show 2 * x - θ = x - (θ - x) by ring, sin_sub x (θ - x),
      cos_sub x (θ - x)]
    ext i
    fin_cases i <;> simp <;> ring
  have hv : (kiteRoll x * R₀)ᵀ *ᵥ ![0, 0, -1] =
      R₀ᵀ *ᵥ ![-sin (2 * x - θ), 0, -cos (2 * x - θ)] := by
    simp only [kiteRoll, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    rw [s4, s3, s2, s1]
  rw [contactPoint, hv, contactPoint, greatCircle, ← WithLp.toLp_smul, ← WithLp.toLp_smul,
    ← WithLp.toLp_add, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
  congr 2
  ext i
  fin_cases i <;> simp

/-- **MLS Proposition 8.7, p. 386.** For `0 ≤ l < π/2` there is a unique `x ∈ [0, π/2]` with
`2(x − tan⁻¹(x/(π/2))) = l`; for it, rolling the unit sphere around the kite ABCDA of Figure 8.5
(sides `x, π/2, π/2, x`, closed by `kite_closes`) from any orientation `R₀` with `R₀ R₀ᵀ = 1`
takes the contact point `α_f = R₀ᵀ(−e₃)` to the point at spherical distance `l` on the great
circle that the first leg starts along: `cos l · α_f + sin l · w`, `w = R₀ᵀ(−e₁)`. -/
theorem prop87_rolling {l : ℝ} (hl₀ : 0 ≤ l) (hl : l < π / 2) :
    ∃! x, x ∈ Icc 0 (π / 2) ∧ 2 * (x - arctan (x / (π / 2))) = l ∧
      ∀ R₀ : Matrix (Fin 3) (Fin 3) ℝ, R₀ * R₀ᵀ = 1 →
        contactPoint (kiteRoll x * R₀) =
            greatCircle (contactPoint R₀) (WithLp.toLp 2 (R₀ᵀ *ᵥ ![-1, 0, 0])) l ∧
          sphereDist (contactPoint R₀) (contactPoint (kiteRoll x * R₀)) = l := by
  obtain ⟨x, ⟨hx, hfx⟩, huniq⟩ := prop87_existsUnique hl₀ hl
  refine ⟨x, ⟨hx, hfx, fun R₀ hR₀ => ?_⟩, fun y hy => huniq y ⟨hy.1, hy.2.1⟩⟩
  have hl' : 2 * x - kiteAngle x = l := by
    rw [kiteAngle, ← hfx]
    ring
  have hinner : ∀ a b : Fin 3 → ℝ,
      inner ℝ (WithLp.toLp 2 (R₀ᵀ *ᵥ a) : Vec3) (WithLp.toLp 2 (R₀ᵀ *ᵥ b)) = a ⬝ᵥ b := by
    intro a b
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hR₀, Matrix.one_mulVec, dotProduct_comm]
  have hcp := contactPoint_kiteRoll x R₀
  rw [hl'] at hcp
  refine ⟨hcp, ?_⟩
  have hp : ‖contactPoint R₀‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, contactPoint, hinner]
    simp [dotProduct, Fin.sum_univ_three]
  have hpd : inner ℝ (contactPoint R₀) (WithLp.toLp 2 (R₀ᵀ *ᵥ ![-1, 0, 0]) : Vec3) = 0 := by
    rw [contactPoint, hinner]
    simp [dotProduct, Fin.sum_univ_three]
  rw [hcp]
  exact sphereDist_greatCircle hp hpd hl₀ (hl.le.trans (by linarith [pi_pos]))

/-- **MLS Proposition 8.7, p. 386: rolling takes `α_f` to `α̃f`.** For `0 < l < π/2`, let the
starting orientation `R₀` (with `R₀ R₀ᵀ = 1`) have contact point `α_f` and first-leg body direction
`R₀ᵀ(−e₁)` equal to `(α̃f − cos l · α_f)/sin l`, the unit tangent at `α_f` of the great circle to
`α̃f` (the proof's "connect `α_f` and `α̃f` by an arc of a great circle, and denote by `A` the
starting point"; this alignment forces `α̃f` to lie at distance `l`). Then rolling around the kite
ABCDA of Figure 8.5 with the solution `x` of `2(x − tan⁻¹(x/(π/2))) = l` takes the contact point
to `α̃f`, and `d(α_f, α̃f) = l`. -/
theorem prop87_rolling_to {l : ℝ} (hl₀ : 0 < l) (hl : l < π / 2) {αf αf' : Vec3}
    {R₀ : Matrix (Fin 3) (Fin 3) ℝ} (hR₀ : R₀ * R₀ᵀ = 1) (hα : contactPoint R₀ = αf)
    (hw : (WithLp.toLp 2 (R₀ᵀ *ᵥ ![-1, 0, 0]) : Vec3) = (sin l)⁻¹ • (αf' - cos l • αf)) :
    ∃ x ∈ Icc 0 (π / 2), 2 * (x - arctan (x / (π / 2))) = l ∧
      contactPoint (kiteRoll x * R₀) = αf' ∧ sphereDist αf αf' = l := by
  obtain ⟨x, ⟨hx, hfx, hroll⟩, -⟩ := prop87_rolling hl₀.le hl
  have hs : sin l ≠ 0 := (sin_pos_of_pos_of_lt_pi hl₀ (by linarith [pi_pos])).ne'
  have hend : contactPoint (kiteRoll x * R₀) = αf' := by
    rw [(hroll R₀ hR₀).1, hα, hw, greatCircle, smul_smul, mul_inv_cancel₀ hs, one_smul]
    abel
  refine ⟨x, hx, hfx, hend, ?_⟩
  rw [← hα, ← hend]
  exact (hroll R₀ hR₀).2

end Nonholonomic
end RoboLean
