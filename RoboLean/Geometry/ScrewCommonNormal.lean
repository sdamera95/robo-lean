import RoboLean.Geometry.WrenchReciprocityGeometry
import RoboLean.Geometry.EulerAngles

/-!
# The common normal of two screw axes and the reciprocal product without a certificate

MLS printed pp. 66–67, eq. (2.72) and Proposition 2.18. The book defines the distance `d` between
two screws as the minimum distance between their axes `l₁ = {q₁ + λω₁}` and `l₂ = {q₂ + λω₂}`,
"achieved along a line perpendicular to both `l₁` and `l₂`", writes this line `d n` with a unit
`n` and `d > 0`, sets `α = atan2(ω₁ × ω₂ · n, ω₁ · ω₂)` and defines the reciprocal product
`S₁ ⊙ S₂ = M₁ M₂ ((h₁ + h₂) cos α - d sin α)`. Proposition 2.18: two screws are reciprocal iff
`S₁ ⊙ S₂ = 0`; the printed proof treats finite pitches only and leaves the other cases as
exercises.

`FiniteScrew.CommonNormal` (in `WrenchReciprocityGeometry`) is a supplied certificate of that
data. This module constructs it. Convention for nonparallel axes (`ω₁ × ω₂ ≠ 0`), with the unit
directions `ω₁ = S.direction`, `ω₂ = T.direction` and `m = (q₂ - q₁) · (ω₁ × ω₂)`
(`offsetMoment`):

* the distance is `d = |m| / ‖ω₁ × ω₂‖` (`commonNormalDistance`), the minimum distance between
  the two affine axes, attained by a pair of feet joined by `d n`;
* the unit normal is `n = ± (ω₁ × ω₂) / ‖ω₁ × ω₂‖`, with the sign of `m` (and `+` when `m = 0`),
  so that it points from `l₁` to `l₂` when `d > 0` (`commonNormalDirection`);
* the angle is `α = atan2(n · (ω₁ × ω₂), ω₁ · ω₂)` with the library's `Rotation.atan2`
  (`commonNormalAngle`), so `cos α = ω₁ · ω₂` and `sin α = n · (ω₁ × ω₂) = ± ‖ω₁ × ω₂‖`.

With this data the reciprocal product (2.72) equals the twist–wrench pairing for every pair of
nonparallel finite screws (`pair_eq_geometricProduct`), and Proposition 2.18 holds without a
supplied certificate. When the axes intersect, `d = 0` and the sign of `n` does not affect the
product; the printed `d > 0` excludes this case, which is stated separately. For skew axes
(`d > 0`) the printed certificate exists on the representatives at the feet
(`exists_commonNormal`). Parallel axes and infinite pitches are separate statements:
parallel axes give `α ∈ {0, π}` and `sin α = 0`, so the product is `M₁ M₂ (h₁ + h₂) cos α` for
every distance; with one infinite pitch reciprocity is perpendicularity of the axes, and two
infinite-pitch screws are always reciprocal. These are identities of the coordinate model.
-/

noncomputable section

namespace RoboLean
namespace FiniteScrew

/-- The moment `(q₂ - q₁) · (ω₁ × ω₂)` of the offset between the representative points along the
common perpendicular direction of the two axes (MLS p. 66, Figure 2.15; `q₁ = S.point`,
`q₂ = T.point`). -/
def offsetMoment (S T : FiniteScrew) : ℝ :=
  inner ℝ (T.point - S.point) (Vec3.cross S.direction T.direction)

/-- The distance `d` of MLS p. 66 for nonparallel axes: `|(q₂ - q₁) · (ω₁ × ω₂)| / ‖ω₁ × ω₂‖`.
For parallel axes the expression divides by zero and is not the book's distance. -/
def commonNormalDistance (S T : FiniteScrew) : ℝ :=
  |offsetMoment S T| / ‖Vec3.cross S.direction T.direction‖

/-- The unit normal `n` of MLS p. 66 for nonparallel axes: `(ω₁ × ω₂) / ‖ω₁ × ω₂‖`, negated when
the offset moment is negative, so that `q₂ - q₁` has a nonnegative component along it. -/
def commonNormalDirection (S T : FiniteScrew) : Vec3 :=
  (if offsetMoment S T < 0 then (-1 : ℝ) else 1) •
    (‖Vec3.cross S.direction T.direction‖⁻¹ • Vec3.cross S.direction T.direction)

/-- The angle `α = atan2(ω₁ × ω₂ · n, ω₁ · ω₂)` of MLS p. 66, with the library's `Rotation.atan2`
(the argument of `x + i y`, in `(-π, π]`). -/
def commonNormalAngle (S T : FiniteScrew) : ℝ :=
  Rotation.atan2 (inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction))
    (inner ℝ S.direction T.direction)

/-- The reciprocal product `S₁ ⊙ S₂ = M₁ M₂ ((h₁ + h₂) cos α - d sin α)` of MLS eq. (2.72), p. 66,
from the constructed common-normal distance and angle. -/
def geometricProduct (S T : FiniteScrew) : ℝ :=
  S.magnitude * T.magnitude *
    ((S.pitch + T.pitch) * Real.cos (commonNormalAngle S T) -
      commonNormalDistance S T * Real.sin (commonNormalAngle S T))

/-- Supporting lemma; no direct MLS counterpart. The coordinates of a vector `p` in the frame
`u, v, u × v` of MLS p. 66, scaled by the Gram determinant `(u · u)(v · v) - (u · v)²`. -/
private theorem gram_smul_eq (u v p : Vec3) :
    (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) • p =
      (inner ℝ v v * inner ℝ p u - inner ℝ u v * inner ℝ p v) • u +
        (inner ℝ u u * inner ℝ p v - inner ℝ u v * inner ℝ p u) • v +
        inner ℝ p (Vec3.cross u v) • Vec3.cross u v := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  ext i
  fin_cases i <;> simp [Vec3.cross, cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Supporting lemma; no direct MLS counterpart. Dividing a scaled three-term decomposition by a
nonzero scale. -/
private theorem eq_div_smul_of_smul_eq {K A B m : ℝ} {p u v c : Vec3} (hK : K ≠ 0)
    (h : K • p = A • u + B • v + m • c) : p = (A / K) • u + (B / K) • v + (m / K) • c := by
  apply smul_right_injective Vec3 hK
  simp only [smul_add, smul_smul, mul_div_cancel₀ _ hK]
  exact h

/-- Supporting lemma for MLS p. 66: for unit directions `(ω₁ · ω₂)² + ‖ω₁ × ω₂‖² = 1`. -/
private theorem inner_sq_add_norm_cross_sq (S T : FiniteScrew) :
    inner ℝ S.direction T.direction ^ 2 + ‖Vec3.cross S.direction T.direction‖ ^ 2 = 1 := by
  rw [Vec3.norm_cross_sq, S.unit_direction, T.unit_direction]
  ring

/-- Supporting lemma for MLS p. 66: `n · (ω₁ × ω₂) = ± ‖ω₁ × ω₂‖`, with the sign of the
offset moment. -/
private theorem inner_commonNormalDirection_cross (S T : FiniteScrew) :
    inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction) =
      (if offsetMoment S T < 0 then (-1 : ℝ) else 1) * ‖Vec3.cross S.direction T.direction‖ := by
  rw [commonNormalDirection, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  by_cases hk : ‖Vec3.cross S.direction T.direction‖ = 0
  · simp [hk]
  · rw [pow_two, ← mul_assoc (‖Vec3.cross S.direction T.direction‖⁻¹), inv_mul_cancel₀ hk,
      one_mul]

/-- Supporting lemma for MLS p. 66: `(ω₁ · ω₂)² + (n · (ω₁ × ω₂))² = 1`, the unit-circle
condition for the angle `α`. -/
private theorem inner_sq_add_inner_commonNormalDirection_sq (S T : FiniteScrew) :
    inner ℝ S.direction T.direction ^ 2 +
      inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction) ^ 2 = 1 := by
  have hn := inner_sq_add_norm_cross_sq S T
  rw [inner_commonNormalDirection_cross]
  split_ifs <;> linear_combination hn

/-- Supporting lemma for MLS p. 66: `d (n · (ω₁ × ω₂))` is the offset moment. -/
private theorem distance_mul_inner_commonNormalDirection {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) :
    commonNormalDistance S T *
        inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction) =
      offsetMoment S T := by
  have hk : ‖Vec3.cross S.direction T.direction‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [inner_commonNormalDirection_cross, commonNormalDistance]
  split_ifs with hm
  · rw [abs_of_neg hm]
    field_simp
  · rw [abs_of_nonneg (not_lt.mp hm)]
    field_simp

/-- Supporting lemma for MLS p. 66: the offset `q₂ - q₁` has component `d` along `n`. -/
private theorem inner_commonNormalDirection_offset (S T : FiniteScrew) :
    inner ℝ (commonNormalDirection S T) (T.point - S.point) = commonNormalDistance S T := by
  rw [commonNormalDirection, real_inner_smul_left, real_inner_smul_left, real_inner_comm]
  change _ * (_ * offsetMoment S T) = _
  rw [commonNormalDistance]
  split_ifs with hm
  · rw [abs_of_neg hm]
    ring
  · rw [abs_of_nonneg (not_lt.mp hm)]
    ring

/-- Supporting lemma for MLS p. 66: `d n = (m / ‖ω₁ × ω₂‖²) (ω₁ × ω₂)` in both sign cases. -/
private theorem smul_commonNormalDirection (S T : FiniteScrew) :
    commonNormalDistance S T • commonNormalDirection S T =
      (offsetMoment S T / ‖Vec3.cross S.direction T.direction‖ ^ 2) •
        Vec3.cross S.direction T.direction := by
  rw [commonNormalDirection, smul_smul, smul_smul, commonNormalDistance]
  congr 1
  split_ifs with hm
  · rw [abs_of_neg hm]
    ring
  · rw [abs_of_nonneg (not_lt.mp hm)]
    ring

/-- The common-normal distance is nonnegative (MLS p. 66). -/
theorem commonNormalDistance_nonneg (S T : FiniteScrew) : 0 ≤ commonNormalDistance S T := by
  exact div_nonneg (abs_nonneg _) (norm_nonneg _)

/-- For nonparallel axes the normal `n` is a unit vector (MLS p. 66). -/
theorem norm_commonNormalDirection {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) : ‖commonNormalDirection S T‖ = 1 := by
  have hk : ‖Vec3.cross S.direction T.direction‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [commonNormalDirection, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hk,
    mul_one]
  split_ifs <;> simp

/-- The normal `n` is perpendicular to the first axis (MLS p. 66). -/
theorem inner_commonNormalDirection_left (S T : FiniteScrew) :
    inner ℝ (commonNormalDirection S T) S.direction = 0 := by
  rw [commonNormalDirection, real_inner_smul_left, real_inner_smul_left, real_inner_comm,
    Vec3.inner_cross_left, mul_zero, mul_zero]

/-- The normal `n` is perpendicular to the second axis (MLS p. 66). -/
theorem inner_commonNormalDirection_right (S T : FiniteScrew) :
    inner ℝ (commonNormalDirection S T) T.direction = 0 := by
  rw [commonNormalDirection, real_inner_smul_left, real_inner_smul_left, real_inner_comm,
    Vec3.inner_cross_right, mul_zero, mul_zero]

/-- `cos α = ω₁ · ω₂` for the angle of MLS p. 66, for unit axes; for parallel axes `n = 0` and
`ω₁ · ω₂ = ±1`, so the identity holds there too. -/
theorem cos_commonNormalAngle (S T : FiniteScrew) :
    Real.cos (commonNormalAngle S T) = inner ℝ S.direction T.direction := by
  have hs := Rotation.sqrt_mul_cos_atan2
    (inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction))
    (inner ℝ S.direction T.direction)
  rw [inner_sq_add_inner_commonNormalDirection_sq S T, Real.sqrt_one, one_mul] at hs
  exact hs

/-- `sin α = n · (ω₁ × ω₂)` for the angle of MLS p. 66, for unit axes (both sides vanish for
parallel axes). -/
theorem sin_commonNormalAngle (S T : FiniteScrew) :
    Real.sin (commonNormalAngle S T) =
      inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction) := by
  have hs := Rotation.sqrt_mul_sin_atan2
    (inner ℝ (commonNormalDirection S T) (Vec3.cross S.direction T.direction))
    (inner ℝ S.direction T.direction)
  rw [inner_sq_add_inner_commonNormalDirection_sq S T, Real.sqrt_one, one_mul] at hs
  exact hs

/-- Supporting lemma for MLS p. 66: the feet `q₁ + a ω₁` and `q₂ + b ω₂` of the common normal,
joined by `d n`. -/
private theorem exists_feet_coeffs {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) :
    ∃ a b : ℝ, T.point + b • T.direction =
      S.point + a • S.direction + commonNormalDistance S T • commonNormalDirection S T := by
  have hK : ‖Vec3.cross S.direction T.direction‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  have hg := gram_smul_eq S.direction T.direction (T.point - S.point)
  have hc : inner ℝ S.direction S.direction * inner ℝ T.direction T.direction -
      inner ℝ S.direction T.direction ^ 2 = ‖Vec3.cross S.direction T.direction‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, S.unit_direction,
      T.unit_direction]
    linarith [inner_sq_add_norm_cross_sq S T]
  rw [hc] at hg
  obtain ⟨a, b, hd⟩ : ∃ a b : ℝ, T.point - S.point = a • S.direction + b • T.direction +
      (offsetMoment S T / ‖Vec3.cross S.direction T.direction‖ ^ 2) •
        Vec3.cross S.direction T.direction :=
    ⟨_, _, eq_div_smul_of_smul_eq hK hg⟩
  refine ⟨a, -b, ?_⟩
  have e : T.point = S.point + (a • S.direction + b • T.direction +
      (offsetMoment S T / ‖Vec3.cross S.direction T.direction‖ ^ 2) •
        Vec3.cross S.direction T.direction) := by
    rw [← hd]
    abel
  rw [smul_commonNormalDirection, e, neg_smul]
  abel

/-- **The common normal joins the two axes (MLS p. 66).** For nonparallel axes there are feet
`x ∈ l₁` and `y ∈ l₂` with `y = x + d n`: the segment `d n` is perpendicular to both axes. -/
theorem exists_feet {S T : FiniteScrew} (h : Vec3.cross S.direction T.direction ≠ 0) :
    ∃ x ∈ S.axis, ∃ y ∈ T.axis,
      y = x + commonNormalDistance S T • commonNormalDirection S T := by
  obtain ⟨a, b, hab⟩ := exists_feet_coeffs h
  exact ⟨S.point + a • S.direction, (mem_axisLine_iff _ _ _).mpr ⟨a, rfl⟩,
    T.point + b • T.direction, (mem_axisLine_iff _ _ _).mpr ⟨b, rfl⟩, hab⟩

/-- **`d` is the minimum distance between the axes (MLS p. 66).** For nonparallel axes the
common-normal distance is the least distance between a point of `l₁` and a point of `l₂`. -/
theorem isLeast_commonNormalDistance {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) :
    IsLeast {d : ℝ | ∃ x ∈ S.axis, ∃ y ∈ T.axis, dist x y = d} (commonNormalDistance S T) := by
  obtain ⟨a, b, hab⟩ := exists_feet_coeffs h
  refine ⟨⟨S.point + a • S.direction, (mem_axisLine_iff _ _ _).mpr ⟨a, rfl⟩,
    T.point + b • T.direction, (mem_axisLine_iff _ _ _).mpr ⟨b, rfl⟩, ?_⟩, ?_⟩
  · rw [dist_eq_norm', hab, add_sub_cancel_left, norm_smul, norm_commonNormalDirection h, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (commonNormalDistance_nonneg S T)]
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (mem_axisLine_iff _ _ _).mp hx
    obtain ⟨s, rfl⟩ := (mem_axisLine_iff _ _ _).mp hy
    have hv : (T.point + s • T.direction) - (S.point + r • S.direction) =
        (T.point - S.point) + s • T.direction - r • S.direction := by abel
    have hi : inner ℝ (commonNormalDirection S T)
        ((T.point + s • T.direction) - (S.point + r • S.direction)) =
          commonNormalDistance S T := by
      rw [hv, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        inner_commonNormalDirection_left, inner_commonNormalDirection_right,
        inner_commonNormalDirection_offset S T]
      ring
    calc
      commonNormalDistance S T = inner ℝ (commonNormalDirection S T)
          ((T.point + s • T.direction) - (S.point + r • S.direction)) := hi.symm
      _ ≤ ‖commonNormalDirection S T‖ *
          ‖(T.point + s • T.direction) - (S.point + r • S.direction)‖ :=
        real_inner_le_norm _ _
      _ = dist (S.point + r • S.direction) (T.point + s • T.direction) := by
        rw [norm_commonNormalDirection h, one_mul, dist_eq_norm']

/-- **Intersecting axes (MLS p. 66; excluded by the printed `d > 0`).** For nonparallel axes the
common-normal distance is zero exactly when the two axes meet. -/
theorem commonNormalDistance_eq_zero_iff {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) :
    commonNormalDistance S T = 0 ↔ ∃ x, x ∈ S.axis ∧ x ∈ T.axis := by
  constructor
  · intro hd
    obtain ⟨a, b, hab⟩ := exists_feet_coeffs h
    rw [hd, zero_smul, add_zero] at hab
    refine ⟨S.point + a • S.direction, (mem_axisLine_iff _ _ _).mpr ⟨a, rfl⟩, ?_⟩
    rw [← hab]
    exact (mem_axisLine_iff _ _ _).mpr ⟨b, rfl⟩
  · rintro ⟨x, hx₁, hx₂⟩
    obtain ⟨r, hr⟩ := (mem_axisLine_iff _ _ _).mp hx₁
    obtain ⟨s, hs⟩ := (mem_axisLine_iff _ _ _).mp hx₂
    have hp : T.point - S.point = r • S.direction - s • T.direction := by
      rw [hr] at hs
      have e : T.point = S.point + r • S.direction - s • T.direction := by
        rw [hs]
        abel
      rw [e]
      abel
    simp [commonNormalDistance, offsetMoment, hp, inner_sub_left, real_inner_smul_left]

/-- **MLS eq. (2.72) and the proof of Proposition 2.18, p. 67, for every pair of nonparallel
finite screws.** The twist–wrench pairing of the twist about `S` and the wrench along `T` equals
the reciprocal product `M₁ M₂ ((h₁ + h₂) cos α - d sin α)` with the constructed common-normal
distance and angle, intersecting axes (`d = 0`) included. No certificate is supplied. -/
theorem pair_eq_geometricProduct {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) :
    Wrench.pair T.toWrench S.toTwist = geometricProduct S T := by
  have ho : inner ℝ (S.point - T.point) (Vec3.cross S.direction T.direction) =
      -offsetMoment S T := by
    rw [offsetMoment, ← inner_neg_left, neg_sub]
  rw [pair_eq_coordinateProduct, coordinateProduct, ho, geometricProduct,
    cos_commonNormalAngle S T, sin_commonNormalAngle S T,
    distance_mul_inner_commonNormalDirection h]
  ring

/-- **The printed certificate exists for skew axes (MLS p. 66, `d > 0`).** For nonparallel axes
at positive distance, moving the representative points to the feet of the common normal gives a
`CommonNormal` certificate whose distance, normal and angle are the constructed ones. -/
theorem exists_commonNormal {S T : FiniteScrew} (h : Vec3.cross S.direction T.direction ≠ 0)
    (hd : 0 < commonNormalDistance S T) :
    ∃ r s : ℝ, ∃ C : CommonNormal (S.shift r) (T.shift s),
      C.distance = commonNormalDistance S T ∧ C.normal = commonNormalDirection S T ∧
        C.angle = commonNormalAngle S T := by
  obtain ⟨a, b, hab⟩ := exists_feet_coeffs h
  exact ⟨a, b,
    ⟨commonNormalDirection S T, commonNormalDistance S T, commonNormalAngle S T, hd,
      norm_commonNormalDirection h, inner_commonNormalDirection_left S T,
      inner_commonNormalDirection_right S T, h, hab, cos_commonNormalAngle S T,
      sin_commonNormalAngle S T⟩, rfl, rfl, rfl⟩

/-- The angle `α = atan2(0, ω₁ · ω₂)` of MLS p. 66 for parallel axes, where `ω₁ × ω₂ = 0` and
`α ∈ {0, π}` whatever unit normal is chosen. -/
def parallelAngle (S T : FiniteScrew) : ℝ := Rotation.atan2 0 (inner ℝ S.direction T.direction)

/-- **Parallel axes (MLS p. 66; not covered by the printed proof of p. 67).** If
`ω₁ × ω₂ = 0`, then `sin α = 0` and
`cos α = ω₁ · ω₂ = ±1` for `α = atan2(0, ω₁ · ω₂)`, and the pairing equals
`M₁ M₂ ((h₁ + h₂) cos α - d sin α)` for every value `d` of the distance. -/
theorem pair_eq_of_parallel {S T : FiniteScrew} (h : Vec3.cross S.direction T.direction = 0)
    (d : ℝ) :
    Real.sin (parallelAngle S T) = 0 ∧
      Real.cos (parallelAngle S T) = inner ℝ S.direction T.direction ∧
      (inner ℝ S.direction T.direction = 1 ∨ inner ℝ S.direction T.direction = -1) ∧
      Wrench.pair T.toWrench S.toTwist =
        S.magnitude * T.magnitude *
          ((S.pitch + T.pitch) * Real.cos (parallelAngle S T) -
            d * Real.sin (parallelAngle S T)) := by
  have hg : inner ℝ S.direction T.direction ^ 2 = 1 := by
    have hn := inner_sq_add_norm_cross_sq S T
    rw [h, norm_zero] at hn
    linarith
  have hr : √(inner ℝ S.direction T.direction ^ 2 + (0 : ℝ) ^ 2) = 1 := by
    rw [hg]
    norm_num
  have hc := Rotation.sqrt_mul_cos_atan2 0 (inner ℝ S.direction T.direction)
  have hs := Rotation.sqrt_mul_sin_atan2 0 (inner ℝ S.direction T.direction)
  rw [hr, one_mul] at hc hs
  refine ⟨hs, hc, sq_eq_one_iff.mp hg, ?_⟩
  rw [pair_eq_coordinateProduct, coordinateProduct, h, inner_zero_right, parallelAngle, hc, hs]
  ring

end FiniteScrew

namespace GeometricScrew

/-- **MLS Proposition 2.18, p. 66, for nonparallel finite screws, without a supplied
certificate.** Two finite screws with nonparallel axes are reciprocal iff the reciprocal product
(2.72), computed from the common normal, vanishes. -/
theorem reciprocal_finite_iff_geometricProduct_eq_zero {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction ≠ 0) :
    Reciprocal (.finite S) (.finite T) ↔ FiniteScrew.geometricProduct S T = 0 := by
  change Wrench.pair T.toWrench S.toTwist = 0 ↔ _
  rw [FiniteScrew.pair_eq_geometricProduct h]

/-- **MLS Proposition 2.18, p. 66, for parallel finite screws (not covered by the printed
proof).** Two finite screws with parallel axes are reciprocal iff their pitches sum to zero. -/
theorem reciprocal_finite_iff_of_parallel {S T : FiniteScrew}
    (h : Vec3.cross S.direction T.direction = 0) :
    Reciprocal (.finite S) (.finite T) ↔ S.pitch + T.pitch = 0 := by
  obtain ⟨-, -, hg, hp⟩ := FiniteScrew.pair_eq_of_parallel h 0
  have hg0 : inner ℝ S.direction T.direction ≠ 0 := by
    rcases hg with hg | hg <;> rw [hg] <;> norm_num
  change Wrench.pair T.toWrench S.toTwist = 0 ↔ _
  rw [FiniteScrew.pair_eq_coordinateProduct, FiniteScrew.coordinateProduct, h, inner_zero_right,
    zero_add]
  simp [S.positive_magnitude.ne', T.positive_magnitude.ne', hg0]

/-- **An infinite-pitch twist and a finite-pitch wrench (MLS p. 66, a case left as an
exercise).** The pure translation along `ω` and the wrench along a finite screw `T` are
reciprocal iff `ω` is perpendicular to the axis of `T`. -/
theorem reciprocal_infinite_finite_iff (ω q : Vec3) (M : ℝ) (hω : ‖ω‖ = 1) (hM : 0 < M)
    (T : FiniteScrew) :
    Reciprocal (.infinite ω q M hω hM) (.finite T) ↔ inner ℝ ω T.direction = 0 := by
  change Wrench.pair T.toWrench ⟨M • ω, 0⟩ = 0 ↔ _
  rw [real_inner_comm T.direction ω]
  simp [Wrench.pair, FiniteScrew.toWrench, real_inner_smul_left, real_inner_smul_right,
    T.positive_magnitude.ne', hM.ne']

/-- **A finite-pitch twist and an infinite-pitch wrench (MLS p. 66, a case left as an
exercise).** The twist about a finite screw `S` and the pure couple along `ω` are reciprocal iff
`ω` is perpendicular to the axis of `S`. -/
theorem reciprocal_finite_infinite_iff (S : FiniteScrew) (ω q : Vec3) (M : ℝ) (hω : ‖ω‖ = 1)
    (hM : 0 < M) :
    Reciprocal (.finite S) (.infinite ω q M hω hM) ↔ inner ℝ S.direction ω = 0 := by
  change Wrench.pair (Wrench.pureCouple ω M) S.toTwist = 0 ↔ _
  rw [real_inner_comm ω S.direction]
  simp [Wrench.pair, Wrench.pureCouple, FiniteScrew.toTwist, Twist.fromScrew,
    real_inner_smul_left, real_inner_smul_right, S.positive_magnitude.ne', hM.ne']

/-- **Two infinite-pitch screws (MLS p. 66, a case left as an exercise).** A pure translation
and a pure couple are always reciprocal. -/
theorem reciprocal_infinite_infinite (ω q : Vec3) (M : ℝ) (hω : ‖ω‖ = 1) (hM : 0 < M)
    (ω' q' : Vec3) (M' : ℝ) (hω' : ‖ω'‖ = 1) (hM' : 0 < M') :
    Reciprocal (.infinite ω q M hω hM) (.infinite ω' q' M' hω' hM') := by
  change Wrench.pair (Wrench.pureCouple ω' M') ⟨M • ω, 0⟩ = 0
  simp [Wrench.pair, Wrench.pureCouple]

end GeometricScrew
end RoboLean
