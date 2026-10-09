import RoboLean.Geometry.Reciprocal
import RoboLean.Geometry.WrenchScrew
import RoboLean.Geometry.ScrewAxis

/-!
# Geometric screws and the reciprocal product

MLS printed pp. 66–67, Definition 2.3, equation (2.72), and Proposition 2.18
(ledger X58/X60). Geometric representatives have unit directions, positive
magnitudes, and actual affine axes. Zero is excluded explicitly. Infinite pitch
has its own constructor; the finite common-normal formula does not cover it.

The common-normal certificate requires distinct nonparallel axes, a positive
separation, a unit normal perpendicular to both directions, and explicit signed
sine/cosine relations. Its separation is proved to be attained and minimal.
No existence theorem for such certificates, `atan2` identification, or principal
angle branch is claimed. Parallel/intersecting axes still satisfy the coordinate
pairing formula, but are excluded from the common-normal angle theorem.
These are geometric/algebraic identities, not contact-feasibility statements.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- Nondegenerate finite screw data with an explicit directed affine-axis representative. -/
structure FiniteScrew where
  direction : Vec3
  point : Vec3
  pitch : ℝ
  magnitude : ℝ
  unit_direction : ‖direction‖ = 1
  positive_magnitude : 0 < magnitude

namespace FiniteScrew

theorem direction_ne_zero (S : FiniteScrew) : S.direction ≠ 0 := by
  intro h
  have hn := S.unit_direction
  simp [h] at hn

/-- The actual affine axis; changing the representative point along it changes no line. -/
def axis (S : FiniteScrew) : AffineSubspace ℝ Vec3 := axisLine S.point S.direction

theorem axis_finrank (S : FiniteScrew) : Module.finrank ℝ S.axis.direction = 1 :=
  axisLine_finrank _ _ S.direction_ne_zero

/-- Twist about the finite geometric screw. -/
def toTwist (S : FiniteScrew) : Twist :=
  S.magnitude • Twist.fromScrew S.direction S.point S.pitch

/-- Wrench along the same finite geometric screw. -/
def toWrench (S : FiniteScrew) : Wrench :=
  Wrench.fromScrew S.direction S.point S.pitch S.magnitude

theorem toWrench_eq_swap_toTwist (S : FiniteScrew) :
    S.toWrench = Twist.swapWrench S.toTwist := rfl

theorem toTwist_ne_zero (S : FiniteScrew) : S.toTwist ≠ 0 := by
  intro h
  have ha := congrArg Twist.angular h
  change S.magnitude • S.direction = 0 at ha
  exact smul_ne_zero (ne_of_gt S.positive_magnitude) S.direction_ne_zero ha

/-- A different representative point on the same directed axis. -/
def shift (S : FiniteScrew) (r : ℝ) : FiniteScrew :=
  { S with point := S.point + r • S.direction }

@[simp] theorem axis_shift (S : FiniteScrew) (r : ℝ) : (S.shift r).axis = S.axis :=
  axisLine_shift S.point S.direction r

@[simp] theorem toTwist_shift (S : FiniteScrew) (r : ℝ) :
    (S.shift r).toTwist = S.toTwist := by
  simp only [toTwist, shift, Twist.fromScrew_axis_shift]

@[simp] theorem toWrench_shift (S : FiniteScrew) (r : ℝ) :
    (S.shift r).toWrench = S.toWrench := by
  simp only [toWrench, shift, Wrench.fromScrew_axis_shift]

/-- The coordinate expression for the reciprocal geometry, before multiplying magnitudes. -/
def coordinateProduct (S T : FiniteScrew) : ℝ :=
  inner ℝ (S.point - T.point) (Vec3.cross S.direction T.direction) +
    (S.pitch + T.pitch) * inner ℝ S.direction T.direction

/-- The actual independently generated wrench/twist pairing equals the finite geometric
coordinate expression, with its common-frame offset sign fixed. -/
theorem pair_eq_coordinateProduct (S T : FiniteScrew) :
    Wrench.pair T.toWrench S.toTwist = S.magnitude * T.magnitude * S.coordinateProduct T := by
  simp [toWrench, toTwist, coordinateProduct, Wrench.fromScrew, Twist.fromScrew,
    Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Vec3.cross, cross_apply,
    dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply]
  ring

/-- Source common-normal and signed-angle data for the nonparallel finite branch.
The positive separation excludes intersecting/coincident axes. -/
structure CommonNormal (S T : FiniteScrew) where
  normal : Vec3
  distance : ℝ
  angle : ℝ
  distance_pos : 0 < distance
  unit_normal : ‖normal‖ = 1
  perpendicular_left : inner ℝ normal S.direction = 0
  perpendicular_right : inner ℝ normal T.direction = 0
  nonparallel : Vec3.cross S.direction T.direction ≠ 0
  point_displacement : T.point = S.point + distance • normal
  cosine : Real.cos angle = inner ℝ S.direction T.direction
  sine : Real.sin angle = inner ℝ normal (Vec3.cross S.direction T.direction)

namespace CommonNormal

/-- The selected points attain the certificate's separation. -/
theorem dist_points {S T : FiniteScrew} (C : CommonNormal S T) :
    dist S.point T.point = C.distance := by
  rw [dist_eq_norm', C.point_displacement]
  simp [norm_smul, C.unit_normal, Real.norm_eq_abs, abs_of_pos C.distance_pos]

/-- Every pair of points on the actual affine axes is at least this far apart. -/
theorem distance_le_dist {S T : FiniteScrew} (C : CommonNormal S T)
    {x y : Vec3} (hx : x ∈ S.axis) (hy : y ∈ T.axis) : C.distance ≤ dist x y := by
  obtain ⟨r, rfl⟩ := (mem_axisLine_iff _ _ _).mp hx
  obtain ⟨s, rfl⟩ := (mem_axisLine_iff _ _ _).mp hy
  have hi : inner ℝ C.normal
      ((T.point + s • T.direction) - (S.point + r • S.direction)) = C.distance := by
    rw [C.point_displacement]
    simp [inner_sub_right, inner_add_right, real_inner_smul_right,
      C.perpendicular_left, C.perpendicular_right, C.unit_normal]
  calc
    C.distance = inner ℝ C.normal
        ((T.point + s • T.direction) - (S.point + r • S.direction)) := hi.symm
    _ ≤ ‖C.normal‖ * ‖(T.point + s • T.direction) - (S.point + r • S.direction)‖ :=
      real_inner_le_norm _ _
    _ = dist (S.point + r • S.direction) (T.point + s • T.direction) := by
      rw [C.unit_normal, one_mul, dist_eq_norm']

/-- The source distance is a minimum distance between the affine axes, not an
unconstrained scalar supplied to the reciprocal formula. -/
theorem isLeast_distance {S T : FiniteScrew} (C : CommonNormal S T) :
    IsLeast {d : ℝ | ∃ x ∈ S.axis, ∃ y ∈ T.axis, dist x y = d} C.distance := by
  refine ⟨⟨S.point, self_mem_axisLine _ _, T.point, self_mem_axisLine _ _, C.dist_points⟩, ?_⟩
  rintro d ⟨x, hx, y, hy, rfl⟩
  exact C.distance_le_dist hx hy

/-- MLS equation (2.72), independently expressed by common-normal distance and angle. -/
def reciprocalProduct {S T : FiniteScrew} (C : CommonNormal S T) : ℝ :=
  S.magnitude * T.magnitude *
    ((S.pitch + T.pitch) * Real.cos C.angle - C.distance * Real.sin C.angle)

/-- The geometric reciprocal product equals the actual twist/wrench pairing. -/
theorem pair_eq_reciprocalProduct {S T : FiniteScrew} (C : CommonNormal S T) :
    Wrench.pair T.toWrench S.toTwist = C.reciprocalProduct := by
  have hp : S.point - T.point = -(C.distance • C.normal) := by
    rw [C.point_displacement]
    abel
  rw [pair_eq_coordinateProduct, coordinateProduct, hp, inner_neg_left,
    real_inner_smul_left, ← C.sine, ← C.cosine]
  unfold reciprocalProduct
  ring

end CommonNormal
end FiniteScrew

/-- Nonzero finite- or infinite-pitch geometric representatives.
Infinite-pitch point choices do not affect their generated coordinates. -/
inductive GeometricScrew where
  | finite (data : FiniteScrew)
  | infinite (direction point : Vec3) (magnitude : ℝ)
      (unit_direction : ‖direction‖ = 1) (positive_magnitude : 0 < magnitude)

namespace GeometricScrew

/-- Actual affine axis of the geometric representative. -/
def axis : GeometricScrew → AffineSubspace ℝ Vec3
  | .finite S => S.axis
  | .infinite ω q _ _ _ => axisLine q ω

/-- Twist about the represented screw, including the pure-translation branch. -/
def toTwist : GeometricScrew → Twist
  | .finite S => S.toTwist
  | .infinite ω _ M _ _ => (M • ω, 0)

/-- Wrench along the represented screw, including the pure-couple branch. -/
def toWrench : GeometricScrew → Wrench
  | .finite S => S.toWrench
  | .infinite ω _ M _ _ => Wrench.pureCouple ω M

theorem toWrench_eq_swap_toTwist (S : GeometricScrew) :
    S.toWrench = Twist.swapWrench S.toTwist := by
  cases S <;> rfl

theorem axis_finrank (S : GeometricScrew) : Module.finrank ℝ S.axis.direction = 1 := by
  cases S with
  | finite S => exact S.axis_finrank
  | infinite ω q M hω hM =>
    apply axisLine_finrank
    intro hzero
    simp [hzero] at hω

theorem toTwist_ne_zero (S : GeometricScrew) : S.toTwist ≠ 0 := by
  cases S with
  | finite S => exact S.toTwist_ne_zero
  | infinite ω q M hω hM =>
    intro h
    have hl := congrArg Twist.linear h
    change M • ω = 0 at hl
    have hω0 : ω ≠ 0 := by intro hz; simp [hz] at hω
    exact smul_ne_zero (ne_of_gt hM) hω0 hl

theorem toWrench_ne_zero (S : GeometricScrew) : S.toWrench ≠ 0 := by
  intro h
  rw [toWrench_eq_swap_toTwist] at h
  apply S.toTwist_ne_zero
  apply Twist.swapWrench.injective
  simpa only [map_zero] using h

/-- MLS Definition 2.3, induced from actual nondegenerate geometric representatives. -/
def Reciprocal (S T : GeometricScrew) : Prop := Wrench.Reciprocal T.toWrench S.toTwist

theorem reciprocal_iff_coordinateProduct_zero (S T : GeometricScrew) :
    Reciprocal S T ↔ Twist.reciprocalProduct S.toTwist T.toTwist = 0 := by
  rw [Reciprocal, Wrench.Reciprocal, toWrench_eq_swap_toTwist]
  change Twist.reciprocalProduct T.toTwist S.toTwist = 0 ↔ _
  rw [Twist.reciprocalProduct_symm]

theorem reciprocal_symm (S T : GeometricScrew) : Reciprocal S T ↔ Reciprocal T S := by
  rw [reciprocal_iff_coordinateProduct_zero, reciprocal_iff_coordinateProduct_zero,
    Twist.reciprocalProduct_symm]

/-- Proposition 2.18 for the explicit finite nonparallel common-normal branch. -/
theorem reciprocal_finite_iff_geometricProduct_zero (S T : FiniteScrew)
    (C : FiniteScrew.CommonNormal S T) :
    Reciprocal (.finite S) (.finite T) ↔ C.reciprocalProduct = 0 := by
  change Wrench.pair T.toWrench S.toTwist = 0 ↔ _
  rw [C.pair_eq_reciprocalProduct]

end GeometricScrew
end RoboLean
