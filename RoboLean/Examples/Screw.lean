import RoboLean.Geometry.TwistScrew
import RoboLean.Examples.RigidTransform

/-!
# Independent exact screw-parameter witnesses

MLS printed pp47–49, equations (2.42)–(2.44), use angular norm rather than a
six-coordinate norm for rotating twists. For `v=(4,-2,6)` and `ω=(0,0,2)`,
`ω·v=12`, `‖ω‖²=4`, and `ω×v=(4,8,0)`: pitch is `3`, perpendicular axis
point `(1,2,0)`, and magnitude `2`. Negative whole-twist scaling preserves
pitch and that point while reversing the angular direction; magnitude is
nonnegative. The zero-twist stationary tag is the explicit library convention.
These coordinate checks do not claim physical calibration or a directed-line API.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix

/-- Nonunit angular coordinates with transverse and axial linear components. -/
def screwTwist : Twist := ⟨vec 4 (-2) 6, vec 0 0 2⟩

private theorem screwTwist_angular_ne_zero : Twist.angular screwTwist ≠ 0 := by
  intro h
  have h₂ := congrArg (fun v : Vec3 => v 2) h
  norm_num [screwTwist, Twist.angular, vec] at h₂

/-- Independently computed pitch `12/4 = 3`. -/
theorem screwTwist_finitePitch : Twist.finitePitch screwTwist screwTwist_angular_ne_zero = 3 := by
  norm_num [Twist.finitePitch, screwTwist, Twist.angular, Twist.linear,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.real_norm_sq_eq,
    dotProduct, Fin.sum_univ_succ, vec]

/-- The rotating branch has a finite pitch, not a translation or stationary tag. -/
theorem screwTwist_pitch_tag : Twist.screwPitch screwTwist = ScrewPitch.finite 3 := by
  rw [Twist.screwPitch_of_angular_ne_zero _ screwTwist_angular_ne_zero, screwTwist_finitePitch]

/-- Independently computed axis point `(4,8,0)/4 = (1,2,0)`. -/
theorem screwTwist_axisPoint :
    Twist.axisPoint screwTwist screwTwist_angular_ne_zero = vec 1 2 0 := by
  ext i
  fin_cases i <;>
    norm_num [Twist.axisPoint, screwTwist, Twist.angular, Twist.linear,
      EuclideanSpace.real_norm_sq_eq, Vec3.cross, cross_apply, Fin.sum_univ_succ, vec]

/-- The displayed axis/pitch reconstruct the literal twist via the origin-sensitive cross sign. -/
theorem screwTwist_fromScrew :
    Twist.fromScrew (vec 0 0 2) (vec 1 2 0) 3 = screwTwist := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    norm_num [Twist.fromScrew, screwTwist, Vec3.cross, cross_apply, vec]

/-- The magnitude is angular norm two, even with a larger nonzero linear component. -/
theorem screwTwist_magnitude : Twist.screwMagnitude screwTwist = 2 := by
  rw [Twist.screwMagnitude_of_angular_ne_zero _ screwTwist_angular_ne_zero]
  norm_num [screwTwist, Twist.angular, EuclideanSpace.norm_eq, Fin.sum_univ_succ, vec]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- A negative scalar changes both coordinate components and reverses the angular sign. -/
theorem screwTwist_negative_components :
    (-3 : ℝ) • screwTwist = ⟨vec (-12) 6 (-18), vec 0 0 (-6)⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;> norm_num [screwTwist, vec]

private theorem negative_screwTwist_angular_ne_zero :
    Twist.angular ((-3 : ℝ) • screwTwist) ≠ 0 :=
  Twist.angular_smul_ne_zero screwTwist screwTwist_angular_ne_zero (-3) (by norm_num)

/-- The negatively scaled coordinates give pitch `108/36 = 3` by direct evaluation. -/
theorem screwTwist_negative_finitePitch :
    Twist.finitePitch ((-3 : ℝ) • screwTwist) negative_screwTwist_angular_ne_zero = 3 := by
  unfold Twist.finitePitch
  rw [screwTwist_negative_components]
  norm_num [Twist.angular, Twist.linear, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.real_norm_sq_eq, dotProduct, Fin.sum_univ_succ, vec]

/-- The scaled cross product `(36,72,0)` divided by `36` keeps the same axis point. -/
theorem screwTwist_negative_axisPoint :
    Twist.axisPoint ((-3 : ℝ) • screwTwist) negative_screwTwist_angular_ne_zero = vec 1 2 0 := by
  unfold Twist.axisPoint
  rw [screwTwist_negative_components]
  ext i
  fin_cases i <;>
    norm_num [Twist.angular, Twist.linear, EuclideanSpace.real_norm_sq_eq,
      Vec3.cross, cross_apply, Fin.sum_univ_succ, vec]

/-- The reversed angular vector has magnitude six, not minus six. -/
theorem screwTwist_negative_magnitude : Twist.screwMagnitude ((-3 : ℝ) • screwTwist) = 6 := by
  rw [Twist.screwMagnitude_of_angular_ne_zero _ negative_screwTwist_angular_ne_zero,
    screwTwist_negative_components]
  norm_num [Twist.angular, EuclideanSpace.norm_eq, Fin.sum_univ_succ, vec]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- A 3–4–5 pure translation receives infinite pitch and linear magnitude five. -/
theorem translation_screw_parameters :
    Twist.screwPitch ⟨vec 0 3 4, 0⟩ = ScrewPitch.infinite ∧
      Twist.screwMagnitude ⟨vec 0 3 4, 0⟩ = 5 := by
  have hv : vec 0 3 4 ≠ 0 := by
    intro h
    have h₂ := congrArg (fun v : Vec3 => v 2) h
    norm_num [vec] at h₂
  constructor
  · exact Twist.screwPitch_pure_translation _ hv
  · rw [Twist.screwMagnitude_of_angular_eq_zero _ rfl]
    norm_num [Twist.linear, EuclideanSpace.norm_eq, Fin.sum_univ_succ, vec]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- Zero is stationary with zero magnitude, separately from nonzero pure translation. -/
theorem stationary_screw_parameters :
    Twist.screwPitch (0 : Twist) = ScrewPitch.stationary ∧
      Twist.screwMagnitude (0 : Twist) = 0 := by
  simp [Twist.screwPitch, Twist.screwMagnitude]

end RoboLean.Examples
