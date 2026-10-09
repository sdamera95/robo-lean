import RoboLean.Geometry.WrenchScrew
import RoboLean.Examples.RigidTransform

/-!
# Independent wrench screw and Poinsot witnesses

MLS printed pp64–66, equations (2.68)–(2.71), measure moment about the stated
frame origin. For `f=(0,0,2)` and `τ=(4,-2,6)`, direct arithmetic gives pitch
`12/4=3`, perpendicular point `(4,8,0)/4=(1,2,0)`, force direction `+z`, and
magnitude `2`. The moment includes the offset contribution `(1,2,0)×f`.
A separate pure-force shift and the pure-couple/zero branches check the origin
sign and degeneracy conventions. No contact-feasibility claim is made.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix

/-- A nonzero force with both offset and axial moment. -/
def screwWrench : Wrench := (vec 0 0 2, vec 4 (-2) 6)

private theorem screwWrench_force_ne_zero : Wrench.force screwWrench ≠ 0 := by
  intro h
  have h₂ := congrArg (fun v : Vec3 => v 2) h
  norm_num [screwWrench, Wrench.force, vec] at h₂

/-- The direct force-moment dot product gives pitch three. -/
theorem screwWrench_finitePitch : Wrench.finitePitch screwWrench screwWrench_force_ne_zero = 3 := by
  rw [Wrench.finitePitch_eq]
  norm_num [screwWrench, Wrench.force, Wrench.torque,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.real_norm_sq_eq,
    dotProduct, Fin.sum_univ_succ, vec]

/-- The direct cross product gives the perpendicular force-line point. -/
theorem screwWrench_axisPoint :
    Wrench.axisPoint screwWrench screwWrench_force_ne_zero = vec 1 2 0 := by
  rw [Wrench.axisPoint_eq]
  ext i
  fin_cases i <;>
    norm_num [screwWrench, Wrench.force, Wrench.torque, EuclideanSpace.real_norm_sq_eq,
      Vec3.cross, cross_apply, Fin.sum_univ_succ, vec]

/-- Force normalization gives the independently specified positive z direction. -/
theorem screwWrench_forceDirection :
    Wrench.forceDirection screwWrench screwWrench_force_ne_zero = vec 0 0 1 := by
  have hn : ‖Wrench.force screwWrench‖ = 2 := by
    norm_num [screwWrench, Wrench.force, EuclideanSpace.norm_eq, Fin.sum_univ_succ, vec]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  unfold Wrench.forceDirection
  rw [hn]
  ext i
  fin_cases i <;> norm_num [screwWrench, Wrench.force, vec]

/-- Literal unit-axis, point, pitch and magnitude reconstruct the original coordinates. -/
theorem screwWrench_fromScrew :
    Wrench.fromScrew (vec 0 0 1) (vec 1 2 0) 3 2 = screwWrench := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    norm_num [Wrench.fromScrew, screwWrench, Vec3.cross, cross_apply, vec]

/-- Magnitude is the force norm two, rather than a norm of all six coordinates. -/
theorem screwWrench_magnitude : Wrench.screwMagnitude screwWrench = 2 := by
  rw [Wrench.screwMagnitude_of_force_ne_zero _ screwWrench_force_ne_zero]
  norm_num [screwWrench, Wrench.force, EuclideanSpace.norm_eq, Fin.sum_univ_succ, vec]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- With `p_AB=(0,3,0)`, the force at B gives moment `(0,0,-6)` about A's origin. -/
theorem shifted_pure_force :
    Wrench.transform (⟨1, vec 0 3 0⟩ : RigidTransform) (vec 2 0 0, 0) =
      (vec 2 0 0, vec 0 0 (-6)) := by
  apply Prod.ext
  · simp [Wrench.transform, Wrench.force]
  · ext i
    fin_cases i <;>
      norm_num [Wrench.transform, Wrench.force, Wrench.torque,
        Vec3.cross, cross_apply, Rotation.act_one, vec]

private theorem shifted_force_ne_zero : Wrench.force (vec 2 0 0, vec 0 0 (-6)) ≠ 0 := by
  intro h
  have h₀ := congrArg (fun v : Vec3 => v 0) h
  norm_num [Wrench.force, vec] at h₀

/-- Zero pitch does not require zero moment about the chosen frame origin. -/
theorem shifted_pure_force_pitch :
    Wrench.finitePitch (vec 2 0 0, vec 0 0 (-6)) shifted_force_ne_zero = 0 := by
  rw [Wrench.finitePitch_eq]
  norm_num [Wrench.force, Wrench.torque, EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.real_norm_sq_eq, dotProduct, Fin.sum_univ_succ, vec]

/-- The shifted pure-force line passes through `(0,3,0)`, with direction +x. -/
theorem shifted_pure_force_axisPoint :
    Wrench.axisPoint (vec 2 0 0, vec 0 0 (-6)) shifted_force_ne_zero = vec 0 3 0 := by
  rw [Wrench.axisPoint_eq]
  ext i
  fin_cases i <;>
    norm_num [Wrench.force, Wrench.torque, EuclideanSpace.real_norm_sq_eq,
      Vec3.cross, cross_apply, Fin.sum_univ_succ, vec]

/-- A normalized 3–4–5 direction and magnitude five give the stated pure couple. -/
theorem couple_reconstruction_five :
    Wrench.pureCouple (vec 0 (3 / 5) (4 / 5)) 5 = (0, vec 0 3 4) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> norm_num [Wrench.pureCouple, vec]

/-- The nonzero pure couple receives infinite pitch and moment magnitude five. -/
theorem couple_parameters_five :
    Wrench.screwPitch (0, vec 0 3 4) = ScrewPitch.infinite ∧
      Wrench.screwMagnitude (0, vec 0 3 4) = 5 := by
  have hτ : vec 0 3 4 ≠ 0 := by
    intro h
    have h₂ := congrArg (fun v : Vec3 => v 2) h
    norm_num [vec] at h₂
  constructor
  · exact (Wrench.screwPitch_eq_infinite_iff _).mpr ⟨rfl, hτ⟩
  · rw [Wrench.screwMagnitude_of_force_eq_zero _ rfl]
    norm_num [Wrench.torque, EuclideanSpace.norm_eq, Fin.sum_univ_succ, vec]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- The zero wrench has no axis, stationary pitch, and zero magnitude. -/
theorem zero_wrench_screw_parameters :
    Wrench.screwPitch (0 : Wrench) = ScrewPitch.stationary ∧
      Wrench.screwMagnitude (0 : Wrench) = 0 ∧ Wrench.screwAxis (0 : Wrench) = none := by
  simp

end RoboLean.Examples
