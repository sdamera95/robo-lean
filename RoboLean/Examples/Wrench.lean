import RoboLean.Geometry.Wrench
import RoboLean.Examples.Twist

/-!
# Exact wrench transfer and power witnesses

For this file, the existing fixture `g = (Rz(π/2), (1,2,3))` represents
`g_AB`, taking B coordinates to A. The wrench and twist fixtures are initially
expressed in B. MLS printed pp61–63, equations (2.65)–(2.67), transfers the
wrench to A's origin as `(Rf, p × Rf + Rτ)`; just rotating the moment omits
that origin shift. Pairing is instantaneous power for compatible velocity and
force units, without a numerical-execution or physical-calibration claim.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix

/-- A force and a nonzero moment, both initially expressed about B's origin. -/
def mixedWrench : Wrench := (vec 1 2 3, vec 4 5 6)

/-- `Rf=(-2,1,3)`, `p×Rf=(3,-9,5)`, and `Rτ=(-5,4,6)`. -/
theorem transform_g_mixedWrench :
    Wrench.transform g mixedWrench = (vec (-2) 1 3, vec (-2) (-5) 11) := by
  apply Prod.ext
  · exact quarterTurn_act 1 2 3
  · change Vec3.cross (vec 1 2 3) (quarterTurn.act (vec 1 2 3)) +
      quarterTurn.act (vec 4 5 6) = _
    rw [quarterTurn_act, quarterTurn_act]
    ext i
    fin_cases i <;> norm_num [Vec3.cross, cross_apply, vec]

/-- In B coordinates the two dot products are `14` and `77`. -/
theorem mixedWrench_pair_mixedTwist : Wrench.pair mixedWrench mixedTwist = 91 := by
  simp only [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular,
    mixedWrench, mixedTwist, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  norm_num [dotProduct, Fin.sum_univ_succ, vec]

/-- In A coordinates the dot products are `35` and `56`, independently giving `91`. -/
theorem transformed_mixedWrench_pair_mixedTwist :
    Wrench.pair (Wrench.transform g mixedWrench) (Twist.adjoint g mixedTwist) = 91 := by
  rw [transform_g_mixedWrench, adjoint_g_mixedTwist]
  simp only [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  norm_num [dotProduct, Fin.sum_univ_succ, vec]

/-- Omitting the moment-origin shift changes this pairing to `112`, rather than `91`. -/
theorem rotated_only_mixedWrench_pair :
    Wrench.pair (quarterTurn.act (vec 1 2 3), quarterTurn.act (vec 4 5 6))
      (Twist.adjoint g mixedTwist) = 112 := by
  rw [quarterTurn_act, quarterTurn_act, adjoint_g_mixedTwist]
  simp only [Wrench.pair, Wrench.force, Wrench.torque, Twist.linear, Twist.angular,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  norm_num [dotProduct, Fin.sum_univ_succ, vec]

end RoboLean.Examples
