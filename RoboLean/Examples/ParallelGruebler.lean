import RoboLean.Kinematics.Gruebler

/-!
# Gruebler counts for the parallel mechanisms of MLS Exercises 20–22

MLS printed pp. 151–153, with Gruebler's formula (3.66), p. 133:
`F = d N - ∑ⱼ (d - fⱼ)`, `d = 6` spatial and `d = 3` planar, `N` the moving links, `fⱼ` the
freedoms of joint `j`. The link and joint counts are read from the printed figures (rendered and
read for this module) and the text; they are convention checks of the count, not theorems about
the mobility of the mechanisms.

* Exercise 20 (slider–crank, figure on p. 152): links `l₁`, `l₂` and the slider carrying the bar
  `l₃` (no joint is drawn between the bar and the slider block), `N = 3`; revolute joints at `S`,
  between `l₁` and `l₂` and between `l₂` and `l₃`, and the prismatic slider joint, `g = 4`. The
  planar count is `1`; the spatial count is `-2`, negative for a mechanism that moves, because
  the joints of a planar mechanism do not impose independent spatial constraints (the equality
  case of the count needs independent constraints).
* Exercise 21 (variable geometry truss, figure on p. 152): the platform and three legs of two
  links each, `N = 7`; three prismatic joints and six revolute joints (the pins shared by `d₂, d₃`
  at the base and by `d₁, d₃` at the platform join three links each and count as two joints),
  `g = 9`. The planar count is `3`.
* Exercise 22(a) (Stewart platform, pp. 138–140, Figure 3.21): the platform and six legs of two
  links each, `N = 13`; twelve spherical joints (`f = 3`) and six prismatic joints, `g = 18`. The
  count is `12`: the six degrees of freedom of the platform and the rotation of each leg about its
  own axis ("an extra degree of freedom in each link", p. 140).
* Exercise 22(c): with the twelve spherical joints replaced by U-joints (`f = 2`) the count is `0`.
-/

namespace RoboLean

namespace Examples

/-- **MLS Exercise 20(a), p. 152: the slider–crank in the plane**, `N = 3`, `g = 4`, `fⱼ = 1`:
`F = 3 (3 - 4) + 4 = 1`. -/
theorem grueblerCount_sliderCrank_planar : grueblerCount 3 3 (fun _ : Fin 4 => 1) = 1 := by
  norm_num [grueblerCount, Fin.sum_univ_four]

/-- **MLS Exercise 20(a), p. 152: the spatial count fails for the slider–crank**,
`F = 6 (3 - 4) + 4 = -2`. -/
theorem grueblerCount_sliderCrank_spatial : grueblerCount 6 3 (fun _ : Fin 4 => 1) = -2 := by
  norm_num [grueblerCount, Fin.sum_univ_four]

/-- **MLS Exercise 21(a), p. 152: the variable geometry truss**, `N = 7`, `g = 9`, `fⱼ = 1`:
`F = 3 (7 - 9) + 9 = 3`. -/
theorem grueblerCount_variableGeometryTruss : grueblerCount 3 7 (fun _ : Fin 9 => 1) = 3 := by
  rw [grueblerCount_eq]
  simp

/-- **MLS Exercise 22(a), p. 153: the Stewart platform**, `N = 13`; twelve spherical joints
(`f = 3`) and six prismatic joints (`f = 1`): `F = 6 (13 - 18) + 36 + 6 = 12`. -/
theorem grueblerCount_stewartPlatform :
    grueblerCount 6 13 (Fin.append (fun _ : Fin 12 => 3) (fun _ : Fin 6 => 1)) = 12 := by
  rw [grueblerCount_eq, Fin.sum_univ_add]
  simp

/-- **MLS Exercise 22(c), p. 153: the Stewart platform with U-joints**, twelve U-joints
(`f = 2`) and six prismatic joints: `F = 6 (13 - 18) + 24 + 6 = 0`. -/
theorem grueblerCount_stewartPlatform_universal :
    grueblerCount 6 13 (Fin.append (fun _ : Fin 12 => 2) (fun _ : Fin 6 => 1)) = 0 := by
  rw [grueblerCount_eq, Fin.sum_univ_add]
  simp

end Examples

end RoboLean
