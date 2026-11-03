import RoboLean.Examples.GraspPlanning

/-!
# Exercise 5.2(a): three point contacts with friction on an equilateral triangle

MLS Chapter 5, Exercise 2(a), printed p. 259 (figure read as a rendered image): "Construct the
grasp map for the grasps shown below and write the friction cone conditions with respect to the
contact basis you choose. Determine if the grasp is force-closure. Assume that all contacts are
point contacts with friction", grasp (a) being an equilateral triangle with one contact on each
edge, the arrows drawn normal to the edges near their midpoints, and `μ = tan 15°`.

Reading (stated here): the triangle of side `1` with vertices `(0, 0)`, `(1, 0)`, `(1/2, √3/2)`,
contacts at the three edge midpoints with frames in the planar convention of p. 222 (`y`-axis the
inward normal); the bottom frame is the identity, the right-edge frame the rotation by `2π/3`, the
left-edge frame the rotation by `-2π/3` (`Examples.triangleRotation`). The three normals meet at
the centroid, so equal normal forces with no tangential force are a strictly internal force for
every `μ > 0`, and the grasp map is onto: the grasp is force-closure for every `μ > 0`
(Proposition 5.2, p. 224), in particular for `μ = tan 15°`. The grasp map itself is
`Grasp.planar_planarPointContact_graspMap` at these frames and the friction cone conditions are
`|f_{i,1}| ≤ μ f_{i,2}` (p. 222).

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp Real

/-- The rotation by `2π/3`, the contact frame at the midpoint of the right edge of the triangle of
MLS Exercise 2(a), printed p. 259 (inward normal `(-√3/2, -1/2)`, planar convention of p. 222). -/
def triangleRotationRight : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![-1 / 2, -√3 / 2; √3 / 2, -1 / 2], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, by ring, ?_⟩
    rw [div_pow, div_pow, neg_sq, neg_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num⟩

/-- The contact frames at the bottom, right and left edge midpoints of the triangle of MLS
Exercise 2(a), printed p. 259. -/
def triangleMidFrames : Fin 3 → Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ![1, triangleRotationRight, triangleRotation]

/-- The edge midpoints `(1/2, 0)`, `(3/4, √3/4)`, `(1/4, √3/4)` of the triangle of MLS
Exercise 2(a), printed p. 259 (side `1`, vertices `(0, 0)`, `(1, 0)`, `(1/2, √3/2)`). -/
def triangleMidPoints : Fin 3 → Fin 2 → ℝ :=
  ![![1 / 2, 0], ![3 / 4, √3 / 4], ![1 / 4, √3 / 4]]

/-- **MLS Exercise 2(a)**, printed p. 259: three point contacts with friction (cone of p. 222) at
the edge midpoints of an equilateral triangle form a force-closure grasp for every `μ > 0`
(Proposition 5.2, p. 224). -/
theorem triangleMid_isForceClosure {μ : ℝ} (hμ : 0 < μ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) triangleMidFrames
      triangleMidPoints).toGrasp.IsForceClosure := by
  rw [Grasp.isForceClosure_iff]
  refine ⟨fun W => ⟨![![W 0 - √3 * (W 1 - 2 * W 2), 2 * (W 1 - W 2)], ![0, 0],
    ![0, 2 * W 1 - 4 * W 2]], ?_⟩, ![![0, 1], ![0, 1], ![0, 1]], ?_, ?_⟩
  · rw [ContactGrasp.toGrasp_map, planar_planarPointContact_graspMap]
    funext i
    fin_cases i <;> simp [Fin.sum_univ_three, planarWrench, cross2, triangleMidFrames,
      triangleRotation, triangleRotationRight, triangleMidPoints, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
      first | ring1 | (ring_nf; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring)
  · rw [ContactGrasp.toGrasp_map, planar_planarPointContact_graspMap]
    funext i
    fin_cases i <;> simp [Fin.sum_univ_three, planarWrench, cross2, triangleMidFrames,
      triangleRotation, triangleRotationRight, triangleMidPoints, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
      ring1
  · rw [ContactGrasp.toGrasp_cone, ContactGrasp.mem_interior_cone]
    intro i
    fin_cases i <;> refine mem_interior_planarPointContactCone ?_ ?_ <;> simp [hμ]

/-- **MLS Exercise 2(a)**, printed p. 259, with the printed coefficient `μ = tan 15°`
(`tan (π/12)`): the grasp of three point contacts at the edge midpoints is force-closure. -/
theorem triangleMid_isForceClosure_tan15 :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact (tan (π / 12))
      (tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith [pi_pos])))
      triangleMidFrames triangleMidPoints).toGrasp.IsForceClosure := by
  exact triangleMid_isForceClosure _

end RoboLean.Examples
