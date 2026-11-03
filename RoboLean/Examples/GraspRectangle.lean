import RoboLean.Grasp.AntipodalGrasp

/-!
# Exercise 8(c): two-contact force-closure grasps of a `2 × 1` rectangle

MLS Chapter 5, Exercise 8(c), printed p. 261 (figure read as a rendered image): "For the objects
given below, find all force-closure grasps using two contacts with friction ... Assume that the
coefficient of friction for all contacts is `μ = tan 45°`." Object (c) is a rectangle of width `2`
and height `1`, placed here as `[0, 2] × [0, 1]` (the book fixes no axes), with frames in the planar
convention of p. 222 (`y`-axis the inward normal, `x`-axis `t` with `t ⊗ n = 1`).

With `μ = 1` (Theorem 5.6, p. 232, the inward normals of a convex object facing each other):

* contacts `(s, 0)` on the bottom and `(t, 1)` on the top: force-closure exactly when `|t - s| < 1`;
* contacts `(0, s)` on the left and `(2, t)` on the right: force-closure exactly when `|t - s| < 2`,
  so every pair of points of the two short edges gives a force-closure grasp;
* contacts on the bottom and on the right edge (adjacent edges): never force-closure;
* two contacts on the same edge (the bottom): never force-closure.

The other adjacent pairs and the other single edges follow by the rectangle's symmetries, which
are not formalized here; the "independent contact regions" of the exercise are a drawing.

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp

/-- The contact frame on the top edge of the rectangle of MLS Exercise 8(c), printed p. 261: the
rotation by `π`, inward normal `(0, -1)`, tangent `(-1, 0)` (planar convention of p. 222). -/
def rectTopRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![-1, 0; 0, -1], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    norm_num⟩

/-- The contact frame on the left edge of the rectangle of MLS Exercise 8(c), printed p. 261: the
rotation by `-π/2`, inward normal `(1, 0)`, tangent `(0, -1)` (planar convention of p. 222). -/
def rectLeftRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    norm_num⟩

/-- The contact frame on the right edge of the rectangle of MLS Exercise 8(c), printed p. 261: the
rotation by `π/2`, inward normal `(-1, 0)`, tangent `(0, 1)` (planar convention of p. 222). -/
def rectRightRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![0, -1; 1, 0], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    norm_num⟩

/-- **MLS Exercise 8(c)**, printed p. 261, bottom and top edges: point contacts with friction
(`μ = tan 45° = 1`, cone of p. 222) at `(s, 0)` and `(t, 1)` form a force-closure grasp exactly
when `|t - s| < 1`. -/
theorem rectangle_bottomTop_isForceClosure_iff (s t : ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![1, rectTopRotation] ![![s, 0], ![t, 1]]).toGrasp.IsForceClosure ↔ |t - s| < 1 := by
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;> simp [contactNormal, rectTopRotation, dotProduct,
        Fin.sum_univ_two]),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, rectTopRotation, dotProduct, Fin.sum_univ_two]

/-- **MLS Exercise 8(c)**, printed p. 261, left and right edges: point contacts with friction
(`μ = 1`) at `(0, s)` and `(2, t)` form a force-closure grasp exactly when `|t - s| < 2`. -/
theorem rectangle_leftRight_isForceClosure_iff (s t : ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![rectLeftRotation, rectRightRotation] ![![0, s], ![2, t]]).toGrasp.IsForceClosure ↔
      |t - s| < 2 := by
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;> simp [contactNormal, rectLeftRotation, rectRightRotation, dotProduct,
        Fin.sum_univ_two]),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, rectLeftRotation, rectRightRotation, dotProduct, Fin.sum_univ_two]
  rw [abs_sub_comm]

/-- **MLS Exercise 8(c)**, printed p. 261: every pair of points `(0, s)`, `(2, t)`,
`s, t ∈ [0, 1]`, of the two short edges gives a force-closure grasp (`μ = 1`). -/
theorem rectangle_leftRight_isForceClosure {s t : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![rectLeftRotation, rectRightRotation] ![![0, s], ![2, t]]).toGrasp.IsForceClosure := by
  rw [rectangle_leftRight_isForceClosure_iff, abs_lt]
  constructor <;> linarith

/-- **MLS Exercise 8(c)**, printed p. 261, adjacent edges: point contacts with friction (`μ = 1`)
at `(s, 0)` on the bottom and `(2, t)` on the right edge, `s ≤ 2`, `t ≥ 0`, never form a
force-closure grasp (the two inward normals are perpendicular). -/
theorem rectangle_bottomRight_not_isForceClosure {s t : ℝ} (hs : s ≤ 2) (ht : 0 ≤ t) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![1, rectRightRotation] ![![s, 0], ![2, t]]).toGrasp.IsForceClosure := by
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;> simp [contactNormal, rectRightRotation, dotProduct,
        Fin.sum_univ_two] <;> linarith),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, rectRightRotation, dotProduct, Fin.sum_univ_two]
  intro h1
  rw [abs_lt] at h1
  rw [abs_of_nonneg ht]
  linarith

/-- **MLS Exercise 8(c)**, printed p. 261, one edge: two point contacts with friction (`μ = 1`) at
`(s, 0)` and `(t, 0)` on the bottom edge never form a force-closure grasp. -/
theorem rectangle_bottomBottom_not_isForceClosure (s t : ℝ) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![1, 1] ![![s, 0], ![t, 0]]).toGrasp.IsForceClosure := by
  apply not_isForceClosure_of_contactNormal_dotProduct_eq_zero
  simp [contactNormal, dotProduct, Fin.sum_univ_two]

end RoboLean.Examples
