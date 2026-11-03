import RoboLean.Examples.GraspRectangle

/-!
# Exercise 8(a): two-contact force-closure grasps of the trapezoid

MLS Chapter 5, Exercise 8(a), printed p. 261 (figure read as a rendered image): "For the objects
given below, find all force-closure grasps using two contacts with friction ... Assume that the
coefficient of friction for all contacts is `µ = tan 45°`." Object (a) is the isosceles trapezoid
with the long edge `2` on top, the short edge `1` at the bottom, interior angles `60°` at the top
corners and `120°` at the bottom corners; its height is `√3/2` and its legs have length `1`. It
is placed here with vertices `(0, √3/2)`, `(2, √3/2)`, `(3/2, 0)`, `(1/2, 0)` (the book fixes no
axes), with frames in the planar convention of p. 222 (`y`-axis the inward normal, `x`-axis `t`
with `t ⊗ n = 1`). Points: bottom `(t, 0)`, `t ∈ [1/2, 3/2]`; top `(s, √3/2)`, `s ∈ [0, 2]`; left
leg `(u/2, √3/2 (1 − u))` and right leg `(2 − v/2, √3/2 (1 − v))`, `u, v ∈ [0, 1]` from the top
corners.

With `µ = 1` (Theorem 5.6, p. 232, the inward normals facing each other), edge pair by edge pair:

* bottom and top: force-closure exactly when `|s − t| < √3/2`;
* left and right legs: exactly when `|1 − u + v/2| < (√3/2)(2 − v)` and
  `|1 − v + u/2| < (√3/2)(2 − u)` (in particular at the two top corners);
* top and left leg: exactly when `|s − u/2| < (√3/2) u` and `|s − 2u| < √3 s`; top and right
  leg: the mirror image (for example `s = 1`, `u = 1` is force-closure);
* bottom and a leg: never;
* two contacts on one edge: never (shown for the top and the left leg).

The "independent contact regions" of the exercise are a drawing and are not formalized.
Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp Real

/-- The contact frame on the left leg of the trapezoid of MLS Exercise 8(a), printed p. 261: inward
normal `(√3/2, 1/2)`, tangent `(1/2, −√3/2)` (planar convention of p. 222; rotation by `−60°`). -/
def trapezoidLeftRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![1 / 2, √3 / 2; -(√3 / 2), 1 / 2], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, by ring, ?_⟩
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num⟩

/-- The contact frame on the right leg of the trapezoid of MLS Exercise 8(a), printed p. 261:
inward normal `(−√3/2, 1/2)`, tangent `(1/2, √3/2)` (planar convention of p. 222; rotation by
`60°`). -/
def trapezoidRightRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![1 / 2, -(√3 / 2); √3 / 2, 1 / 2], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, rfl, ?_⟩
    rw [neg_sq, div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num⟩

/-- **MLS Exercise 8(a)**, printed p. 261, bottom and top edges: point contacts with friction
(`µ = tan 45° = 1`) at `(t, 0)` and `(s, √3/2)` form a force-closure grasp exactly when
`|s − t| < √3/2`. -/
theorem trapezoid_bottomTop_isForceClosure_iff (t s : ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![1, rectTopRotation] ![![t, 0], ![s, √3 / 2]]).toGrasp.IsForceClosure ↔
      |s - t| < √3 / 2 := by
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;> simp [contactNormal, rectTopRotation, dotProduct,
        Fin.sum_univ_two] <;> positivity),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, rectTopRotation, dotProduct, Fin.sum_univ_two]

/-- **MLS Exercise 8(a)**, printed p. 261, the two legs: point contacts with friction (`µ = 1`) at
`(u/2, √3/2 (1 − u))` and `(2 − v/2, √3/2 (1 − v))`, `u, v ≤ 2`, form a force-closure grasp exactly
when `|1 − u + v/2| < (√3/2)(2 − v)` and `|1 − v + u/2| < (√3/2)(2 − u)`. -/
theorem trapezoid_leftRight_isForceClosure_iff (u v : ℝ) (hu : u ≤ 2) (hv : v ≤ 2) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![trapezoidLeftRotation, trapezoidRightRotation]
        ![![u / 2, √3 / 2 * (1 - u)], ![2 - v / 2, √3 / 2 * (1 - v)]]).toGrasp.IsForceClosure ↔
      |1 - u + v / 2| < √3 / 2 * (2 - v) ∧ |1 - v + u / 2| < √3 / 2 * (2 - u) := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : 0 ≤ √3 := Real.sqrt_nonneg 3
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;>
        simp [contactNormal, trapezoidLeftRotation, trapezoidRightRotation, dotProduct,
          Fin.sum_univ_two] <;> nlinarith),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, trapezoidLeftRotation, trapezoidRightRotation, dotProduct,
    Fin.sum_univ_two]
  rw [show 2⁻¹ * (2 - v / 2 - u / 2) + -(√3 / 2 * (√3 / 2 * (1 - v) - √3 / 2 * (1 - u))) =
      1 - u + v / 2 by linear_combination (-(u - v) / 4) * h3,
    show √3 / 2 * (2 - v / 2 - u / 2) + 2⁻¹ * (√3 / 2 * (1 - v) - √3 / 2 * (1 - u)) =
      √3 / 2 * (2 - v) by ring,
    show 2⁻¹ * (u / 2 - (2 - v / 2)) + √3 / 2 * (√3 / 2 * (1 - u) - √3 / 2 * (1 - v)) =
      -(1 - v + u / 2) by linear_combination ((v - u) / 4) * h3, abs_neg]
  have e : ∀ x : ℝ, √3 / 2 * (u / 2 - (2 - v / 2)) + x < 2⁻¹ * (√3 / 2 * (1 - u) - √3 / 2 * (1 - v))
      ↔ x < √3 / 2 * (2 - u) := fun x => by constructor <;> intro h <;> linarith
  rw [e]

/-- **MLS Exercise 8(a)**, printed p. 261, top edge and left leg: point contacts with friction
(`µ = 1`) at `(s, √3/2)` and `(u/2, √3/2 (1 − u))`, `s, u ≥ 0`, form a force-closure grasp exactly
when `|s − u/2| < (√3/2) u` and `|s − 2u| < √3 s`. -/
theorem trapezoid_topLeft_isForceClosure_iff (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![rectTopRotation, trapezoidLeftRotation]
        ![![s, √3 / 2], ![u / 2, √3 / 2 * (1 - u)]]).toGrasp.IsForceClosure ↔
      |s - u / 2| < √3 / 2 * u ∧ |s - 2 * u| < √3 * s := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : 0 ≤ √3 := Real.sqrt_nonneg 3
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;>
        simp [contactNormal, rectTopRotation, trapezoidLeftRotation, dotProduct,
          Fin.sum_univ_two] <;> nlinarith),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, rectTopRotation, trapezoidLeftRotation, dotProduct,
    Fin.sum_univ_two]
  have e2 : ∀ x y : ℝ, 2⁻¹ * x < 2⁻¹ * y ↔ x < y := fun x y => by
    constructor <;> intro h <;> linarith
  rw [show √3 / 2 - √3 / 2 * (1 - u) = √3 / 2 * u by ring,
    show 2⁻¹ * (s - u / 2) + -(√3 / 2 * (√3 / 2 * u)) = 2⁻¹ * (s - 2 * u) by
      linear_combination (-u / 4) * h3,
    show √3 / 2 * (s - u / 2) + 2⁻¹ * (√3 / 2 * u) = 2⁻¹ * (√3 * s) by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), e2]

/-- **MLS Exercise 8(a)**, printed p. 261, top edge and right leg: point contacts with friction
(`µ = 1`) at `(s, √3/2)` and `(2 − v/2, √3/2 (1 − v))`, `s ≤ 2`, `v ≥ 0`, form a force-closure grasp
exactly when `|2 − s − v/2| < (√3/2) v` and `|2 − s − 2v| < √3 (2 − s)` (the mirror image of the
left leg). -/
theorem trapezoid_topRight_isForceClosure_iff (s v : ℝ) (hs : s ≤ 2) (hv : 0 ≤ v) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![rectTopRotation, trapezoidRightRotation]
        ![![s, √3 / 2], ![2 - v / 2, √3 / 2 * (1 - v)]]).toGrasp.IsForceClosure ↔
      |2 - s - v / 2| < √3 / 2 * v ∧ |2 - s - 2 * v| < √3 * (2 - s) := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : 0 ≤ √3 := Real.sqrt_nonneg 3
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;>
        simp [contactNormal, rectTopRotation, trapezoidRightRotation, dotProduct,
          Fin.sum_univ_two] <;> nlinarith),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, rectTopRotation, trapezoidRightRotation, dotProduct,
    Fin.sum_univ_two]
  have e2 : ∀ x y : ℝ, 2⁻¹ * x < 2⁻¹ * y ↔ x < y := fun x y => by
    constructor <;> intro h <;> linarith
  rw [show √3 / 2 - √3 / 2 * (1 - v) = √3 / 2 * v by ring, abs_sub_comm s,
    show 2 - v / 2 - s = 2 - s - v / 2 by ring,
    show 2⁻¹ * (s - (2 - v / 2)) + √3 / 2 * (√3 / 2 * v) =
      -(2⁻¹ * (2 - s - 2 * v)) by linear_combination (v / 4) * h3,
    abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  have e : ∀ x : ℝ, √3 / 2 * (s - (2 - v / 2)) + 2⁻¹ * x < 2⁻¹ * (√3 / 2 * v) ↔
      x < √3 * (2 - s) := fun x => by constructor <;> intro h <;> linarith
  rw [e]

/-- **MLS Exercise 8(a)**, printed p. 261, bottom edge and left leg: point contacts with friction
(`µ = 1`) at `(t, 0)`, `t ≥ 1/2`, and `(u/2, √3/2 (1 − u))`, `u ≤ 1`, never form a force-closure
grasp. -/
theorem trapezoid_bottomLeft_not_isForceClosure {t u : ℝ} (ht : 1 / 2 ≤ t) (hu : u ≤ 1) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![1, trapezoidLeftRotation] ![![t, 0], ![u / 2, √3 / 2 * (1 - u)]]).toGrasp.IsForceClosure := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : 0 ≤ √3 := Real.sqrt_nonneg 3
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;>
        simp [contactNormal, trapezoidLeftRotation, dotProduct,
          Fin.sum_univ_two] <;> nlinarith),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, trapezoidLeftRotation, dotProduct,
    Fin.sum_univ_two]
  intro hA
  have hA' := (abs_lt.mp hA).1
  have hc1 : 1 < √3 := by nlinarith
  have hl : 0 ≤ (√3 - 1) / 2 := by linarith
  nlinarith [le_abs_self (2⁻¹ * (t - u / 2) + √3 / 2 * (√3 / 2 * (1 - u))),
    mul_nonneg hl (by linarith : (0 : ℝ) ≤ √3 / 2 * (1 - u) - (t - u / 2)),
    congrArg (· * (1 - u)) h3]

/-- **MLS Exercise 8(a)**, printed p. 261, bottom edge and right leg: point contacts with friction
(`µ = 1`) at `(t, 0)`, `t ≤ 3/2`, and `(2 − v/2, √3/2 (1 − v))`, `v ≤ 1`, never form a
force-closure grasp. -/
theorem trapezoid_bottomRight_not_isForceClosure {t v : ℝ} (ht : t ≤ 3 / 2) (hv : v ≤ 1) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![1, trapezoidRightRotation]
        ![![t, 0], ![2 - v / 2, √3 / 2 * (1 - v)]]).toGrasp.IsForceClosure := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : 0 ≤ √3 := Real.sqrt_nonneg 3
  rw [isForceClosure_iff_antipodalConditions one_pos _ _ (by
      refine ⟨?_, ?_⟩ <;>
        simp [contactNormal, trapezoidRightRotation, dotProduct,
          Fin.sum_univ_two] <;> nlinarith),
    AntipodalConditions, insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct]
  simp [contactNormal, contactTangent, trapezoidRightRotation, dotProduct,
    Fin.sum_univ_two]
  intro hA
  have hA' := (abs_lt.mp hA).2
  have hc1 : 1 < √3 := by nlinarith
  have hl : 0 ≤ (√3 - 1) / 2 := by linarith
  nlinarith [neg_abs_le (2⁻¹ * (t - (2 - v / 2)) + -(√3 / 2 * (√3 / 2 * (1 - v)))),
    mul_nonneg hl (by linarith : (0 : ℝ) ≤ √3 / 2 * (1 - v) - (2 - v / 2 - t)),
    congrArg (· * (1 - v)) h3]

/-- **MLS Exercise 8(a)**, printed p. 261, one edge: two point contacts with friction (`µ = 1`) on
the top edge never form a force-closure grasp. -/
theorem trapezoid_topTop_not_isForceClosure (s s' : ℝ) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![rectTopRotation, rectTopRotation] ![![s, √3 / 2], ![s', √3 / 2]]).toGrasp.IsForceClosure := by
  apply not_isForceClosure_of_contactNormal_dotProduct_eq_zero
  simp [contactNormal, rectTopRotation, dotProduct, Fin.sum_univ_two]

/-- **MLS Exercise 8(a)**, printed p. 261, one edge: two point contacts with friction (`µ = 1`) on
the left leg never form a force-closure grasp. -/
theorem trapezoid_leftLeft_not_isForceClosure (u u' : ℝ) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
        ![trapezoidLeftRotation, trapezoidLeftRotation]
        ![![u / 2, √3 / 2 * (1 - u)], ![u' / 2, √3 / 2 * (1 - u')]]).toGrasp.IsForceClosure := by
  apply not_isForceClosure_of_contactNormal_dotProduct_eq_zero
  simp [contactNormal, trapezoidLeftRotation, dotProduct, Fin.sum_univ_two]
  ring

end RoboLean.Examples
