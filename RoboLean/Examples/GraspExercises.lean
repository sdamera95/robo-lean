import RoboLean.Grasp.SoftFingerAntipodal
import RoboLean.Examples.GraspPlanning

/-!
# Chapter 5 exercises with stated results: Exercises 1, 2(b), 3(b) and 9

MLS Chapter 5, §9, printed pp. 259 and 261, with the figures of p. 259 read as rendered images.

* **Exercise 1** (p. 259): the three figured grasps (two triangles and a framed rectangle) each
  have three frictionless point contacts in the plane. None is force-closure, whatever the contact
  locations and normals: a planar frictionless force-closure grasp needs at least four contacts
  (p. 231).
* **Exercise 2(b)** (p. 259): two point contacts with friction, `μ = tan 45° = 1`, on two edges of
  an equilateral triangle; the figure draws them near the edge midpoints, read here as the
  midpoints in the parametrization of Figure 5.13 (p. 233). The grasp is force-closure.
* **Exercise 3(b)** (p. 259): two soft-finger contacts at antipodal points of a sphere of radius
  `r > 0`, any `μ > 0`, `γ > 0`: force-closure by Theorem 5.7 ("if", p. 233); the normals and the
  line are coplanar, so the configuration also meets the hypotheses of the coplanar "only if".
* **Exercise 9** (p. 261): two point contacts with friction on a circle of radius `r > 0` at
  angles `α`, `β` (frames with the inward normal as `y`-axis, p. 222): force-closure exactly when
  `|sin (β - α)| < μ (1 - cos (β - α))`, equivalently `|cos ((β - α)/2)| < μ |sin ((β - α)/2)|`:
  the chord makes the angle `(π - |β - α|)/2` with each inward normal. The sketch of the regions
  and the "independent contact regions" asked for are drawings, not statements.

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp Real

/-- **MLS Exercise 1**, printed p. 259: a planar grasp of three frictionless point contacts
(Example 5.1, p. 220; grasp matrix `G ∈ ℝ^{3×3}` over the orthant) is never force-closure, so none
of the three figured grasps is, whatever its contact locations (bound `k ≥ 4` of p. 231). -/
theorem exercise1_not_forceClosure (G : Matrix (Fin 3) (Fin 3) ℝ) :
    ¬ ForceClosure G.mulVecLin (orthantCone (Fin 3)) := by
  intro h
  have := four_le_of_forceClosure_planar h
  omega

/-- **MLS Exercise 2(b)**, printed p. 259: two point contacts with friction, `μ = tan 45° = 1`,
at the midpoints of two edges of the equilateral triangle of side `1` (the parametrization of
Figure 5.13, p. 233, with `s = t = 1/2`) form a force-closure grasp. -/
theorem exercise2b_isForceClosure :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos) triangleFrames
      (trianglePoints (1 / 2) (1 / 2))).toGrasp.IsForceClosure := by
  have hlo : 1 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hhi : √3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [triangle_isForceClosure_iff (by norm_num) (by norm_num)]
  constructor <;> nlinarith

/-- The two contact frames of MLS Exercise 3(b), printed p. 259, on a sphere of radius `r` centered
at the object origin: the identity at the south pole `(0, 0, -r)` (inward normal `e_z`) and the
rotation by `π` about `x` at the north pole `(0, 0, r)` (inward normal `-e_z`); contact `z`-axes
along the inward normals (pp. 214–215). -/
def sphereSoftFrame (r : ℝ) : Fin 2 → RigidTransform :=
  ![⟨1, WithLp.toLp 2 ![0, 0, -r]⟩, ⟨Rotation.xRotation π, WithLp.toLp 2 ![0, 0, r]⟩]

/-- **MLS Exercise 3(b)**, printed p. 259: two soft-finger contacts (eq. (5.4), p. 217) at
antipodal points of a sphere of radius `r > 0` form a force-closure grasp for every `μ > 0` and
`γ > 0` (Theorem 5.7, "if", p. 233). -/
theorem sphereSoftGrasp_isForceClosure {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) {r : ℝ}
    (hr : 0 < r) :
    (ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
      (sphereSoftFrame r)).toGrasp.IsForceClosure := by
  have e0 : ∀ k, contactDirection (sphereSoftFrame r) 0 1 k = ![0, 0, 2 * r] k := by
    intro k
    fin_cases k <;> simp [contactDirection, sphereSoftFrame, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
    ring
  have e1 : ∀ k, contactDirection (sphereSoftFrame r) 1 0 k = ![0, 0, 2 * r] k := by
    intro k
    fin_cases k <;> simp [contactDirection, sphereSoftFrame, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Rotation.xMatrix]
    ring
  apply spatial_softFinger_isForceClosure_of_lineInsideCones
  · rw [e0, e0, e0]; simp; positivity
  · rw [e1, e1, e1]; simp; positivity

/-- The antipodal sphere grasp of MLS Exercise 3(b), printed p. 259, meets the hypotheses of the
coplanar form of Theorem 5.7 (p. 233): `e_x` is orthogonal to both normals and to the line, and
the first normal faces the second contact (for `r ≥ 0`). -/
theorem sphereSoftFrame_coplanar {r : ℝ} (hr : 0 ≤ r) :
    ![1, 0, 0] ⬝ᵥ spatialContactNormal (sphereSoftFrame r) 0 = 0 ∧
      ![1, 0, 0] ⬝ᵥ spatialContactNormal (sphereSoftFrame r) 1 = 0 ∧
      ![1, 0, 0] ⬝ᵥ contactLine (sphereSoftFrame r) = 0 ∧
      0 ≤ contactDirection (sphereSoftFrame r) 0 1 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [spatialContactNormal, sphereSoftFrame, dotProduct, Fin.sum_univ_three]
  · simp [spatialContactNormal, sphereSoftFrame, dotProduct, Fin.sum_univ_three, Rotation.xMatrix]
  · simp [contactLine, sphereSoftFrame, dotProduct, Fin.sum_univ_three]
  · simp [contactDirection, sphereSoftFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linarith

/-- The contact frame at angle `α` on a circle centered at the object origin, MLS Exercise 9,
printed p. 261, in the planar convention of p. 222: the rotation by `α + π/2`, with `x`-axis the
tangent `(-sin α, cos α)` and `y`-axis the inward normal `(-cos α, -sin α)`. -/
def circleRotation (α : ℝ) : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![-sin α, -cos α; cos α, -sin α], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, by ring, ?_⟩
    nlinarith [sin_sq_add_cos_sq α]⟩

/-- The two contact frames of MLS Exercise 9, printed p. 261, at angles `α` and `β`. -/
def circleFrames (α β : ℝ) : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ![circleRotation α, circleRotation β]

/-- The two contact points of MLS Exercise 9, printed p. 261, on the circle of radius `r`:
`r (cos α, sin α)` and `r (cos β, sin β)`. -/
def circlePoints (r α β : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![r * cos α, r * sin α], ![r * cos β, r * sin β]]

/-- **MLS Exercise 9**, printed p. 261: two point contacts with friction (`μ > 0`, cone of p. 222)
at angles `α`, `β` on a circle of radius `r > 0` form a force-closure grasp exactly when
`|sin (β - α)| < μ (1 - cos (β - α))` (Theorem 5.6, p. 232: the inward normals of a circle face
each other). -/
theorem circle_isForceClosure_iff {μ : ℝ} (hμ : 0 < μ) {r : ℝ} (hr : 0 < r) (α β : ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) (circleFrames α β)
        (circlePoints r α β)).toGrasp.IsForceClosure ↔
      |sin (β - α)| < μ * (1 - cos (β - α)) := by
  have e0 : contactTangent (circleFrames α β 0) ⬝ᵥ (circlePoints r α β 1 - circlePoints r α β 0) =
      r * sin (β - α) := by
    simp [contactTangent, circleFrames, circleRotation, circlePoints, dotProduct, Fin.sum_univ_two,
      sin_sub]
    ring
  have e1 : contactNormal (circleFrames α β 0) ⬝ᵥ (circlePoints r α β 1 - circlePoints r α β 0) =
      r * (1 - cos (β - α)) := by
    simp [contactNormal, circleFrames, circleRotation, circlePoints, dotProduct, Fin.sum_univ_two,
      cos_sub]
    nlinarith [sin_sq_add_cos_sq α]
  have e2 : contactTangent (circleFrames α β 1) ⬝ᵥ (circlePoints r α β 0 - circlePoints r α β 1) =
      -(r * sin (β - α)) := by
    simp [contactTangent, circleFrames, circleRotation, circlePoints, dotProduct, Fin.sum_univ_two,
      sin_sub]
    ring
  have e3 : contactNormal (circleFrames α β 1) ⬝ᵥ (circlePoints r α β 0 - circlePoints r α β 1) =
      r * (1 - cos (β - α)) := by
    simp [contactNormal, circleFrames, circleRotation, circlePoints, dotProduct, Fin.sum_univ_two,
      cos_sub]
    nlinarith [sin_sq_add_cos_sq β]
  have hc : 0 ≤ 1 - cos (β - α) := by linarith [cos_le_one (β - α)]
  have hface : NormalsFaceEachOther (circleFrames α β) (circlePoints r α β) := by
    refine ⟨?_, ?_⟩
    · rw [e1]; positivity
    · rw [e3]; positivity
  rw [isForceClosure_iff_antipodalConditions hμ _ _ hface, AntipodalConditions,
    insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct, e0, e1, e2, e3, abs_neg,
    abs_mul, abs_of_pos hr, and_self]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **MLS Exercise 9**, printed p. 261, in half-angle form: the circle grasp is force-closure
exactly when `|cos ((β - α)/2)| < μ |sin ((β - α)/2)|`, that is, when the chord between the
contacts makes an angle smaller than `arctan μ` with both inward normals. -/
theorem circle_isForceClosure_iff_half {μ : ℝ} (hμ : 0 < μ) {r : ℝ} (hr : 0 < r) (α β : ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) (circleFrames α β)
        (circlePoints r α β)).toGrasp.IsForceClosure ↔
      |cos ((β - α) / 2)| < μ * |sin ((β - α) / 2)| := by
  rw [circle_isForceClosure_iff hμ hr]
  set x := (β - α) / 2 with hxdef
  have hx : β - α = 2 * x := by rw [hxdef]; ring
  rw [hx, sin_two_mul, cos_two_mul, abs_mul, abs_mul, abs_two]
  have h1 : μ * (1 - (2 * cos x ^ 2 - 1)) = 2 * μ * |sin x| ^ 2 := by
    rw [sq_abs]
    linear_combination (-2 * μ) * sin_sq_add_cos_sq x
  rw [h1]
  have ha := abs_nonneg (sin x)
  have hb := abs_nonneg (cos x)
  constructor
  · intro h
    rcases ha.lt_or_eq with ha' | ha'
    · by_contra hc
      nlinarith
    · rw [← ha'] at h
      simp at h
  · intro h
    have ha' : 0 < |sin x| := by
      by_contra hc
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left h (by positivity : (0 : ℝ) < 2 * |sin x|)]

end RoboLean.Examples
