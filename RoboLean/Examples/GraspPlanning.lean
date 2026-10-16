import RoboLean.Grasp.AntipodalGrasp
import RoboLean.Grasp.PositiveSpanBounds
import RoboLean.Examples.PlanarGrasp

/-!
# MLS Chapter 5, §4: examples, the dimension-zero failures and counterexamples

Printed pp. 230–233 and Exercises 7–8, p. 261.

* Theorems 5.4 and 5.5 (p. 230) fail for `p = 0`; three vectors positively spanning `ℝ²` attain
  the bound `p + 1` of Theorem 5.4.
* Theorem 5.6 (p. 232): the rectangle of Example 5.3 (p. 222) satisfies A–D when its contacts face
  each other (`r > 0`); with the contacts exchanged (`r = -1`) the grasp is force-closure
  (`rectangleGrasp_isForceClosure`) while A–D fail, so the printed "if and only if" is false
  without an orientation hypothesis (`antipodal_printed_iff_counterexample`). A grasp whose
  connecting line lies on an edge of one friction cone satisfies the closed (non-strict) A–D and
  the orientation hypothesis and is not force-closure (`antipodal_closed_reading_counterexample`),
  so "inside" means the open cone (Q6).
* Figure 5.13 and Exercise 8(b) (pp. 233, 261): the equilateral triangle with side `1`. The book
  defines no axes for the figure; here `E1` is the bottom edge, contact at `(s, 0)` with inward
  normal `(0, 1)`, and `E2` the left edge, contact at `(t/2, t√3/2)` with inward normal
  `(√3/2, -1/2)`, both parameters measured from the shared vertex `(0, 0)`. For `μ = tan 45° = 1`
  the force-closure grasps are exactly the open wedge `(√3 - 1) s < t < ((1 + √3)/2) s`
  (`triangle_isForceClosure_iff`), which contains the square `[3/4, 1]²`; for
  `μ ≤ tan 30°` no grasp on these two edges is force-closure.
* p. 231 ("polyhedral objects ... can be grasped with at most seven contacts"): seven
  frictionless point contacts on the cube `[-1, 1]³` give a force-closure grasp
  (`cubeGrasp_isForceClosure`), so the lower bound `7` of Theorem 5.4 is attained.
* Theorem 5.7 (p. 233): an exact two-soft-finger grasp that is force-closure although the line
  connecting the contacts lies outside the (closed) friction cone at the first contact
  (`softAntipodal_onlyIf_counterexample`): the printed "only if" fails in the library's soft-finger
  model.

These are convention checks and counterexamples on concrete inputs. Finite-force caveat:
force-closure assumes unbounded contact forces at maintained rigid contacts (MLS p. 214).
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp

/-! ### Theorems 5.4 and 5.5 -/

/-- **MLS Theorem 5.4 fails for `p = 0`** (printed p. 230): the empty family positively spans
`ℝ⁰ = (Fin 0 → ℝ)` (p. 225) and has `0 < 0 + 1` members; `PositivelySpans.succ_le` needs its added
hypothesis `p ≥ 1`. -/
theorem positivelySpans_fin_zero_card :
    PositivelySpans (Fin.elim0 : Fin 0 → Fin 0 → ℝ) ∧ ¬ (0 + 1 ≤ 0) := by
  refine ⟨fun x => ⟨fun _ => 1, fun i => Fin.elim0 i, ?_⟩, by norm_num⟩
  funext i
  exact Fin.elim0 i

/-- **MLS Theorem 5.5 fails for `p = 0`** (printed p. 230): in `ℝ⁰ = (Fin 0 → ℝ)`, `q = 0` lies in
`int(co {0})`, but no `X` with `|X| ≤ 2p = 0` has `q ∈ int(co X)`; the Steinitz bound needs the
added hypothesis `p ≥ 1`. -/
theorem steinitz_fin_zero :
    (0 : Fin 0 → ℝ) ∈ interior (convexHull ℝ ({0} : Set (Fin 0 → ℝ))) ∧
      ∀ X : Finset (Fin 0 → ℝ), X.card ≤ 2 * 0 →
        (0 : Fin 0 → ℝ) ∉ interior (convexHull ℝ (X : Set (Fin 0 → ℝ))) := by
  refine ⟨?_, ?_⟩
  · have h : ({0} : Set (Fin 0 → ℝ)) = Set.univ :=
      Set.eq_univ_of_forall fun x => Subsingleton.elim x 0
    rw [h, convexHull_univ, interior_univ]
    trivial
  · intro X hX
    have h : X = ∅ := Finset.card_eq_zero.mp (by omega)
    subst h
    simp

/-- Three vectors `(1, 0)`, `(0, 1)`, `(-1, -1)` positively span `ℝ²` (MLS printed p. 225 and
Figure 5.11, p. 230): the bound `k ≥ p + 1 = 3` of Theorem 5.4 is attained. -/
theorem positivelySpans_three :
    PositivelySpans (![![1, 0], ![0, 1], ![-1, -1]] : Fin 3 → Fin 2 → ℝ) := by
  rw [positivelySpans_iff_nonneg]
  intro x
  refine ⟨![x 0 + (|x 0| + |x 1|), x 1 + (|x 0| + |x 1|), |x 0| + |x 1|], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;>
      linarith [neg_abs_le (x 0), neg_abs_le (x 1), abs_nonneg (x 0), abs_nonneg (x 1)]
  · funext j
    fin_cases j <;> simp [Fin.sum_univ_succ] <;> ring

/-! ### Theorem 5.6 on the rectangle of Example 5.3 -/

/-- The frames of the rectangle of MLS Example 5.3 (printed p. 222) with contacts at
`(-r, 0)`, `(r, 0)` satisfy the printed A–D of p. 232 when `r > 0` (contacts facing each other),
for every `μ > 0`. -/
theorem rectangle_antipodalConditions {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) :
    AntipodalConditions μ ![rectangleRotation₁, rectangleRotation₂] ![![-r, 0], ![r, 0]] := by
  refine ⟨?_, ?_⟩ <;> rw [insideFrictionCone_iff] <;>
    simp [rectangleRotation₁, rectangleRotation₂, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> nlinarith

/-- The inward normals of the rectangle of MLS Example 5.3 (printed p. 222) face each other when
`r ≥ 0` (the orientation hypothesis of `isForceClosure_iff_antipodalConditions`, p. 232). -/
theorem rectangle_normalsFaceEachOther {r : ℝ} (hr : 0 ≤ r) :
    NormalsFaceEachOther ![rectangleRotation₁, rectangleRotation₂] ![![-r, 0], ![r, 0]] := by
  refine ⟨?_, ?_⟩ <;>
    simp [contactNormal, rectangleRotation₁, rectangleRotation₂, dotProduct,
      Fin.sum_univ_two] <;> linarith

/-- With the contacts of MLS Example 5.3 (printed p. 222) exchanged (`r < 0`: inward normals
pointing away from the other contact), the printed A–D of p. 232 fail, for every `μ > 0`. -/
theorem rectangle_not_antipodalConditions {μ r : ℝ} (hμ : 0 < μ) (hr : r < 0) :
    ¬ AntipodalConditions μ ![rectangleRotation₁, rectangleRotation₂] ![![-r, 0], ![r, 0]] := by
  rintro ⟨h0, -⟩
  rw [insideFrictionCone_iff] at h0
  simp [rectangleRotation₁, rectangleRotation₂, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h0
  nlinarith

/-- With the contacts of MLS Example 5.3 (printed p. 222) exchanged (`r < 0`), A–D hold with the
connecting line reversed (the second alternative of
`isForceClosure_iff_antipodalConditions_or_flipped`, p. 232). -/
theorem rectangle_flipped {μ r : ℝ} (hμ : 0 < μ) (hr : r < 0) :
    InsideFrictionCone μ rectangleRotation₁ (![-r, 0] - ![r, 0]) ∧
      InsideFrictionCone μ rectangleRotation₂ (![r, 0] - ![-r, 0]) := by
  refine ⟨?_, ?_⟩ <;> rw [insideFrictionCone_iff] <;>
    simp [rectangleRotation₁, rectangleRotation₂, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> nlinarith

/-- **The printed Theorem 5.6 is false without an orientation hypothesis** (MLS printed p. 232,
in the library's planar grasp): it is not true that for every `μ > 0` and all frames a planar grasp
of two point contacts with friction is force-closure if and only if A–D hold. Witness: the
rectangle of Example 5.3 at `r = -1`, `μ = 1`, force-closure by `rectangleGrasp_isForceClosure`
(Proposition 5.2), with A–D false (`rectangle_not_antipodalConditions`). -/
theorem antipodal_printed_iff_counterexample :
    ¬ ∀ (μ : ℝ) (hμ : 0 < μ) (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ)
      (p : Fin 2 → Fin 2 → ℝ),
      (Grasp.IsForceClosure
        (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp ↔
        AntipodalConditions μ R p) := by
  intro h
  have hfc : (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos)
      ![rectangleRotation₁, rectangleRotation₂] ![![-(-1), 0], ![-1, 0]]).toGrasp.IsForceClosure :=
    rectangleGrasp_isForceClosure 1 (-1) one_pos (by norm_num)
  exact rectangle_not_antipodalConditions one_pos (by norm_num : (-1 : ℝ) < 0)
    ((h 1 one_pos _ _).mp hfc)

/-! ### Theorem 5.6 on the boundary of a friction cone (Q6) -/

/-- The planar rotation `[[-4/5, -3/5], [3/5, -4/5]] ∈ SO(2)`: contact `x`-axis `(-4/5, 3/5)`,
inward normal `(-3/5, -4/5)` (frame convention of MLS printed p. 222). -/
def boundaryRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![-4 / 5, -3 / 5; 3 / 5, -4 / 5], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    norm_num⟩

/-- Two planar contact frames for the boundary case of MLS Theorem 5.6 (printed p. 232): the
identity (inward normal `(0, 1)`) and `boundaryRotation` (inward normal `(-3/5, -4/5)`). -/
def boundaryFrames : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ := ![1, boundaryRotation]

/-- The contact points `(0, 0)` and `(1, 1)` of the boundary case of MLS Theorem 5.6 (printed
p. 232): with `μ = 1` the connecting line lies on an edge of the first friction cone. -/
def boundaryPoints : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![1, 1]]

/-- The four printed expressions of A–D (MLS printed p. 232) for the boundary case, `μ = 1`:
`A = 0`, `B = -2`, `C = 6/5`, `D = -8/5`. -/
theorem boundary_cross2_values :
    cross2 (contactNormal (boundaryFrames 0) - (1 : ℝ) • perp2 (contactNormal (boundaryFrames 0)))
        (boundaryPoints 1 - boundaryPoints 0) = 0 ∧
      cross2 (contactNormal (boundaryFrames 0) + (1 : ℝ) • perp2 (contactNormal (boundaryFrames 0)))
        (boundaryPoints 1 - boundaryPoints 0) = -2 ∧
      cross2 (contactNormal (boundaryFrames 1) - (1 : ℝ) • perp2 (contactNormal (boundaryFrames 1)))
        (boundaryPoints 0 - boundaryPoints 1) = 6 / 5 ∧
      cross2 (contactNormal (boundaryFrames 1) + (1 : ℝ) • perp2 (contactNormal (boundaryFrames 1)))
        (boundaryPoints 0 - boundaryPoints 1) = -8 / 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [cross2, perp2, contactNormal, boundaryFrames, boundaryRotation, boundaryPoints] <;>
    norm_num

/-- The inward normals of the boundary case face each other (MLS printed p. 232, the orientation
hypothesis of `isForceClosure_iff_antipodalConditions`): `n₁ · (p₂ - p₁) = 1`,
`n₂ · (p₁ - p₂) = 7/5`. -/
theorem boundary_normalsFaceEachOther : NormalsFaceEachOther boundaryFrames boundaryPoints := by
  refine ⟨?_, ?_⟩
  · simp [contactNormal, boundaryFrames, boundaryPoints, dotProduct, Fin.sum_univ_two]
  · simp [contactNormal, boundaryFrames, boundaryRotation, boundaryPoints, dotProduct,
      Fin.sum_univ_two]
    norm_num

/-- The boundary case of MLS Theorem 5.6 (printed p. 232) is not force-closure: condition A holds
with equality (`not_isForceClosure_of_cross2_eq_zero`). -/
theorem boundaryGrasp_not_isForceClosure :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos) boundaryFrames
      boundaryPoints).toGrasp.IsForceClosure :=
  not_isForceClosure_of_cross2_eq_zero one_pos _ _ (Or.inl boundary_cross2_values.1)

/-- **"Inside" cannot be read as the closed cone (Q6)**, MLS Theorem 5.6, printed p. 232: it is
not true that the non-strict versions of A–D, together with the orientation hypothesis, imply
force-closure. Witness: the boundary case, `μ = 1`. -/
theorem antipodal_closed_reading_counterexample :
    ¬ ∀ (μ : ℝ) (hμ : 0 < μ) (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ)
      (p : Fin 2 → Fin 2 → ℝ), NormalsFaceEachOther R p →
      0 ≤ cross2 (contactNormal (R 0) - μ • perp2 (contactNormal (R 0))) (p 1 - p 0) →
      cross2 (contactNormal (R 0) + μ • perp2 (contactNormal (R 0))) (p 1 - p 0) ≤ 0 →
      0 ≤ cross2 (contactNormal (R 1) - μ • perp2 (contactNormal (R 1))) (p 0 - p 1) →
      cross2 (contactNormal (R 1) + μ • perp2 (contactNormal (R 1))) (p 0 - p 1) ≤ 0 →
      Grasp.IsForceClosure
        (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp := by
  intro h
  obtain ⟨hA, hB, hC, hD⟩ := boundary_cross2_values
  exact boundaryGrasp_not_isForceClosure
    (h 1 one_pos boundaryFrames boundaryPoints boundary_normalsFaceEachOther hA.ge
      (by rw [hB]; norm_num) (by rw [hC]; norm_num) (by rw [hD]; norm_num))

/-! ### Figure 5.13 and Exercise 8(b): the equilateral triangle -/

/-- The frame of a contact on the left edge `E2` of the equilateral triangle with vertices
`(0, 0)`, `(1, 0)`, `(1/2, √3/2)` (MLS Figure 5.13, printed p. 233; Exercise 8(b), p. 261):
`R = [[-1/2, √3/2], [-√3/2, -1/2]]`, contact `x`-axis `(-1/2, -√3/2)`, inward normal
`(√3/2, -1/2)` (frame convention of p. 222). -/
def triangleRotation : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![-1 / 2, √3 / 2; -√3 / 2, -1 / 2], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, by ring, ?_⟩
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num⟩

/-- The two contact frames on the edges of the equilateral triangle (MLS Figure 5.13, printed
p. 233): the identity on the bottom edge `E1` (inward normal `(0, 1)`) and `triangleRotation` on
the left edge `E2`. -/
def triangleFrames : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ := ![1, triangleRotation]

/-- The contact points of MLS Figure 5.13 (printed p. 233) in the parametrization chosen here (the
book defines none): `(s, 0)` on the bottom edge `E1` and `(t/2, t√3/2)` on the left edge `E2`,
`s, t ∈ (0, 1]` the distances from the shared vertex `(0, 0)`. -/
def trianglePoints (s t : ℝ) : Fin 2 → Fin 2 → ℝ := ![![s, 0], ![t / 2, t * √3 / 2]]

/-- The triangle grasps of MLS Figure 5.13 (printed p. 233) for any `μ > 0` and `s, t > 0`:
force-closure exactly when `|t/2 - s| < μ (√3/2) t` and `|t - s/2| < μ (√3/2) s`, the printed
A–D of p. 232 in these coordinates (the inward normals face each other). -/
theorem triangle_isForceClosure_iff_abs {μ : ℝ} (hμ : 0 < μ) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) triangleFrames
        (trianglePoints s t)).toGrasp.IsForceClosure ↔
      |t / 2 - s| < μ * (√3 / 2 * t) ∧ |t - s / 2| < μ * (√3 / 2 * s) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have e0 : contactTangent (triangleFrames 0) ⬝ᵥ (trianglePoints s t 1 - trianglePoints s t 0) =
      t / 2 - s := by
    simp [contactTangent, triangleFrames, trianglePoints, dotProduct, Fin.sum_univ_two]
  have e1 : contactNormal (triangleFrames 0) ⬝ᵥ (trianglePoints s t 1 - trianglePoints s t 0) =
      √3 / 2 * t := by
    simp [contactNormal, triangleFrames, trianglePoints, dotProduct, Fin.sum_univ_two]
    ring
  have e2 : contactTangent (triangleFrames 1) ⬝ᵥ (trianglePoints s t 0 - trianglePoints s t 1) =
      t - s / 2 := by
    simp [contactTangent, triangleFrames, triangleRotation, trianglePoints, dotProduct,
      Fin.sum_univ_two]
    linear_combination (t / 4) * h3
  have e3 : contactNormal (triangleFrames 1) ⬝ᵥ (trianglePoints s t 0 - trianglePoints s t 1) =
      √3 / 2 * s := by
    simp [contactNormal, triangleFrames, triangleRotation, trianglePoints, dotProduct,
      Fin.sum_univ_two]
    ring
  have hface : NormalsFaceEachOther triangleFrames (trianglePoints s t) := by
    refine ⟨?_, ?_⟩
    · rw [e1]
      positivity
    · rw [e3]
      positivity
  rw [isForceClosure_iff_antipodalConditions hμ _ _ hface, AntipodalConditions,
    insideFrictionCone_iff_dotProduct, insideFrictionCone_iff_dotProduct, e0, e1, e2, e3]

/-- **MLS Figure 5.13 and Exercise 8(b)**, printed pp. 233, 261: for the equilateral triangle of
side `1` with `μ = tan 45° = 1` (Mathlib `Real.tan_pi_div_four`), contacts at distance `s > 0`
along `E1` and `t > 0` along `E2` from their shared vertex give a force-closure grasp exactly in
the open wedge `(√3 - 1) s < t < ((1 + √3)/2) s`, whose slopes match the shaded region of the
figure. In this parametrization the two boundary lines are the zero lines of conditions B and C
(the figure labels them C and D), and the zero lines of A and D lie where `s` and `t` have opposite
signs. -/
theorem triangle_isForceClosure_iff {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos) triangleFrames
        (trianglePoints s t)).toGrasp.IsForceClosure ↔
      (√3 - 1) * s < t ∧ t < (1 + √3) / 2 * s := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr1 : 1 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  rw [triangle_isForceClosure_iff_abs one_pos hs ht, abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨h1, -⟩, ⟨-, h4⟩⟩
    refine ⟨?_, by linarith⟩
    have h5 : 2 * s < t * (1 + √3) := by linarith
    nlinarith [mul_lt_mul_of_pos_left h5 (sub_pos.mpr hr1)]
  · rintro ⟨h1, h2⟩
    have h5 : 2 * s < t * (1 + √3) := by
      nlinarith [mul_lt_mul_of_pos_left h1 (by linarith : (0 : ℝ) < 1 + √3)]
    refine ⟨⟨by linarith, ?_⟩, ⟨?_, by linarith⟩⟩
    · nlinarith [mul_lt_mul_of_pos_left hr1 ht]
    · nlinarith [mul_lt_mul_of_pos_left hr1 hs]

/-- **The dark square of MLS Figure 5.13** (printed p. 233), `[3/4, 1]²` as read from the figure:
every grasp with `3/4 ≤ s, t ≤ 1` on the edges `E1`, `E2` of the equilateral triangle with
`μ = 1` (Exercise 8(b), p. 261) is force-closure. -/
theorem triangle_isForceClosure_of_mem_square {s t : ℝ} (hs : 3 / 4 ≤ s) (hs1 : s ≤ 1)
    (ht : 3 / 4 ≤ t) (ht1 : t ≤ 1) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact 1 one_pos) triangleFrames
      (trianglePoints s t)).toGrasp.IsForceClosure := by
  have hlo : 5 / 3 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hhi : √3 < 7 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [triangle_isForceClosure_iff (by linarith) (by linarith)]
  constructor <;> nlinarith

/-- **The threshold `tan 30°` for the equilateral triangle** (MLS printed p. 231, "equilateral
triangle in the plane and choosing `μ < tan 19.5°`", and p. 260, Exercise 5(a), `μ = tan 30°`):
for `0 < μ ≤ tan 30°` (Mathlib `Real.tan_pi_div_six`, `tan(π/6) = 1/√3`) no grasp with contacts at
`s, t > 0` on the edges `E1`, `E2` of the equilateral triangle is force-closure. -/
theorem triangle_not_isForceClosure {μ : ℝ} (hμ : 0 < μ) (hμ30 : μ ≤ Real.tan (Real.pi / 6))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ¬ (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) triangleFrames
      (trianglePoints s t)).toGrasp.IsForceClosure := by
  have hr3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.tan_pi_div_six] at hμ30
  have hμ3 : μ * √3 ≤ 1 := by
    rw [le_div_iff₀ hr3] at hμ30
    linarith
  rw [triangle_isForceClosure_iff_abs hμ hs ht, abs_lt, abs_lt]
  rintro ⟨⟨h1, -⟩, ⟨-, h4⟩⟩
  have h5 : μ * (√3 / 2 * t) ≤ t / 2 := by nlinarith
  have h6 : μ * (√3 / 2 * s) ≤ s / 2 := by nlinarith
  linarith

/-! ### Seven frictionless contacts on a cube (p. 231) -/

/-- A proper rotation given by its matrix, with membership in `SO(3)` checked entrywise
(supporting declaration for the cube example of MLS printed p. 231). -/
private theorem mem_rotation_of_entries (A : Matrix (Fin 3) (Fin 3) ℝ) (h1 : A * Aᵀ = 1)
    (h2 : A.det = 1) : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  exact ⟨h1, h2⟩

/-- Contact orientation with inward normal `-e_x` (third column), for the face `x = 1` of the
cube `[-1, 1]³` (frame convention of MLS printed pp. 214–215). -/
def cubeRotationNegX : Rotation :=
  ⟨!![0, 0, -1; 0, 1, 0; 1, 0, 0], mem_rotation_of_entries _
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])⟩

/-- Contact orientation with inward normal `e_x`, for the face `x = -1` of the cube
(MLS printed pp. 214–215). -/
def cubeRotationPosX : Rotation :=
  ⟨!![0, 0, 1; 0, 1, 0; -1, 0, 0], mem_rotation_of_entries _
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])⟩

/-- Contact orientation with inward normal `-e_y`, for the face `y = 1` of the cube
(MLS printed pp. 214–215). -/
def cubeRotationNegY : Rotation :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], mem_rotation_of_entries _
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])⟩

/-- Contact orientation with inward normal `e_y`, for the face `y = -1` of the cube
(MLS printed pp. 214–215). -/
def cubeRotationPosY : Rotation :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, -1, 0], mem_rotation_of_entries _
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])⟩

/-- Contact orientation with inward normal `-e_z`, for the face `z = 1` of the cube
(MLS printed pp. 214–215). -/
def cubeRotationNegZ : Rotation :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], mem_rotation_of_entries _
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])⟩

/-- Contact orientation with inward normal `e_z`, for the face `z = -1` of the cube
(MLS printed pp. 214–215). -/
def cubeRotationPosZ : Rotation :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], mem_rotation_of_entries _
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.det_fin_three])⟩

/-- Seven frictionless contact frames on the cube `[-1, 1]³` (MLS printed p. 231, "polyhedral
objects ... can be grasped with at most seven contacts"): points `(1, 1/2, 0)`, `(-1, 0, 1/2)`,
`(1/2, 1, 0)`, `(0, -1, 0)`, `(0, 0, 1)`, `(0, 1/2, 1)`, `(1/4, 1/4, -1)` on the faces
`x = 1`, `x = -1`, `y = 1`, `y = -1`, `z = 1` (twice), `z = -1`, with inward normals. Chosen so
that the first six contact wrenches are linearly independent and the seventh is `-1/2` times their
sum. -/
def cubeFrame : Fin 7 → RigidTransform :=
  ![⟨cubeRotationNegX, WithLp.toLp 2 ![1, 1 / 2, 0]⟩,
    ⟨cubeRotationPosX, WithLp.toLp 2 ![-1, 0, 1 / 2]⟩,
    ⟨cubeRotationNegY, WithLp.toLp 2 ![1 / 2, 1, 0]⟩,
    ⟨cubeRotationPosY, WithLp.toLp 2 ![0, -1, 0]⟩,
    ⟨cubeRotationNegZ, WithLp.toLp 2 ![0, 0, 1]⟩,
    ⟨cubeRotationNegZ, WithLp.toLp 2 ![0, 1 / 2, 1]⟩,
    ⟨cubeRotationPosZ, WithLp.toLp 2 ![1 / 4, 1 / 4, -1]⟩]

/-- **The lower bound `7` of MLS printed p. 231 is attained**: the spatial grasp of seven
frictionless point contacts (Example 5.1, p. 220) at `cubeFrame` is force-closure (p. 224, the
columns `(nᵢ; pᵢ × nᵢ)` positively span the wrench space). Finite-force caveat: unbounded contact
forces at maintained rigid contacts (MLS p. 214). -/
theorem cubeGrasp_isForceClosure :
    Grasp.IsForceClosure
      (ContactGrasp.spatial (fun _ => ContactModel.frictionless) cubeFrame).toGrasp := by
  rw [spatial_frictionless_isForceClosure_iff, positivelySpans_iff_nonneg]
  intro z
  set c1 := 2 * z.torque 1 - z.force 0
  set c2 := 2 * z.torque 1
  set c3 := 2 * z.torque 1 - z.force 0 - 2 * z.torque 2
  set c4 := z.force 1 + (2 * z.torque 1 - z.force 0 - 2 * z.torque 2)
  set c5 := -z.force 2 + 2 * z.torque 0
  set c6 := -2 * z.torque 0
  set M := |c1| + |c2| + |c3| + |c4| + |c5| + |c6|
  refine ⟨![c1 + M, c2 + M, c3 + M, c4 + M, c5 + M, c6 + M, 2 * M], ?_, ?_⟩
  · have h1 := neg_abs_le c1
    have h2 := neg_abs_le c2
    have h3 := neg_abs_le c3
    have h4 := neg_abs_le c4
    have h5 := neg_abs_le c5
    have h6 := neg_abs_le c6
    have a1 := abs_nonneg c1
    have a2 := abs_nonneg c2
    have a3 := abs_nonneg c3
    have a4 := abs_nonneg c4
    have a5 := abs_nonneg c5
    have a6 := abs_nonneg c6
    intro i
    fin_cases i <;> simp <;> linarith
  · apply Wrench.ext
    · ext j
      fin_cases j <;>
        simp [Fin.sum_univ_succ, Rotation.act_apply, Rotation.zAxis, cubeFrame,
          cubeRotationNegX, cubeRotationPosX, cubeRotationNegY, cubeRotationPosY,
          cubeRotationNegZ, cubeRotationPosZ, Matrix.mulVec, dotProduct, c1, c2, c3, c4, c5,
          c6] <;> ring
    · ext j
      fin_cases j <;>
        simp [Fin.sum_univ_succ, Rotation.act_apply, Rotation.zAxis, Vec3.cross_coordinates,
          crossProduct, cubeFrame, cubeRotationNegX, cubeRotationPosX, cubeRotationNegY,
          cubeRotationPosY, cubeRotationNegZ, cubeRotationPosZ, Matrix.mulVec, dotProduct, c1,
          c2, c3, c4, c5, c6] <;> ring

/-! ### Theorem 5.7: an exact two-soft-finger grasp -/

/-- The identity rotation, frame of the first soft-finger contact of the Theorem 5.7 instance
(MLS printed p. 233): inward normal `e_z` (contact `z`-axis, p. 214–215). -/
def softRotation₁ : Rotation :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- The rotation `[[-12/13, 0, -5/13], [0, 1, 0], [5/13, 0, -12/13]]` about the `y`-axis, frame of
the second soft-finger contact of the Theorem 5.7 instance (MLS printed p. 233): inward normal
(third column) `(-5/13, 0, -12/13)`. -/
def softRotation₂ : Rotation :=
  ⟨!![-12 / 13, 0, -5 / 13; 0, 1, 0; 5 / 13, 0, -12 / 13], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
    · simp [Matrix.det_fin_three]
      norm_num⟩

/-- The contact frames of the Theorem 5.7 instance (MLS printed p. 233): contact 1 at the origin
with normal `e_z`, contact 2 at `(0, 1, 1)` with normal `(-5/13, 0, -12/13)`. -/
def softFrame : Fin 2 → RigidTransform :=
  ![⟨softRotation₁, WithLp.toLp 2 ![0, 0, 0]⟩, ⟨softRotation₂, WithLp.toLp 2 ![0, 1, 1]⟩]

/-- The two-soft-finger grasp of the Theorem 5.7 instance (MLS printed p. 233): soft-finger
contacts (eq. (5.4), p. 217) with `μ = 1/2` and torsional coefficient `γ = 3` at `softFrame`. -/
def softGrasp : ContactGrasp Wrench (Fin 2) fun _ => 4 :=
  ContactGrasp.spatial (fun _ => ContactModel.softFinger (1 / 2) 3 (by norm_num) (by norm_num))
    softFrame

/-- The grasp map of the Theorem 5.7 instance (MLS printed p. 233) in force and moment form,
computed with the wrench transfer (2.66) (`f i j` is coefficient `j` of contact `i`, from `0`). -/
theorem softGrasp_graspMap (f : Fin 2 → Fin 4 → ℝ) :
    softGrasp.graspMap f =
      ⟨WithLp.toLp 2 ![f 0 0 - 12 / 13 * f 1 0 - 5 / 13 * f 1 2, f 0 1 + f 1 1,
          f 0 2 + 5 / 13 * f 1 0 - 12 / 13 * f 1 2],
        WithLp.toLp 2 ![5 / 13 * f 1 0 - 12 / 13 * f 1 2 - f 1 1 - 5 / 13 * f 1 3,
          -12 / 13 * f 1 0 - 5 / 13 * f 1 2,
          f 0 3 + 12 / 13 * f 1 0 + 5 / 13 * f 1 2 - 12 / 13 * f 1 3]⟩ := by
  rw [ContactGrasp.graspMap_apply, Fin.sum_univ_two, softGrasp,
    ContactGrasp.spatial_contactMap_apply, ContactGrasp.spatial_contactMap_apply,
    ContactModel.softFinger_wrench, ContactModel.softFinger_wrench]
  apply Wrench.ext
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, softFrame, softRotation₁, softRotation₂,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, Vec3.cross_coordinates, crossProduct,
        softFrame, softRotation₁, softRotation₂, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;> ring

/-- The strictly internal force of the Theorem 5.7 instance (MLS Definition 5.3, printed p. 223):
normal force `1` with torsion `-12/5` at contact 1, the force `(0, 0, -1)` (coefficients
`(-5/13, 0, 12/13)`) with torsion `-13/5` at contact 2. -/
def softInternalForce : Fin 2 → Fin 4 → ℝ :=
  ![![0, 0, 1, -12 / 5], ![-5 / 13, 0, 12 / 13, -13 / 5]]

/-- `softInternalForce` is a strictly internal force of the Theorem 5.7 instance (MLS
Definition 5.3, printed p. 223): zero net wrench, and each contact force strictly inside the
soft-finger cone (5.4) with `μ = 1/2`, `γ = 3`. -/
theorem softGrasp_isStrictlyInternalForce :
    IsStrictlyInternalForce softGrasp.graspMap (softGrasp.cone : Set (Fin 2 → Fin 4 → ℝ))
      softInternalForce := by
  refine ⟨?_, ?_⟩
  · rw [softGrasp_graspMap]
    apply Wrench.ext
    · ext i
      fin_cases i <;> simp [softInternalForce] <;> norm_num
    · ext i
      fin_cases i <;> simp [softInternalForce] <;> norm_num
  · rw [ContactGrasp.mem_interior_cone]
    intro i
    fin_cases i
    · refine mem_interior_softFingerCone ?_ ?_ ?_
      · simp [softInternalForce]
      · simp [softInternalForce]
      · show |(-12 / 5 : ℝ)| < 3 * 1
        rw [abs_of_neg (by norm_num)]
        norm_num
    · have h1 : √((-5 / 13 : ℝ) ^ 2 + 0 ^ 2) < 1 / 2 * (12 / 13) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have h3 : |(-13 / 5 : ℝ)| < 3 * (12 / 13) := by
        rw [abs_of_neg (by norm_num)]
        norm_num
      exact mem_interior_softFingerCone (by simpa [softInternalForce] using h1)
        (by simp [softInternalForce]) (by simpa [softInternalForce] using h3)

/-- The grasp map of the Theorem 5.7 instance (MLS printed p. 233) is surjective onto the
wrenches. -/
theorem softGrasp_surjective : Function.Surjective softGrasp.graspMap := by
  intro F
  refine ⟨![![F.force 0 - F.torque 1, F.force 1, F.force 2 - F.torque 0, F.torque 2 + F.torque 1],
    ![5 / 13 * F.torque 0 - 12 / 13 * F.torque 1, 0,
      -12 / 13 * F.torque 0 - 5 / 13 * F.torque 1, 0]], ?_⟩
  rw [softGrasp_graspMap]
  apply Wrench.ext
  · ext i
    fin_cases i <;> simp <;> ring
  · ext i
    fin_cases i <;> simp <;> ring

/-- **MLS Theorem 5.7, "only if" direction, fails in the library's soft-finger model** (printed
p. 233, "A spatial grasp with two soft-finger contacts is force-closure if and only if the line
connecting the contact point lies inside both friction cones"): the two-soft-finger grasp
`softGrasp` (`μ = 1/2`, `γ = 3`) is force-closure (Proposition 5.2, p. 224), its inward normals
face each other (`e_z · (0, 1, 1) = 1 > 0`, `(-5/13, 0, -12/13) · (0, -1, -1) = 12/13 > 0`), and
the connecting direction `p₂ - p₁ = (0, 1, 1)`, written in the first contact frame (the identity),
is not in the closed friction cone `√(f₁² + f₂²) ≤ μ f₃` of eq. (5.3) at contact 1. The torsional
moments `-12/5`, `-13/5` balance the moment of the non-collinear forces. -/
theorem softAntipodal_onlyIf_counterexample :
    softGrasp.toGrasp.IsForceClosure ∧
      (softFrame 0).rotation.val = 1 ∧
      WithLp.ofLp ((softFrame 1).translation - (softFrame 0).translation) = ![0, 1, 1] ∧
      (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 1] = 1 ∧
      (![-5 / 13, 0, -12 / 13] : Fin 3 → ℝ) ⬝ᵥ ![0, -1, -1] = 12 / 13 ∧
      (fun i => (softFrame 0).rotation.val i 2) = ![0, 0, 1] ∧
      (fun i => (softFrame 1).rotation.val i 2) = ![-5 / 13, 0, -12 / 13] ∧
      (![0, 1, 1] : Fin 3 → ℝ) ∉ pointContactCone (1 / 2) := by
  refine ⟨(Grasp.isForceClosure_iff _).mpr
    ⟨softGrasp_surjective, _, softGrasp_isStrictlyInternalForce⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [softFrame, softRotation₁]
  · funext i
    fin_cases i <;> simp [softFrame]
  · simp [dotProduct, Fin.sum_univ_succ]
  · simp [dotProduct, Fin.sum_univ_succ]
    norm_num
  · funext i
    fin_cases i <;> simp [softFrame, softRotation₁]
  · funext i
    fin_cases i <;> simp [softFrame, softRotation₂]
  · rw [mem_pointContactCone]
    rintro ⟨h, -⟩
    simp at h
    norm_num at h

end RoboLean.Examples
