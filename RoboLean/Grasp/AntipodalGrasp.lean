import RoboLean.Grasp.PlanarWrench

/-!
# Planar antipodal grasps: Theorem 5.6

MLS Chapter 5, §4.2, printed p. 232: "**Theorem 5.6. Planar antipodal grasps** [82]. A planar grasp
with two point contacts with friction is force-closure if and only if the line connecting the
contact point lies inside both friction cones." The proof is left as Exercise 7 (p. 261). The
page then writes the condition as four strict inequalities, with `n₁`, `n₂` the inward normals at
`p₁`, `p₂` and `n^⊥` defined by `n ⊗ n^⊥ = +1`:

* A: `(n₁ - μ n₁^⊥) ⊗ (p₂ - p₁) > 0`,
* B: `(n₁ + μ n₁^⊥) ⊗ (p₂ - p₁) < 0`,
* C: `(n₂ - μ n₂^⊥) ⊗ (p₁ - p₂) > 0`,
* D: `(n₂ + μ n₂^⊥) ⊗ (p₁ - p₂) < 0`.

Carrier. The grasp is the library's planar grasp `ContactGrasp.planar` (Example 5.3, p. 222) of
two planar point contacts with friction `ContactModel.planarPointContact μ hμ`, one coefficient
`μ > 0` for both contacts as printed, with frames `(Rᵢ, pᵢ)`, `Rᵢ ∈ SO(2)`. The inward normal
`nᵢ` is the contact `y`-axis `contactNormal Rᵢ` and `nᵢ^⊥ = perp2 nᵢ = -tᵢ` (`PlanarWrench`).
Contact `0` and `1` in Lean are the book's `1` and `2`.

Results.
* "Lies inside" is the open cone (design question Q6, settled): A ∧ B holds exactly when
  `R₁ᵀ (p₂ - p₁)` is in the interior of the planar friction cone of p. 222
  (`insideFrictionCone_iff_mem_interior`), equivalently when `p₂ - p₁` is in the interior of the
  friction cone at `p₁` in object coordinates (`insideFrictionCone_iff_mem_interior_image`); the
  interior of the planar cone is exactly `|f₁| < μ f₂` (`mem_interior_planarPointContactCone_iff`).
  A grasp with any of A–D at equality is not force-closure
  (`not_isForceClosure_of_cross2_eq_zero`).
* "If": A–D imply force-closure (`isForceClosure_of_antipodalConditions`).
* "Only if" holds under an orientation hypothesis the book does not state: the inward normals
  face each other, `n₁ · (p₂ - p₁) ≥ 0` and `n₂ · (p₁ - p₂) ≥ 0`, as on a convex object
  (`isForceClosure_iff_antipodalConditions`; one of the two inequalities suffices,
  `antipodalConditions_of_isForceClosure`). Without it, force-closure holds exactly when A–D hold
  or A–D hold with the connecting line reversed at both contacts
  (`isForceClosure_iff_antipodalConditions_or_flipped`); the rectangle of Example 5.3 with its
  contacts exchanged is force-closure without satisfying A–D (`Examples.GraspPlanning`).

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214); nothing here concerns a physical hand or object.
-/

noncomputable section

open Matrix

namespace RoboLean.Grasp

/-! ### The interior of the planar friction cone -/

/-- Supporting lemma: from an interior point `f` of the planar friction cone (MLS Example 5.3,
printed p. 222) a small positive step in any direction stays in the cone. -/
private theorem exists_pos_add_smul_mem_planarPointContactCone {μ : ℝ} {f : Fin 2 → ℝ}
    (hf : f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ))) (e : Fin 2 → ℝ) :
    ∃ t : ℝ, 0 < t ∧ f + t • e ∈ planarPointContactCone μ := by
  have hcont : Continuous fun t : ℝ => f + t • e := by fun_prop
  have h0 : f + (0 : ℝ) • e ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) := by
    simpa using hf
  have hev : ∀ᶠ t in nhds (0 : ℝ),
      f + t • e ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) :=
    hcont.continuousAt.eventually_mem (isOpen_interior.mem_nhds h0)
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f + t • e ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) ∧ t ∈ Set.Ioi 0 :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ht, htpos⟩ := hev'.exists
  exact ⟨t, htpos, interior_subset ht⟩

/-- **The interior of the planar friction cone is given by the strict inequality**, converse of
`mem_interior_planarPointContactCone` (MLS Example 5.3, printed p. 222, cone `|f₁| ≤ μ f₂,
f₂ ≥ 0`; `int(FC)` of p. 223): an interior point satisfies `|f₁| < μ f₂`. Home: beside
`mem_interior_planarPointContactCone` in `Grasp/FrictionCone` (move follow-up). -/
theorem abs_lt_of_mem_interior_planarPointContactCone {μ : ℝ} {f : Fin 2 → ℝ}
    (hf : f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ))) : |f 0| < μ * f 1 := by
  by_cases h : 0 ≤ f 0
  · obtain ⟨t, ht, hmem⟩ := exists_pos_add_smul_mem_planarPointContactCone hf ![1, 0]
    have h1 := (mem_planarPointContactCone.mp hmem).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at h1
    rw [abs_of_nonneg (by linarith)] at h1
    rw [abs_of_nonneg h]
    linarith
  · replace h : f 0 < 0 := not_le.mp h
    obtain ⟨t, ht, hmem⟩ := exists_pos_add_smul_mem_planarPointContactCone hf ![-1, 0]
    have h1 := (mem_planarPointContactCone.mp hmem).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_neg, mul_one, mul_zero,
      add_zero] at h1
    rw [abs_of_neg (by linarith)] at h1
    rw [abs_of_neg h]
    linarith

/-- **The interior of the planar friction cone**, MLS Example 5.3, printed p. 222 (cone
`|f₁| ≤ μ f₂, f₂ ≥ 0`) with `int(FC)` of p. 223: for `μ > 0`, `f` is an interior point exactly
when `|f₁| < μ f₂` (then `f₂ > 0`). Home: beside `mem_interior_planarPointContactCone` in
`Grasp/FrictionCone` (move follow-up). -/
theorem mem_interior_planarPointContactCone_iff {μ : ℝ} (hμ : 0 < μ) {f : Fin 2 → ℝ} :
    f ∈ interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) ↔ |f 0| < μ * f 1 := by
  refine ⟨abs_lt_of_mem_interior_planarPointContactCone, fun h => ?_⟩
  have hpos : 0 < f 1 := by
    have : 0 < μ * f 1 := lt_of_le_of_lt (abs_nonneg _) h
    exact pos_of_mul_pos_right this hμ.le
  exact mem_interior_planarPointContactCone h hpos

/-! ### Conditions A–D -/

/-- The printed condition that a direction `d` lies inside the friction cone at a planar contact
with frame `R ∈ SO(2)` (MLS printed p. 232, conditions A and B at contact 1, C and D at contact 2):
`(n - μ n^⊥) ⊗ d > 0` and `(n + μ n^⊥) ⊗ d < 0`, with `n = contactNormal R` the inward normal
(p. 222 convention), `n^⊥ = perp2 n` and `⊗ = cross2`. Strict, as printed (Q6). -/
def InsideFrictionCone (μ : ℝ) (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) : Prop :=
  0 < cross2 (contactNormal R - μ • perp2 (contactNormal R)) d ∧
    cross2 (contactNormal R + μ • perp2 (contactNormal R)) d < 0

/-- The two printed cross products of MLS p. 232 in contact coordinates `x = Rᵀ d`:
`(n - μ n^⊥) ⊗ d = μ x₂ - x₁` (with `n^⊥ = -t`, `t ⊗ n = 1`). -/
theorem cross2_contactNormal_sub_eq (μ : ℝ) (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) :
    cross2 (contactNormal R - μ • perp2 (contactNormal R)) d =
      μ * ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 1 - ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 0 := by
  obtain ⟨h1, h2, -⟩ := so2_entries R
  simp only [cross2, perp2, contactNormal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, h1, h2]
  ring

/-- The two printed cross products of MLS p. 232 in contact coordinates `x = Rᵀ d`:
`(n + μ n^⊥) ⊗ d = -μ x₂ - x₁` (with `n^⊥ = -t`, `t ⊗ n = 1`). -/
theorem cross2_contactNormal_add_eq (μ : ℝ) (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) :
    cross2 (contactNormal R + μ • perp2 (contactNormal R)) d =
      -(μ * ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 1) -
        ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 0 := by
  obtain ⟨h1, h2, -⟩ := so2_entries R
  simp only [cross2, perp2, contactNormal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, h1, h2]
  ring

/-- **A ∧ B in contact coordinates**, MLS printed p. 232: the printed pair of inequalities at a
contact with frame `R` holds exactly when `x = Rᵀ d` satisfies `|x₁| < μ x₂`, the strict form of
the planar friction cone of p. 222. -/
theorem insideFrictionCone_iff (μ : ℝ) (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) :
    InsideFrictionCone μ R d ↔
      |((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 0| <
        μ * ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) 1 := by
  rw [InsideFrictionCone, cross2_contactNormal_sub_eq, cross2_contactNormal_add_eq, abs_lt]
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **A ∧ B with the contact axes**, MLS printed p. 232: `|t · d| < μ (n · d)`, with `t` the
contact `x`-axis and `n` the inward normal of the frame `R` (p. 222). -/
theorem insideFrictionCone_iff_dotProduct (μ : ℝ) (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) :
    InsideFrictionCone μ R d ↔ |contactTangent R ⬝ᵥ d| < μ * (contactNormal R ⬝ᵥ d) := by
  rw [insideFrictionCone_iff, contactTangent_dotProduct, contactNormal_dotProduct]

/-- **"Lies inside" is the interior (Q6)**, MLS printed p. 232 with the cone of p. 222: for
`μ > 0`, A ∧ B at a contact with frame `R` holds exactly when `Rᵀ d` lies in the interior of the
planar friction cone. -/
theorem insideFrictionCone_iff_mem_interior {μ : ℝ} (hμ : 0 < μ)
    (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) (d : Fin 2 → ℝ) :
    InsideFrictionCone μ R d ↔
      (R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d ∈
        interior (planarPointContactCone μ : Set (Fin 2 → ℝ)) := by
  rw [insideFrictionCone_iff, mem_interior_planarPointContactCone_iff hμ]

/-- The rotation `f ↦ R f` of the plane by `R ∈ SO(2)` as a homeomorphism (supporting
declaration for MLS printed pp. 222, 232). -/
private def so2Homeomorph (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) where
  toFun f := (R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f
  invFun f := (R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ f
  left_inv f := so2_transpose_mulVec_mulVec R f
  right_inv f := so2_mulVec_transpose_mulVec R f
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

/-- **"Lies inside" in object coordinates (Q6)**, MLS printed p. 232: for `μ > 0`, A ∧ B at a
contact with frame `R` holds exactly when `d` lies in the interior of that contact's friction
cone in object coordinates, `{R f : |f₁| ≤ μ f₂, f₂ ≥ 0}` (p. 222). -/
theorem insideFrictionCone_iff_mem_interior_image {μ : ℝ} (hμ : 0 < μ)
    (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) (d : Fin 2 → ℝ) :
    InsideFrictionCone μ R d ↔
      d ∈ interior ((fun f => (R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f) ''
        (planarPointContactCone μ : Set (Fin 2 → ℝ))) := by
  rw [insideFrictionCone_iff_mem_interior hμ]
  change _ ↔ d ∈ interior (so2Homeomorph R '' (planarPointContactCone μ : Set (Fin 2 → ℝ)))
  rw [← (so2Homeomorph R).image_interior]
  constructor
  · intro h
    exact ⟨_, h, so2_mulVec_transpose_mulVec R d⟩
  · rintro ⟨f, hf, rfl⟩
    change (R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ((R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f) ∈ _
    rwa [so2_transpose_mulVec_mulVec]

/-- Inside the cone (MLS printed p. 232) forces `n · d > 0`: the direction makes an acute angle
with the inward normal. -/
theorem InsideFrictionCone.dotProduct_pos {μ : ℝ} {R : Matrix.specialOrthogonalGroup (Fin 2) ℝ}
    {d : Fin 2 → ℝ} (hμ : 0 < μ) (h : InsideFrictionCone μ R d) :
    0 < contactNormal R ⬝ᵥ d := by
  rw [insideFrictionCone_iff_dotProduct] at h
  have : 0 < μ * (contactNormal R ⬝ᵥ d) := lt_of_le_of_lt (abs_nonneg _) h
  exact pos_of_mul_pos_right this hμ.le

/-- Inside the cone (MLS printed p. 232) is invariant under positive scaling of the direction. -/
theorem InsideFrictionCone.smul {μ : ℝ} {R : Matrix.specialOrthogonalGroup (Fin 2) ℝ}
    {d : Fin 2 → ℝ} (h : InsideFrictionCone μ R d) {s : ℝ} (hs : 0 < s) :
    InsideFrictionCone μ R (s • d) := by
  rw [insideFrictionCone_iff] at h ⊢
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hs]
  nlinarith

/-- The printed conditions A–D of MLS printed p. 232 for a planar grasp of two point contacts
with friction with frames `(R i, p i)` (Lean contacts `0`, `1` are the book's `1`, `2`): the
direction `p₂ - p₁` lies inside the friction cone at `p₁` (A ∧ B) and `p₁ - p₂` inside the
friction cone at `p₂` (C ∧ D), all strict, one coefficient `μ` (`antipodalConditions_iff` gives
the four printed inequalities). A grasp satisfying them is called antipodal (p. 232). -/
def AntipodalConditions (μ : ℝ) (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (p : Fin 2 → Fin 2 → ℝ) : Prop :=
  InsideFrictionCone μ (R 0) (p 1 - p 0) ∧ InsideFrictionCone μ (R 1) (p 0 - p 1)

/-- **Conditions A–D as printed**, MLS printed p. 232:
A `(n₁ - μ n₁^⊥) ⊗ (p₂ - p₁) > 0`, B `(n₁ + μ n₁^⊥) ⊗ (p₂ - p₁) < 0`,
C `(n₂ - μ n₂^⊥) ⊗ (p₁ - p₂) > 0`, D `(n₂ + μ n₂^⊥) ⊗ (p₁ - p₂) < 0`. -/
theorem antipodalConditions_iff (μ : ℝ) (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (p : Fin 2 → Fin 2 → ℝ) :
    AntipodalConditions μ R p ↔
      0 < cross2 (contactNormal (R 0) - μ • perp2 (contactNormal (R 0))) (p 1 - p 0) ∧
      cross2 (contactNormal (R 0) + μ • perp2 (contactNormal (R 0))) (p 1 - p 0) < 0 ∧
      0 < cross2 (contactNormal (R 1) - μ • perp2 (contactNormal (R 1))) (p 0 - p 1) ∧
      cross2 (contactNormal (R 1) + μ • perp2 (contactNormal (R 1))) (p 0 - p 1) < 0 := by
  simp only [AntipodalConditions, InsideFrictionCone, and_assoc]

/-- The inward normals of two planar contacts face each other (an orientation hypothesis MLS
does not state for Theorem 5.6, printed p. 232): `n₁ · (p₂ - p₁) ≥ 0` and `n₂ · (p₁ - p₂) ≥ 0`.
It holds for boundary points of a convex object with inward normals. -/
def NormalsFaceEachOther (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (p : Fin 2 → Fin 2 → ℝ) : Prop :=
  0 ≤ contactNormal (R 0) ⬝ᵥ (p 1 - p 0) ∧ 0 ≤ contactNormal (R 1) ⬝ᵥ (p 0 - p 1)

/-! ### The two-contact planar grasp -/

/-- The grasp map of two planar point contacts with friction (MLS eq. (5.6) with Example 5.3,
printed pp. 219, 222): `G f = (R₁ f₁, p₁ ⊗ R₁ f₁) + (R₂ f₂, p₂ ⊗ R₂ f₂)`. -/
theorem planar_planarPointContact_graspMap_two (μ : ℝ) (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (f : Fin 2 → Fin 2 → ℝ) :
    (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).graspMap f =
      planarWrench (p 0) ((R 0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f 0) +
        planarWrench (p 1) ((R 1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f 1) := by
  rw [planar_planarPointContact_graspMap, Fin.sum_univ_two]

/-- **Surjectivity of the two-contact planar grasp map** (MLS printed pp. 222–224): the grasp map
of two planar point contacts with friction is onto the planar wrenches exactly when the contact
points are distinct. -/
theorem planar_planarPointContact_two_surjective_iff (μ : ℝ) (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ) :
    Function.Surjective
        (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).graspMap ↔
      p 0 ≠ p 1 := by
  constructor
  · intro hs hp
    obtain ⟨f, hf⟩ := hs ![0, 0, 1]
    rw [planar_planarPointContact_graspMap_two, hp, ← planarWrench_add] at hf
    set F := (R 0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f 0 + (R 1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f 1
    have h0 := congrFun hf 0
    have h1 := congrFun hf 1
    have h2 := congrFun hf 2
    simp only [planarWrench, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at h0 h1 h2
    have hF : F = 0 := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
    rw [hF] at h2
    simp [cross2] at h2
  · intro hp w
    set a : Fin 2 → ℝ := p 0 - p 1
    set W : Fin 2 → ℝ := ![w 0, w 1]
    set c : ℝ := w 2 - cross2 (p 1) W
    have ha : a 0 ^ 2 + a 1 ^ 2 ≠ 0 := by
      intro h0
      have ha0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
      have ha1 : a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
      apply hp
      funext i
      fin_cases i
      · have : p 0 0 - p 1 0 = 0 := ha0
        simpa [sub_eq_zero] using this
      · have : p 0 1 - p 1 1 = 0 := ha1
        simpa [sub_eq_zero] using this
    set F : Fin 2 → ℝ := (c / (a 0 ^ 2 + a 1 ^ 2)) • perp2 a
    have hF : cross2 a F = c := by
      rw [cross2_smul_right, cross2_perp2]
      field_simp
    refine ⟨![(R 0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ F,
      (R 1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ (W - F)], ?_⟩
    rw [planar_planarPointContact_graspMap_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [so2_mulVec_transpose_mulVec, so2_mulVec_transpose_mulVec]
    have hτ : cross2 (p 0) F + cross2 (p 1) (W - F) = w 2 := by
      rw [cross2_sub_right]
      have : cross2 (p 0) F - cross2 (p 1) F = cross2 a F := by
        rw [cross2_sub_left]
      linarith
    funext i
    fin_cases i
    · simp [planarWrench, W]
    · simp [planarWrench, W]
    · simp only [planarWrench, Pi.add_apply, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Fin.reduceFinMk, Fin.isValue]
      exact hτ

/-- Supporting lemma for MLS Theorem 5.6, printed p. 232: if a direction `e` is parallel to the
connecting line (`(p₂ - p₁) ⊗ e = 0`), inside the friction cone at `p₁` and `-e` inside the cone
at `p₂`, then the opposite forces `e` at `p₁` and `-e` at `p₂`, in contact coordinates
`(R₁ᵀ e, R₂ᵀ (-e))`, are a strictly internal force (Definition 5.3, p. 223). -/
theorem isStrictlyInternalForce_of_insideFrictionCone {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    {e : Fin 2 → ℝ} (he : cross2 (p 1 - p 0) e = 0) (h0 : InsideFrictionCone μ (R 0) e)
    (h1 : InsideFrictionCone μ (R 1) (-e)) :
    IsStrictlyInternalForce
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).graspMap
      ((ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).cone :
        Set (Fin 2 → Fin 2 → ℝ))
      ![(R 0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ e, (R 1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ (-e)] := by
  refine ⟨?_, ?_⟩
  · rw [planar_planarPointContact_graspMap_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [so2_mulVec_transpose_mulVec, so2_mulVec_transpose_mulVec, planarWrench_neg,
      ← sub_eq_add_neg]
    have hτ : cross2 (p 0) e - cross2 (p 1) e = 0 := by
      rw [← cross2_sub_left, ← neg_sub, cross2_neg_left, he, neg_zero]
    funext i
    fin_cases i
    · simp [planarWrench]
    · simp [planarWrench]
    · simp only [planarWrench, Pi.sub_apply, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Fin.reduceFinMk, Fin.isValue, Pi.zero_apply]
      exact hτ
  · rw [ContactGrasp.mem_interior_cone]
    intro i
    fin_cases i
    · exact (insideFrictionCone_iff_mem_interior hμ (R 0) e).mp h0
    · exact (insideFrictionCone_iff_mem_interior hμ (R 1) (-e)).mp h1

/-- Supporting lemma for MLS Theorem 5.6, printed p. 232: a direction `e` parallel to the
connecting line, inside the cone at `p₁` with `-e` inside the cone at `p₂`, makes the
two-contact planar grasp force-closure (Proposition 5.2, p. 224). Finite-force caveat:
unbounded contact forces at maintained rigid contacts (MLS p. 214). -/
theorem isForceClosure_of_insideFrictionCone {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (hp : p 0 ≠ p 1) {e : Fin 2 → ℝ} (he : cross2 (p 1 - p 0) e = 0)
    (h0 : InsideFrictionCone μ (R 0) e) (h1 : InsideFrictionCone μ (R 1) (-e)) :
    Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp :=
  (Grasp.isForceClosure_iff _).mpr
    ⟨(planar_planarPointContact_two_surjective_iff μ hμ R p).mpr hp, _,
      isStrictlyInternalForce_of_insideFrictionCone hμ R p he h0 h1⟩

/-- Under A ∧ B the contact points are distinct (MLS printed p. 232): `(n - μ n^⊥) ⊗ 0 = 0`. -/
theorem InsideFrictionCone.ne_zero {μ : ℝ} {R : Matrix.specialOrthogonalGroup (Fin 2) ℝ}
    {d : Fin 2 → ℝ} (h : InsideFrictionCone μ R d) : d ≠ 0 := by
  rintro rfl
  have := h.1
  simp [cross2] at this

/-- **MLS Theorem 5.6, "if" direction**, printed p. 232 (Exercise 7, p. 261): a planar grasp of
two point contacts with friction (`μ > 0`) whose frames satisfy the printed conditions A–D is
force-closure. No hypothesis beyond A–D and `μ > 0` is needed (A–D force `p₁ ≠ p₂`). The strictly
internal force is the pair of opposite forces along the connecting line. Finite-force caveat:
unbounded contact forces at maintained rigid contacts (MLS p. 214). -/
theorem isForceClosure_of_antipodalConditions {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (h : AntipodalConditions μ R p) :
    Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp := by
  have hp : p 0 ≠ p 1 := by
    intro hp
    exact h.1.ne_zero (by rw [hp, sub_self])
  refine isForceClosure_of_insideFrictionCone hμ R p hp (cross2_self _) h.1 ?_
  rw [neg_sub]
  exact h.2

/-- In two dimensions, `b ⊗ a = 0` with `b ≠ 0` makes `a` a multiple of `b`:
`a = ((b · a) / |b|²) b` (supporting lemma for MLS Theorem 5.6, printed p. 232). -/
private theorem eq_smul_of_cross2_eq_zero {a b : Fin 2 → ℝ} (hb : b ≠ 0) (h : cross2 b a = 0) :
    a = ((b ⬝ᵥ a) / (b 0 ^ 2 + b 1 ^ 2)) • b := by
  have hb2 : b 0 ^ 2 + b 1 ^ 2 ≠ 0 := by
    intro h0
    apply hb
    funext i
    fin_cases i
    · show b 0 = 0
      nlinarith [sq_nonneg (b 0), sq_nonneg (b 1)]
    · show b 1 = 0
      nlinarith [sq_nonneg (b 0), sq_nonneg (b 1)]
  simp only [cross2] at h
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, dotProduct,
      Fin.sum_univ_two]
    rw [div_mul_eq_mul_div, eq_div_iff hb2]
    linear_combination (-b 1) * h
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, dotProduct,
      Fin.sum_univ_two]
    rw [div_mul_eq_mul_div, eq_div_iff hb2]
    linear_combination b 0 * h

/-- **MLS Theorem 5.6, "only if" direction without an orientation hypothesis**, printed p. 232:
a force-closure planar grasp of two point contacts with friction (`μ > 0`) satisfies the printed
conditions A–D, or A–D with the connecting line reversed at both contacts (`p₁ - p₂` inside the
cone at `p₁` and `p₂ - p₁` inside the cone at `p₂`). Proof: by Proposition 5.2 (p. 224) there is a
strictly internal force; its two contact forces are opposite and, having zero net moment,
parallel to the connecting line; their direction decides which alternative holds. -/
theorem antipodalConditions_or_flipped_of_isForceClosure {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (h : Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp) :
    AntipodalConditions μ R p ∨
      (InsideFrictionCone μ (R 0) (p 0 - p 1) ∧ InsideFrictionCone μ (R 1) (p 1 - p 0)) := by
  obtain ⟨hsurj, fN, hGf, hint⟩ := (Grasp.isForceClosure_iff _).mp h
  rw [ContactGrasp.toGrasp_map] at hsurj hGf
  rw [ContactGrasp.toGrasp_cone] at hint
  have hp : p 0 ≠ p 1 := (planar_planarPointContact_two_surjective_iff μ hμ R p).mp hsurj
  rw [ContactGrasp.mem_interior_cone] at hint
  have hg0 : |fN 0 0| < μ * fN 0 1 := abs_lt_of_mem_interior_planarPointContactCone (hint 0)
  have hg1 : |fN 1 0| < μ * fN 1 1 := abs_lt_of_mem_interior_planarPointContactCone (hint 1)
  set F0 := (R 0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ fN 0 with hF0
  set F1 := (R 1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ fN 1 with hF1
  set d : Fin 2 → ℝ := p 1 - p 0 with hd
  have hGf' : planarWrench (p 0) F0 + planarWrench (p 1) F1 = 0 := by
    rw [← planar_planarPointContact_graspMap_two μ hμ R p fN]
    exact hGf
  have e0 := congrFun hGf' 0
  have e1 := congrFun hGf' 1
  have e2 := congrFun hGf' 2
  simp only [planarWrench, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e0 e1 e2
  have hF1eq : F1 = -F0 := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.neg_apply]
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Pi.neg_apply]
      linarith
  rw [hF1eq, cross2_neg_right, ← sub_eq_add_neg, ← cross2_sub_left] at e2
  -- `F0` is parallel to `d`
  have hd0 : d ≠ 0 := by
    intro h0
    apply hp
    have : p 1 - p 0 = 0 := h0
    exact (sub_eq_zero.mp this).symm
  have hcross : cross2 F0 d = 0 := by
    rw [cross2_comm, hd, ← neg_sub, cross2_neg_left, e2, neg_zero, neg_zero]
  have hF0ne : F0 ≠ 0 := by
    intro h0
    have : fN 0 = 0 := by
      have h' : fN 0 = (R 0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ F0 := by
        rw [hF0, so2_transpose_mulVec_mulVec]
      rw [h', h0, Matrix.mulVec_zero]
    rw [this] at hg0
    simp at hg0
  set κ := (F0 ⬝ᵥ d) / (F0 0 ^ 2 + F0 1 ^ 2) with hκ
  have hdκ : d = κ • F0 := eq_smul_of_cross2_eq_zero hF0ne hcross
  have hκne : κ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hdκ
    exact hd0 hdκ
  -- contact coordinates of `± d`
  have hx0 : (R 0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d = κ • fN 0 := by
    rw [hdκ, Matrix.mulVec_smul, hF0, so2_transpose_mulVec_mulVec]
  have hx1 : (R 1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ (-d) = κ • fN 1 := by
    have : -d = κ • F1 := by rw [hF1eq, hdκ, smul_neg]
    rw [this, Matrix.mulVec_smul, hF1, so2_transpose_mulVec_mulVec]
  rcases lt_or_gt_of_ne hκne with hneg | hpos
  · right
    have hneg' : 0 < -κ := neg_pos.mpr hneg
    refine ⟨?_, ?_⟩
    · rw [insideFrictionCone_iff]
      have : (R 0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ (p 0 - p 1) = (-κ) • fN 0 := by
        rw [← neg_sub, ← hd, Matrix.mulVec_neg, hx0, neg_smul]
      rw [this]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hneg']
      nlinarith
    · rw [insideFrictionCone_iff]
      have : (R 1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ (p 1 - p 0) = (-κ) • fN 1 := by
        rw [← hd, ← neg_neg d, Matrix.mulVec_neg, hx1, neg_smul]
      rw [this]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hneg']
      nlinarith
  · left
    refine ⟨?_, ?_⟩
    · rw [insideFrictionCone_iff, ← hd, hx0]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hpos]
      nlinarith
    · rw [insideFrictionCone_iff, ← neg_sub, ← hd, hx1]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hpos]
      nlinarith

/-- **MLS Theorem 5.6, unoriented form**, printed p. 232: a planar grasp of two point contacts with
friction (`μ > 0`, any frames) is force-closure if and only if the printed conditions A–D hold or
A–D hold with the connecting line reversed at both contacts. Finite-force caveat: unbounded
contact forces at maintained rigid contacts (MLS p. 214). -/
theorem isForceClosure_iff_antipodalConditions_or_flipped {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ) :
    Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp ↔
      AntipodalConditions μ R p ∨
        (InsideFrictionCone μ (R 0) (p 0 - p 1) ∧ InsideFrictionCone μ (R 1) (p 1 - p 0)) := by
  refine ⟨antipodalConditions_or_flipped_of_isForceClosure hμ R p, ?_⟩
  rintro (h | ⟨h0, h1⟩)
  · exact isForceClosure_of_antipodalConditions hμ R p h
  · have hp : p 0 ≠ p 1 := by
      intro hp
      exact h0.ne_zero (by rw [hp, sub_self])
    refine isForceClosure_of_insideFrictionCone hμ R p hp ?_ h0 ?_
    · rw [← neg_sub (p 1) (p 0), cross2_neg_right, cross2_self, neg_zero]
    · rw [neg_sub]
      exact h1

/-- **MLS Theorem 5.6, "only if" direction with the orientation hypothesis**, printed p. 232:
a force-closure planar grasp of two point contacts with friction (`μ > 0`) satisfies the printed
A–D as soon as one inward normal faces the other contact (`n₁ · (p₂ - p₁) ≥ 0` or
`n₂ · (p₁ - p₂) ≥ 0`), a hypothesis the book does not state; without it the statement is false
(`Examples.antipodal_printed_iff_counterexample`). Finite-force caveat: unbounded contact forces
at maintained rigid contacts (MLS p. 214). -/
theorem antipodalConditions_of_isForceClosure {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (h : Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp)
    (hface : 0 ≤ contactNormal (R 0) ⬝ᵥ (p 1 - p 0) ∨ 0 ≤ contactNormal (R 1) ⬝ᵥ (p 0 - p 1)) :
    AntipodalConditions μ R p := by
  rcases antipodalConditions_or_flipped_of_isForceClosure hμ R p h with h' | ⟨h0, h1⟩
  · exact h'
  · exfalso
    have hn0 := h0.dotProduct_pos hμ
    have hn1 := h1.dotProduct_pos hμ
    rw [← neg_sub (p 1) (p 0), dotProduct_neg] at hn0
    rw [← neg_sub (p 0) (p 1), dotProduct_neg] at hn1
    rcases hface with hf | hf <;> linarith

/-- **MLS Theorem 5.6**, printed p. 232, with the orientation hypothesis the book does not
state: for a planar grasp of two point contacts with friction (`μ > 0`) whose inward normals face
each other (`NormalsFaceEachOther`, true on a convex object), force-closure holds if and only if
the printed conditions A–D hold (strict: "inside" is the open cone, Q6). Exercise 7 (p. 261) asks
for this proof. Finite-force caveat: unbounded contact forces at maintained rigid contacts
(MLS p. 214). -/
theorem isForceClosure_iff_antipodalConditions {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (hface : NormalsFaceEachOther R p) :
    Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp ↔
      AntipodalConditions μ R p :=
  ⟨fun h => antipodalConditions_of_isForceClosure hμ R p h (Or.inl hface.1),
    isForceClosure_of_antipodalConditions hμ R p⟩

/-- **The boundary of the cones is not force-closure (Q6)**, MLS printed p. 232: if any of the
four printed expressions of A–D vanishes (the connecting line on an edge of a friction cone), the
two-contact planar grasp (`μ > 0`, any frames) is not force-closure. Hence the printed strict
inequalities, not their closed versions, characterize force-closure. -/
theorem not_isForceClosure_of_cross2_eq_zero {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (h : cross2 (contactNormal (R 0) - μ • perp2 (contactNormal (R 0))) (p 1 - p 0) = 0 ∨
      cross2 (contactNormal (R 0) + μ • perp2 (contactNormal (R 0))) (p 1 - p 0) = 0 ∨
      cross2 (contactNormal (R 1) - μ • perp2 (contactNormal (R 1))) (p 0 - p 1) = 0 ∨
      cross2 (contactNormal (R 1) + μ • perp2 (contactNormal (R 1))) (p 0 - p 1) = 0) :
    ¬ Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp := by
  intro hfc
  rcases antipodalConditions_or_flipped_of_isForceClosure hμ R p hfc with
    ⟨⟨hA, hB⟩, ⟨hC, hD⟩⟩ | ⟨⟨hA, hB⟩, ⟨hC, hD⟩⟩
  · rcases h with h | h | h | h <;> linarith
  · rw [← neg_sub (p 1) (p 0), cross2_neg_right] at hA hB
    rw [← neg_sub (p 0) (p 1), cross2_neg_right] at hC hD
    rcases h with h | h | h | h <;> linarith

/-- A two-contact planar grasp whose connecting line is tangent at the first contact
(`n₁ · (p₂ - p₁) = 0`, for example two contacts on one edge of a polygon with equal frames) is not
force-closure (MLS Theorem 5.6, printed p. 232). -/
theorem not_isForceClosure_of_contactNormal_dotProduct_eq_zero {μ : ℝ} (hμ : 0 < μ)
    (R : Fin 2 → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℝ)
    (h : contactNormal (R 0) ⬝ᵥ (p 1 - p 0) = 0) :
    ¬ Grasp.IsForceClosure
      (ContactGrasp.planar (fun _ => ContactModel.planarPointContact μ hμ) R p).toGrasp := by
  intro hfc
  rcases antipodalConditions_or_flipped_of_isForceClosure hμ R p hfc with ⟨h0, -⟩ | ⟨h0, -⟩
  · have := h0.dotProduct_pos hμ
    linarith
  · have := h0.dotProduct_pos hμ
    rw [← neg_sub (p 1) (p 0), dotProduct_neg] at this
    linarith

end RoboLean.Grasp
