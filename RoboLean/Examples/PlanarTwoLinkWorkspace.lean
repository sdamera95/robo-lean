import RoboLean.Examples.PlanarTwoLink

/-!
# The reachable workspace of the planar two-link arm, and a design certificate

For the planar two-revolute chain `planarTwoLink a b` of `PlanarTwoLink` (MLS Example 3.1,
printed pp. 87–89, specialized to `l₀ = θ₃ = θ₄ = 0`, `l₁ = a`, `l₂ = b`; both axes `+z`,
zero configuration along `+y`) with positive link lengths and unrestricted joints, the
reachable workspace of MLS eq. (3.12), p. 95, is the closed annulus

  `{x ∈ ℝ³ : x₃ = 0, |a - b| ≤ ‖x‖ ≤ a + b}`

in the plane through the base origin perpendicular to the joint axes (Lean writes the third
coordinate as `x 2`). This annulus statement and the design certificate built on it come from
the research design document `research/reports/mls-lean-assessment.md`, paragraph "Robot
design and workspace coverage". They are not theorems printed in MLS: MLS Example 3.4
(pp. 96–97) describes the analogous annulus for two links only informally, as one step of a
planar three-link construction, in a different frame. Every docstring below that concerns the
annulus or the certificate says so.

The contents:

* `planarTwoLinkPosition_norm_sq`, the law of cosines `‖p(q)‖² = a² + b² + 2ab cos q₂`;
* the two inclusions `planarTwoLink_reachableWorkspace_subset` (`0 ≤ a`, `0 ≤ b`) and
  `planarTwoLink_annulus_subset_reachableWorkspace` (`0 < a`, `0 < b`), proved separately,
  and the characterization `planarTwoLink_reachableWorkspace_eq`. The second inclusion
  constructs the joint angles: `q₂ = arccos((‖x‖² - a² - b²) / (2ab))` and `q₁` the argument
  of a complex quotient (`exists_planarTwoLinkPosition_eq`);
* the design certificates: every set `W` of points of the annulus is reachable
  (`planarTwoLink_workspace_certificate`), the condition is also necessary
  (`planarTwoLink_subset_reachableWorkspace_iff`), and a radial band
  `r₁ ≤ ‖x‖ ≤ r₂` with `|a - b| ≤ r₁`, `r₂ ≤ a + b` is reachable
  (`planarTwoLink_radialBand_certificate`);
* zero radius and equal lengths: the origin is reachable exactly when `a = b`
  (`zero_mem_planarTwoLink_reachableWorkspace_iff`), the equal-length workspace is the disk of
  radius `2a` (`planarTwoLink_reachableWorkspace_eq_disk`), and for `a = b` the origin is
  reached exactly at the folded configurations `cos q₂ = -1`
  (`planarTwoLinkPosition_eq_zero_iff`);
* an exact convention check for `a = b = 1`.

Lean joint `0` is the book's joint `1`, so `q 0 = θ₁` and `q 1 = θ₂`. These are statements
about position reachability of the ideal coordinate model with unrestricted joints. They say
nothing about orientation, joint limits, collisions, continuous paths, dynamics or a physical
arm.
-/

noncomputable section

namespace RoboLean.Examples

/-- The tool position of the planar two-link arm lies in the plane `x₃ = 0` (Lean coordinate
`2`) through the base origin and perpendicular to the common joint axis `+z`: the third entry
of MLS eq. (3.4), p. 89, specialized as in `planarTwoLinkPosition_eq`. -/
theorem planarTwoLinkPosition_two (a b : ℝ) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q 2 = 0 := by
  rw [planarTwoLinkPosition_eq]
  simp [vec]

/-- **Law of cosines for the planar two-link arm.** The squared distance of the tool position
`p(q)` (MLS eq. (3.4), p. 89, specialized: `l₁ = a`, `l₂ = b`) from the base origin is
`a² + b² + 2ab cos θ₂`, where `θ₂ = q 1` is the relative angle of the second joint. Holds for
all real `a, b`. -/
theorem planarTwoLinkPosition_norm_sq (a b : ℝ) (q : Fin 2 → ℝ) :
    ‖planarTwoLinkPosition a b q‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * Real.cos (q 1) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, planarTwoLinkPosition_eq]
  simp only [vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.sin_add, Real.cos_add]
  linear_combination
    (a ^ 2 + 2 * a * b * Real.cos (q 1) + b ^ 2 * (Real.sin (q 1) ^ 2 + Real.cos (q 1) ^ 2)) *
        Real.sin_sq_add_cos_sq (q 0) +
      b ^ 2 * Real.sin_sq_add_cos_sq (q 1)

/-- The tool position of the planar two-link arm with nonnegative link lengths lies in the
annulus `x₃ = 0`, `|a - b| ≤ ‖x‖ ≤ a + b`. Source: the annulus statement of
`research/reports/mls-lean-assessment.md` ("Robot design and workspace coverage"), a design
statement rather than an MLS theorem; the position is MLS eq. (3.4), p. 89, specialized. -/
theorem planarTwoLinkPosition_mem_annulus {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q 2 = 0 ∧ |a - b| ≤ ‖planarTwoLinkPosition a b q‖ ∧
      ‖planarTwoLinkPosition a b q‖ ≤ a + b := by
  have hsq := planarTwoLinkPosition_norm_sq a b q
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hc₁ := Real.neg_one_le_cos (q 1)
  have hc₂ := Real.cos_le_one (q 1)
  refine ⟨planarTwoLinkPosition_two a b q, ?_, ?_⟩
  · have hlo : (a - b) ^ 2 ≤ ‖planarTwoLinkPosition a b q‖ ^ 2 := by
      rw [hsq]
      nlinarith [mul_nonneg hab (by linarith : (0 : ℝ) ≤ 1 + Real.cos (q 1))]
    simpa only [abs_norm] using sq_le_sq.mp hlo
  · have hhi : ‖planarTwoLinkPosition a b q‖ ^ 2 ≤ (a + b) ^ 2 := by
      rw [hsq]
      nlinarith [mul_nonneg hab (by linarith : (0 : ℝ) ≤ 1 - Real.cos (q 1))]
    exact (abs_le_of_sq_le_sq' hhi (add_nonneg ha hb)).2

/-- The forward-kinematics position of `planarTwoLink` is the geometric position
`planarTwoLinkPosition` (the translation part of `planarTwoLink_fk`, MLS eq. (3.4), p. 89). -/
private theorem planarTwoLink_fk_translation_eq (a b : ℝ) (q : Fin 2 → ℝ) :
    ((planarTwoLink a b).fk q).translation = planarTwoLinkPosition a b q := by
  rw [planarTwoLink_fk]

/-- **Easy inclusion.** The reachable workspace `W_R = {p(θ) : θ ∈ Q}` of MLS eq. (3.12),
p. 95, of the planar two-link arm with unrestricted joints (`Q = Set.univ`) and nonnegative
link lengths lies in the annulus `x₃ = 0`, `|a - b| ≤ ‖x‖ ≤ a + b`. Source of the annulus:
`research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage" (a design
statement, not an MLS theorem). -/
theorem planarTwoLink_reachableWorkspace_subset {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (planarTwoLink a b).reachableWorkspace Set.univ ⊆
      {x : Vec3 | x 2 = 0 ∧ |a - b| ≤ ‖x‖ ∧ ‖x‖ ≤ a + b} := by
  rintro x ⟨q, -, rfl⟩
  simp only [Set.mem_ofPred_eq, planarTwoLink_fk_translation_eq]
  exact planarTwoLinkPosition_mem_annulus ha hb q

/-- A point of the plane `x₃ = 0` read as the complex number `x₂ - i x₁` (Lean coordinates
`x 1 - i x 0`): the zero-configuration direction `+y` of the arm is the positive real axis and a
positive rotation about `+z` is multiplication by `e^{iθ}`. -/
private def planarComplex (x : Vec3) : ℂ := ⟨x 1, -x 0⟩

private theorem norm_planarComplex {x : Vec3} (hx : x 2 = 0) : ‖planarComplex x‖ = ‖x‖ := by
  have h : ‖planarComplex x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three, hx]
    simp only [planarComplex]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Existence of joint angles (inverse position kinematics of the planar two-link arm).**
For positive link lengths `a, b`, every point `x` of the plane `x₃ = 0` with
`|a - b| ≤ ‖x‖ ≤ a + b` is the tool position `planarTwoLinkPosition a b q` of some joint vector
`q`. The construction: `θ₂ = arccos((‖x‖² - a² - b²) / (2ab))` (law of cosines,
`planarTwoLinkPosition_norm_sq`; the bounds give an argument in `[-1, 1]`), and `θ₁` the
argument of `ζ / w`, where `ζ = x₂ - i x₁` is the target and `w = a + b e^{iθ₂}` the position
at `θ₁ = 0`, both of modulus `‖x‖`. Source: the annulus statement of
`research/reports/mls-lean-assessment.md` ("Robot design and workspace coverage"), a design
statement rather than an MLS theorem; the position is MLS eq. (3.4), p. 89, specialized. No
uniqueness, continuity or branch selection is claimed. -/
theorem exists_planarTwoLinkPosition_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : Vec3}
    (hx : x 2 = 0) (h₁ : |a - b| ≤ ‖x‖) (h₂ : ‖x‖ ≤ a + b) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x := by
  have hab : 0 < 2 * a * b := by positivity
  have hr : 0 ≤ ‖x‖ := norm_nonneg x
  have hlo : (a - b) ^ 2 ≤ ‖x‖ ^ 2 := sq_le_sq.mpr (by rwa [abs_norm])
  have hhi : ‖x‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hr h₂ 2
  set c := (‖x‖ ^ 2 - a ^ 2 - b ^ 2) / (2 * a * b) with hc
  have hc₁ : -1 ≤ c := by
    rw [hc, le_div_iff₀ hab]
    nlinarith
  have hc₂ : c ≤ 1 := by
    rw [hc, div_le_iff₀ hab]
    nlinarith
  set q₂ := Real.arccos c with hq₂
  have hcos : Real.cos q₂ = c := Real.cos_arccos hc₁ hc₂
  set w : ℂ := (a : ℂ) + (b : ℂ) * Complex.exp (q₂ * Complex.I) with hw
  set ζ := planarComplex x with hζ
  have hwn : ‖w‖ = ‖x‖ := by
    have h : ‖w‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hw, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, hcos]
      have hs := Real.sin_sq_add_cos_sq q₂
      rw [hcos] at hs
      have hc' : 2 * a * b * c = ‖x‖ ^ 2 - a ^ 2 - b ^ 2 := by
        rw [hc]
        field_simp
      linear_combination b ^ 2 * hs + hc'
    exact (pow_left_inj₀ (norm_nonneg _) hr two_ne_zero).mp h
  have hζn : ‖ζ‖ = ‖x‖ := norm_planarComplex hx
  set q₁ := Complex.arg (ζ / w) with hq₁
  have key : Complex.exp (q₁ * Complex.I) * w = ζ := by
    by_cases hw0 : w = 0
    · have hζ0 : ζ = 0 := by
        rw [← norm_eq_zero, hζn, ← hwn, hw0, norm_zero]
      rw [hw0, hζ0, mul_zero]
    · have hx0 : ‖x‖ ≠ 0 := by
        rw [← hwn]
        exact norm_ne_zero_iff.mpr hw0
      have hn : ‖ζ / w‖ = 1 := by
        rw [norm_div, hζn, hwn, div_self hx0]
      have h := Complex.norm_mul_exp_arg_mul_I (ζ / w)
      rw [hn, Complex.ofReal_one, one_mul] at h
      rw [hq₁, h, div_mul_cancel₀ _ hw0]
  have hexp : Complex.exp (q₁ * Complex.I) * w =
      (a : ℂ) * Complex.exp (q₁ * Complex.I) +
        (b : ℂ) * Complex.exp (((q₁ + q₂ : ℝ) : ℂ) * Complex.I) := by
    rw [hw, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  rw [hexp] at key
  have hre := congrArg Complex.re key
  have him := congrArg Complex.im key
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hζ, planarComplex] at hre him
  refine ⟨![q₁, q₂], ?_⟩
  rw [planarTwoLinkPosition_eq]
  ext i
  fin_cases i
  · simp [vec]
    linarith
  · simp [vec]
    linarith
  · simp [vec, hx]

/-- **Hard inclusion.** For positive link lengths, every point of the annulus `x₃ = 0`,
`|a - b| ≤ ‖x‖ ≤ a + b` lies in the reachable workspace `W_R` of MLS eq. (3.12), p. 95, of the
planar two-link arm with unrestricted joints (`Q = Set.univ`). Source of the annulus:
`research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage" (a design
statement, not an MLS theorem). -/
theorem planarTwoLink_annulus_subset_reachableWorkspace {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    {x : Vec3 | x 2 = 0 ∧ |a - b| ≤ ‖x‖ ∧ ‖x‖ ≤ a + b} ⊆
      (planarTwoLink a b).reachableWorkspace Set.univ := by
  rintro x ⟨hx, h₁, h₂⟩
  obtain ⟨q, hq⟩ := exists_planarTwoLinkPosition_eq ha hb hx h₁ h₂
  refine ⟨q, Set.mem_univ q, ?_⟩
  simp only [planarTwoLink_fk_translation_eq, hq]

/-- **The reachable workspace of the planar two-link arm is the annulus.** For positive link
lengths `a, b` and unrestricted joints (`Q = Set.univ`), the reachable workspace
`W_R = {p(θ) : θ ∈ Q}` of MLS eq. (3.12), p. 95, is
`{x : x₃ = 0, |a - b| ≤ ‖x‖ ≤ a + b}`. The two inclusions are
`planarTwoLink_reachableWorkspace_subset` and
`planarTwoLink_annulus_subset_reachableWorkspace`. Source of the annulus:
`research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage" (a design
statement, not an MLS theorem). -/
theorem planarTwoLink_reachableWorkspace_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (planarTwoLink a b).reachableWorkspace Set.univ =
      {x : Vec3 | x 2 = 0 ∧ |a - b| ≤ ‖x‖ ∧ ‖x‖ ≤ a + b} :=
  (planarTwoLink_reachableWorkspace_subset ha.le hb.le).antisymm
    (planarTwoLink_annulus_subset_reachableWorkspace ha hb)

/-! ### Design certificates -/

/-- **Design certificate (position reachability).** For positive link lengths `a, b` and any
task region `W` of points in the plane `x₃ = 0` whose distances from the base origin lie in
`[|a - b|, a + b]`, every point of `W` is the tool position of some joint vector:
`∀ x ∈ W, ∃ q, planarTwoLinkPosition a b q = x`, the quantified certificate
`∀ x ∈ W, ∃ q ∈ Q_d, FK_d(q) = x` of `research/reports/mls-lean-assessment.md` ("Robot design
and workspace coverage") with unrestricted joints. This is a design statement, not a result
printed in MLS; it certifies position reachability of the ideal model only, not orientation,
collision avoidance, a continuous path or dynamic feasibility. -/
theorem planarTwoLink_workspace_certificate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (W : Set Vec3)
    (hW : ∀ x ∈ W, x 2 = 0 ∧ |a - b| ≤ ‖x‖ ∧ ‖x‖ ≤ a + b) :
    ∀ x ∈ W, ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x := fun x hx =>
  exists_planarTwoLinkPosition_eq ha hb (hW x hx).1 (hW x hx).2.1 (hW x hx).2.2

/-- **The certificate condition is necessary and sufficient.** For positive link lengths, a
task region `W` lies in the reachable workspace (MLS eq. (3.12), p. 95) of the planar two-link
arm with unrestricted joints exactly when every point of `W` lies in the plane `x₃ = 0` with
`|a - b| ≤ ‖x‖ ≤ a + b`. Source of the annulus and certificate:
`research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage" (a design
statement, not an MLS theorem). -/
theorem planarTwoLink_subset_reachableWorkspace_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (W : Set Vec3) :
    W ⊆ (planarTwoLink a b).reachableWorkspace Set.univ ↔
      ∀ x ∈ W, x 2 = 0 ∧ |a - b| ≤ ‖x‖ ∧ ‖x‖ ≤ a + b := by
  rw [planarTwoLink_reachableWorkspace_eq ha hb]
  rfl

/-- **Radial-band certificate.** For positive link lengths `a, b` and radii `r₁, r₂` with
`|a - b| ≤ r₁` and `r₂ ≤ a + b`, every point of the plane `x₃ = 0` with `r₁ ≤ ‖x‖ ≤ r₂` is the
tool position of some joint vector of the planar two-link arm: a prescribed radial band inside
the annulus bounds is reachable. Source: `research/reports/mls-lean-assessment.md`, "Robot
design and workspace coverage" ("check that a prescribed radial band lies within those
bounds"), a design statement rather than an MLS theorem; position reachability only. -/
theorem planarTwoLink_radialBand_certificate {a b r₁ r₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : |a - b| ≤ r₁) (h₂ : r₂ ≤ a + b) (x : Vec3) (hx : x 2 = 0) (hx₁ : r₁ ≤ ‖x‖)
    (hx₂ : ‖x‖ ≤ r₂) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x :=
  exists_planarTwoLinkPosition_eq ha hb hx (h₁.trans hx₁) (hx₂.trans h₂)

/-! ### Zero radius and equal link lengths -/

/-- **Zero radius.** For positive link lengths, the base origin belongs to the reachable
workspace (MLS eq. (3.12), p. 95) of the planar two-link arm with unrestricted joints exactly
when the links have equal length, `a = b`. A consequence of the annulus characterization of
`research/reports/mls-lean-assessment.md` ("Robot design and workspace coverage"), a design
statement rather than an MLS theorem. -/
theorem zero_mem_planarTwoLink_reachableWorkspace_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : Vec3) ∈ (planarTwoLink a b).reachableWorkspace Set.univ ↔ a = b := by
  rw [planarTwoLink_reachableWorkspace_eq ha hb, Set.mem_ofPred_eq, norm_zero, abs_nonpos_iff,
    sub_eq_zero]
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨rfl, h, by linarith⟩

/-- **Equal link lengths.** For `a = b > 0` the reachable workspace (MLS eq. (3.12), p. 95) of
the planar two-link arm with unrestricted joints is the closed disk `‖x‖ ≤ 2a` of the plane
`x₃ = 0`, base origin included ("equal lengths allow the base-centered disk of radius `a + b`",
`research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage"; a design
statement, not an MLS theorem). -/
theorem planarTwoLink_reachableWorkspace_eq_disk {a : ℝ} (ha : 0 < a) :
    (planarTwoLink a a).reachableWorkspace Set.univ = {x : Vec3 | x 2 = 0 ∧ ‖x‖ ≤ a + a} := by
  rw [planarTwoLink_reachableWorkspace_eq ha ha]
  ext x
  simp only [Set.mem_ofPred_eq, sub_self, abs_zero, norm_nonneg, true_and]

/-- **The origin is reached only at the folded configurations.** For equal nonzero link
lengths `a = b`, the tool position of the planar two-link arm (MLS eq. (3.4), p. 89,
specialized) is the base origin exactly when `cos θ₂ = -1`, i.e. the second link folds back
onto the first (`θ₂ ≡ π`), for every `θ₁`. These are the configurations that the assessment
(`research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage") calls
singular; reachability of the origin is not dexterity there. Only the position condition is
proved here, no Jacobian rank statement. -/
theorem planarTwoLinkPosition_eq_zero_iff {a : ℝ} (ha : a ≠ 0) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a a q = 0 ↔ Real.cos (q 1) = -1 := by
  have hsq := planarTwoLinkPosition_norm_sq a a q
  have ha2 : 0 < a ^ 2 := by positivity
  rw [← norm_eq_zero, ← sq_eq_zero_iff, hsq]
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-- Convention check (one exact instance, not a general result): for `a = b = 1` the joint
vector `q = (-π/2, π/2)` puts the tool of the planar two-link arm (MLS eq. (3.4), p. 89,
specialized) at `(1, 1, 0)`, a point at distance `√2` from the base origin. -/
example : planarTwoLinkPosition 1 1 ![-(Real.pi / 2), Real.pi / 2] = vec 1 1 0 := by
  rw [planarTwoLinkPosition_eq]
  ext i
  fin_cases i <;> simp [vec]

end RoboLean.Examples
