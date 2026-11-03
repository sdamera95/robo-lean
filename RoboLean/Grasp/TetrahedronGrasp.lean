import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import RoboLean.Grasp.SpatialGrasp

/-!
# A tetrahedron that three fingers with friction `μ = tan 15°` cannot grasp (MLS Exercise 5(b))

MLS Chapter 5, Exercise 5(b), printed p. 260: "Construct a 3-D object which cannot be grasped by
three point-contact-with-friction fingers and `µ = tan 15°`. Prove explicitly that the object
cannot be grasped", with "vertex contacts are not allowed" (Exercise 5, verifying the lower
bounds of Table 5.3).

**Formalized.** The object is the regular tetrahedron
`T = {x : ⟨vₖ, x⟩ ≥ −1 for k = 0, …, 3}` with `v₀ = (1, 1, 1)`, `v₁ = (1, −1, −1)`,
`v₂ = (−1, 1, −1)`, `v₃ = (−1, −1, 1)` (`tetrahedron`); its face `k` lies in the plane
`⟨vₖ, x⟩ = −1` and has the inward unit normal `vₖ/√3` (`tetraNormal`). A point contact with
friction on face `k` has a contact frame whose `z`-axis is that inward normal (MLS p. 214); its
position is not used.

* For any finite set of point contacts with friction `0 < μ ≤ 1/3` whose normals avoid one face
  `j`, the grasp is not force-closure, wherever the contacts are
  (`not_isForceClosure_of_normal_ne`): every contact force has a nonnegative component along
  `−vⱼ`, so the net force cannot be `vⱼ`.
* Three contacts touch at most three of the four faces, so three point contacts with friction
  `0 < μ ≤ 1/3` on faces of `T` never form a force-closure grasp
  (`tetrahedron_three_not_isForceClosure`); `tan 15° ≤ 1/3` (`tan_pi_div_twelve_le`), so this is
  Exercise 5(b) with the printed coefficient (`tetrahedron_three_not_isForceClosure_tan15`).

Reading. "Vertex contacts are not allowed" is read as contacts on the faces with the face
normals; a contact on an edge, whose normal is not determined by the surface, is not covered.
The bound `μ ≤ 1/3` is a convenient sufficient condition (the argument works for
`μ < 1/(2√2)`). Force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214); nothing here concerns a physical object.
-/

noncomputable section

open Real Matrix

namespace RoboLean

namespace Grasp

/-- The vertices `(1, 1, 1)`, `(1, −1, −1)`, `(−1, 1, −1)`, `(−1, −1, 1)` of the regular tetrahedron
used for MLS Chapter 5, Exercise 5(b), printed p. 260. -/
def tetraVertex : Fin 4 → Vec3 :=
  ![WithLp.toLp 2 ![1, 1, 1], WithLp.toLp 2 ![1, -1, -1], WithLp.toLp 2 ![-1, 1, -1],
    WithLp.toLp 2 ![-1, -1, 1]]

/-- The regular tetrahedron `{x : ⟨vₖ, x⟩ ≥ −1, k = 0, …, 3}` (MLS Chapter 5, Exercise 5(b), printed
p. 260): the convex hull of `tetraVertex`, with face `k` in the plane `⟨vₖ, x⟩ = −1`. -/
def tetrahedron : Set Vec3 := {x | ∀ k, -1 ≤ inner ℝ (tetraVertex k) x}

/-- The inward unit normal `vₖ/√3` of face `k` of `tetrahedron` (MLS Exercise 5(b), p. 260; the
contact `z`-axis of MLS p. 214). -/
def tetraNormal (k : Fin 4) : Vec3 := (√3)⁻¹ • tetraVertex k

/-- Each vertex of `tetrahedron` lies on the three faces not opposite to it (MLS Exercise 5(b),
p. 260): `⟨vₖ, vⱼ⟩ = −1` for `j ≠ k`, and `⟨vₖ, vₖ⟩ = 3`. -/
theorem inner_tetraVertex (j k : Fin 4) :
    inner ℝ (tetraVertex k) (tetraVertex j) = if j = k then 3 else -1 := by
  fin_cases j <;> fin_cases k <;>
    simp [tetraVertex, PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.real_norm_sq_eq] <;>
    norm_num

/-- The vertices belong to `tetrahedron` (MLS Exercise 5(b), p. 260). -/
theorem tetraVertex_mem (j : Fin 4) : tetraVertex j ∈ tetrahedron := by
  intro k
  rw [inner_tetraVertex]
  split_ifs <;> norm_num

/-- `tetraNormal k` is a unit vector (MLS Exercise 5(b), p. 260). -/
theorem norm_tetraNormal (k : Fin 4) : ‖tetraNormal k‖ = 1 := by
  have h3 : ‖tetraVertex k‖ = √3 := by
    rw [norm_eq_sqrt_real_inner, inner_tetraVertex]
    simp
  rw [tetraNormal, norm_smul, h3, norm_inv, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'

/-- **MLS Chapter 5, Exercise 5(b), printed p. 260, the key step.** Point contacts with friction
`0 < μ ≤ 1/3` whose contact normals (the `z`-axes of their frames) are inward face normals of the
regular tetrahedron other than face `j` never form a force-closure grasp, wherever they are
placed. -/
theorem not_isForceClosure_of_normal_ne {ι : Type*} [Fintype ι] (frame : ι → RigidTransform)
    (μ : ℝ) (hμ : 0 < μ) (hμ3 : μ ≤ 1 / 3) (j : Fin 4)
    (hn : ∀ i, ∃ k, k ≠ j ∧ ∀ a, (frame i).rotation.val a 2 = tetraNormal k a) :
    ¬ (SpatialGrasp.mk (fun _ => ContactModel.pointContact μ hμ) frame :
      SpatialGrasp ι fun _ => 3).toGrasp.IsForceClosure := by
  intro hfc
  set d : Vec3 := -tetraVertex j with hd
  obtain ⟨fc, hmem, hG⟩ := hfc ⟨d, 0⟩
  have hmem' : ∀ i, fc i ∈ (ContactModel.pointContact μ hμ).cone :=
    (SpatialGrasp.mem_cone _).mp hmem
  let L : Wrench →+ ℝ :=
    { toFun := fun w => inner ℝ d w.force
      map_zero' := by simp [Wrench.zero_force]
      map_add' := fun a b => by simp [inner_add_right] }
  have hsum : L ((SpatialGrasp.mk (fun _ => ContactModel.pointContact μ hμ) frame :
      SpatialGrasp ι fun _ => 3).graspMap fc) = ∑ i, L (Wrench.transform (frame i)
        ((ContactModel.pointContact μ hμ).wrench (fc i))) := by
    rw [SpatialGrasp.graspMap_apply, map_sum]
  have hneg : L ((SpatialGrasp.mk (fun _ => ContactModel.pointContact μ hμ) frame :
      SpatialGrasp ι fun _ => 3).graspMap fc) = -3 := by
    change inner ℝ d (SpatialGrasp.graspMap _ fc).force = -3
    have hf := congrArg Wrench.force hG
    rw [SpatialGrasp.toGrasp_map] at hf
    rw [hf]
    change inner ℝ d (-d) = -3
    simp only [hd, inner_neg_left, neg_neg, inner_tetraVertex]
    simp
  have hterm (i : ι) : 0 ≤ L (Wrench.transform (frame i)
      ((ContactModel.pointContact μ hμ).wrench (fc i))) := by
    obtain ⟨k, hkj, hk⟩ := hn i
    set R := (frame i).rotation
    set e : Vec3 := R⁻¹.act d with he
    have hu : ((ContactModel.pointContact μ hμ).wrench (fc i)).force =
        WithLp.toLp 2 ![fc i 0, fc i 1, fc i 2] := by
      rw [ContactModel.wrench_apply]
      ext a
      fin_cases a <;> simp [ContactModel.pointContact, Fin.sum_univ_three, Rotation.xAxis,
        Rotation.yAxis, Rotation.zAxis]
    have hL : L (Wrench.transform (frame i) ((ContactModel.pointContact μ hμ).wrench (fc i))) =
        e 0 * fc i 0 + e 1 * fc i 1 + e 2 * fc i 2 := by
      change inner ℝ d (R.act ((ContactModel.pointContact μ hμ).wrench (fc i)).force) = _
      rw [hu, ← Rotation.act_inv_act R d, Rotation.inner_act]
      simp [PiLp.inner_apply, Fin.sum_univ_three, he]
      ring
    have he2 : e 2 = (√3)⁻¹ := by
      rw [he]
      change (R⁻¹.val *ᵥ WithLp.ofLp d) 2 = _
      simp only [Rotation.inv_val, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Fin.sum_univ_three]
      rw [hk 0, hk 1, hk 2]
      fin_cases j <;> fin_cases k <;> simp_all [tetraNormal, tetraVertex]
    have hd3 : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 = 3 := by
      fin_cases j <;> simp [hd, tetraVertex] <;> norm_num
    have hnorm : e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 = 3 := by
      have h1 : ‖e‖ = ‖d‖ := by rw [he, Rotation.norm_act]
      have h2 := EuclideanSpace.real_norm_sq_eq e
      have h3 := EuclideanSpace.real_norm_sq_eq d
      rw [Fin.sum_univ_three] at h2 h3
      rw [← h2, h1, h3, hd3]
    obtain ⟨hc, h2⟩ := hmem' i
    have hs2 : ((√3)⁻¹) ^ 2 = 1 / 3 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hspos : 0 < (√3)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
    have hsq : fc i 0 ^ 2 + fc i 1 ^ 2 ≤ (μ * fc i 2) ^ 2 := by
      have h0 := Real.sqrt_nonneg (fc i 0 ^ 2 + fc i 1 ^ 2)
      have h4 := Real.sq_sqrt (by positivity : 0 ≤ fc i 0 ^ 2 + fc i 1 ^ 2)
      have h5 := pow_le_pow_left₀ h0 hc 2
      linarith
    have hcs : (e 0 * fc i 0 + e 1 * fc i 1) ^ 2 ≤
        (e 0 ^ 2 + e 1 ^ 2) * (fc i 0 ^ 2 + fc i 1 ^ 2) := by
      nlinarith [sq_nonneg (e 0 * fc i 1 - e 1 * fc i 0)]
    have he01 : e 0 ^ 2 + e 1 ^ 2 = 8 / 3 := by rw [he2] at hnorm; linarith
    have hμ2 : μ ^ 2 ≤ 1 / 9 := by nlinarith
    have hb : (e 0 * fc i 0 + e 1 * fc i 1) ^ 2 ≤ ((√3)⁻¹ * fc i 2) ^ 2 := by
      rw [mul_pow, hs2]
      rw [he01] at hcs
      have : (μ * fc i 2) ^ 2 ≤ 1 / 9 * fc i 2 ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hμ2 (sq_nonneg _)
      nlinarith
    have hab := (abs_le_of_sq_le_sq' hb (by positivity)).1
    rw [hL, he2]
    linarith
  have hnn := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← hsum, hneg] at hnn
  norm_num at hnn

/-- **MLS Chapter 5, Exercise 5(b), printed p. 260.** Three point contacts with friction
`0 < μ ≤ 1/3` on faces of the regular tetrahedron (contact normals inward face normals, no vertex
or edge contacts) never form a force-closure grasp. -/
theorem tetrahedron_three_not_isForceClosure (frame : Fin 3 → RigidTransform) (μ : ℝ)
    (hμ : 0 < μ) (hμ3 : μ ≤ 1 / 3)
    (hn : ∀ i, ∃ k, ∀ a, (frame i).rotation.val a 2 = tetraNormal k a) :
    ¬ (SpatialGrasp.mk (fun _ => ContactModel.pointContact μ hμ) frame :
      SpatialGrasp (Fin 3) fun _ => 3).toGrasp.IsForceClosure := by
  choose k hk using hn
  have hmiss : ∃ j, ∀ i, k i ≠ j := by
    by_contra hcon
    push Not at hcon
    have hcard := Fintype.card_le_of_surjective k fun j => hcon j
    simp at hcard
  obtain ⟨j, hj⟩ := hmiss
  exact not_isForceClosure_of_normal_ne frame μ hμ hμ3 j fun i => ⟨k i, hj i, hk i⟩

/-- `tan 15° ≤ 1/3` (the printed coefficient of MLS Exercise 5(b), p. 260, with
`15° = π/12`). -/
theorem tan_pi_div_twelve_le : tan (π / 12) ≤ 1 / 3 := by
  have hx0 : 0 ≤ π / 12 := by positivity
  have hx : π / 12 < 0.2625 := by linarith [pi_lt_d2]
  have hs := sin_le hx0
  have hc := one_sub_sq_div_two_le_cos (x := π / 12)
  have hcpos : 0 < cos (π / 12) :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  rw [tan_eq_sin_div_cos, div_le_iff₀ hcpos]
  nlinarith [mul_le_mul hx.le hx.le hx0 (by norm_num : (0 : ℝ) ≤ 0.2625)]

/-- **MLS Chapter 5, Exercise 5(b), printed p. 260, with the printed `μ = tan 15°`**: three point
contacts with friction on faces of the regular tetrahedron never form a force-closure grasp. -/
theorem tetrahedron_three_not_isForceClosure_tan15 (frame : Fin 3 → RigidTransform)
    (hn : ∀ i, ∃ k, ∀ a, (frame i).rotation.val a 2 = tetraNormal k a) :
    ¬ (SpatialGrasp.mk (fun _ => ContactModel.pointContact (tan (π / 12))
        (tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith [pi_pos]))) frame :
      SpatialGrasp (Fin 3) fun _ => 3).toGrasp.IsForceClosure :=
  tetrahedron_three_not_isForceClosure frame _ _ tan_pi_div_twelve_le hn

end Grasp

end RoboLean
