import RoboLean.Grasp.SoftFingerAntipodal

/-!
# Theorem 5.7's printed "only if" fails at every torsional coefficient

MLS Chapter 5, §4.2, printed p. 233, Theorem 5.7: "A spatial grasp with two soft-finger contacts
is force-closure if and only if the line connecting the contact point lies inside both friction
cones." This file gives, for `μ = 1` and **every** torsional coefficient `γ > 0`, a two-soft-finger
grasp (eq. (5.4), p. 217) that is force-closure while the connecting line lies on the boundary of
the first friction cone, so not inside it; both inward normals face the other contact and the line
lies strictly inside the second cone. A small torsional coefficient therefore does not rescue the
printed "only if"; what fails is coplanarity of the two normals with the line
(`spatial_softFinger_lineInsideCones_of_isForceClosure` holds for coplanar normals at every `γ`).

Data (chosen here): contact 1 at the origin with the identity frame (normal `e_z`); contact 2 at
`(1, 0, 1)` with the rotation whose columns are `(6, 2, -3)/7`, `(3, -6, 2)/7`, `(-2, -3, -6)/7`
(normal `(-2, -3, -6)/7`, not in the plane of `e_z` and the line). For `τ = min (γ/2) 1` the
contact forces `F = (1 - 3τ/14, 2τ/7, 1 + 3τ/14)` and `-F`, with torsions `8τ/7` and `τ`, form a
strictly internal force (Definition 5.3, p. 223): the torsions balance the moment of the two
forces about the line, which tilts `F` into the open first cone.

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp

/-- The frame rotation of the second contact of the torsion instance (MLS Theorem 5.7, printed
p. 233): columns `(6, 2, -3)/7`, `(3, -6, 2)/7`, `(-2, -3, -6)/7`, a rotation (orthogonal with
determinant `1`); its third column is the inward normal (pp. 214–215). -/
def torsionRotation : Rotation :=
  ⟨!![6 / 7, 3 / 7, -2 / 7; 2 / 7, -6 / 7, -3 / 7; -3 / 7, 2 / 7, -6 / 7], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
    · simp [Matrix.det_fin_three]
      norm_num⟩

/-- The two contact frames of the torsion instance (MLS Theorem 5.7, printed p. 233): the identity
at the origin and `torsionRotation` at `(1, 0, 1)`. -/
def torsionFrame : Fin 2 → RigidTransform :=
  ![⟨1, WithLp.toLp 2 ![0, 0, 0]⟩, ⟨torsionRotation, WithLp.toLp 2 ![1, 0, 1]⟩]

/-- The two-soft-finger grasp of the torsion instance (MLS Theorem 5.7, printed p. 233):
soft-finger contacts (eq. (5.4), p. 217) with `μ = 1` and torsional coefficient `γ > 0` at
`torsionFrame`. -/
def torsionGrasp (γ : ℝ) (hγ : 0 < γ) : ContactGrasp Wrench (Fin 2) fun _ => 4 :=
  ContactGrasp.spatial (fun _ => ContactModel.softFinger 1 γ one_pos hγ) torsionFrame

/-- The grasp map of the torsion instance (MLS Theorem 5.7, printed p. 233) in force and moment
form, computed with the wrench transfer (2.66). -/
private theorem torsionGrasp_graspMap (γ : ℝ) (hγ : 0 < γ) (f : Fin 2 → Fin 4 → ℝ) :
    (torsionGrasp γ hγ).graspMap f =
      ⟨WithLp.toLp 2 ![f 0 0 + (6 * f 1 0 + 3 * f 1 1 - 2 * f 1 2) / 7,
          f 0 1 + (2 * f 1 0 - 6 * f 1 1 - 3 * f 1 2) / 7,
          f 0 2 + (-3 * f 1 0 + 2 * f 1 1 - 6 * f 1 2) / 7],
        WithLp.toLp 2 ![-(2 * f 1 0 - 6 * f 1 1 - 3 * f 1 2) / 7 - 2 * f 1 3 / 7,
          (9 * f 1 0 + f 1 1 + 4 * f 1 2) / 7 - 3 * f 1 3 / 7,
          f 0 3 + (2 * f 1 0 - 6 * f 1 1 - 3 * f 1 2) / 7 - 6 * f 1 3 / 7]⟩ := by
  rw [ContactGrasp.graspMap_apply, Fin.sum_univ_two, torsionGrasp,
    ContactGrasp.spatial_contactMap_apply, ContactGrasp.spatial_contactMap_apply,
    ContactModel.softFinger_wrench, ContactModel.softFinger_wrench]
  apply Wrench.ext
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, torsionFrame, torsionRotation,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, Vec3.cross_coordinates, crossProduct,
        torsionFrame, torsionRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The torsion instance (MLS Theorem 5.7, printed p. 233) is force-closure for every torsional
coefficient `γ > 0` (Proposition 5.2, p. 224). -/
theorem torsionGrasp_isForceClosure (γ : ℝ) (hγ : 0 < γ) :
    (torsionGrasp γ hγ).toGrasp.IsForceClosure := by
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = min (γ / 2) 1 := ⟨_, rfl⟩
  have hτ0 : 0 < τ := hτ ▸ lt_min (by linarith) one_pos
  have hτ1 : τ ≤ 1 := hτ ▸ min_le_right _ _
  have hτγ : τ ≤ γ / 2 := hτ ▸ min_le_left _ _
  rw [Grasp.isForceClosure_iff]
  refine ⟨?_, ![![1 - 3 * τ / 14, 2 * τ / 7, 1 + 3 * τ / 14, 8 * τ / 7],
    ![(-3 + 19 * τ / 14) / 7, (-5 + 27 * τ / 14) / 7, (8 + 12 * τ / 7) / 7, τ]], ?_, ?_⟩
  · intro W
    refine ⟨![![W.force 0 - W.torque 1, W.force 1 + W.torque 0, W.force 2,
      W.torque 2 + W.torque 0],
      ![(6 * W.torque 1 - 2 * W.torque 0) / 7, (3 * W.torque 1 + 6 * W.torque 0) / 7,
        (-2 * W.torque 1 + 3 * W.torque 0) / 7, 0]], ?_⟩
    rw [ContactGrasp.toGrasp_map, torsionGrasp_graspMap]
    apply Wrench.ext
    · ext i
      fin_cases i <;> simp <;> ring
    · ext i
      fin_cases i <;> simp <;> ring
  · rw [ContactGrasp.toGrasp_map, torsionGrasp_graspMap]
    apply Wrench.ext
    · ext i
      fin_cases i <;> simp <;> ring
    · ext i
      fin_cases i <;> simp <;> ring
  · rw [ContactGrasp.toGrasp_cone, ContactGrasp.mem_interior_cone]
    intro i
    fin_cases i
    · refine mem_interior_softFingerCone ?_ ?_ ?_
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [Real.sqrt_lt' (by positivity)]
        nlinarith
      · simp
        positivity
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        rw [abs_of_pos (by positivity)]
        nlinarith
    · refine mem_interior_softFingerCone ?_ ?_ ?_
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [Real.sqrt_lt' (by positivity)]
        nlinarith
      · simp
        positivity
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        rw [abs_of_pos hτ0]
        nlinarith

/-- **MLS Theorem 5.7, printed "only if", fails at every torsional coefficient** (printed
p. 233): for `μ = 1` and every `γ > 0` the torsion instance is force-closure, both inward normals
face the other contact, and the connecting line, written in the first contact frame as
`(1, 0, 1)`, is not inside the open friction cone there (it lies on its boundary). -/
theorem softAntipodal_onlyIf_fails (γ : ℝ) (hγ : 0 < γ) :
    (torsionGrasp γ hγ).toGrasp.IsForceClosure ∧
      0 ≤ contactDirection torsionFrame 0 1 2 ∧ 0 ≤ contactDirection torsionFrame 1 0 2 ∧
      ¬ √(contactDirection torsionFrame 0 1 0 ^ 2 + contactDirection torsionFrame 0 1 1 ^ 2) <
        1 * contactDirection torsionFrame 0 1 2 := by
  have e0 : ∀ k, contactDirection torsionFrame 0 1 k = ![1, 0, 1] k := by
    intro k
    fin_cases k <;> simp [contactDirection, torsionFrame, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  have e1 : contactDirection torsionFrame 1 0 2 = 8 / 7 := by
    simp [contactDirection, torsionFrame, torsionRotation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
    norm_num
  refine ⟨torsionGrasp_isForceClosure γ hγ, ?_, ?_, ?_⟩
  · rw [e0]
    simp
  · rw [e1]
    norm_num
  · rw [e0, e0, e0]
    simp

end RoboLean.Examples
