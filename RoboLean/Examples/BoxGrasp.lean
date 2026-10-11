import RoboLean.Grasp.GraspMap

/-!
# MLS Example 5.2: soft-finger grasp of a box

MLS printed p. 221 (Figure 5.5): a box grasped by two soft-finger contacts with contact frames
`g_{ocᵢ} = (p_{cᵢ}, R_{cᵢ})`,

`R_{c₁} = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]`, `p_{c₁} = (0, -r, 0)`,
`R_{c₂} = [[1, 0, 0], [0, 0, -1], [0, 1, 0]]`, `p_{c₂} = (0, r, 0)`,

soft-finger wrench bases and cones (eq. (5.4), p. 217), and the printed `6 × 8` grasp map. Here
the grasp is built from the printed frames with the library's `ContactGrasp.spatial` (wrench
transfer `Wrench.transform`, MLS (2.66)), and the printed matrix is checked against it, column
order `f_c = (f¹_{c₁}, …, f⁴_{c₁}, f¹_{c₂}, …, f⁴_{c₂})` as printed. MLS p. 242 states that this
grasp is force-closure ("From Example 5.2 we have that the grasp is force-closure"); Example 5.2
itself prints no such conclusion. Here it is proved from Proposition 5.2 with the strictly
internal force of equal normal forces `(0, 0, 1, 0, 0, 0, 1, 0)` and the surjectivity of `G`
for `r ≠ 0`, for every `μ, γ > 0`.

These are convention checks on concrete inputs and satisfying instances of the general
theorems. Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid
contacts (MLS p. 214); nothing here concerns a physical hand.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix

/-- The contact orientation `R_{c₁} = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]` of MLS Example 5.2, printed
p. 221, as a proper rotation (its third column `(0, 1, 0)` is the inward normal at
`p_{c₁} = (0, -r, 0)`). -/
def boxRotation₁ : Rotation :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- The contact orientation `R_{c₂} = [[1, 0, 0], [0, 0, -1], [0, 1, 0]]` of MLS Example 5.2, printed
p. 221, as a proper rotation (its third column `(0, -1, 0)` is the inward normal at
`p_{c₂} = (0, r, 0)`). -/
def boxRotation₂ : Rotation :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- The contact frames `g_{oc₁} = ((0, -r, 0), R_{c₁})` and `g_{oc₂} = ((0, r, 0), R_{c₂})` of MLS
Example 5.2, printed p. 221; `r` is half the box width. -/
def boxFrame (r : ℝ) : Fin 2 → RigidTransform :=
  ![⟨boxRotation₁, WithLp.toLp 2 ![0, -r, 0]⟩, ⟨boxRotation₂, WithLp.toLp 2 ![0, r, 0]⟩]

/-- The soft-finger grasp of a box, MLS Example 5.2, printed p. 221: two soft-finger contacts
(eq. (5.4), `μ > 0`, `γ > 0`) at the frames `boxFrame r`. -/
def boxGrasp (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) : ContactGrasp Wrench (Fin 2) fun _ => 4 :=
  ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ) (boxFrame r)

/-- The grasp map of MLS Example 5.2, printed p. 221, in force and moment form, computed from the
printed frames by the wrench transfer (2.66): contact 1 contributes force `(f₂, f₃, f₁)` and moment
`(-r f₁, f₄, r f₂)`, contact 2 force `(f₁, -f₃, f₂)` and moment `(r f₂, -f₄, -r f₁)` (book indices
`1, …, 4`; here `f i j` is coefficient `j` of contact `i`, indexed from `0`). -/
theorem boxGrasp_graspMap (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (f : Fin 2 → Fin 4 → ℝ) :
    (boxGrasp μ γ r hμ hγ).graspMap f =
      ⟨WithLp.toLp 2 ![f 0 1 + f 1 0, f 0 2 - f 1 2, f 0 0 + f 1 1],
        WithLp.toLp 2 ![-r * f 0 0 + r * f 1 1, f 0 3 - f 1 3, r * f 0 1 - r * f 1 0]⟩ := by
  rw [ContactGrasp.graspMap_apply, Fin.sum_univ_two, boxGrasp,
    ContactGrasp.spatial_contactMap_apply, ContactGrasp.spatial_contactMap_apply,
    ContactModel.softFinger_wrench, ContactModel.softFinger_wrench]
  apply Wrench.ext
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, boxFrame, boxRotation₁, boxRotation₂,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, Vec3.cross_coordinates, crossProduct, boxFrame,
        boxRotation₁, boxRotation₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The printed grasp map of MLS Example 5.2, printed p. 221, as a `6 × 8` matrix with force rows
(`Sum.inl`) above moment rows (`Sum.inr`) and columns in the printed order
`(f¹_{c₁}, …, f⁴_{c₁}, f¹_{c₂}, …, f⁴_{c₂})`. -/
def boxPrintedMatrix (r : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 8) ℝ :=
  Matrix.fromRows
    !![0, 1, 0, 0, 1, 0, 0, 0;
      0, 0, 1, 0, 0, 0, -1, 0;
      1, 0, 0, 0, 0, 1, 0, 0]
    !![-r, 0, 0, 0, 0, r, 0, 0;
      0, 0, 0, 1, 0, 0, 0, -1;
      0, r, 0, 0, -r, 0, 0, 0]

/-- **MLS Example 5.2, printed p. 221**: the grasp map computed from the printed frames by the
wrench transfer (2.66) is the printed `6 × 8` matrix applied to the stacked contact forces. -/
theorem boxGrasp_coordinates_graspMap (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (f : Fin 2 → Fin 4 → ℝ) :
    ((boxGrasp μ γ r hμ hγ).graspMap f).coordinates =
      boxPrintedMatrix r *ᵥ ![f 0 0, f 0 1, f 0 2, f 0 3, f 1 0, f 1 1, f 1 2, f 1 3] := by
  rw [boxGrasp_graspMap]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Wrench.coordinates, boxPrintedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The internal force of equal unit normal forces at both contacts,
`f_N = (0, 0, 1, 0, 0, 0, 1, 0)` (supporting the force-closure claim of MLS p. 242 for the grasp
of Example 5.2, printed p. 221). -/
def boxInternalForce : Fin 2 → Fin 4 → ℝ := ![![0, 0, 1, 0], ![0, 0, 1, 0]]

/-- Equal normal forces squeezing the box are a strictly internal force (MLS Definition 5.3,
printed p. 223) of the grasp of Example 5.2 (printed p. 221), for every `μ, γ > 0` and `r`. -/
theorem boxGrasp_isStrictlyInternalForce (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    Grasp.IsStrictlyInternalForce (boxGrasp μ γ r hμ hγ).graspMap
      ((boxGrasp μ γ r hμ hγ).cone : Set (Fin 2 → Fin 4 → ℝ)) boxInternalForce := by
  refine ⟨?_, ?_⟩
  · rw [boxGrasp_graspMap]
    apply Wrench.ext
    · ext i
      fin_cases i <;> simp [boxInternalForce]
    · ext i
      fin_cases i <;> simp [boxInternalForce]
  · rw [ContactGrasp.mem_interior_cone]
    intro i
    fin_cases i <;>
      exact Grasp.mem_interior_softFingerCone (by simpa [boxInternalForce] using hμ)
        (by simp [boxInternalForce]) (by simpa [boxInternalForce] using hγ)

/-- The grasp map of MLS Example 5.2 (printed p. 221) is surjective onto the wrenches when the
contacts are apart, `r ≠ 0`. -/
theorem boxGrasp_surjective (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hr : r ≠ 0) :
    Function.Surjective (boxGrasp μ γ r hμ hγ).graspMap := by
  intro F
  refine ⟨![![(F.force 2 - F.torque 0 / r) / 2, (F.force 0 + F.torque 2 / r) / 2, F.force 1,
      F.torque 1], ![(F.force 0 - F.torque 2 / r) / 2, (F.force 2 + F.torque 0 / r) / 2, 0, 0]],
    ?_⟩
  rw [boxGrasp_graspMap]
  apply Wrench.ext
  · ext i
    fin_cases i <;> simp <;> ring
  · ext i
    fin_cases i <;> simp <;> field_simp <;> ring

/-- **MLS p. 242, for the grasp of Example 5.2 (printed p. 221)**: the soft-finger grasp of the
box is force-closure, for every `μ, γ > 0` and `r ≠ 0`, by Proposition 5.2 (surjective grasp map
and a strictly internal force). Finite-force caveat: unbounded contact forces at maintained rigid
contacts (MLS p. 214); actuator limits are not considered. -/
theorem boxGrasp_isForceClosure (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hr : r ≠ 0) :
    (boxGrasp μ γ r hμ hγ).toGrasp.IsForceClosure :=
  (Grasp.isForceClosure_iff _).mpr
    ⟨boxGrasp_surjective μ γ r hμ hγ hr, _, boxGrasp_isStrictlyInternalForce μ γ r hμ hγ⟩

end RoboLean.Examples
