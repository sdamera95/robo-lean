import RoboLean.Grasp.Contact
import RoboLean.Grasp.ForceClosure

/-!
# The contact map and the grasp map

MLS Chapter 5, §2.2, printed pp. 218–222. Contact `i` applies `F_{cᵢ} = B_{cᵢ} f_{cᵢ}` at the origin
of its contact frame `Cᵢ`, written in `Cᵢ`; in object coordinates this is
`F_o = Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ} f_{cᵢ}` (p. 218), so the contact map is
`Gᵢ := Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ}`.
With `k` contacts, wrenches written in the one object frame superpose, and the grasp map is
`G = [Ad_{g_{oc₁}⁻¹}ᵀ B_{c₁} ⋯ Ad_{g_{oc_k}⁻¹}ᵀ B_{c_k}]` (eq. (5.6), p. 219), with
`F_o = G f_c`, `f_c ∈ FC = FC_{c₁} × ⋯ × FC_{c_k}` (eq. (5.7), pp. 219–220).

Representation (the brief's design question Q2). `ContactGrasp W ι m` holds, for each contact
`i : ι`, a contact model (`ContactModel W (m i)`) and the linear wrench transformation from its
contact frame to the object frame. The grasp map is a real linear map on the contact force space
`(i : ι) → Fin (m i) → ℝ` (the book's `f_c = (f_{c₁}, …, f_{c_k})`); its friction cone is the
product cone `FrictionCone.pi`. `ContactGrasp.spatial` builds the spatial grasp from contact frames
`g_{ocᵢ} : RigidTransform`, with transformation `Wrench.transform g_{ocᵢ}`, which the library
identifies with `Ad_{g_{ocᵢ}⁻¹}ᵀ` (`Wrench.transformMatrix_eq_adjointMatrix_inv_transpose`);
`ContactGrasp.planar` builds the planar grasp of Example 5.3 with the planar rule of p. 222. The
`p × m` matrix of the book is the derived view `ContactGrasp.matrix`, with columns indexed by
`Σ i, Fin (m i)` in the stacked order of `f_c`, and `matrix_mulVec` is the bridge.

Superposition presupposes that all contacts act on one rigid object (MLS p. 214), at fixed contact
locations; the types do not enforce it.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- A grasp with fixed contacts, MLS §2.2, printed pp. 218–220: `k` contacts indexed by a finite
type `ι`; contact `i` has a contact model `(B_{cᵢ}, FC_{cᵢ})` with `m i` force coefficients and the
real linear wrench transformation from its contact frame to the object frame (for spatial grasps
`Ad_{g_{ocᵢ}⁻¹}ᵀ`, `ContactGrasp.spatial`; for planar grasps the rule of p. 222,
`ContactGrasp.planar`). -/
structure ContactGrasp (W : Type*) [AddCommGroup W] [Module ℝ W] (ι : Type*) [Fintype ι]
    (m : ι → ℕ) where
  /-- The contact model of contact `i`, MLS printed p. 218. -/
  model : (i : ι) → ContactModel W (m i)
  /-- The wrench transformation from contact frame `Cᵢ` to the object frame `O`, MLS printed
  p. 218 (`Ad_{g_{ocᵢ}⁻¹}ᵀ` for a spatial grasp). -/
  transfer : ι → (W →ₗ[ℝ] W)

namespace ContactGrasp

variable {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι] {m : ι → ℕ}

/-- The contact map `Gᵢ := Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ}`, MLS printed p. 218: contact force coefficients
of contact `i` to the object wrench they produce, in object coordinates. -/
def contactMap (g : ContactGrasp W ι m) (i : ι) : (Fin (m i) → ℝ) →ₗ[ℝ] W :=
  g.transfer i ∘ₗ (g.model i).wrench

/-- The contact map applies the wrench basis, then the frame transformation (MLS printed
p. 218). -/
theorem contactMap_apply (g : ContactGrasp W ι m) (i : ι) (f : Fin (m i) → ℝ) :
    g.contactMap i f = g.transfer i ((g.model i).wrench f) := rfl

/-- The grasp map `G = [G₁ ⋯ G_k]`, MLS eq. (5.6), printed p. 219, as a real linear map from the
contact force space `f_c = (f_{c₁}, …, f_{c_k})` to object wrenches. -/
def graspMap (g : ContactGrasp W ι m) : ((i : ι) → Fin (m i) → ℝ) →ₗ[ℝ] W :=
  ∑ i, g.contactMap i ∘ₗ LinearMap.proj i

/-- MLS printed p. 219: the net object wrench is `F_o = G₁ f_{c₁} + ⋯ + G_k f_{c_k}`, the sum of
the contact wrenches transformed to the object frame. -/
theorem graspMap_apply (g : ContactGrasp W ι m) (f : (i : ι) → Fin (m i) → ℝ) :
    g.graspMap f = ∑ i, g.contactMap i (f i) := by
  simp [graspMap, LinearMap.sum_apply]

/-- The grasp map on the forces of one contact alone is that contact's contact map (MLS
eq. (5.6), printed p. 219: the `i`-th block of `G` is `Gᵢ`). -/
theorem graspMap_single [DecidableEq ι] (g : ContactGrasp W ι m) (i : ι) (f : Fin (m i) → ℝ) :
    g.graspMap (Pi.single i f) = g.contactMap i f := by
  rw [graspMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- The friction cone of the grasp, `FC = FC_{c₁} × ⋯ × FC_{c_k}`, MLS printed p. 220 (after
eq. (5.7)): a friction cone again (Definition 5.1). -/
def cone (g : ContactGrasp W ι m) : FrictionCone ((i : ι) → Fin (m i) → ℝ) :=
  FrictionCone.pi fun i => (g.model i).cone

/-- Contact forces lie in the grasp's friction cone exactly when each contact's forces lie in its
own cone, MLS printed p. 220. -/
@[simp] theorem mem_cone (g : ContactGrasp W ι m) {f : (i : ι) → Fin (m i) → ℝ} :
    f ∈ g.cone ↔ ∀ i, f i ∈ (g.model i).cone :=
  FrictionCone.mem_pi _

/-- Contact forces lie in the interior of the grasp's friction cone exactly when each contact's
forces lie in the interior of its own cone (MLS printed pp. 220 and 223, `int(FC)`). -/
theorem mem_interior_cone (g : ContactGrasp W ι m) {f : (i : ι) → Fin (m i) → ℝ} :
    f ∈ interior (g.cone : Set ((i : ι) → Fin (m i) → ℝ)) ↔
      ∀ i, f i ∈ interior ((g.model i).cone : Set (Fin (m i) → ℝ)) :=
  FrictionCone.mem_interior_pi _

/-- The grasp `(G, FC)` of a contact grasp, MLS Definition 5.1, printed p. 220: grasp map (5.6)
and product friction cone. -/
def toGrasp (g : ContactGrasp W ι m) : Grasp ((i : ι) → Fin (m i) → ℝ) W :=
  ⟨g.graspMap, g.cone⟩

/-- The grasp map of `toGrasp` is the grasp map (5.6) (MLS printed p. 220). -/
@[simp] theorem toGrasp_map (g : ContactGrasp W ι m) : g.toGrasp.map = g.graspMap := rfl

/-- The friction cone of `toGrasp` is the product cone (MLS printed p. 220). -/
@[simp] theorem toGrasp_cone (g : ContactGrasp W ι m) : g.toGrasp.cone = g.cone := rfl

/-- The stacked contact force vector `f_c = (f_{c₁}, …, f_{c_k}) ∈ ℝ^m`, `m = m₁ + ⋯ + m_k`, MLS
printed p. 220: coefficient `j` of contact `i` is entry `⟨i, j⟩` of a vector indexed by
`Σ i, Fin (m i)`. -/
def stack : ((i : ι) → Fin (m i) → ℝ) ≃ₗ[ℝ] ((Σ i, Fin (m i)) → ℝ) :=
  (LinearEquiv.piCurry ℝ fun (i : ι) (_ : Fin (m i)) => ℝ).symm

omit [Fintype ι] in
/-- Entry `⟨i, j⟩` of the stacked vector is coefficient `j` of contact `i` (MLS printed
p. 220). -/
@[simp] theorem stack_apply (f : (i : ι) → Fin (m i) → ℝ) (c : Σ i, Fin (m i)) :
    stack f c = f c.1 c.2 := rfl

/-- The grasp map as a real `p × m` matrix, MLS eq. (5.6), printed p. 219 (`G ∈ ℝ^{p×m}`), in the
wrench coordinates `e : W →ₗ (κ → ℝ)` (for spatial grasps `Wrench.coordinatesEquiv`, six rows
force first; for planar grasps the identity): column `⟨i, j⟩` holds the coordinates of `Gᵢ eⱼ`. -/
def matrix {κ : Type*} [DecidableEq ι] (g : ContactGrasp W ι m) (e : W →ₗ[ℝ] (κ → ℝ)) :
    Matrix κ (Σ i, Fin (m i)) ℝ :=
  LinearMap.toMatrix' (e ∘ₗ g.graspMap ∘ₗ stack.symm.toLinearMap)

/-- Column `⟨i, j⟩` of the grasp matrix is the `j`-th column of the contact map `Gᵢ`, MLS
eq. (5.6), printed p. 219, `G = [G₁ ⋯ G_k]`. -/
theorem matrix_apply {κ : Type*} [DecidableEq ι] (g : ContactGrasp W ι m)
    (e : W →ₗ[ℝ] (κ → ℝ)) (r : κ) (c : Σ i, Fin (m i)) :
    g.matrix e r c = e (g.contactMap c.1 (Pi.single c.2 1)) r := by
  rw [matrix, LinearMap.toMatrix'_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  change e (g.graspMap ((LinearEquiv.piCurry ℝ _) (Pi.single c 1))) r = _
  rw [LinearEquiv.piCurry_apply, Sigma.curry_single (γ := fun _ _ => ℝ), graspMap_single]

/-- **The matrix bridge**, MLS eqs. (5.6)–(5.7), printed pp. 219–220: the grasp matrix applied to
the stacked contact force vector is the coordinate vector of `F_o = G f_c`. -/
theorem matrix_mulVec {κ : Type*} [DecidableEq ι] (g : ContactGrasp W ι m)
    (e : W →ₗ[ℝ] (κ → ℝ)) (f : (i : ι) → Fin (m i) → ℝ) :
    g.matrix e *ᵥ stack f = e (g.graspMap f) := by
  rw [matrix, LinearMap.toMatrix'_mulVec]
  simp

/-! ### Spatial grasps -/

/-- The spatial grasp with contact models `(B_{cᵢ}, FC_{cᵢ})` and contact frames
`g_{ocᵢ} = (p_{ocᵢ}, R_{ocᵢ})`, MLS printed pp. 214–219: contact `i`'s wrench is carried to the
object frame by `Wrench.transform g_{ocᵢ}`, the book's `Ad_{g_{ocᵢ}⁻¹}ᵀ` (p. 218; library
`Wrench.transformMatrix_eq_adjointMatrix_inv_transpose`). Convention: `g_{ocᵢ}` takes contact
coordinates to object coordinates; the contact `z`-axis is the inward normal (p. 214–215). -/
def spatial (model : (i : ι) → ContactModel Wrench (m i)) (frame : ι → RigidTransform) :
    ContactGrasp Wrench ι m where
  model := model
  transfer i := Wrench.transformLinearMap (frame i)

/-- The spatial contact map `Gᵢ f = Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ} f`, MLS printed p. 218, with the
library's coordinate-free wrench transfer. -/
theorem spatial_contactMap_apply (model : (i : ι) → ContactModel Wrench (m i))
    (frame : ι → RigidTransform) (i : ι) (f : Fin (m i) → ℝ) :
    (spatial model frame).contactMap i f = Wrench.transform (frame i) ((model i).wrench f) := rfl

/-- The spatial contact map in matrices, MLS printed p. 218: `Gᵢ = Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ}`, with
`Ad` the `6 × 6` adjoint matrix of MLS eq. (2.58) and `B_{cᵢ}` the `6 × mᵢ` wrench basis
(`ContactModel.basisMatrix`); wrench coordinates force first. -/
theorem coordinates_spatial_contactMap (model : (i : ι) → ContactModel Wrench (m i))
    (frame : ι → RigidTransform) (i : ι) (f : Fin (m i) → ℝ) :
    ((spatial model frame).contactMap i f).coordinates =
      ((Twist.adjointMatrix (frame i)⁻¹)ᵀ * (model i).basisMatrix) *ᵥ f := by
  rw [spatial_contactMap_apply, Wrench.coordinates_transform, ← Matrix.mulVec_mulVec,
    ContactModel.basisMatrix_mulVec]

/-- **MLS eqs. (5.6)–(5.7), printed pp. 219–220**: the spatial grasp map applied to contact forces
`f_c` is the net wrench `Wrench.net` of the contact wrenches `B_{cᵢ} f_{cᵢ}`, each transferred from
its contact frame to the object frame before summing (the superposition "as long as they are all
written in the same coordinate frame", p. 219; library `Wrench.net`, MLS p. 63). -/
theorem spatial_graspMap_eq_net (model : (i : ι) → ContactModel Wrench (m i))
    (frame : ι → RigidTransform) (f : (i : ι) → Fin (m i) → ℝ) :
    (spatial model frame).graspMap f =
      Wrench.net Finset.univ frame fun i => (model i).wrench (f i) := by
  rw [graspMap_apply]
  rfl

/-- **MLS Example 5.1, printed p. 220**: a frictionless point contact with frame
`g_{oc} = (p_c, R_c)` applies the object wrench `(n_c; p_c × n_c) f_c` (`Wrench.pointForce p_c n_c`
scaled by `f_c`), where `n_c = R_c e_z` is the contact normal in object coordinates (inward, by
the frame convention of p. 214–215). -/
theorem spatial_frictionless_contactMap (frame : ι → RigidTransform) (i : ι) (f : Fin 1 → ℝ) :
    (spatial (fun _ => ContactModel.frictionless) frame).contactMap i f =
      f 0 • Wrench.pointForce (frame i).translation ((frame i).rotation.act Rotation.zAxis) := by
  rw [spatial_contactMap_apply, ContactModel.wrench_apply, Fin.sum_univ_one,
    Wrench.transform_smul]
  congr 1
  apply Wrench.ext
  · simp [ContactModel.frictionless]
  · simp [ContactModel.frictionless]

/-- **MLS Example 5.1, printed p. 220**: for frictionless point contacts the grasp map is
`G f_c = ∑ᵢ f_{cᵢ} (n_{cᵢ}; p_{cᵢ} × n_{cᵢ})`, i.e. `G = [n_{c₁} ⋯ n_{c_k}; p_{c₁} × n_{c₁} ⋯
p_{c_k} × n_{c_k}]`, with `n_{cᵢ} = R_{cᵢ} e_z` the (inward) contact normal in object
coordinates. -/
theorem spatial_frictionless_graspMap (frame : ι → RigidTransform) (f : ι → Fin 1 → ℝ) :
    (spatial (fun _ => ContactModel.frictionless) frame).graspMap f =
      ∑ i, f i 0 •
        Wrench.pointForce (frame i).translation ((frame i).rotation.act Rotation.zAxis) := by
  rw [graspMap_apply]
  exact Finset.sum_congr rfl fun i _ => spatial_frictionless_contactMap frame i (f i)

/-! ### Planar grasps -/

/-- The planar grasp of MLS Example 5.3, printed p. 222: contact `i` has a planar contact model
(wrenches `(f_x, f_y, τ)`), orientation `R_{cᵢ} ∈ SO(2)` and position `p_{cᵢ} ∈ ℝ²` relative to the
object frame; its wrench is carried to the object frame by the printed planar rule
`Planar.wrenchTransform`. Convention (p. 222): the contact `y`-axis is the inward normal. -/
def planar (model : (i : ι) → ContactModel (Fin 3 → ℝ) (m i))
    (R : ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : ι → Fin 2 → ℝ) :
    ContactGrasp (Fin 3 → ℝ) ι m where
  model := model
  transfer i := (Planar.wrenchTransform (R i) (p i)).mulVecLin

/-- The planar contact map, MLS Example 5.3, printed p. 222: `Gᵢ f = [[R, 0], [[-p_y, p_x] R, 1]]
B_{cᵢ} f`. -/
theorem planar_contactMap_apply (model : (i : ι) → ContactModel (Fin 3 → ℝ) (m i))
    (R : ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : ι → Fin 2 → ℝ) (i : ι)
    (f : Fin (m i) → ℝ) :
    (planar model R p).contactMap i f =
      Planar.wrenchTransform (R i) (p i) *ᵥ (model i).wrench f := rfl

/-- **The planar grasp map is the spatial grasp map restricted to the plane** (MLS Example 5.3,
printed p. 222, "we specialize our results to SE(2)"): embedding the planar object wrench
`G f_c` as a spatial wrench gives the net (MLS p. 63) of the embedded contact wrenches, each
carried by the spatial frame change `([[R, 0], [0, 1]], (p_x, p_y, 0))`. -/
theorem embedWrench_planar_graspMap (model : (i : ι) → ContactModel (Fin 3 → ℝ) (m i))
    (R : ι → Matrix.specialOrthogonalGroup (Fin 2) ℝ) (p : ι → Fin 2 → ℝ)
    (f : (i : ι) → Fin (m i) → ℝ) :
    Planar.embedWrench ((planar model R p).graspMap f) =
      Wrench.net Finset.univ (fun i => Planar.rigidTransform (R i) (p i))
        fun i => Planar.embedWrench ((model i).wrench (f i)) := by
  rw [graspMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [planar_contactMap_apply, Planar.transform_embedWrench]

end ContactGrasp

end RoboLean
