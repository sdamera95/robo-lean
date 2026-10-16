import RoboLean.Grasp.GraspMap
import RoboLean.Kinematics.ForcePullback

/-!
# Spatial grasps with contact frames, and the transpose of the grasp map

MLS Chapter 5, §2, printed pp. 214–219, with §5.1, printed pp. 235–236.

`SpatialGrasp ι m` keeps what a spatial grasp with fixed contacts is made of: for each contact
`i : ι` a spatial contact model `(B_{cᵢ}, FC_{cᵢ})` (MLS p. 218; Table 5.2, p. 219) and the contact
frame `g_{ocᵢ} = (p_{cᵢ}, R_{cᵢ})` (MLS pp. 214–215), which takes contact coordinates to object
coordinates. The contact grasp `ContactGrasp.spatial model frame` is derived from it
(`SpatialGrasp.toContactGrasp`), so the grasp map (5.6), the product friction cone and the grasp
`(G, FC)` of Definition 5.1 are those of `ContactGrasp`, unchanged; the bridge lemmas below restate
them in terms of the frames.

The velocity side. The constraint of a contact with wrench basis `B_c` on a twist `V` is
`B_cᵀ V` (MLS eq. (5.9), p. 235); here `ContactModel.constraint` (in `Grasp/Contact`, with its
surjectivity lemmas and its transpose identities `sum_constraint_mul`,
`basisMatrix_transpose_mulVec`, `frictionless_constraint`), whose coefficient `j` is the pairing
`f · v + τ · ω` (MLS p. 61) of basis column `j` with `V`. The transpose of the grasp map acts on
the object twist `V^b_{po}` by `Gᵢᵀ V = (Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ})ᵀ V = B_{cᵢ}ᵀ Ad_{g_{ocᵢ}⁻¹} V`
(MLS eq. (5.13), p. 236); here `SpatialGrasp.graspTranspose`. It is the transpose with respect to
the twist–wrench pairing on the object side and the dot product of coefficients on the contact
side (`sum_graspTranspose_mul`), and in six coordinates it is the matrix transpose of the grasp
matrix (`stack_graspTranspose`).

Conventions as in "Grasp and contact conventions" of `geometry-conventions.md`: wrench
order `(f, τ)`, twist order `(v, ω)`, contact `z`-axis along the inward normal (a convention
the types do not enforce), `Wrench.transform g_{oc}` is the book's `Ad_{g_{oc}⁻¹}ᵀ`. Rigid bodies,
fixed and maintained contacts and accurate models are standing assumptions (MLS p. 214); nothing
here claims that a physical contact behaves as modeled.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- A spatial grasp with fixed contacts that keeps its contact frames, MLS §2, printed
pp. 214–219: `k` contacts indexed by a finite type `ι`; contact `i` has a spatial contact model
`(B_{cᵢ}, FC_{cᵢ})` with `m i` force coefficients (MLS p. 218, Table 5.2, p. 219) and the contact
frame `g_{ocᵢ} = (p_{cᵢ}, R_{cᵢ})`, the pose of the contact frame `Cᵢ` relative to the object frame
`O` (MLS pp. 214–215: contact coordinates to object coordinates; the contact `z`-axis is the
inward normal, a convention the type does not enforce). The contact location is fixed on the
object (MLS p. 214). -/
structure SpatialGrasp (ι : Type*) [Fintype ι] (m : ι → ℕ) where
  /-- The contact model `(B_{cᵢ}, FC_{cᵢ})` of contact `i`, MLS printed p. 218. -/
  model : (i : ι) → ContactModel Wrench (m i)
  /-- The contact frame `g_{ocᵢ}` of contact `i` relative to the object frame, MLS printed
  p. 215. -/
  frame : ι → RigidTransform

namespace SpatialGrasp

variable {ι : Type*} [Fintype ι] {m : ι → ℕ}

/-- The contact grasp built from the frames, `ContactGrasp.spatial model frame` (MLS
printed pp. 218–219): contact `i`'s wrench is carried to the object frame by
`Wrench.transform g_{ocᵢ}`, the book's `Ad_{g_{ocᵢ}⁻¹}ᵀ`. -/
def toContactGrasp (g : SpatialGrasp ι m) : ContactGrasp Wrench ι m :=
  ContactGrasp.spatial g.model g.frame

/-- The derived contact grasp is `ContactGrasp.spatial` of the models and frames (MLS
printed pp. 218–219). -/
theorem toContactGrasp_eq (g : SpatialGrasp ι m) :
    g.toContactGrasp = ContactGrasp.spatial g.model g.frame := rfl

/-- The derived contact grasp keeps the contact models (MLS printed p. 218). -/
@[simp] theorem toContactGrasp_model (g : SpatialGrasp ι m) : g.toContactGrasp.model = g.model :=
  rfl

/-- The wrench transformation of contact `i` in the derived contact grasp is the transfer
`Wrench.transform g_{ocᵢ}`, the book's `Ad_{g_{ocᵢ}⁻¹}ᵀ` (MLS printed p. 218). -/
theorem toContactGrasp_transfer (g : SpatialGrasp ι m) (i : ι) :
    g.toContactGrasp.transfer i = Wrench.transformLinearMap (g.frame i) := rfl

/-- The contact map `Gᵢ = Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ}`, MLS printed p. 218, of the spatial grasp. -/
def contactMap (g : SpatialGrasp ι m) (i : ι) : (Fin (m i) → ℝ) →ₗ[ℝ] Wrench :=
  g.toContactGrasp.contactMap i

/-- The contact map applies the wrench basis in the contact frame, then transfers the wrench to
the object frame by `g_{ocᵢ}` (MLS printed p. 218). -/
theorem contactMap_apply (g : SpatialGrasp ι m) (i : ι) (f : Fin (m i) → ℝ) :
    g.contactMap i f = Wrench.transform (g.frame i) ((g.model i).wrench f) := rfl

/-- The contact map in matrices, MLS printed p. 218: `Gᵢ = Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ}` with the
`6 × 6` adjoint matrix (MLS eq. (2.58)) and the `6 × mᵢ` basis matrix; wrench coordinates force
first. -/
theorem coordinates_contactMap (g : SpatialGrasp ι m) (i : ι) (f : Fin (m i) → ℝ) :
    (g.contactMap i f).coordinates =
      ((Twist.adjointMatrix (g.frame i)⁻¹)ᵀ * (g.model i).basisMatrix) *ᵥ f :=
  ContactGrasp.coordinates_spatial_contactMap g.model g.frame i f

/-- The grasp map `G = [G₁ ⋯ G_k]`, MLS eq. (5.6), printed p. 219, of the spatial grasp. -/
def graspMap (g : SpatialGrasp ι m) : ((i : ι) → Fin (m i) → ℝ) →ₗ[ℝ] Wrench :=
  g.toContactGrasp.graspMap

/-- MLS printed p. 219: `G f_c = ∑ᵢ Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ} f_{cᵢ}`, the contact wrenches transferred
to the object frame by the contact frames and summed. -/
theorem graspMap_apply (g : SpatialGrasp ι m) (f : (i : ι) → Fin (m i) → ℝ) :
    g.graspMap f = ∑ i, Wrench.transform (g.frame i) ((g.model i).wrench (f i)) :=
  ContactGrasp.graspMap_apply _ f

/-- MLS eqs. (5.6)–(5.7), printed pp. 219–220: `G f_c` is the net wrench (MLS p. 63) of the
contact wrenches `B_{cᵢ} f_{cᵢ}` at the contact frames `g_{ocᵢ}`. -/
theorem graspMap_eq_net (g : SpatialGrasp ι m) (f : (i : ι) → Fin (m i) → ℝ) :
    g.graspMap f = Wrench.net Finset.univ g.frame fun i => (g.model i).wrench (f i) :=
  ContactGrasp.spatial_graspMap_eq_net g.model g.frame f

/-- The friction cone `FC = FC_{c₁} × ⋯ × FC_{c_k}` of the spatial grasp, MLS printed p. 220. -/
def cone (g : SpatialGrasp ι m) : FrictionCone ((i : ι) → Fin (m i) → ℝ) :=
  g.toContactGrasp.cone

/-- Contact forces lie in the friction cone of the grasp exactly when each contact's forces lie
in its own cone (MLS printed p. 220). -/
@[simp] theorem mem_cone (g : SpatialGrasp ι m) {f : (i : ι) → Fin (m i) → ℝ} :
    f ∈ g.cone ↔ ∀ i, f i ∈ (g.model i).cone :=
  ContactGrasp.mem_cone _

/-- The grasp `(G, FC)` of MLS Definition 5.1, printed p. 220, of the spatial grasp. -/
def toGrasp (g : SpatialGrasp ι m) : Grasp ((i : ι) → Fin (m i) → ℝ) Wrench :=
  g.toContactGrasp.toGrasp

/-- The grasp map of `toGrasp` is the grasp map (5.6) (MLS printed p. 220). -/
@[simp] theorem toGrasp_map (g : SpatialGrasp ι m) : g.toGrasp.map = g.graspMap := rfl

/-- The friction cone of `toGrasp` is the product cone (MLS printed p. 220). -/
@[simp] theorem toGrasp_cone (g : SpatialGrasp ι m) : g.toGrasp.cone = g.cone := rfl

/-- The transpose of the grasp map acting on object twists, MLS eq. (5.13), printed p. 236:
`(Gᵀ V)ᵢ = Gᵢᵀ V = (Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ})ᵀ V = B_{cᵢ}ᵀ Ad_{g_{ocᵢ}⁻¹} V`, the object twist written
in contact frame `i` and read in the directions of its wrench basis. For `V = V^b_{po}`, the body
velocity of the object relative to the palm, this is the right-hand side of the grasping
constraint (5.15). Twist order `(v, ω)`. -/
def graspTranspose (g : SpatialGrasp ι m) : Twist →ₗ[ℝ] ((i : ι) → Fin (m i) → ℝ) :=
  LinearMap.pi fun i => (g.model i).constraint ∘ₗ Twist.adjointLinearMap (g.frame i)⁻¹

/-- Block `i` of `Gᵀ V` is `B_{cᵢ}ᵀ Ad_{g_{ocᵢ}⁻¹} V` (MLS eq. (5.13), printed p. 236). -/
theorem graspTranspose_apply (g : SpatialGrasp ι m) (V : Twist) (i : ι) :
    g.graspTranspose V i = (g.model i).constraint (Twist.adjoint (g.frame i)⁻¹ V) := rfl

/-- Entry `(i, j)` of `Gᵀ V` is the pairing (MLS printed p. 61) of column `(i, j)` of `G`, the
object wrench `Gᵢ eⱼ`, with the object twist `V`: `Gᵀ` is the transpose of `G` (MLS eq. (5.13),
printed p. 236, `(Ad_{g_{ocᵢ}⁻¹}ᵀ B_{cᵢ})ᵀ V`). -/
theorem graspTranspose_apply_apply (g : SpatialGrasp ι m) (V : Twist) (i : ι) (j : Fin (m i)) :
    g.graspTranspose V i j = Wrench.pair (g.contactMap i (Pi.single j 1)) V := by
  rw [graspTranspose_apply, ContactModel.constraint_apply, contactMap_apply,
    Wrench.pair_transform, ContactModel.wrench_single]

/-- **`Gᵀ` is the transpose of `G`** (MLS eq. (5.13), printed p. 236, with eq. (5.6), p. 219):
`(Gᵀ V) · f_c = (G f_c) · V`, the dot product of contact coefficients against the twist–wrench
pairing of MLS printed p. 61 (the power of the object wrench `G f_c` on the object twist `V`). -/
theorem sum_graspTranspose_mul (g : SpatialGrasp ι m) (V : Twist)
    (f : (i : ι) → Fin (m i) → ℝ) :
    ∑ i, ∑ j, g.graspTranspose V i j * f i j = Wrench.pair (g.graspMap f) V := by
  rw [graspMap_apply, Wrench.pair_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Wrench.pair_transform, ← ContactModel.sum_constraint_mul]
  rfl

/-- **The matrix bridge for `Gᵀ`** (MLS eq. (5.13), printed p. 236): the stacked vector of
`Gᵀ V` is the transpose of the grasp matrix (`ContactGrasp.matrix`, six rows force first)
applied to the six twist coordinates (linear first). -/
theorem stack_graspTranspose [DecidableEq ι] (g : SpatialGrasp ι m) (V : Twist) :
    ContactGrasp.stack (g.graspTranspose V) =
      (g.toContactGrasp.matrix Wrench.coordinatesEquiv.toLinearMap)ᵀ *ᵥ V.coordinates := by
  funext c
  rw [ContactGrasp.stack_apply, graspTranspose_apply_apply, Wrench.pair_eq_coordinates_dotProduct]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, ContactGrasp.matrix_apply,
    LinearEquiv.coe_coe, Wrench.coordinatesEquiv_apply]
  rfl

/-- If the grasp map is surjective (for example, if the grasp is force-closure,
`Grasp.ForceClosure.surjective`), then `Gᵀ` is injective: an object twist is determined by the
contact velocities it induces (MLS printed pp. 236–238, eq. (5.15)). -/
theorem graspTranspose_injective (g : SpatialGrasp ι m) (hG : Function.Surjective g.graspMap) :
    Function.Injective g.graspTranspose := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro V hV
  apply Twist.eq_zero_of_forall_pair_eq_zero
  intro F
  obtain ⟨f, rfl⟩ := hG F
  rw [← sum_graspTranspose_mul, hV]
  simp

end SpatialGrasp

end RoboLean
