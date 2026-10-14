import RoboLean.Dynamics.ObjectChart
import RoboLean.Grasp.HandJacobian

/-!
# The grasp constraint in local coordinates and coordinated lifting (MLS §6.2, (6.18), Fig. 6.3)

MLS Chapter 6, §2.1, printed p. 277, eq. (6.18), and §2.3, pp. 281–282 (renders inspected this
session); Chapter 5, eq. (5.15), pp. 236–237.

**The chart link.** The library's fundamental grasping constraint `HandGrasp.GraspingConstraint`
(MLS (5.15), E028) is written with the body velocity `V^b_{po}` of the object relative to the palm.
MLS writes (6.18) `J_h(θ, x) θ̇ = Gᵀ(θ, x) ẋ` "in local coordinates" `x` of the object pose. For a
chart `x_o = φ(x)` with body-velocity Jacobian `Jφ` (`IsBodyJacobian`, Exercise 4(b), p. 314),
`V^b_{po} = Jφ(x) ẋ`, so (5.15) along a motion is (6.18) with `J_h(θ, x) = J_h(θ, φ(x))` and
`Gᵀ(θ, x) = Gᵀ Jφ(x)`, that is `G(θ, x) = Jφ(x)ᵀ G` (`graspingConstraint_chart_iff`, with the
matrices of `HandJacobian`; `localGrasp`).

**Coordinated lifting (MLS pp. 281–282, Figure 6.3).** "Assume that each robot firmly grasps the
object and can exert arbitrary wrenches without losing contact. ... The contact model for a robot
firmly grasping an object is given by `B_{cᵢ} = I ∈ ℝ^{p×p}` and `FC = ℝᵖ`." Substituting into the
grasp constraint and identifying contact and tool frames gives
`J = blockdiag(Ad⁻¹_{g_{sᵢtᵢ}} J^s_{sᵢtᵢ})` and `Gᵀ = (Ad⁻¹_{g_{otᵢ}})ᵢ` (display of p. 282). Here:
the rigid contact model `rigidContact` (`B_c = I`, `FC = ℝ⁶`; `rigidContact_basisMatrix`,
`rigidContact_constraint`); for a hand whose contacts are all rigid, the blocks of `J_h`
(`fingerJacobian_rigid`, `fingerJacobianMatrix_rigid`) and of `Gᵀ` (`graspTranspose_rigid`) are the
printed ones, with the contact frame identified with the tool frame the block is the body Jacobian
`J^b_{sᵢtᵢ} = Ad⁻¹_{g_{sᵢtᵢ}} J^s_{sᵢtᵢ}` (`fingerJacobian_rigid_of_contactFrame_eq`); the grasp is
force-closure as soon as there is one robot (`isForceClosure_rigid`), and `Gᵀ` is injective. "The
dynamics of the system follow exactly as in the grasping case": the composite dynamics (6.19)–(6.22)
and Lemma 6.1 of `CompositeDynamics` apply to these `J_h`, `G` in local coordinates; `J_h` is
invertible when every robot's spatial Jacobian is (six-joint robots,
`fingerJacobian_rigid_bijective`).

Twist order `(v, ω)`, wrench order `(f, τ)`; the six contact coefficients of a rigid contact are the
six wrench coordinates in the order `Fin 3 ⊕ Fin 3 ≃ Fin 6` (`finSumFinEquiv`). Nothing here models
compliance or the internal forces of a rigid grasp.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Composite

/-! ### The grasp constraint (5.15) in local coordinates: eq. (6.18) -/

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ} {p : ℕ}

/-- **The grasp map in local coordinates, `G(θ, x) = Jφ(x)ᵀ G` (MLS eq. (6.18), p. 277, with
Exercise 4(b), p. 314):** the six-row grasp matrix of `HandJacobian` (wrench coordinates force
first) composed with the chart Jacobian, so that `Gᵀ(θ, x) = Gᵀ Jφ(x)`. -/
def localGrasp [DecidableEq ι] (h : HandGrasp ι m n) (Jφ : Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ) :
    Matrix (Fin p) (Σ i, Fin (m i)) ℝ :=
  Jφᵀ * h.grasp.toContactGrasp.matrix Wrench.coordinatesEquiv.toLinearMap

/-- **MLS eq. (6.18), p. 277, from eq. (5.15), pp. 236–237, through a chart of the object pose
("written here in local coordinates").** Let `Jφ` be a body-velocity Jacobian of the chart `φ`, `x`
a motion of the object coordinates with velocity `ẋ` at `t` and `D` the derivative of the pose curve
`φ ∘ x` at `t`. The grasping constraint (5.15) `J_h(θ, x_o) θ̇ = Gᵀ V^b_{po}` at the pose
`x_o = φ(x(t))` with the object's body velocity holds exactly when `J_h(θ, φ(x)) θ̇ = Gᵀ(θ, x) ẋ`
with `Gᵀ(θ, x) = Gᵀ Jφ(x)`, in the matrices of `HandJacobian`. -/
theorem graspingConstraint_chart_iff [DecidableEq ι] (h : HandGrasp ι m n)
    {φ : (Fin p → ℝ) → RigidTransform} {Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ}
    (hφ : IsBodyJacobian φ Jφ) {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}
    {D : HomogeneousMatrix} (hx : HasDerivAt x x' t)
    (hD : HasDerivAt (fun s => (φ (x s)).toHomogeneous) D t) (θ θ' : (i : ι) → Fin (n i) → ℝ) :
    h.GraspingConstraint θ (φ (x t)) θ' (RigidTransform.bodyVelocity (fun s => φ (x s)) D t hD) ↔
      h.handJacobianMatrix θ (φ (x t)) *ᵥ ContactGrasp.stack θ' =
        (localGrasp h (Jφ (x t)))ᵀ *ᵥ x' := by
  rw [HandGrasp.graspingConstraint_iff_matrix, hφ.bodyVelocity_eq hx hD, localGrasp,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec]

/-! ### Coordinated lifting: the rigid contact model (MLS pp. 281–282) -/

/-- **The friction cone `FC = ℝᵐ` (MLS printed p. 281, "`F C = ℝᵖ`"):** every vector of contact
force coefficients is admissible. -/
def fullCone (k : ℕ) : FrictionCone (Fin k → ℝ) where
  toConvexCone := ⊤
  isClosed := by simp
  interior_nonempty := by simp

/-- **The contact model of a robot firmly grasping an object (MLS printed p. 281):
`B_c = I ∈ ℝ^{6×6}` and `FC = ℝ⁶`**, "the mathematical statement that the robot can exert arbitrary
forces and torques". Basis column `j` is the unit wrench of coordinate `finSumFinEquiv.symm j`
(force first). -/
def rigidContact : ContactModel Wrench 6 where
  basis j := Wrench.coordinatesEquiv.symm (Pi.single (finSumFinEquiv.symm j) 1)
  cone := fullCone 6

/-- The coordinates of the wrench with six given coordinates (MLS p. 61). -/
private theorem coordinates_coordinatesEquiv_symm (x : Fin 3 ⊕ Fin 3 → ℝ) :
    (Wrench.coordinatesEquiv.symm x).coordinates = x :=
  Wrench.coordinatesEquiv.apply_symm_apply x

/-- **MLS printed p. 281: `B_c = I`** for the rigid contact, as the `6 × 6` basis matrix with the
coefficient index read through `Fin 3 ⊕ Fin 3 ≃ Fin 6`. -/
theorem rigidContact_basisMatrix :
    rigidContact.basisMatrix =
      (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ).submatrix id finSumFinEquiv.symm := by
  ext r j
  simp [ContactModel.basisMatrix, rigidContact, Matrix.one_apply, Pi.single_apply,
    coordinates_coordinatesEquiv_symm]

/-- **The rigid contact constrains the full relative twist (MLS eq. (5.9), p. 235, with `B_c = I`,
p. 281):** `B_cᵀ V` is the six coordinates of `V`. -/
theorem rigidContact_constraint (V : Twist) :
    rigidContact.constraint V = V.coordinates ∘ finSumFinEquiv.symm := by
  funext j
  rw [ContactModel.constraint_apply, Wrench.pair_eq_coordinates_dotProduct]
  simp [rigidContact, coordinates_coordinatesEquiv_symm, single_dotProduct]

/-- Every coefficient vector lies in `FC = ℝᵏ` (MLS p. 281). -/
private theorem mem_fullCone {k : ℕ} (f : Fin k → ℝ) : f ∈ fullCone k :=
  (fullCone k).mem_toConvexCone.mp trivial

/-- `B_c` applied to the six coordinates of `W` is `W` for the rigid contact (MLS p. 281). -/
private theorem rigidContact_wrench (W : Wrench) :
    rigidContact.wrench (W.coordinates ∘ (finSumFinEquiv (m := 3) (n := 3)).symm) = W := by
  apply Wrench.coordinatesEquiv.injective
  rw [Wrench.coordinatesEquiv_apply, Wrench.coordinatesEquiv_apply,
    ← ContactModel.basisMatrix_mulVec, rigidContact_basisMatrix, Matrix.submatrix_mulVec_equiv]
  funext r
  simp

/-- **MLS printed p. 281: "the robot can exert arbitrary forces and torques"**: every wrench is
`B_c f_c` with `f_c ∈ FC`. -/
theorem mem_wrenchCone_rigidContact (F : Wrench) : F ∈ rigidContact.wrenchCone := by
  rw [ContactModel.mem_wrenchCone]
  exact ⟨F.coordinates ∘ (finSumFinEquiv (m := 3) (n := 3)).symm, mem_fullCone _,
    rigidContact_wrench F⟩

variable {n : ι → ℕ}

/-- **The blocks of the coordinated-lifting `J` (MLS printed p. 282):** for a hand whose contacts
are all rigid, block `i` of `J_h` (MLS eq. (5.13), p. 236) is `Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ} θ̇ᵢ` in
six coordinates. -/
theorem fingerJacobian_rigid (h : HandGrasp ι (fun _ => 6) n)
    (hm : ∀ i, h.grasp.model i = rigidContact) (xo : RigidTransform) (i : ι)
    (θi θ' : Fin (n i) → ℝ) :
    h.fingerJacobian xo i θi θ' =
      (Twist.adjoint (h.contactFrame xo i)⁻¹
        (∑ l, θ' l • (h.finger i).spatialJacobian θi l)).coordinates ∘ finSumFinEquiv.symm := by
  rw [HandGrasp.fingerJacobian_apply, hm, rigidContact_constraint]

/-- **The printed blocks of the coordinated-lifting `J` (MLS printed p. 282):** for rigid contacts
the block matrix of `J_h` is `Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θᵢ)`, the `6 × 6` adjoint matrix times the
`6 × nᵢ` spatial Jacobian matrix, rows read through `Fin 6 ≃ Fin 3 ⊕ Fin 3`. -/
theorem fingerJacobianMatrix_rigid (h : HandGrasp ι (fun _ => 6) n)
    (hm : ∀ i, h.grasp.model i = rigidContact) (xo : RigidTransform) (i : ι)
    (θi : Fin (n i) → ℝ) :
    h.fingerJacobianMatrix xo i θi =
      (Twist.adjointMatrix (h.contactFrame xo i)⁻¹ *
        (h.finger i).spatialJacobianMatrix θi).submatrix finSumFinEquiv.symm id := by
  rw [HandGrasp.fingerJacobianMatrix, hm, rigidContact_basisMatrix, Matrix.mul_assoc]
  ext r j
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- **MLS printed p. 282, "identifying the contact and tool frames":** when the contact frame of
robot `i` coincides with its tool frame at the current configuration, `g_{sᵢcᵢ} = g_{sᵢtᵢ}(θᵢ)`, the
block `Ad⁻¹_{g_{sᵢtᵢ}} J^s_{sᵢtᵢ}` is the body Jacobian `J^b_{sᵢtᵢ}(θᵢ)` of robot `i` (MLS eq.
(3.56), p. 117), in six coordinates. -/
theorem fingerJacobian_rigid_of_contactFrame_eq (h : HandGrasp ι (fun _ => 6) n)
    (hm : ∀ i, h.grasp.model i = rigidContact) (xo : RigidTransform) (i : ι)
    (θi θ' : Fin (n i) → ℝ) (hf : h.contactFrame xo i = (h.finger i).fk θi) :
    h.fingerJacobian xo i θi θ' =
      (∑ l, θ' l • (h.finger i).bodyJacobian θi l).coordinates ∘ finSumFinEquiv.symm := by
  have key : Twist.adjoint ((h.finger i).fk θi)⁻¹ (∑ l, θ' l • (h.finger i).spatialJacobian θi l) =
      ∑ l, θ' l • (h.finger i).bodyJacobian θi l := by
    have h1 := map_sum (Twist.adjointLinearMap ((h.finger i).fk θi)⁻¹)
      (fun l => θ' l • (h.finger i).spatialJacobian θi l) Finset.univ
    simp only [map_smul] at h1
    rw [show Twist.adjoint ((h.finger i).fk θi)⁻¹ = Twist.adjointLinearMap ((h.finger i).fk θi)⁻¹
      from rfl, h1]
    simp only [SerialChain.bodyJacobian_eq_adjoint_inv_spatialJacobian]
    rfl
  rw [fingerJacobian_rigid h hm, hf, key]

/-- **The blocks of the coordinated-lifting `Gᵀ` (MLS printed p. 282):** for rigid contacts, block
`i` of `Gᵀ V` is `Ad⁻¹_{g_{ocᵢ}} V` in six coordinates (the printed `Ad⁻¹_{g_{otᵢ}}`, contact and
tool frames identified). -/
theorem graspTranspose_rigid (h : HandGrasp ι (fun _ => 6) n)
    (hm : ∀ i, h.grasp.model i = rigidContact) (V : Twist) (i : ι) :
    h.grasp.graspTranspose V i =
      (Twist.adjoint (h.grasp.frame i)⁻¹ V).coordinates ∘ finSumFinEquiv.symm := by
  rw [SpatialGrasp.graspTranspose_apply, hm, rigidContact_constraint]

/-- **Coordinated lifting is force-closure (MLS printed p. 281, "can exert arbitrary wrenches"):**
with rigid contacts and at least one robot, the grasp is force-closure (MLS Definition 5.2, p. 223);
in particular `G` is onto and `Gᵀ` injective (`SpatialGrasp.graspTranspose_injective`). -/
theorem isForceClosure_rigid (h : HandGrasp ι (fun _ => 6) n)
    (hm : ∀ i, h.grasp.model i = rigidContact) [Nonempty ι] : h.grasp.toGrasp.IsForceClosure := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [Grasp.isForceClosure_iff_image_eq_univ, Set.eq_univ_iff_forall]
  intro F
  refine ⟨Pi.single i₀
    ((Wrench.transform (h.grasp.frame i₀)⁻¹ F).coordinates ∘
      (finSumFinEquiv (m := 3) (n := 3)).symm), ?_, ?_⟩
  · simp only [SpatialGrasp.toGrasp_cone, SetLike.mem_coe, SpatialGrasp.mem_cone]
    intro i
    rw [hm]
    exact mem_fullCone _
  · rw [SpatialGrasp.toGrasp_map, SpatialGrasp.graspMap_apply, Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same, hm, rigidContact_wrench]
      simp
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, map_zero, Wrench.transform_zero]
    · intro hi
      exact absurd (Finset.mem_univ i₀) hi

/-- `B_cᵀ = I` is a bijection from twists onto `ℝ⁶` (MLS p. 281). -/
private theorem rigidContact_constraint_bijective :
    Function.Bijective rigidContact.constraint := by
  constructor
  · intro V W hVW
    rw [rigidContact_constraint, rigidContact_constraint] at hVW
    apply Twist.coordinates_injective
    funext r
    simpa using congrFun hVW (finSumFinEquiv r)
  · intro y
    refine ⟨Twist.coordinatesEquiv.symm (y ∘ finSumFinEquiv), ?_⟩
    rw [rigidContact_constraint]
    funext j
    have h := Twist.coordinatesEquiv.apply_symm_apply (y ∘ finSumFinEquiv)
    rw [Twist.coordinatesEquiv_apply] at h
    simp [h]

/-- **MLS printed p. 282 with p. 277 (assumption 2, "The hand Jacobian is invertible"):** for a
rigid contact, block `i` of `J_h` is a bijection exactly when the spatial Jacobian of robot `i`,
`θ̇ᵢ ↦ ∑ₗ θ̇ₗ ξ'ₗ`, is a bijection onto twists (a nonsingular six-joint robot). -/
theorem fingerJacobian_rigid_bijective (h : HandGrasp ι (fun _ => 6) n)
    (hm : ∀ i, h.grasp.model i = rigidContact) (xo : RigidTransform) (i : ι)
    (θi : Fin (n i) → ℝ) :
    Function.Bijective (h.fingerJacobian xo i θi) ↔
      Function.Bijective (Fintype.linearCombination ℝ ((h.finger i).spatialJacobian θi)) := by
  have hA : Function.Bijective (Twist.adjointLinearMap (h.contactFrame xo i)⁻¹) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨Twist.adjoint (h.contactFrame xo i), fun ξ => ?_, fun ξ => ?_⟩
    · show Twist.adjoint _ (Twist.adjoint _ ξ) = ξ
      simp
    · exact Twist.adjoint_inv_adjoint (h.contactFrame xo i) ξ
  rw [HandGrasp.fingerJacobian, LinearMap.coe_comp, LinearMap.coe_comp, hm]
  exact Function.Bijective.of_comp_iff' (rigidContact_constraint_bijective.comp hA) _

/-! ### (6.18) in the composite carrier of `CompositeDynamics` -/

section CompositeCarrier

variable {m : ι → ℕ} {k N : ℕ}

/-- **The finger joint angles `θ = (θ_{f₁}, …, θ_{f_k})` of a hand from a vector `θ ∈ ℝᵏ` (MLS p.
276)**, the stacked joints relabeled by `ej : (Σ i, Fin (n i)) ≃ Fin k`. -/
def unstackJoints (ej : (Σ i, Fin (n i)) ≃ Fin k) (θ : Fin k → ℝ) : (i : ι) → Fin (n i) → ℝ :=
  fun i a => θ (ej ⟨i, a⟩)

/-- **The hand Jacobian `J_h(θ, x)` of (6.18) as a square matrix on `Fin k` (MLS p. 277, assumption
2: `J_h` square):** the block-diagonal matrix of `HandJacobian` at the pose `φ(x)`, rows (contact
coefficients) relabeled by `ec`, columns (joints) by `ej`. -/
def chartHandJacobian [DecidableEq ι] (h : HandGrasp ι m n) (ec : (Σ i, Fin (m i)) ≃ Fin k)
    (ej : (Σ i, Fin (n i)) ≃ Fin k) (φ : (Fin p → ℝ) → RigidTransform) (θ : Fin k → ℝ)
    (x : Fin p → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (h.handJacobianMatrix (unstackJoints ej θ) (φ x)).submatrix ec.symm ej.symm

/-- **The grasp map `G(θ, x) = Jφ(x)ᵀ G` of (6.18) on `Fin`-indexed contact coefficients (MLS p.
277).** -/
def chartGrasp [DecidableEq ι] (h : HandGrasp ι m n) (ec : (Σ i, Fin (m i)) ≃ Fin k)
    (Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ) (x : Fin p → ℝ) :
    Matrix (Fin p) (Fin k) ℝ :=
  (localGrasp h (Jφ x)).submatrix id ec.symm

/-- **MLS eq. (6.18), p. 277, from (5.15) on `Fin`-indexed coordinates:** for a body-velocity
Jacobian `Jφ` of the chart `φ`, a motion `x` with velocity `ẋ` at `t` and the pose derivative `D`,
(5.15) at the joints `θ`, joint rates `θ̇` and the pose `φ(x(t))` with the object's body velocity
holds exactly when `J_h(θ, x) θ̇ = Gᵀ(θ, x) ẋ` for the square `chartHandJacobian` and `chartGrasp`.
-/
theorem graspingConstraint_chart_iff_fin [DecidableEq ι] (h : HandGrasp ι m n)
    (ec : (Σ i, Fin (m i)) ≃ Fin k) (ej : (Σ i, Fin (n i)) ≃ Fin k)
    {φ : (Fin p → ℝ) → RigidTransform} {Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ}
    (hφ : IsBodyJacobian φ Jφ) {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}
    {D : HomogeneousMatrix} (hx : HasDerivAt x x' t)
    (hD : HasDerivAt (fun s => (φ (x s)).toHomogeneous) D t) (θ θ' : Fin k → ℝ) :
    h.GraspingConstraint (unstackJoints ej θ) (φ (x t)) (unstackJoints ej θ')
        (RigidTransform.bodyVelocity (fun s => φ (x s)) D t hD) ↔
      chartHandJacobian h ec ej φ θ (x t) *ᵥ θ' = (chartGrasp h ec Jφ (x t))ᵀ *ᵥ x' := by
  have hst : ContactGrasp.stack (unstackJoints ej θ') = θ' ∘ ej := by
    funext c
    rfl
  rw [graspingConstraint_chart_iff h hφ hx hD, hst, chartHandJacobian, chartGrasp,
    Matrix.transpose_submatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  rw [show ((localGrasp h (Jφ (x t)))ᵀ.submatrix ec.symm id) *ᵥ x' =
      ((localGrasp h (Jφ (x t)))ᵀ *ᵥ x') ∘ ec.symm from by
    funext c
    simp [Matrix.mulVec, dotProduct]]
  constructor
  · intro h1
    rw [h1]
  · intro h1
    funext c
    have := congrFun h1 (ec c)
    simpa using this

/-- **MLS eq. (6.18), p. 277, as the Pfaffian constraint of `CompositeDynamics`, derived from
(5.15).** For the composite configuration `q ∈ ℝᴺ` relabeled by `e : Fin p ⊕ Fin k ≃ Fin N` (object
coordinates `x = q ∘ e ∘ inl`, finger joints `θ = q ∘ e ∘ inr`), a body-velocity Jacobian `Jφ` of
the chart `φ`, a motion `q` with velocity `q'` at `t` and the derivative `D` of the object pose
`φ(x(s))` at `t`: the constraint `[J_h −Gᵀ] q̇ = 0` of `handPfaffian` with
`J_h(q) = chartHandJacobian` and `G(q) = chartGrasp` holds at `(q(t), q'(t))` exactly when the
fundamental grasping constraint (5.15) holds at the joints `θ(t)`, the joint rates `θ̇(t)` and the
pose `φ(x(t))` with the object's body velocity. So every theorem of `CompositeDynamics` (the
Lagrange–d'Alembert equations (6.20), (6.21)–(6.22), Lemma 6.1, (6.24)–(6.25)) applies to a
`HandGrasp` with a chart of the object pose. -/
theorem pfaffianAt_handPfaffian_chart_iff [DecidableEq ι] (h : HandGrasp ι m n)
    (ec : (Σ i, Fin (m i)) ≃ Fin k) (ej : (Σ i, Fin (n i)) ≃ Fin k) (e : Fin p ⊕ Fin k ≃ Fin N)
    {φ : (Fin p → ℝ) → RigidTransform} {Jφ : (Fin p → ℝ) → Matrix (Fin 3 ⊕ Fin 3) (Fin p) ℝ}
    (hφ : IsBodyJacobian φ Jφ) {q q' : ℝ → Fin N → ℝ} {t : ℝ} {D : HomogeneousMatrix}
    (hq : HasDerivAt q (q' t) t)
    (hD : HasDerivAt (fun s => (φ (Constrained.splitFst e (q s))).toHomogeneous) D t) :
    Constrained.PfaffianAt
        (handPfaffian e
          (fun y =>
            chartHandJacobian h ec ej φ (Constrained.splitSnd e y) (Constrained.splitFst e y))
          (fun y => chartGrasp h ec Jφ (Constrained.splitFst e y))) (q t) (q' t) ↔
      h.GraspingConstraint (unstackJoints ej (Constrained.splitSnd e (q t)))
        (φ (Constrained.splitFst e (q t))) (unstackJoints ej (Constrained.splitSnd e (q' t)))
        (RigidTransform.bodyVelocity (fun s => φ (Constrained.splitFst e (q s))) D t hD) := by
  have hx : HasDerivAt (fun s => Constrained.splitFst e (q s)) (Constrained.splitFst e (q' t)) t :=
    hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mp hq (e (Sum.inl a))
  rw [pfaffianAt_handPfaffian_iff,
    graspingConstraint_chart_iff_fin h ec ej hφ hx hD (Constrained.splitSnd e (q t))]

/-- **MLS p. 277, assumption 2 ("The hand Jacobian is invertible"), from the fingers:** if every
block `B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}` of `J_h` at the pose `φ(x)` is onto, the square
`chartHandJacobian` is invertible. For rigid contacts (coordinated lifting, p. 282) the blocks are
onto when every robot's spatial Jacobian is (`fingerJacobian_rigid_bijective`). -/
theorem isUnit_det_chartHandJacobian [DecidableEq ι] (h : HandGrasp ι m n)
    (ec : (Σ i, Fin (m i)) ≃ Fin k) (ej : (Σ i, Fin (n i)) ≃ Fin k)
    (φ : (Fin p → ℝ) → RigidTransform) (θ : Fin k → ℝ) (x : Fin p → ℝ)
    (hs : ∀ i, Function.Surjective (h.fingerJacobian (φ x) i (unstackJoints ej θ i))) :
    IsUnit (chartHandJacobian h ec ej φ θ x).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  intro y
  obtain ⟨θ', hθ'⟩ := ((h.handJacobian_surjective_iff (unstackJoints ej θ) (φ x)).mpr hs)
    (fun i a => y (ec ⟨i, a⟩))
  refine ⟨ContactGrasp.stack θ' ∘ ej.symm, ?_⟩
  rw [chartHandJacobian, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  have hst : ContactGrasp.stack θ' ∘ ej.symm ∘ ej = ContactGrasp.stack θ' := by
    funext c
    simp
  rw [Function.comp_assoc, hst, HandGrasp.handJacobianMatrix_mulVec, hθ']
  funext j
  simp [ContactGrasp.stack_apply]

end CompositeCarrier

end Composite
end RoboLean
