import RoboLean.Grasp.SpatialGrasp
import RoboLean.Geometry.RigidVelocityComposition

/-!
# Finger kinematics, the hand Jacobian and the grasping constraint

MLS Chapter 5, §5.1, printed pp. 234–237: eqs. (5.8)–(5.15) and Definition 5.4.

Frames (MLS pp. 234–235, Figure 5.14). The palm frame `P` is fixed; the object frame `O` has
configuration `x_o := g_{po}` relative to the palm (p. 237); finger `i` is a serial chain from its
base frame `Sᵢ`, fixed in the palm, to the fingertip frame `Fᵢ` at the contact point, which moves
with the fingertip; the contact frame `Cᵢ`, at the same point, moves with the object, and
`g_{ocᵢ}` is constant (fixed contact, p. 234). In this file:

* `HandGrasp ι m n` holds the spatial grasp (`SpatialGrasp`: contact models and `g_{ocᵢ}`), the
  fingers (`SerialChain (n i)`: joint twists in `Sᵢ` at the reference configuration and
  `g_{sᵢfᵢ}(0)`), and the finger bases `g_{psᵢ}` (the book writes `g_{sᵢp} = g_{psᵢ}⁻¹`);
* `contactFrame xo i` is `g_{sᵢcᵢ} = g_{sᵢp} g_{po} g_{ocᵢ}` (MLS pp. 236, 240);
* `fingerJacobian xo i θᵢ` is the block `B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ})` (eq. (5.13)), with
  the library's spatial Jacobian `SerialChain.spatialJacobian` (MLS eq. (3.54)) and the contact
  constraint map `ContactModel.constraint` (`B_{cᵢ}ᵀ`, eq. (5.9); defined in `Grasp/Contact`);
* `handJacobian θ xo` is `J_h(θ, x_o)`, block diagonal by construction (`handJacobian_apply`,
  `handJacobian_single`), and `handJacobianMatrix` is the printed block-diagonal matrix of p. 236
  (`Matrix.blockDiagonal'`), bridged by `handJacobianMatrix_mulVec`;
* `GraspingConstraint` is the fundamental grasping constraint (5.15),
  `J_h(θ, x_o) θ̇ = Gᵀ V^b_{po}`.

The velocity constraint is derived, not assumed. For actual joint and object trajectories (with
`HasDerivAt` evidence), the fingertip pose `g_{pfᵢ} = g_{psᵢ} g_{sᵢfᵢ}(θᵢ)` (finger base fixed in
the palm, eq. (5.11)) and the contact pose `g_{pcᵢ} = g_{po} g_{ocᵢ}` (contact fixed on the object,
eq. (5.12)), `bodyVelocity_fingertipContact` computes the body velocity of
`g_{fᵢcᵢ} = g_{pfᵢ}⁻¹ g_{pcᵢ}` from the library's velocity composition rules (MLS Propositions
2.14–2.15, Lemma 2.16) and the body-Jacobian velocity (MLS eq. (3.55)):
`V^b_{fᵢcᵢ} = Ad⁻¹_{g_{ocᵢ}} V^b_{po} − Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ} θ̇_{fᵢ}` (eqs. (5.10)–(5.12) with
(5.8)). The contact constraint (5.9), `B_{cᵢ}ᵀ V^b_{fᵢcᵢ} = 0`, is the modeling hypothesis of a
maintained contact (`ContactConstraint`); `contactConstraint_iff` proves it equivalent to (5.13)
and `graspingConstraint_iff_forall_contactConstraint` proves (5.15) equivalent to (5.9) at every
contact ("Equation (5.15) is merely a restatement of equation (5.9)", p. 237). The frames `Fᵢ`
and `Cᵢ` are not required to coincide; the derivation does not use it.

Printed slip (MLS p. 236, render inspected): the sentence before (5.15) reads "the constraints in
equation (5.13)" with the label "(5.14)" overprinted on "(5.13)", and the hand-Jacobian display
carries no number. This file calls the display (5.14).

The joint-torque side (5.16), `τ = J_hᵀ f_c`, is `handTorque`; MLS derives it "by equating the
work done by the joints and contacts" (p. 238). As in `Kinematics/ForcePullback`, only the
instantaneous algebraic identity (joint power equals contact power, `sum_handTorque_mul`) and the
uniqueness step are formalized (`eq_handTorque_iff`), not a physical work premise.

MLS assumes in §5 that every contact is a point contact with friction or a soft-finger contact
(p. 234); the definitions here accept any contact model. Nothing here concerns a physical hand,
actuator limits or contact persistence.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

/-- A hand grasping an object with fixed contacts, MLS §5.1, printed pp. 234–237 (Figure 5.14):
the spatial grasp (contact models `(B_{cᵢ}, FC_{cᵢ})` and contact frames `g_{ocᵢ}`), finger `i` as a
serial chain with `n i` joints from its base frame `Sᵢ` to its fingertip frame `Fᵢ` (joint twists
written in `Sᵢ` at the reference configuration and `g_{sᵢfᵢ}(0)`, MLS Chapter 3), and the pose
`g_{psᵢ}` of the finger base relative to the palm frame `P`, fixed in the palm (MLS p. 236). -/
structure HandGrasp (ι : Type*) [Fintype ι] (m n : ι → ℕ) where
  /-- The contacts: models `(B_{cᵢ}, FC_{cᵢ})` and frames `g_{ocᵢ}`, MLS printed pp. 214–219. -/
  grasp : SpatialGrasp ι m
  /-- Finger `i` as a serial chain from `Sᵢ` to `Fᵢ`, MLS printed p. 234, eq. (5.8). -/
  finger : (i : ι) → SerialChain (n i)
  /-- The finger base pose `g_{psᵢ}` in palm coordinates, MLS printed p. 236 (constant). -/
  base : ι → RigidTransform

namespace HandGrasp

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ}

/-- The contact frame relative to the finger base, `g_{sᵢcᵢ} = g_{sᵢp} g_{po} g_{ocᵢ}`, MLS printed
pp. 236 and 240, at the object configuration `x_o = g_{po}`. -/
def contactFrame (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι) : RigidTransform :=
  (h.base i)⁻¹ * xo * h.grasp.frame i

/-- The adjoint identity of MLS printed p. 236,
`Ad⁻¹_{g_{pcᵢ}} Ad_{g_{pfᵢ}} Ad⁻¹_{g_{sᵢfᵢ}} = (Ad_{g_{sᵢp}} Ad_{g_{po}} Ad_{g_{ocᵢ}})⁻¹ = Ad⁻¹_{g_{sᵢcᵢ}}`,
with `g_{pcᵢ} = g_{po} g_{ocᵢ}` and `g_{pfᵢ} = g_{psᵢ} g_{sᵢfᵢ}`, for every fingertip pose
`g_{sᵢfᵢ}`. -/
theorem adjoint_contactFrame_inv (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι)
    (gsf : RigidTransform) (ξ : Twist) :
    Twist.adjoint (xo * h.grasp.frame i)⁻¹
        (Twist.adjoint (h.base i * gsf) (Twist.adjoint gsf⁻¹ ξ)) =
      Twist.adjoint (h.contactFrame xo i)⁻¹ ξ := by
  rw [← Twist.adjoint_mul, ← Twist.adjoint_mul, contactFrame]
  congr 1
  group

/-- Block `i` of the hand Jacobian, MLS eq. (5.13), printed p. 236:
`B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ})`, from the joint rates `θ̇_{fᵢ}` of finger `i` to `ℝ^{mᵢ}`.
`J^s_{sᵢfᵢ}` is the spatial Jacobian of the finger (MLS eq. (3.54)) acting by
`θ̇ ↦ ∑ₗ θ̇ₗ ξₗ'`; `Ad⁻¹_{g_{sᵢcᵢ}}` writes that twist in the contact frame; `B_{cᵢ}ᵀ` reads it in the
directions of the wrench basis. Lean joint `l` is the book's joint `l + 1`. -/
def fingerJacobian (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι)
    (θi : Fin (n i) → ℝ) : (Fin (n i) → ℝ) →ₗ[ℝ] (Fin (m i) → ℝ) :=
  (h.grasp.model i).constraint ∘ₗ Twist.adjointLinearMap (h.contactFrame xo i)⁻¹ ∘ₗ
    Fintype.linearCombination ℝ ((h.finger i).spatialJacobian θi)

/-- The block of MLS eq. (5.13), printed p. 236, applied to joint rates:
`B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} (∑ₗ θ̇ₗ ξₗ')`. -/
theorem fingerJacobian_apply (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι)
    (θi θ' : Fin (n i) → ℝ) :
    h.fingerJacobian xo i θi θ' =
      (h.grasp.model i).constraint
        (Twist.adjoint (h.contactFrame xo i)⁻¹ (∑ l, θ' l • (h.finger i).spatialJacobian θi l)) := by
  simp only [fingerJacobian, LinearMap.coe_comp, Function.comp_apply,
    Fintype.linearCombination_apply]
  rfl

/-- The block of MLS eq. (5.13) as the printed matrix product of p. 236,
`B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ}) ∈ ℝ^{mᵢ × nᵢ}`: the transposed `6 × mᵢ` basis matrix, the
`6 × 6` adjoint matrix of `g_{sᵢcᵢ}⁻¹` (MLS eq. (2.58)) and the `6 × nᵢ` spatial Jacobian matrix;
six-coordinate rows `(v, ω)` against wrench rows `(f, τ)`. -/
def fingerJacobianMatrix (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι)
    (θi : Fin (n i) → ℝ) : Matrix (Fin (m i)) (Fin (n i)) ℝ :=
  (h.grasp.model i).basisMatrixᵀ * Twist.adjointMatrix (h.contactFrame xo i)⁻¹ *
    (h.finger i).spatialJacobianMatrix θi

/-- The printed matrix of MLS eq. (5.13) acts as the block (MLS printed p. 236). -/
theorem fingerJacobianMatrix_mulVec (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι)
    (θi θ' : Fin (n i) → ℝ) :
    h.fingerJacobianMatrix xo i θi *ᵥ θ' = h.fingerJacobian xo i θi θ' := by
  rw [fingerJacobianMatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    SerialChain.spatialJacobianMatrix_mulVec, Twist.adjointMatrix_mulVec,
    ContactModel.basisMatrix_transpose_mulVec, fingerJacobian_apply]

/-- The hand Jacobian `J_h(θ, x_o) : ℝⁿ → ℝᵐ`, MLS printed p. 236 (display (5.14) in this
library's numbering; see the module docstring): block diagonal with blocks
`B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ})`. Joint rates `θ̇ = (θ̇_{f₁}, …, θ̇_{f_k})` are
`(i : ι) → Fin (n i) → ℝ` and contact velocities `(i : ι) → Fin (m i) → ℝ`, the coefficient space
of the contact forces `f_c`. -/
def handJacobian (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) :
    ((i : ι) → Fin (n i) → ℝ) →ₗ[ℝ] ((i : ι) → Fin (m i) → ℝ) :=
  LinearMap.pi fun i => h.fingerJacobian xo i (θ i) ∘ₗ LinearMap.proj i

/-- Block row `i` of `J_h θ̇` depends only on the joint rates of finger `i` (MLS printed p. 236,
the block-diagonal form). -/
theorem handJacobian_apply (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (θ' : (i : ι) → Fin (n i) → ℝ) (i : ι) :
    h.handJacobian θ xo θ' i = h.fingerJacobian xo i (θ i) (θ' i) := rfl

/-- The off-diagonal blocks of `J_h` vanish (MLS printed p. 236): moving the joints of finger `i`
alone changes only the contact velocities of contact `i`. -/
theorem handJacobian_single [DecidableEq ι] (h : HandGrasp ι m n)
    (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (i : ι) (v : Fin (n i) → ℝ) :
    h.handJacobian θ xo (Pi.single i v) = Pi.single i (h.fingerJacobian xo i (θ i) v) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [handJacobian_apply]
  · simp [handJacobian_apply, Pi.single_eq_of_ne hk]

/-- A block-diagonal hand Jacobian is surjective exactly when every block is (MLS printed p. 236,
the block-diagonal form of `J_h`). -/
theorem handJacobian_surjective_iff (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) :
    Function.Surjective (h.handJacobian θ xo) ↔
      ∀ i, Function.Surjective (h.fingerJacobian xo i (θ i)) := by
  classical
  constructor
  · intro hJ i y
    obtain ⟨θ', hθ'⟩ := hJ (Pi.single i y)
    refine ⟨θ' i, ?_⟩
    have := congrFun hθ' i
    rwa [handJacobian_apply, Pi.single_eq_same] at this
  · intro hB y
    choose θ' hθ' using fun i => hB i (y i)
    exact ⟨θ', funext fun i => hθ' i⟩

/-- The hand Jacobian as the printed block-diagonal matrix of MLS printed p. 236, rows indexed by
the stacked contact coefficients `Σ i, Fin (m i)` and columns by the stacked joints
`Σ i, Fin (n i)` (in the stacked order of `ContactGrasp.stack`). -/
def handJacobianMatrix [DecidableEq ι] (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) : Matrix (Σ i, Fin (m i)) (Σ i, Fin (n i)) ℝ :=
  Matrix.blockDiagonal' fun i => h.fingerJacobianMatrix xo i (θ i)

/-- **The matrix bridge for `J_h`** (MLS printed p. 236): the block-diagonal matrix applied to the
stacked joint rates is the stacked vector of `J_h θ̇`. -/
theorem handJacobianMatrix_mulVec [DecidableEq ι] (h : HandGrasp ι m n)
    (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (θ' : (i : ι) → Fin (n i) → ℝ) :
    h.handJacobianMatrix θ xo *ᵥ ContactGrasp.stack θ' =
      ContactGrasp.stack (h.handJacobian θ xo θ') := by
  funext ⟨i, j⟩
  rw [ContactGrasp.stack_apply, handJacobian_apply, ← fingerJacobianMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, ContactGrasp.stack_apply]
  rw [Finset.sum_eq_single i]
  · simp [handJacobianMatrix]
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [handJacobianMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hk)]
  · simp

/-- The fundamental grasping constraint, MLS eq. (5.15), printed pp. 236–237:
`J_h(θ, x_o) θ̇ = Gᵀ V^b_{po}`, for finger joint angles `θ`, object configuration `x_o = g_{po}`,
joint rates `θ̇` and the body velocity `V^b_{po}` of the object relative to the palm. -/
def GraspingConstraint (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform)
    (θ' : (i : ι) → Fin (n i) → ℝ) (V : Twist) : Prop :=
  h.handJacobian θ xo θ' = h.grasp.graspTranspose V

/-- MLS eq. (5.15) is eq. (5.13) for every finger (printed p. 236, "stacking equation (5.13) for
each finger"): `B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ} θ̇_{fᵢ} = Gᵢᵀ V^b_{po}` for all `i`. -/
theorem graspingConstraint_iff_forall (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (θ' : (i : ι) → Fin (n i) → ℝ) (V : Twist) :
    h.GraspingConstraint θ xo θ' V ↔
      ∀ i, h.fingerJacobian xo i (θ i) (θ' i) = h.grasp.graspTranspose V i :=
  funext_iff

/-- MLS eq. (5.15) in matrices (printed pp. 236–237): the block-diagonal hand Jacobian matrix
applied to the stacked joint rates equals the transposed grasp matrix (six rows force first)
applied to the six coordinates of `V^b_{po}` (linear first). -/
theorem graspingConstraint_iff_matrix [DecidableEq ι] (h : HandGrasp ι m n)
    (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform) (θ' : (i : ι) → Fin (n i) → ℝ)
    (V : Twist) :
    h.GraspingConstraint θ xo θ' V ↔
      h.handJacobianMatrix θ xo *ᵥ ContactGrasp.stack θ' =
        (h.grasp.toContactGrasp.matrix Wrench.coordinatesEquiv.toLinearMap)ᵀ *ᵥ V.coordinates := by
  rw [handJacobianMatrix_mulVec, ← SpatialGrasp.stack_graspTranspose, GraspingConstraint]
  exact ContactGrasp.stack.injective.eq_iff.symm

/-! ### The contact constraint along trajectories: eqs. (5.8)–(5.13) -/

/-- The pose of the contact frame `Cᵢ` relative to the fingertip frame `Fᵢ`,
`g_{fᵢcᵢ} = g_{pfᵢ}⁻¹ g_{pcᵢ}`, MLS printed pp. 235–236, with the fingertip pose
`g_{pfᵢ} = g_{psᵢ} g_{sᵢfᵢ}(θ_{fᵢ})` (finger forward kinematics, base fixed in the palm) and the
contact pose `g_{pcᵢ} = g_{po} g_{ocᵢ}` (contact fixed on the object). -/
def fingertipContact (h : HandGrasp ι m n) (i : ι) (θi : Fin (n i) → ℝ) (xo : RigidTransform) :
    RigidTransform :=
  (h.base i * (h.finger i).fk θi)⁻¹ * (xo * h.grasp.frame i)

private theorem bodyVelocity_congr {g g' : ℝ → RigidTransform} {D D' : HomogeneousMatrix} {t : ℝ}
    (hg : g = g') (hd : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hd' : HasDerivAt (fun s => (g' s).toHomogeneous) D' t) :
    RigidTransform.bodyVelocity g D t hd = RigidTransform.bodyVelocity g' D' t hd' := by
  subst hg
  obtain rfl := hd.unique hd'
  rfl

private theorem hasDerivAt_toHomogeneous_const (a : RigidTransform) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => a.toHomogeneous) (0 : HomogeneousMatrix) t :=
  hasDerivAt_const t _

private theorem bodyVelocity_const (a : RigidTransform) (t : ℝ) :
    RigidTransform.bodyVelocity (fun _ => a) 0 t (hasDerivAt_toHomogeneous_const a t) = 0 := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_bodyVelocity, Matrix.mul_zero, Twist.hat_zero]

private theorem adjoint_neg (g : RigidTransform) (ξ : Twist) :
    Twist.adjoint g (-ξ) = -Twist.adjoint g ξ :=
  map_neg (Twist.adjointLinearMap g) ξ

private theorem bodyVelocity_inv {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => (g s)⁻¹) _ t
        (RigidTransform.hasDerivAt_toHomogeneous_inv hg) =
      -Twist.adjoint (g t) (RigidTransform.bodyVelocity g D t hg) := by
  rw [RigidTransform.bodyVelocity_eq_neg_spatialVelocity_inv hg,
    RigidTransform.spatialVelocity_eq_adjoint_body
      (RigidTransform.hasDerivAt_toHomogeneous_inv hg),
    adjoint_neg, neg_neg, Twist.adjoint_adjoint_inv]

/-- The fingertip-to-contact pose `g_{fᵢcᵢ}` of MLS printed pp. 235–236 has an actual derivative
along differentiable joint and object trajectories; so the derivative hypotheses of
`bodyVelocity_fingertipContact` and `ContactConstraint` are satisfiable. -/
theorem hasDerivAt_fingertipContact (h : HandGrasp ι m n) (i : ι) {θ : ℝ → Fin (n i) → ℝ}
    {θ' : Fin (n i) → ℝ} {xo : ℝ → RigidTransform} {Do : HomogeneousMatrix} {t : ℝ}
    (hθ : ∀ l, HasDerivAt (fun s => θ s l) (θ' l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t) :
    ∃ D, HasDerivAt (fun s => (h.fingertipContact i (θ s) (xo s)).toHomogeneous) D t := by
  have hA := RigidTransform.hasDerivAt_toHomogeneous_const_mul (h.base i)
    ((h.finger i).hasDerivAt_fk_toHomogeneous hθ)
  have hB := RigidTransform.hasDerivAt_toHomogeneous_mul (h := fun _ => h.grasp.frame i) ho
    (hasDerivAt_toHomogeneous_const (h.grasp.frame i) t)
  exact ⟨_, RigidTransform.hasDerivAt_toHomogeneous_mul
    (RigidTransform.hasDerivAt_toHomogeneous_inv hA) hB⟩

/-- **MLS eqs. (5.8), (5.10)–(5.12), printed pp. 234–236, derived.** Along joint trajectories
`θ_{fᵢ}(s)` and an object trajectory `g_{po}(s)` with actual derivatives, with the finger base
fixed in the palm and the contact frame fixed on the object, the body velocity of the contact
frame relative to the fingertip is
`V^b_{fᵢcᵢ} = Ad⁻¹_{g_{ocᵢ}} V^b_{po} − Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ}) θ̇_{fᵢ}`,
with `g_{sᵢcᵢ}` at the current object configuration. Computed from the velocity composition rules
(MLS Propositions 2.14–2.15, Lemma 2.16, eq. (2.63)) and the body Jacobian (MLS eq. (3.55)); no
velocity relation is assumed. The derivative `D` exists by `hasDerivAt_fingertipContact`. Twist
order `(v, ω)`; Lean joint `l` is the book's joint `l + 1`. -/
theorem bodyVelocity_fingertipContact (h : HandGrasp ι m n) (i : ι) {θ : ℝ → Fin (n i) → ℝ}
    {θ' : Fin (n i) → ℝ} {xo : ℝ → RigidTransform} {Do D : HomogeneousMatrix} {t : ℝ}
    (hθ : ∀ l, HasDerivAt (fun s => θ s l) (θ' l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t)
    (hD : HasDerivAt (fun s => (h.fingertipContact i (θ s) (xo s)).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => h.fingertipContact i (θ s) (xo s)) D t hD =
      Twist.adjoint (h.grasp.frame i)⁻¹ (RigidTransform.bodyVelocity xo Do t ho) -
        Twist.adjoint (h.contactFrame (xo t) i)⁻¹
          (∑ l, θ' l • (h.finger i).spatialJacobian (θ t) l) := by
  have hfk := (h.finger i).hasDerivAt_fk_toHomogeneous hθ
  have hA := RigidTransform.hasDerivAt_toHomogeneous_const_mul (h.base i) hfk
  have hc := hasDerivAt_toHomogeneous_const (h.grasp.frame i) t
  have hB := RigidTransform.hasDerivAt_toHomogeneous_mul (h := fun _ => h.grasp.frame i) ho hc
  have hAi := RigidTransform.hasDerivAt_toHomogeneous_inv hA
  rw [bodyVelocity_congr (g := fun s => h.fingertipContact i (θ s) (xo s))
      (g' := fun s => (h.base i * (h.finger i).fk (θ s))⁻¹ *
      (xo s * h.grasp.frame i)) rfl hD (RigidTransform.hasDerivAt_toHomogeneous_mul hAi hB),
    RigidTransform.bodyVelocity_mul hAi hB, bodyVelocity_inv hA,
    RigidTransform.bodyVelocity_const_mul (h.base i) hfk, (h.finger i).bodyVelocity_fk hθ hfk,
    RigidTransform.bodyVelocity_mul ho hc, bodyVelocity_const, add_zero]
  have hJ : ∑ l, θ' l • (h.finger i).bodyJacobian (θ t) l =
      Twist.adjoint ((h.finger i).fk (θ t))⁻¹
        (∑ l, θ' l • (h.finger i).spatialJacobian (θ t) l) := by
    have hmap : Twist.adjoint ((h.finger i).fk (θ t))⁻¹
        (∑ l, θ' l • (h.finger i).spatialJacobian (θ t) l) =
        ∑ l, Twist.adjoint ((h.finger i).fk (θ t))⁻¹
          (θ' l • (h.finger i).spatialJacobian (θ t) l) :=
      map_sum (Twist.adjointLinearMap ((h.finger i).fk (θ t))⁻¹) _ Finset.univ
    rw [hmap]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Twist.adjoint_smul, SerialChain.bodyJacobian_eq_adjoint_inv_spatialJacobian]
  rw [hJ, adjoint_neg, ← Twist.adjoint_mul, ← Twist.adjoint_mul, sub_eq_add_neg, add_comm]
  congr 3
  rw [contactFrame]
  group

/-- The contact constraint of MLS eq. (5.9), printed p. 235, at time `t`: the relative pose
`g_{fᵢcᵢ}` of contact frame and fingertip is differentiable at `t` and its body velocity has no
component along the wrench basis, `B_{cᵢ}ᵀ V^b_{fᵢcᵢ} = 0` ("the directions in which motion is
constrained are precisely those in which forces can be exerted"). This is the modeling hypothesis
of a maintained contact (MLS p. 234), not a consequence of the kinematics. -/
def ContactConstraint (h : HandGrasp ι m n) (i : ι) (θ : ℝ → Fin (n i) → ℝ)
    (xo : ℝ → RigidTransform) (t : ℝ) : Prop :=
  ∃ D, ∃ hD : HasDerivAt (fun s => (h.fingertipContact i (θ s) (xo s)).toHomogeneous) D t,
    (h.grasp.model i).constraint
      (RigidTransform.bodyVelocity (fun s => h.fingertipContact i (θ s) (xo s)) D t hD) = 0

/-- **MLS eq. (5.13), printed p. 236, derived from eq. (5.9).** Along joint and object
trajectories with actual derivatives, the contact constraint `B_{cᵢ}ᵀ V^b_{fᵢcᵢ} = 0` holds at `t`
if and only if `B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s_{sᵢfᵢ}(θ_{fᵢ}) θ̇_{fᵢ} = Gᵢᵀ V^b_{po}`. Finger base fixed in
the palm and contact fixed on the object are built into `fingertipContact`. -/
theorem contactConstraint_iff (h : HandGrasp ι m n) (i : ι) {θ : ℝ → Fin (n i) → ℝ}
    {θ' : Fin (n i) → ℝ} {xo : ℝ → RigidTransform} {Do : HomogeneousMatrix} {t : ℝ}
    (hθ : ∀ l, HasDerivAt (fun s => θ s l) (θ' l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t) :
    h.ContactConstraint i θ xo t ↔
      h.fingerJacobian (xo t) i (θ t) θ' =
        h.grasp.graspTranspose (RigidTransform.bodyVelocity xo Do t ho) i := by
  have key : ∀ D (hD : HasDerivAt (fun s => (h.fingertipContact i (θ s) (xo s)).toHomogeneous)
      D t), (h.grasp.model i).constraint
        (RigidTransform.bodyVelocity (fun s => h.fingertipContact i (θ s) (xo s)) D t hD) =
      h.grasp.graspTranspose (RigidTransform.bodyVelocity xo Do t ho) i -
        h.fingerJacobian (xo t) i (θ t) θ' := by
    intro D hD
    rw [bodyVelocity_fingertipContact h i hθ ho hD, map_sub, fingerJacobian_apply,
      SpatialGrasp.graspTranspose_apply]
  constructor
  · rintro ⟨D, hD, hc⟩
    rw [key D hD] at hc
    exact (sub_eq_zero.mp hc).symm
  · intro he
    obtain ⟨D, hD⟩ := h.hasDerivAt_fingertipContact i hθ ho
    exact ⟨D, hD, by rw [key D hD, he, sub_self]⟩

/-- **MLS eq. (5.15), printed pp. 236–237, derived from eq. (5.9) at every contact.** Along joint
trajectories `θ(s)` and an object trajectory `g_{po}(s)` with actual derivatives `θ̇` and body
velocity `V^b_{po}`, the grasping constraint `J_h(θ, x_o) θ̇ = Gᵀ V^b_{po}` holds at `t` if and only
if every contact satisfies the contact constraint (5.9) at `t` ("Equation (5.15) is merely a
restatement of equation (5.9)", p. 237). -/
theorem graspingConstraint_iff_forall_contactConstraint (h : HandGrasp ι m n)
    {θ : ℝ → (i : ι) → Fin (n i) → ℝ} {θ' : (i : ι) → Fin (n i) → ℝ} {xo : ℝ → RigidTransform}
    {Do : HomogeneousMatrix} {t : ℝ}
    (hθ : ∀ i l, HasDerivAt (fun s => θ s i l) (θ' i l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t) :
    h.GraspingConstraint (θ t) (xo t) θ' (RigidTransform.bodyVelocity xo Do t ho) ↔
      ∀ i, h.ContactConstraint i (fun s => θ s i) xo t := by
  rw [graspingConstraint_iff_forall]
  exact forall_congr' fun i => (h.contactConstraint_iff i (hθ i) ho).symm

/-! ### Joint torques: eq. (5.16) -/

/-- The joint torques balancing contact forces, `τ = J_hᵀ f_c`, MLS eq. (5.16), printed p. 238:
torque `l` of finger `i` is `∑ⱼ (J_h)_{(i,j),(i,l)} f_{cᵢ,j}`, the transpose of the block of
eq. (5.13) applied to `f_{cᵢ}`. MLS derives (5.16) "by equating the work done by the joints and
contacts"; this definition is the transpose itself, and `sum_handTorque_mul` and
`eq_handTorque_iff` are the instantaneous power identity and its uniqueness step, not a physical
work premise. MLS requires the contact forces to lie in the friction cone (p. 238); the
definition takes any `f_c`. Lean joint `l` is the book's joint `l + 1`. -/
def handTorque (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ) (xo : RigidTransform)
    (fc : (i : ι) → Fin (m i) → ℝ) : (i : ι) → Fin (n i) → ℝ :=
  fun i l => ∑ j, h.fingerJacobian xo i (θ i) (Pi.single l 1) j * fc i j

/-- **MLS eq. (5.16), printed p. 238, per finger, against eq. (3.60), p. 121.** The torques of
finger `i` are the spatial force pullback `(J^s_{sᵢfᵢ})ᵀ F` of the contact wrench `F = B_{cᵢ} f_{cᵢ}`
carried from the contact frame to the finger base frame `Sᵢ` (`Wrench.transform g_{sᵢcᵢ}`, the
book's `Ad⁻ᵀ_{g_{sᵢcᵢ}}`): `(B_{cᵢ}ᵀ Ad⁻¹_{g_{sᵢcᵢ}} J^s)ᵀ f = (J^s)ᵀ Ad⁻ᵀ_{g_{sᵢcᵢ}} B_{cᵢ} f`. Wrench
`(f, τ)`, twist `(v, ω)`. -/
theorem handTorque_eq_spatialWrenchTorques (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (fc : (i : ι) → Fin (m i) → ℝ) (i : ι) :
    h.handTorque θ xo fc i =
      (h.finger i).spatialWrenchTorques (θ i)
        (Wrench.transform (h.contactFrame xo i) ((h.grasp.model i).wrench (fc i))) := by
  funext l
  rw [SerialChain.spatialWrenchTorques, Wrench.pair_transform, ← ContactModel.sum_constraint_mul]
  simp only [handTorque, fingerJacobian_apply]
  congr 1
  simp [Pi.single_apply]

/-- **The power identity behind MLS eq. (5.16)**, printed p. 238: for `τ = J_hᵀ f_c`, the joint
power `∑ τ · θ̇` equals the contact power `f_c · (J_h θ̇)` for every joint rate `θ̇`. This is the
algebraic identity, not the work premise "equating the work done by the joints and contacts". -/
theorem sum_handTorque_mul (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (fc : (i : ι) → Fin (m i) → ℝ) (θ' : (i : ι) → Fin (n i) → ℝ) :
    ∑ i, ∑ l, h.handTorque θ xo fc i l * θ' i l =
      ∑ i, ∑ j, fc i j * h.handJacobian θ xo θ' i j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [handJacobian_apply, LinearMap.pi_apply_eq_sum_univ (h.fingerJacobian xo i (θ i)) (θ' i)]
  simp only [handTorque, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : (fun k : Fin (n i) => if l = k then (1 : ℝ) else 0) = Pi.single l 1 := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [hs]
  ring

/-- **MLS eq. (5.16), printed p. 238, uniqueness ("since θ̇ is free", as for eq. (3.59), p. 121).**
A joint-torque vector `τ` is `J_hᵀ f_c` if and only if its power `∑ τ · θ̇` equals the contact
power `f_c · (J_h θ̇)` for every joint rate `θ̇`. -/
theorem eq_handTorque_iff (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (fc : (i : ι) → Fin (m i) → ℝ) (τ : (i : ι) → Fin (n i) → ℝ) :
    τ = h.handTorque θ xo fc ↔
      ∀ θ' : (i : ι) → Fin (n i) → ℝ,
        ∑ i, ∑ l, τ i l * θ' i l = ∑ i, ∑ j, fc i j * h.handJacobian θ xo θ' i j := by
  classical
  constructor
  · rintro rfl θ'
    exact h.sum_handTorque_mul θ xo fc θ'
  · intro hτ
    funext i l
    have hi := hτ (Pi.single i (Pi.single l 1))
    rw [← h.sum_handTorque_mul θ xo fc] at hi
    have hsum : ∀ σ : (i : ι) → Fin (n i) → ℝ,
        ∑ k, ∑ l', σ k l' * (Pi.single i (Pi.single l 1) : (i : ι) → Fin (n i) → ℝ) k l' =
          σ i l := by
      intro σ
      rw [Finset.sum_eq_single i]
      · simp [Pi.single_apply]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
      · simp
    rwa [hsum, hsum] at hi

/-- **The force and velocity domains of MLS Figure 5.15 agree** (printed p. 238, eqs. (5.15)–(5.16),
with eq. (5.6)): if joint rates `θ̇` and the object twist `V^b_{po}` satisfy the grasping
constraint (5.15), the joint power of `τ = J_hᵀ f_c` equals the power `(G f_c) · V^b_{po}` of the
object wrench (MLS p. 61 pairing). -/
theorem sum_handTorque_mul_eq_pair (h : HandGrasp ι m n) {θ : (i : ι) → Fin (n i) → ℝ}
    {xo : RigidTransform} {θ' : (i : ι) → Fin (n i) → ℝ} {V : Twist}
    (hc : h.GraspingConstraint θ xo θ' V) (fc : (i : ι) → Fin (m i) → ℝ) :
    ∑ i, ∑ l, h.handTorque θ xo fc i l * θ' i l = Wrench.pair (h.grasp.graspMap fc) V := by
  rw [sum_handTorque_mul, hc, ← SpatialGrasp.sum_graspTranspose_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- MLS eq. (5.16) in matrices (printed p. 238): the stacked torques are the transpose of the
block-diagonal hand Jacobian matrix applied to the stacked contact forces. -/
theorem stack_handTorque [DecidableEq ι] (h : HandGrasp ι m n) (θ : (i : ι) → Fin (n i) → ℝ)
    (xo : RigidTransform) (fc : (i : ι) → Fin (m i) → ℝ) :
    ContactGrasp.stack (h.handTorque θ xo fc) =
      (h.handJacobianMatrix θ xo)ᵀ *ᵥ ContactGrasp.stack fc := by
  funext ⟨i, l⟩
  rw [ContactGrasp.stack_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, ContactGrasp.stack_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_eq_single i]
  · simp only [handJacobianMatrix, Matrix.blockDiagonal'_apply_eq, handTorque]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← fingerJacobianMatrix_mulVec, Matrix.mulVec_single_one]
    rfl
  · intro k _ hk
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [handJacobianMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ hk]
  · simp

end HandGrasp

end RoboLean
