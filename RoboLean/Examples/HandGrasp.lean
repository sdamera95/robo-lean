import RoboLean.Grasp.Manipulability
import RoboLean.Examples.BoxGrasp

/-!
# Hands grasping the box of MLS Example 5.2: manipulability, force-closure and summary item 6

The box of MLS Example 5.2 (printed p. 221, Figure 5.5; frames `boxFrame r`, contacts at
`p_{c₁} = (0, -r, 0)` and `p_{c₂} = (0, r, 0)`) is used for concrete instances of the general
results of `Grasp/HandJacobian` and `Grasp/Manipulability`.

* `boxSpatialGrasp` is Example 5.2 as a `SpatialGrasp`; its contact grasp is E025's `boxGrasp`, so
  it is force-closure for `r ≠ 0` (the claim of MLS p. 242, E025).
* **Summary item 6 (MLS p. 257) is false for a general multifingered grasp** (Definition 5.4):
  `summaryItem6_counterexample` takes the force-closure box grasp with `J_h = Gᵀ` (six joint
  rates, read as twist coordinates); it is manipulable, and `J_h` is not surjective, since the
  strictly internal force `(0, 0, 1, 0, 0, 0, 1, 0)` is not in the range of `Gᵀ`.
* Two hands with Cartesian fingers (three prismatic joints along the base axes `x, y, z`, MLS
  p. 87 prismatic twists `(v, 0)`), with finger bases `g_{ps₁} = (I, (0, -b, 0))`,
  `g_{ps₂} = (I, (0, b, 0))` (the layout of MLS Figure 5.17, p. 241, without its SCARA links):
  with point contacts with friction (`pointHand`) the hand is manipulable at every configuration
  and the grasp is not force-closure (no contact force has a moment about the line through the
  contacts); with the soft-finger contacts of Example 5.2 (`softHand`) the grasp is force-closure
  and the hand is manipulable at no configuration (the fingers cannot rotate about the contact
  normals, so the fourth row of each block of `J_h` vanishes). These are the cases "not
  force-closure, manipulable" and "force closure, not manipulable" of MLS Figure 5.16 (p. 240),
  for these hands; the second matches the conclusion MLS draws for the SCARA hand of Example 5.6
  (p. 242), not re-derived here.

These are convention checks and satisfying instances on concrete inputs. Finite-force caveat:
force-closure and manipulability assume unbounded contact forces and joint rates at maintained
rigid contacts (MLS pp. 214, 234); nothing here concerns a physical hand.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp

/-- The grasp of MLS Example 5.2, printed p. 221, as a spatial grasp that keeps its frames:
soft-finger contacts (eq. (5.4), `μ, γ > 0`) at the frames `boxFrame r`. -/
def boxSpatialGrasp (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) : SpatialGrasp (Fin 2) fun _ => 4 :=
  ⟨fun _ => ContactModel.softFinger μ γ hμ hγ, boxFrame r⟩

/-- The contact grasp of `boxSpatialGrasp` is E025's `boxGrasp` (MLS Example 5.2, printed
p. 221). -/
theorem boxSpatialGrasp_toContactGrasp (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (boxSpatialGrasp μ γ r hμ hγ).toContactGrasp = boxGrasp μ γ r hμ hγ := rfl

/-- The grasp of MLS Example 5.2 is force-closure for `r ≠ 0` (the claim of MLS printed p. 242,
proved by E025 as `boxGrasp_isForceClosure`). Finite-force caveat (MLS p. 214). -/
theorem boxSpatialGrasp_isForceClosure (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hr : r ≠ 0) :
    (boxSpatialGrasp μ γ r hμ hγ).toGrasp.IsForceClosure :=
  boxGrasp_isForceClosure μ γ r hμ hγ hr

/-! ### Summary item 6, MLS p. 257: a counterexample in the generality of Definition 5.4 -/

/-- A multifingered grasp in the sense of MLS Definition 5.4 (printed p. 237) on the box of
Example 5.2: the hand Jacobian is `J_h = Gᵀ`, from six joint rates read as twist coordinates
(linear first) to the eight contact coefficients. It is not the hand Jacobian (5.14) of any
fingers in this library; Definition 5.4 does not require one. -/
def boxTransposeGrasp (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    MultifingeredGrasp (Fin 3 ⊕ Fin 3 → ℝ) (Fin 2) fun _ => 4 :=
  ⟨(boxSpatialGrasp μ γ r hμ hγ).graspTranspose ∘ₗ Twist.coordinatesEquiv.symm.toLinearMap,
    boxSpatialGrasp μ γ r hμ hγ⟩

/-- The grasp `boxTransposeGrasp` is force-closure for `r ≠ 0` (MLS Definition 5.2; Example 5.2 and
p. 242). Finite-force caveat (MLS p. 214). -/
theorem boxTransposeGrasp_isForceClosure (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hr : r ≠ 0) :
    (boxTransposeGrasp μ γ r hμ hγ).IsForceClosure :=
  boxSpatialGrasp_isForceClosure μ γ r hμ hγ hr

/-- The grasp `boxTransposeGrasp` is manipulable (MLS Definition 5.5, printed p. 237): the joint
rates `θ̇ = (coordinates of V)` give `J_h θ̇ = Gᵀ V`. -/
theorem boxTransposeGrasp_isManipulable (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (boxTransposeGrasp μ γ r hμ hγ).IsManipulable := fun V =>
  ⟨V.coordinates, by
    simp [boxTransposeGrasp, ← Twist.coordinatesEquiv_apply]⟩

/-- The internal force `(0, 0, 1, 0, 0, 0, 1, 0)` of Example 5.2 is not zero (supporting lemma). -/
theorem boxInternalForce_ne_zero : boxInternalForce ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp [boxInternalForce] at this

/-- The hand Jacobian `J_h = Gᵀ` of `boxTransposeGrasp` is not surjective: the strictly internal
force `(0, 0, 1, 0, 0, 0, 1, 0)` of Example 5.2 is not in the range of `Gᵀ`
(`SpatialGrasp.not_mem_range_graspTranspose`). -/
theorem boxTransposeGrasp_not_surjective (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    ¬ Function.Surjective (boxTransposeGrasp μ γ r hμ hγ).handJacobian := by
  intro hs
  obtain ⟨x, hx⟩ := hs boxInternalForce
  exact (boxSpatialGrasp μ γ r hμ hγ).not_mem_range_graspTranspose
    (boxGrasp_isStrictlyInternalForce μ γ r hμ hγ).1 boxInternalForce_ne_zero ⟨_, hx⟩

/-- **Summary item 6 of MLS printed p. 257 fails for multifingered grasps in the generality of
Definition 5.4 (printed p. 237).** The item reads "A force-closure grasp is manipulable if and only
if `J_h` is surjective". There is a force-closure, manipulable multifingered grasp whose hand
Jacobian is not surjective: the box grasp of Example 5.2 (`μ = γ = r = 1`) with `J_h = Gᵀ`. For
the hand Jacobians (5.14) of hands with the contact models of Table 5.2 the item holds
(`HandGrasp.isManipulable_iff_surjective`). Finite-force caveat (MLS p. 214). -/
theorem summaryItem6_counterexample :
    ∃ mg : MultifingeredGrasp (Fin 3 ⊕ Fin 3 → ℝ) (Fin 2) (fun _ => 4),
      mg.IsForceClosure ∧ mg.IsManipulable ∧ ¬ Function.Surjective mg.handJacobian :=
  ⟨boxTransposeGrasp 1 1 1 one_pos one_pos,
    boxTransposeGrasp_isForceClosure 1 1 1 one_pos one_pos one_ne_zero,
    boxTransposeGrasp_isManipulable 1 1 1 one_pos one_pos,
    boxTransposeGrasp_not_surjective 1 1 1 one_pos one_pos⟩

/-! ### Cartesian fingers -/

/-- A Cartesian finger: three prismatic joints along the base axes `x`, `y`, `z` of the finger
base frame (MLS p. 87, prismatic twists `(v, 0)`; Lean joint `l` is the book's joint `l + 1`),
with reference fingertip pose `g_{sf}(0) = tool`. -/
def cartesianFinger (tool : RigidTransform) : SerialChain 3 where
  twist := ![Twist.prismatic Rotation.xAxis, Twist.prismatic Rotation.yAxis,
    Twist.prismatic Rotation.zAxis]
  toolRef := tool

private theorem translation_applyVector (p v : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyVector v = v := by
  simp [RigidTransform.applyVector]

/-- The spatial Jacobian (MLS eq. (3.54), p. 116) of a Cartesian finger is constant: column `l`
is the joint twist `(e_l, 0)` at every configuration (translations do not move prismatic twists,
`Twist.adjoint_prismatic`). -/
theorem cartesianFinger_spatialJacobian (tool : RigidTransform) (θ : Fin 3 → ℝ) (l : Fin 3) :
    (cartesianFinger tool).spatialJacobian θ l = (cartesianFinger tool).twist l := by
  fin_cases l <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, cartesianFinger,
      List.ofFn_succ, Twist.exp_prismatic, Twist.adjoint_prismatic, translation_applyVector]

/-- The finger twist `J^s θ̇` of a Cartesian finger is the pure translation `(θ̇, 0)` (MLS
eq. (3.54), p. 116, with the prismatic twists of p. 87). -/
theorem cartesianFinger_sum_spatialJacobian (tool : RigidTransform) (θ θ' : Fin 3 → ℝ) :
    ∑ l, θ' l • (cartesianFinger tool).spatialJacobian θ l =
      Twist.prismatic (WithLp.toLp 2 ![θ' 0, θ' 1, θ' 2]) := by
  simp only [cartesianFinger_spatialJacobian]
  apply Twist.ext
  · ext k
    fin_cases k <;>
      simp [cartesianFinger, Fin.sum_univ_succ, Twist.prismatic, Rotation.xAxis, Rotation.yAxis,
        Rotation.zAxis]
  · simp [cartesianFinger, Fin.sum_univ_succ, Twist.prismatic]

/-- The finger base poses of the box hands, `g_{ps₁} = (I, (0, -b, 0))` and `g_{ps₂} = (I, (0, b, 0))`
in palm coordinates (the layout of MLS Figure 5.17, printed p. 241, which gives `p_{s₁p} = (0, b, 0)`
and `p_{s₂p} = (0, -b, 0)`). -/
def boxHandBase (b : ℝ) : Fin 2 → RigidTransform :=
  ![⟨1, WithLp.toLp 2 ![0, -b, 0]⟩, ⟨1, WithLp.toLp 2 ![0, b, 0]⟩]

/-- A two-fingered hand grasping the box of MLS Example 5.2 (printed p. 221) at the frames
`boxFrame r`, with contact models `model`, two Cartesian fingers (reference fingertip pose the
identity) and the finger bases `boxHandBase b` (MLS §5.1, pp. 234–237). -/
def boxHand {m : Fin 2 → ℕ} (model : (i : Fin 2) → ContactModel Wrench (m i)) (r b : ℝ) :
    HandGrasp (Fin 2) m fun _ => 3 :=
  ⟨⟨model, boxFrame r⟩, fun _ => cartesianFinger 1, boxHandBase b⟩

/-- The blocks of the box hands (MLS eq. (5.13), printed p. 236): a Cartesian finger moves its
fingertip by the translation `θ̇`, written in the contact frame as `g_{sᵢcᵢ}⁻¹_* θ̇`, and the contact
model reads it in the directions of its wrench basis. -/
theorem boxHand_fingerJacobian {m : Fin 2 → ℕ} (model : (i : Fin 2) → ContactModel Wrench (m i))
    (r b : ℝ) (xo : RigidTransform) (i : Fin 2) (θi θ' : Fin 3 → ℝ) :
    (boxHand model r b).fingerJacobian xo i θi θ' =
      (model i).constraint (Twist.prismatic
        (((boxHand model r b).contactFrame xo i)⁻¹.applyVector
          (WithLp.toLp 2 ![θ' 0, θ' 1, θ' 2]))) := by
  rw [HandGrasp.fingerJacobian_apply]
  change (model i).constraint (Twist.adjoint _ (∑ l, θ' l • (cartesianFinger 1).spatialJacobian θi l)) = _
  rw [cartesianFinger_sum_spatialJacobian, Twist.adjoint_prismatic]

/-- The point-contact constraint (MLS eq. (5.9), printed p. 235) on a pure translation `(w, 0)`
reads its three coordinates. -/
theorem pointContact_constraint_prismatic (μ : ℝ) (hμ : 0 < μ) (w : Vec3) :
    (ContactModel.pointContact μ hμ).constraint (Twist.prismatic w) =
      ![WithLp.ofLp w 0, WithLp.ofLp w 1, WithLp.ofLp w 2] := by
  funext j
  fin_cases j <;>
    simp [ContactModel.constraint_apply, ContactModel.pointContact, Wrench.pair, Twist.prismatic,
      Rotation.xAxis, Rotation.yAxis, Rotation.zAxis, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ]

/-- The soft-finger constraint (MLS eq. (5.9), printed p. 235) on a pure translation `(w, 0)` has
zero fourth coordinate: a translation has no rotation about the contact normal. -/
theorem softFinger_constraint_prismatic (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (w : Vec3) :
    (ContactModel.softFinger μ γ hμ hγ).constraint (Twist.prismatic w) 3 = 0 := by
  simp [ContactModel.constraint_apply, ContactModel.softFinger, Wrench.pair, Twist.prismatic]

/-! ### Point contacts: manipulable, not force-closure -/

/-- The box hand with point contacts with friction (MLS eq. (5.3), `μ > 0`) and Cartesian
fingers. -/
def pointHand (μ r b : ℝ) (hμ : 0 < μ) : HandGrasp (Fin 2) (fun _ => 3) fun _ => 3 :=
  boxHand (fun _ => ContactModel.pointContact μ hμ) r b

/-- Every block of the point-contact box hand is onto `ℝ³` (MLS eq. (5.13), printed p. 236):
`θ̇ = g_{sᵢcᵢ *} y` gives `y`. -/
theorem pointHand_fingerJacobian_surjective (μ r b : ℝ) (hμ : 0 < μ) (xo : RigidTransform)
    (i : Fin 2) (θi : Fin 3 → ℝ) :
    Function.Surjective ((pointHand μ r b hμ).fingerJacobian xo i θi) := by
  intro y
  rw [show pointHand μ r b hμ = boxHand (fun _ => ContactModel.pointContact μ hμ) r b from rfl]
  set g := (boxHand (fun _ => ContactModel.pointContact μ hμ) r b).contactFrame xo i
  refine ⟨WithLp.ofLp (g.applyVector (WithLp.toLp 2 ![y 0, y 1, y 2])), ?_⟩
  rw [boxHand_fingerJacobian, pointContact_constraint_prismatic]
  have hw : (WithLp.toLp 2 ![WithLp.ofLp (g.applyVector (WithLp.toLp 2 ![y 0, y 1, y 2])) 0,
      WithLp.ofLp (g.applyVector (WithLp.toLp 2 ![y 0, y 1, y 2])) 1,
      WithLp.ofLp (g.applyVector (WithLp.toLp 2 ![y 0, y 1, y 2])) 2] : Vec3) =
      g.applyVector (WithLp.toLp 2 ![y 0, y 1, y 2]) := by
    ext k
    fin_cases k <;> rfl
  rw [hw, ← RigidTransform.mul_applyVector, inv_mul_cancel, RigidTransform.one_applyVector]
  funext j
  fin_cases j <;> rfl

/-- **The point-contact box hand is manipulable at every configuration** (MLS Definition 5.5,
printed p. 237): its hand Jacobian is onto (`HandGrasp.isManipulable_iff_surjective`, with the
point-contact constraint onto `ℝ³`). -/
theorem pointHand_isManipulable (μ r b : ℝ) (hμ : 0 < μ) (θ : Fin 2 → Fin 3 → ℝ)
    (xo : RigidTransform) : ((pointHand μ r b hμ).toMultifingeredGrasp θ xo).IsManipulable :=
  ((pointHand μ r b hμ).isManipulable_iff_surjective θ xo
    fun _ => ContactModel.pointContact_constraint_surjective μ hμ).mpr
    (((pointHand μ r b hμ).handJacobian_surjective_iff θ xo).mpr
      fun i => pointHand_fingerJacobian_surjective μ r b hμ xo i (θ i))

/-- **A moving instance of the derived grasping constraint** (MLS eqs. (5.9) and (5.15), printed
pp. 235–237, through `HandGrasp.graspingConstraint_iff_forall_contactConstraint`): for the
point-contact box hand and an object translating with constant velocity `v`
(`g_{po}(s) = exp(ξ s) · I`, `ξ = (v, 0)`), there are joint rates `θ̇` such that along
`θ(s) = s θ̇` every contact satisfies the contact constraint (5.9) at `s = 0`. The joint rates
come from manipulability (`pointHand_isManipulable`). -/
theorem pointHand_exists_contactConstraint (μ r b : ℝ) (hμ : 0 < μ) (v : Vec3) :
    ∃ θ' : Fin 2 → Fin 3 → ℝ, ∀ i, (pointHand μ r b hμ).ContactConstraint i
      (fun s => s • θ' i) (fun s => Twist.exp (Twist.prismatic v) s * 1) 0 := by
  have ho := RigidTransform.hasDerivAt_toHomogeneous_exp_mul (Twist.prismatic v) 1
    (hasDerivAt_id' (x := (0 : ℝ)))
  obtain ⟨θ', hθ'⟩ := pointHand_isManipulable μ r b hμ 0
    (Twist.exp (Twist.prismatic v) 0 * 1) (RigidTransform.bodyVelocity _ _ 0 ho)
  refine ⟨θ', ?_⟩
  have hθ : ∀ i l, HasDerivAt (fun s : ℝ => (s • θ') i l) (θ' i l) 0 := by
    intro i l
    simpa using (hasDerivAt_id' (x := (0 : ℝ))).mul_const (θ' i l)
  have hc := ((pointHand μ r b hμ).graspingConstraint_iff_forall_contactConstraint
    (θ := fun s => s • θ') hθ ho).mp (by
      rw [zero_smul]
      exact hθ')
  exact hc

/-- No contact force of the point-contact box grasp has a moment about the `y`-axis, the line
through the contacts `(0, ±r, 0)` (MLS Example 5.2 frames, printed p. 221; point-contact wrenches
(5.3) are pure forces at the contact points). -/
theorem pointHand_graspMap_torque_y (μ r b : ℝ) (hμ : 0 < μ) (f : Fin 2 → Fin 3 → ℝ) :
    WithLp.ofLp ((pointHand μ r b hμ).grasp.graspMap f).torque 1 = 0 := by
  rw [SpatialGrasp.graspMap_apply, Fin.sum_univ_two]
  simp [pointHand, boxHand, ContactModel.pointContact_wrench, Wrench.transform, boxFrame,
    Vec3.cross_coordinates, crossProduct]

/-- **The point-contact box grasp is not force-closure** (MLS Definition 5.2, printed p. 223): the
grasp map is not onto, since the pure moment `(0, 0, 0, 0, 1, 0)` about the contact line is not
`G f_c` for any contact forces. Finite-force caveat (MLS p. 214). -/
theorem pointHand_not_isForceClosure (μ r b : ℝ) (hμ : 0 < μ) (θ : Fin 2 → Fin 3 → ℝ)
    (xo : RigidTransform) : ¬ ((pointHand μ r b hμ).toMultifingeredGrasp θ xo).IsForceClosure := by
  intro hfc
  obtain ⟨f, hf⟩ := Grasp.ForceClosure.surjective hfc ⟨0, WithLp.toLp 2 ![0, 1, 0]⟩
  have h := pointHand_graspMap_torque_y μ r b hμ f
  change WithLp.ofLp ((pointHand μ r b hμ).grasp.graspMap f).torque 1 = 0 at h
  have hf' : (pointHand μ r b hμ).grasp.graspMap f = ⟨0, WithLp.toLp 2 ![0, 1, 0]⟩ := hf
  rw [hf'] at h
  simp at h

/-! ### Soft fingers: force-closure, not manipulable -/

/-- The box hand with the soft-finger contacts of MLS Example 5.2 (eq. (5.4), `μ, γ > 0`) and
Cartesian fingers; its spatial grasp is `boxSpatialGrasp`. -/
def softHand (μ γ r b : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) : HandGrasp (Fin 2) (fun _ => 4) fun _ => 3 :=
  boxHand (fun _ => ContactModel.softFinger μ γ hμ hγ) r b

/-- The soft-finger box hand has the spatial grasp of Example 5.2 (MLS printed p. 221). -/
theorem softHand_grasp (μ γ r b : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (softHand μ γ r b hμ hγ).grasp = boxSpatialGrasp μ γ r hμ hγ := rfl

/-- **The soft-finger box grasp is force-closure** for `r ≠ 0` (MLS p. 242, Example 5.2).
Finite-force caveat (MLS p. 214). -/
theorem softHand_isForceClosure (μ γ r b : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hr : r ≠ 0)
    (θ : Fin 2 → Fin 3 → ℝ) (xo : RigidTransform) :
    ((softHand μ γ r b hμ hγ).toMultifingeredGrasp θ xo).IsForceClosure :=
  boxSpatialGrasp_isForceClosure μ γ r hμ hγ hr

/-- **The soft-finger box hand is manipulable at no configuration** (MLS Definition 5.5, printed
p. 237): the fourth row (rotation about the contact normal) of every block of `J_h` vanishes, so
`J_h` is not onto, and manipulability would need it (`HandGrasp.isManipulable_iff_surjective`,
with the soft-finger constraint onto `ℝ⁴`). -/
theorem softHand_not_isManipulable (μ γ r b : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ : Fin 2 → Fin 3 → ℝ) (xo : RigidTransform) :
    ¬ ((softHand μ γ r b hμ hγ).toMultifingeredGrasp θ xo).IsManipulable := by
  rw [(softHand μ γ r b hμ hγ).isManipulable_iff_surjective θ xo
    fun _ => ContactModel.softFinger_constraint_surjective μ γ hμ hγ,
    HandGrasp.handJacobian_surjective_iff]
  intro hB
  obtain ⟨θ', hθ'⟩ := hB 0 (Pi.single 3 1)
  have h3 := congrFun hθ' 3
  rw [softHand, boxHand_fingerJacobian, softFinger_constraint_prismatic] at h3
  simp at h3

end RoboLean.Examples
