import RoboLean.Examples.ScaraHand

/-!
# The two-fingered SCARA grasp of MLS §6.3.3 (printed pp. 291–293)

MLS Chapter 6, §3.3, printed pp. 291–293, Figure 6.6: two SCARA fingers with soft-finger contacts
grasp a box. The hand Jacobian `J_h ∈ ℝ^{8×8}` is square but not invertible: the grasp is not
manipulable (rotations about the line through the contacts) and has internal motions (the first
three joints of each finger), as shown in Chapter 5 (`RoboLean.Examples.ScaraHand`). The book
augments the constraint with the internal variables `y = (θ₁₁ + θ₁₂ + θ₁₃, θ₂₁ + θ₂₂ + θ₂₃)`
(rows `1 1 1 0 | 0 0 0 0` and `0 0 0 0 | 1 1 1 0`), and restricts the object velocity to
`V = H′ w′` with `H′ ∈ ℝ^{6×5}` the identity with its fifth column removed: the object's angular
velocity about its `y`-axis, the line through the two contacts `(0, ∓r, 0)`, is excluded. It then
states (p. 293): "A detailed calculation verifies that this constraint is manipulable and that no
internal motions exist."

**Formalized.** The hand, the object pose and the blocks `J₁₁`, `J₂₂` are those of the library's
SCARA hand (`scaraHand`, `scaraObjectPose`, computed from the SCARA chains and checked against the
printed blocks of p. 242). With `J̄ θ̇ = (J_h θ̇, ẏ)` (`scaraAugmentedJacobian`) and the right-hand
side `(Gᵀ H′ w′, ẏ)` (`scaraAugmentedGraspTranspose`):

* `J̄` is injective (no internal motions) **if and only if** `l₁ l₂ sin θ₁₂ ≠ 0` and
  `l₃ l₄ sin θ₂₂ ≠ 0`, at every configuration (`scaraAugmentedJacobian_injective_iff`); at the
  configurations where the third joints are internal motions of `J_h` (the configuration of the
  figure) this reads `r ≠ b`, `l₁ sin θ₁₁ ≠ 0` and `l₃ sin θ₂₁ ≠ 0`
  (`scaraAugmentedJacobian_injective_iff_of_contact`);
* under the same conditions the augmented constraint is manipulable
  (`scaraAugmented_manipulable`), and the columns of `H′` span exactly the allowable object
  velocities `W = {V : Gᵀ V ∈ R(J_h)}` (`scara_graspTranspose_mem_range_iff`);
* with the full object velocity (`H = I`) the augmented constraint is still not manipulable, at
  every configuration (`scaraAugmented_not_manipulable_full`), as the book says.

**Hypotheses the book does not print.** The book prints no condition for "manipulable and no
internal motions"; the conditions above are derived here and are necessary for injectivity
(`l₁ l₂ sin θ₁₂ = 0` gives an internal motion of finger 1: an elbow singularity of the planar
two-link part, or a zero link). The finger with links `l₁, l₂` and angles `θ₁₁, θ₁₂` is the
book's finger 1; the library's names for finger 2 are `l₃, l₄` (the book's `l₃` is also the
fingertip length, here zero, p. 240). Joint indices in Lean start at `0`: `θ 0 1` is `θ₁₂`.

Kinematics only; the dynamics (6.33) for this example are not formed, and nothing here concerns a
physical hand.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp Real

/-- **The internal-variable rates of MLS p. 292:** `ẏ = (θ̇₁₁ + θ̇₁₂ + θ̇₁₃, θ̇₂₁ + θ̇₂₂ + θ̇₂₃)`, the
rows `1 1 1 0 | 0 0 0 0` and `0 0 0 0 | 1 1 1 0` of the augmented constraint (Lean joint indices
`0, 1, 2` of each finger). -/
def scaraInternalRates : (Fin 2 → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun θ' i := θ' i 0 + θ' i 1 + θ' i 2
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **The augmented hand Jacobian of MLS p. 292–293:** `J̄ θ̇ = (J_h θ̇, ẏ)`, the hand Jacobian of the
two-SCARA hand at the object pose of Figure 5.17 (Figure 6.6) stacked with the internal-variable
rates; the `10 × 8` matrix `[[J_{h1}, 0], [0, J_{h2}], [K₁, K₂]]` of p. 293. -/
def scaraAugmentedJacobian (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ : Fin 2 → Fin 4 → ℝ) : (Fin 2 → Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 4 → ℝ) × (Fin 2 → ℝ) :=
  LinearMap.prod ((scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a))
    scaraInternalRates

/-- **The allowable object velocities of MLS p. 293:** `V = H′ w′` with `H′ ∈ ℝ^{6×5}` the identity
with its fifth column removed, so `w′ = (v_x, v_y, v_z, ω_x, ω_z)` and `ω_y = 0` (twist order
`(v, ω)`; the object's `y`-axis is the line through the contacts). -/
def scaraAllowableBasis : (Fin 5 → ℝ) →ₗ[ℝ] Twist where
  toFun w := ⟨vec (w 0) (w 1) (w 2), vec (w 3) 0 (w 4)⟩
  map_add' x y := by
    apply Twist.ext <;> ext i <;> fin_cases i <;> simp [vec, Twist.add_linear, Twist.add_angular]
  map_smul' c x := by
    apply Twist.ext <;> ext i <;> fin_cases i <;> simp [vec, Twist.smul_linear, Twist.smul_angular]

/-- **The augmented right-hand side of MLS p. 293:** `(w′, ẏ) ↦ (Gᵀ H′ w′, ẏ)`, the matrix
`[[G₁ᵀ H′, 0], [G₂ᵀ H′, 0], [0, I]]`, with `Gᵀ` the grasp of Example 5.2 (the box). -/
def scaraAugmentedGraspTranspose (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (Fin 5 → ℝ) × (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 4 → ℝ) × (Fin 2 → ℝ) :=
  LinearMap.prodMap ((boxSpatialGrasp μ γ r hμ hγ).graspTranspose ∘ₗ scaraAllowableBasis)
    LinearMap.id

/-! ### Private helpers -/

private theorem sg_soft_adjoint_frame₁ (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (p q s vx vy vz wx wy wz : ℝ) :
    (ContactModel.softFinger μ γ hμ hγ).constraint
        (Twist.adjoint (⟨boxRotation₁, vec p q s⟩ : RigidTransform)⁻¹
          ⟨vec vx vy vz, vec wx wy wz⟩) =
      ![vz - (p * wy - q * wx), vx - (q * wz - s * wy), vy - (s * wx - p * wz), wy] := by
  funext j
  fin_cases j <;>
    simp [ContactModel.constraint_apply, ContactModel.softFinger, Wrench.pair, Twist.adjoint,
      Rotation.act_apply, Vec3.cross_coordinates, crossProduct, boxRotation₁, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Rotation.xAxis, Rotation.yAxis, Rotation.zAxis, vec,
      EuclideanSpace.inner_eq_star_dotProduct]
  all_goals ring

private theorem sg_soft_adjoint_frame₂ (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (p q s vx vy vz wx wy wz : ℝ) :
    (ContactModel.softFinger μ γ hμ hγ).constraint
        (Twist.adjoint (⟨boxRotation₂, vec p q s⟩ : RigidTransform)⁻¹
          ⟨vec vx vy vz, vec wx wy wz⟩) =
      ![vx - (q * wz - s * wy), vz - (p * wy - q * wx), -(vy - (s * wx - p * wz)), -wy] := by
  funext j
  fin_cases j <;>
    simp [ContactModel.constraint_apply, ContactModel.softFinger, Wrench.pair, Twist.adjoint,
      Rotation.act_apply, Vec3.cross_coordinates, crossProduct, boxRotation₂, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Rotation.xAxis, Rotation.yAxis, Rotation.zAxis, vec,
      EuclideanSpace.inner_eq_star_dotProduct]
  all_goals ring

private theorem sg_twist_eq (V : Twist) :
    V = ⟨vec (V.linear 0) (V.linear 1) (V.linear 2), vec (V.angular 0) (V.angular 1)
      (V.angular 2)⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;> rfl

/-- `Gᵀ V` for the box grasp of Example 5.2 (MLS p. 221), contact by contact. -/
private theorem sg_graspTranspose (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (V : Twist) :
    (boxSpatialGrasp μ γ r hμ hγ).graspTranspose V =
      ![![V.linear 2 - r * V.angular 0, V.linear 0 + r * V.angular 2, V.linear 1, V.angular 1],
        ![V.linear 0 - r * V.angular 2, V.linear 2 + r * V.angular 0, -V.linear 1,
          -V.angular 1]] := by
  funext i
  fin_cases i
  · change (ContactModel.softFinger μ γ hμ hγ).constraint
      (Twist.adjoint (⟨boxRotation₁, vec 0 (-r) 0⟩ : RigidTransform)⁻¹ V) = _
    rw [sg_twist_eq V, sg_soft_adjoint_frame₁]
    funext j
    fin_cases j <;> simp [vec]
  · change (ContactModel.softFinger μ γ hμ hγ).constraint
      (Twist.adjoint (⟨boxRotation₂, vec 0 r 0⟩ : RigidTransform)⁻¹ V) = _
    rw [sg_twist_eq V, sg_soft_adjoint_frame₂]
    funext j
    fin_cases j <;> simp [vec]

/-- The square matrix of rows `0, 1, 2` of a block `J` and the internal row `1 1 1 0`. -/
private def sgReduced (J : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => if i = 3 then (if k = 3 then 0 else 1) else J i k

private theorem sgReduced_mulVec (J : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (i : Fin 4) :
    (sgReduced J *ᵥ x) i = if i = 3 then x 0 + x 1 + x 2 else (J *ᵥ x) i := by
  fin_cases i <;> simp [sgReduced, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem sgReduced_mulVec_eq_zero_iff {J : Matrix (Fin 4) (Fin 4) ℝ}
    (hJ : ∀ k, J 3 k = 0) (x : Fin 4 → ℝ) :
    sgReduced J *ᵥ x = 0 ↔ J *ᵥ x = 0 ∧ x 0 + x 1 + x 2 = 0 := by
  have h3 : (J *ᵥ x) 3 = 0 := by simp [Matrix.mulVec, dotProduct, hJ]
  constructor
  · intro h
    refine ⟨funext fun i => ?_, ?_⟩
    · fin_cases i
      · simpa [sgReduced_mulVec] using congrFun h 0
      · simpa [sgReduced_mulVec] using congrFun h 1
      · simpa [sgReduced_mulVec] using congrFun h 2
      · exact h3
    · simpa [sgReduced_mulVec] using congrFun h 3
  · rintro ⟨h, hs⟩
    funext i
    rw [sgReduced_mulVec]
    split_ifs
    · simpa using hs
    · simp [h]

private theorem sgReduced_solve {J : Matrix (Fin 4) (Fin 4) ℝ} (hJ : ∀ k, J 3 k = 0)
    (hS : (sgReduced J).det ≠ 0) (t : Fin 4 → ℝ) (ht : t 3 = 0) (y : ℝ) :
    ∃ x : Fin 4 → ℝ, J *ᵥ x = t ∧ x 0 + x 1 + x 2 = y := by
  let u : Fin 4 → ℝ := fun i => if i = 3 then y else t i
  have hu : sgReduced J *ᵥ ((sgReduced J)⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS),
      Matrix.one_mulVec]
  refine ⟨(sgReduced J)⁻¹ *ᵥ u, funext fun i => ?_, ?_⟩
  · have h := congrFun hu i
    rw [sgReduced_mulVec] at h
    fin_cases i
    · simpa [u] using h
    · simpa [u] using h
    · simpa [u] using h
    · simp [Matrix.mulVec, dotProduct, hJ, ht]
  · simpa [sgReduced_mulVec, u] using congrFun hu 3

private theorem sgReduced_injective_iff {J : Matrix (Fin 4) (Fin 4) ℝ} (hJ : ∀ k, J 3 k = 0) :
    (∀ x : Fin 4 → ℝ, J *ᵥ x = 0 → x 0 + x 1 + x 2 = 0 → x = 0) ↔ (sgReduced J).det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro h ⟨v, hv, hSv⟩
    obtain ⟨h1, h2⟩ := (sgReduced_mulVec_eq_zero_iff hJ v).mp hSv
    exact hv (h v h1 h2)
  · intro h x h1 h2
    by_contra hx
    exact h ⟨x, hx, (sgReduced_mulVec_eq_zero_iff hJ x).mpr ⟨h1, h2⟩⟩

private theorem sg_J₁₁_row3 (r b l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) (k : Fin 4) :
    scaraPrintedJ₁₁ r b l₁ l₂ θ 3 k = 0 := by
  fin_cases k <;> simp [scaraPrintedJ₁₁]

private theorem sg_J₂₂_row3 (r b l₃ l₄ : ℝ) (θ : Fin 4 → ℝ) (k : Fin 4) :
    scaraPrintedJ₂₂ r b l₃ l₄ θ 3 k = 0 := by
  fin_cases k <;> simp [scaraPrintedJ₂₂]

private theorem sg_det₁ (r b l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (sgReduced (scaraPrintedJ₁₁ r b l₁ l₂ θ)).det = -(l₁ * l₂ * sin (θ 1)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, sgReduced, scaraPrintedJ₁₁,
    Matrix.submatrix, Fin.succAbove]
  rw [cos_add, sin_add]
  linear_combination (-(l₁ * l₂ * sin (θ 1))) * sin_sq_add_cos_sq (θ 0)

private theorem sg_det₂ (r b l₃ l₄ : ℝ) (θ : Fin 4 → ℝ) :
    (sgReduced (scaraPrintedJ₂₂ r b l₃ l₄ θ)).det = -(l₃ * l₄ * sin (θ 1)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, sgReduced, scaraPrintedJ₂₂,
    Matrix.submatrix, Fin.succAbove]
  rw [cos_add, sin_add]
  linear_combination (-(l₃ * l₄ * sin (θ 1))) * sin_sq_add_cos_sq (θ 0)

private theorem sg_handJacobian (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ θ' : Fin 2 → Fin 4 → ℝ) :
    (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a) θ' =
      ![scaraPrintedJ₁₁ r b l₁ l₂ (θ 0) *ᵥ θ' 0, scaraPrintedJ₂₂ r b l₃ l₄ (θ 1) *ᵥ θ' 1] := by
  have e0 := scaraHand_fingerJacobianMatrix_zero μ γ r b l₁ l₂ l₃ l₄ a hμ hγ (θ 0)
  have e1 := scaraHand_fingerJacobianMatrix_one μ γ r b l₁ l₂ l₃ l₄ a hμ hγ (θ 1)
  funext i
  fin_cases i
  · show (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a) θ' 0 = _
    rw [HandGrasp.handJacobian_apply, ← HandGrasp.fingerJacobianMatrix_mulVec, e0]
    rfl
  · show (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a) θ' 1 = _
    rw [HandGrasp.handJacobian_apply, ← HandGrasp.fingerJacobianMatrix_mulVec, e1]
    rfl

private theorem sg_augmented_apply (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ θ' : Fin 2 → Fin 4 → ℝ) :
    scaraAugmentedJacobian μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ θ' =
      (![scaraPrintedJ₁₁ r b l₁ l₂ (θ 0) *ᵥ θ' 0, scaraPrintedJ₂₂ r b l₃ l₄ (θ 1) *ᵥ θ' 1],
        fun i => θ' i 0 + θ' i 1 + θ' i 2) := by
  show ((scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a) θ',
    scaraInternalRates θ') = _
  rw [sg_handJacobian]
  rfl

/-! ### No internal motions, manipulability and the allowable velocities (MLS p. 293) -/

/-- **MLS p. 293, "no internal motions exist", with the hypotheses the book omits.** The augmented
Jacobian `J̄ θ̇ = (J_h θ̇, ẏ)` of the two-SCARA grasp is injective if and only if
`l₁ l₂ sin θ₁₂ ≠ 0` and `l₃ l₄ sin θ₂₂ ≠ 0` (Lean `θ 0 1`, `θ 1 1`), at every finger
configuration: the determinant of the four nonzero rows of each finger's augmented block is
`−l₁ l₂ sin θ₁₂` (respectively `−l₃ l₄ sin θ₂₂`). The book prints no condition. -/
theorem scaraAugmentedJacobian_injective_iff (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) :
    Function.Injective (scaraAugmentedJacobian μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ) ↔
      l₁ * l₂ * sin (θ 0 1) ≠ 0 ∧ l₃ * l₄ * sin (θ 1 1) ≠ 0 := by
  have e1 : l₁ * l₂ * sin (θ 0 1) ≠ 0 ↔ (sgReduced (scaraPrintedJ₁₁ r b l₁ l₂ (θ 0))).det ≠ 0 := by
    rw [sg_det₁, neg_ne_zero]
  have e2 : l₃ * l₄ * sin (θ 1 1) ≠ 0 ↔ (sgReduced (scaraPrintedJ₂₂ r b l₃ l₄ (θ 1))).det ≠ 0 := by
    rw [sg_det₂, neg_ne_zero]
  rw [e1, e2, ← sgReduced_injective_iff (sg_J₁₁_row3 r b l₁ l₂ (θ 0)),
    ← sgReduced_injective_iff (sg_J₂₂_row3 r b l₃ l₄ (θ 1)), injective_iff_map_eq_zero]
  constructor
  · intro h
    refine ⟨fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
    · have hx := h (Pi.single 0 x) (by
        rw [sg_augmented_apply]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · fin_cases i <;> simp [h1]
        · fin_cases i <;> simp [h2])
      simpa using congrFun hx 0
    · have hx := h (Pi.single 1 x) (by
        rw [sg_augmented_apply]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · fin_cases i <;> simp [h1]
        · fin_cases i <;> simp [h2])
      simpa using congrFun hx 1
  · rintro ⟨h1, h2⟩ θ' h
    rw [sg_augmented_apply] at h
    have hJ := congrArg Prod.fst h
    have hK := congrArg Prod.snd h
    funext i
    fin_cases i
    · exact h1 (θ' 0) (by simpa using congrFun hJ 0) (by simpa using congrFun hK 0)
    · exact h2 (θ' 1) (by simpa using congrFun hJ 1) (by simpa using congrFun hK 1)

/-- **MLS p. 293, "this constraint is manipulable", with the hypotheses the book omits.** If
`l₁ l₂ sin θ₁₂ ≠ 0` and `l₃ l₄ sin θ₂₂ ≠ 0`, then for every `w′ ∈ ℝ⁵` and `ẏ ∈ ℝ²` there are joint
rates with `J_h θ̇ = Gᵀ H′ w′` and internal rates `ẏ`: the augmented constraint of p. 293 is
manipulable (MLS Definition 5.5, p. 237, `Grasp.Manipulable`). -/
theorem scaraAugmented_manipulable (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ : Fin 2 → Fin 4 → ℝ) (h₁ : l₁ * l₂ * sin (θ 0 1) ≠ 0)
    (h₂ : l₃ * l₄ * sin (θ 1 1) ≠ 0) :
    Grasp.Manipulable (scaraAugmentedJacobian μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ)
      (scaraAugmentedGraspTranspose μ γ r hμ hγ) := by
  rintro ⟨w, y⟩
  set t := (boxSpatialGrasp μ γ r hμ hγ).graspTranspose (scaraAllowableBasis w) with ht
  have hω : (scaraAllowableBasis w).angular 1 = 0 := by
    simp [scaraAllowableBasis, vec]
  have ht0 : t 0 3 = 0 := by rw [ht, sg_graspTranspose]; simp [hω]
  have ht1 : t 1 3 = 0 := by rw [ht, sg_graspTranspose]; simp [hω]
  obtain ⟨x₀, hx₀, hy₀⟩ := sgReduced_solve (sg_J₁₁_row3 r b l₁ l₂ (θ 0))
    (by rw [sg_det₁, neg_ne_zero]; exact h₁) (t 0) ht0 (y 0)
  obtain ⟨x₁, hx₁, hy₁⟩ := sgReduced_solve (sg_J₂₂_row3 r b l₃ l₄ (θ 1))
    (by rw [sg_det₂, neg_ne_zero]; exact h₂) (t 1) ht1 (y 1)
  refine ⟨![x₀, x₁], ?_⟩
  rw [sg_augmented_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i
    · simpa [scaraAugmentedGraspTranspose, ← ht] using hx₀
    · simpa [scaraAugmentedGraspTranspose, ← ht] using hx₁
  · fin_cases i
    · simpa [scaraAugmentedGraspTranspose] using hy₀
    · simpa [scaraAugmentedGraspTranspose] using hy₁

/-- **MLS p. 293: the columns of `H′` span the allowable object velocities.** If
`l₁ l₂ sin θ₁₂ ≠ 0` and `l₃ l₄ sin θ₂₂ ≠ 0`, an object twist `V` satisfies `Gᵀ V ∈ R(J_h)` (it lies
in `W(θ, x)` of p. 291) exactly when `V = H′ w′` for some `w′`, i.e. its angular velocity about the
object's `y`-axis, the line through the contacts, is zero. -/
theorem scara_graspTranspose_mem_range_iff (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) (h₁ : l₁ * l₂ * sin (θ 0 1) ≠ 0)
    (h₂ : l₃ * l₄ * sin (θ 1 1) ≠ 0) (V : Twist) :
    (∃ θ', (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a) θ' =
        (boxSpatialGrasp μ γ r hμ hγ).graspTranspose V) ↔
      ∃ w, V = scaraAllowableBasis w := by
  constructor
  · rintro ⟨θ', hθ'⟩
    rw [sg_handJacobian, sg_graspTranspose] at hθ'
    have h3 := congrFun (congrFun hθ' 0) 3
    have hz : (scaraPrintedJ₁₁ r b l₁ l₂ (θ 0) *ᵥ θ' 0) 3 = 0 := by
      simp [Matrix.mulVec, dotProduct, sg_J₁₁_row3]
    simp only [Matrix.cons_val_zero] at h3
    rw [hz] at h3
    have hω : V.angular 1 = 0 := by simpa using h3.symm
    refine ⟨![V.linear 0, V.linear 1, V.linear 2, V.angular 0, V.angular 2], ?_⟩
    apply Twist.ext <;> ext i <;> fin_cases i <;> simp [scaraAllowableBasis, vec, hω]
  · rintro ⟨w, rfl⟩
    have hω : (scaraAllowableBasis w).angular 1 = 0 := by
      simp [scaraAllowableBasis, vec]
    set t := (boxSpatialGrasp μ γ r hμ hγ).graspTranspose (scaraAllowableBasis w) with ht
    have ht0 : t 0 3 = 0 := by rw [ht, sg_graspTranspose]; simp [hω]
    have ht1 : t 1 3 = 0 := by rw [ht, sg_graspTranspose]; simp [hω]
    obtain ⟨x₀, hx₀, -⟩ := sgReduced_solve (sg_J₁₁_row3 r b l₁ l₂ (θ 0))
      (by rw [sg_det₁, neg_ne_zero]; exact h₁) (t 0) ht0 0
    obtain ⟨x₁, hx₁, -⟩ := sgReduced_solve (sg_J₂₂_row3 r b l₃ l₄ (θ 1))
      (by rw [sg_det₂, neg_ne_zero]; exact h₂) (t 1) ht1 0
    refine ⟨![x₀, x₁], ?_⟩
    rw [sg_handJacobian]
    funext i
    fin_cases i
    · simpa using hx₀
    · simpa using hx₁

/-- **MLS p. 293: "The addition of the internal variables does not alter the nonmanipulable nature
of the grasp"**: with the full object velocity (`H = I`), the augmented constraint
`J̄ θ̇ = (Gᵀ V, ẏ)` is not manipulable, at every finger configuration (the rotation about the line
through the contacts, `V = (0, (0, 1, 0))`, is never reached). -/
theorem scaraAugmented_not_manipulable_full (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) :
    ¬ Grasp.Manipulable (scaraAugmentedJacobian μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ)
      (LinearMap.prodMap (boxSpatialGrasp μ γ r hμ hγ).graspTranspose
        (LinearMap.id : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))) := by
  intro h
  obtain ⟨θ', hθ'⟩ := h (⟨0, vec 0 1 0⟩, 0)
  exact scaraHand_graspTranspose_rotY_not_mem_range μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ
    ⟨θ', congrArg Prod.fst hθ'⟩

/-- At a configuration of finger 1 where its third joint is an internal motion of `J_h` (MLS
p. 242: `l₁ cos θ₁₁ + l₂ cos(θ₁₁ + θ₁₂) = b − r`, `l₁ sin θ₁₁ + l₂ sin(θ₁₁ + θ₁₂) = 0`, the
configuration of Figure 6.6, p. 292), `l₁ l₂ sin θ₁₂ = (r − b) l₁ sin θ₁₁`. -/
theorem scara_sin_of_contact₁ {r b l₁ l₂ θ₁ θ₂ : ℝ}
    (h : l₁ * cos θ₁ + l₂ * cos (θ₁ + θ₂) = b - r)
    (h' : l₁ * sin θ₁ + l₂ * sin (θ₁ + θ₂) = 0) :
    l₁ * l₂ * sin θ₂ = (r - b) * (l₁ * sin θ₁) := by
  have hs : sin θ₂ = sin (θ₁ + θ₂) * cos θ₁ - cos (θ₁ + θ₂) * sin θ₁ := by
    have := sin_sub (θ₁ + θ₂) θ₁
    rwa [add_sub_cancel_left] at this
  rw [hs]
  linear_combination (l₁ * cos θ₁) * h' - (l₁ * sin θ₁) * h

/-- At a configuration of finger 2 where its third joint is an internal motion of `J_h` (MLS
p. 242: `l₃ cos θ₂₁ + l₄ cos(θ₂₁ + θ₂₂) = −(b − r)`, `l₃ sin θ₂₁ + l₄ sin(θ₂₁ + θ₂₂) = 0`),
`l₃ l₄ sin θ₂₂ = (b − r) l₃ sin θ₂₁`. -/
theorem scara_sin_of_contact₂ {r b l₃ l₄ θ₁ θ₂ : ℝ}
    (h : l₃ * cos θ₁ + l₄ * cos (θ₁ + θ₂) = -(b - r))
    (h' : l₃ * sin θ₁ + l₄ * sin (θ₁ + θ₂) = 0) :
    l₃ * l₄ * sin θ₂ = (b - r) * (l₃ * sin θ₁) := by
  have hs : sin θ₂ = sin (θ₁ + θ₂) * cos θ₁ - cos (θ₁ + θ₂) * sin θ₁ := by
    have := sin_sub (θ₁ + θ₂) θ₁
    rwa [add_sub_cancel_left] at this
  rw [hs]
  linear_combination (l₃ * cos θ₁) * h' - (l₃ * sin θ₁) * h

/-- **MLS p. 293 at the configuration of Figure 6.6.** Where the third joints of both fingers are
internal motions of `J_h` (the hypotheses of `scaraHand_isInternalMotion`, p. 242), the augmented
Jacobian is injective (no internal motions) if and only if `r ≠ b`, `l₁ sin θ₁₁ ≠ 0` and
`l₃ sin θ₂₁ ≠ 0`: the box is not as wide as the distance between the finger bases, and neither
first link is aligned with the line of the bases. These hypotheses are not printed. -/
theorem scaraAugmentedJacobian_injective_iff_of_contact (μ γ r b l₁ l₂ l₃ l₄ a : ℝ)
    (hμ : 0 < μ) (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ)
    (h₁ : l₁ * cos (θ 0 0) + l₂ * cos (θ 0 0 + θ 0 1) = b - r)
    (h₁' : l₁ * sin (θ 0 0) + l₂ * sin (θ 0 0 + θ 0 1) = 0)
    (h₂ : l₃ * cos (θ 1 0) + l₄ * cos (θ 1 0 + θ 1 1) = -(b - r))
    (h₂' : l₃ * sin (θ 1 0) + l₄ * sin (θ 1 0 + θ 1 1) = 0) :
    Function.Injective (scaraAugmentedJacobian μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ) ↔
      r ≠ b ∧ l₁ * sin (θ 0 0) ≠ 0 ∧ l₃ * sin (θ 1 0) ≠ 0 := by
  rw [scaraAugmentedJacobian_injective_iff, scara_sin_of_contact₁ h₁ h₁',
    scara_sin_of_contact₂ h₂ h₂']
  constructor
  · rintro ⟨h1, h3⟩
    exact ⟨fun hrb => h1 (by rw [hrb, sub_self, zero_mul]), right_ne_zero_of_mul h1,
      right_ne_zero_of_mul h3⟩
  · rintro ⟨hr, h1, h3⟩
    exact ⟨mul_ne_zero (sub_ne_zero.mpr hr) h1, mul_ne_zero (sub_ne_zero.mpr (Ne.symm hr)) h3⟩

end RoboLean.Examples
