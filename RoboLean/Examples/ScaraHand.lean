import RoboLean.Examples.HandGrasp
import RoboLean.Examples.ScaraDynamics

/-!
# The SCARA example of MLS §5.3 (printed pp. 240–242): two SCARA fingers grasping a box

MLS §5.3 (Figure 5.17, p. 241) grasps the box of Example 5.2 (soft-finger contacts at
`p_{cᵢ} = (0, ±r, 0)`, frames `boxFrame r`) with two SCARA fingers whose fingertip length is zero
(the book's `l₃ = 0`, p. 240), so that the Jacobian of each finger is that of Example 3.8. The
finger bases are fixed in the palm at `g_{ps₁} = (I, (0, -b, 0))` and `g_{ps₂} = (I, (0, b, 0))`
(`boxHandBase b`; MLS prints `p_{s₁c₁} = (0, b - r, a)`, `p_{s₂c₂} = (0, -b + r, a)` with
`R_{sᵢcᵢ} = R_{cᵢ}`, p. 241), and the object configuration is `R_{po} = I`, `p_{po} = (0, 0, a)`
(p. 241). Finger 1 has links `l₁, l₂` and joint angles `θ₁, θ₂`; finger 2 has links `l₃, l₄` and
joint angles `θ₃, θ₄`, the names of the printed `J₂₂` (p. 242). (MLS uses `l₃` also for the
fingertip length, p. 240; the two uses are unrelated.)

Here the hand is built from the library's SCARA chain (`scaraChain`, the joint twists of MLS
Examples 3.1, 3.8 and 4.4), and the printed quantities are checked against it, not transcribed:
the spatial Jacobian of Example 3.8 (p. 240), the contact frames `g_{sᵢcᵢ}` (p. 241), the blocks
`J₁₁`, `J₂₂` of the hand Jacobian (p. 242), the printed product
`Gᵀ (0, 0, 0, 0, 1, 0) = (0, 0, 0, 1, 0, 0, 0, -1)` and the conclusion that the grasp is not
manipulable (p. 242).

Source check of `J₁₁`. The printed internal motions
`θ̇_{N₁} = e₃`, `θ̇_{N₂} = e₇` (p. 242) require the third column of `J₁₁` (and of `J₂₂`) to vanish.
The printed `J₁₁` is the block at every finger configuration `(θ₁, θ₂)`, and its third column
vanishes exactly when `l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) = b - r` and `l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) = 0`,
that is, when the axis of the third joint (the fingertip, `l₃ = 0`) passes through the contact
point `(0, b - r)` of the finger base plane; the configuration of Figure 5.17 is of that kind. So
the printed `J₁₁` and `θ̇_{N₁} = e₃` are consistent, with the configuration constraint implicit in
"at the configuration shown".

These are convention checks on concrete inputs. Finite-force caveat: force-closure and
manipulability assume unbounded contact forces and joint rates at maintained rigid contacts
(MLS pp. 214, 234); nothing here concerns a physical hand.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp Real

/-- The two-SCARA hand of the unnumbered example of MLS §5.3 (printed pp. 240–242, Figure 5.17): the
soft-finger box grasp of Example 5.2 (`boxSpatialGrasp`), finger 1 the SCARA chain with links
`l₁, l₂`, finger 2 the SCARA chain with links `l₃, l₄` (`scaraChain`, MLS Examples 3.1 and 3.8;
fingertip length zero), and the finger bases `g_{ps₁} = (I, (0, -b, 0))`,
`g_{ps₂} = (I, (0, b, 0))`. -/
def scaraHand (μ γ r b l₁ l₂ l₃ l₄ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    HandGrasp (Fin 2) (fun _ => 4) fun _ => 4 :=
  ⟨boxSpatialGrasp μ γ r hμ hγ, ![scaraChain l₁ l₂, scaraChain l₃ l₄], boxHandBase b⟩

/-- The object configuration of MLS Figure 5.17, printed p. 241: `R_{po} = I`,
`p_{po} = (0, 0, a)`. -/
def scaraObjectPose (a : ℝ) : RigidTransform := ⟨1, vec 0 0 a⟩

/-- The spatial Jacobian of a SCARA finger as printed in MLS §5.3, printed p. 240 (Example 3.8,
p. 118): six twist rows `(v, ω)`, linear first, columns the joints
`θ₁, θ₂` (revolute), `θ₃` (revolute), `θ₄` (prismatic), here Lean `θ 0, …, θ 3`. -/
def scaraPrintedSpatialJacobian (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 4) ℝ :=
  Matrix.fromRows
    !![0, l₁ * cos (θ 0), l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1), 0;
      0, l₁ * sin (θ 0), l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1), 0;
      0, 0, 0, 1]
    !![0, 0, 0, 0; 0, 0, 0, 0; 1, 1, 1, 0]

/-! ### Private coordinate helpers: the columns of the SCARA spatial Jacobian -/

private theorem sh_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem sh_exp_zAxis_act (t x y z : ℝ) :
    (Rotation.exp Rotation.zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  change (Rotation.zRotation t).act (vec x y z) = _
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem sh_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

/-- A revolute twist about `+z` through `(x, y, z)` is `((y, -x, 0), (0, 0, 1))` (MLS p. 87). -/
private theorem sh_revolute_z (x y z : ℝ) :
    Twist.revolute Rotation.zAxis (vec x y z) = ⟨vec y (-x) 0, vec 0 0 1⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, Rotation.zAxis, vec]

/-- A revolute joint motion about a vertical axis fixes the vertical direction. -/
private theorem sh_exp_z_applyVector_zAxis (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyVector Rotation.zAxis =
      Rotation.zAxis := by
  rw [RigidTransform.applyVector, Twist.exp_rotation]
  change (Rotation.exp Rotation.zAxis t).act (vec 0 0 1) = vec 0 0 1
  rw [sh_exp_zAxis_act]
  apply sh_vec_eq <;> ring

/-- A revolute joint motion about the vertical axis through `(qx, qy, qz)` on a point
(MLS p. 47, eq. (2.40) with zero pitch). -/
private theorem sh_exp_z_applyPoint (qx qy qz t x y z : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec qx qy qz)) t).applyPoint (vec x y z) =
      vec (cos t * (x - qx) - sin t * (y - qy) + qx)
        (sin t * (x - qx) + cos t * (y - qy) + qy) z := by
  rw [Twist.exp_revolute_applyPoint _ _ sh_norm_zAxis]
  have : vec x y z - vec qx qy qz = vec (x - qx) (y - qy) (z - qz) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [this, sh_exp_zAxis_act]
  ext i
  fin_cases i <;> simp [vec]

private theorem sh_col0 (l₁ l₂ : ℝ) :
    (scaraChain l₁ l₂).twist 0 = ⟨vec 0 0 0, vec 0 0 1⟩ := by
  change Twist.revolute Rotation.zAxis (vec 0 0 0) = _
  rw [sh_revolute_z]
  congr 1
  apply sh_vec_eq <;> ring

private theorem sh_col1 (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraChain l₁ l₂).spatialJacobian θ 1 =
      ⟨vec (l₁ * cos (θ 0)) (l₁ * sin (θ 0)) 0, vec 0 0 1⟩ := by
  simp only [SerialChain.spatialJacobian, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero]
  simp only [scaraChain]
  simp
  rw [Twist.adjoint_revolute, sh_exp_z_applyVector_zAxis, sh_exp_z_applyPoint, sh_revolute_z]
  congr 1
  apply sh_vec_eq <;> ring

private theorem sh_col2 (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraChain l₁ l₂).spatialJacobian θ 2 =
      ⟨vec (l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1)) (l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1)) 0,
        vec 0 0 1⟩ := by
  simp only [SerialChain.spatialJacobian, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero]
  simp only [scaraChain]
  simp
  simp only [Twist.adjoint_revolute, sh_exp_z_applyVector_zAxis, sh_exp_z_applyPoint]
  rw [sh_revolute_z, cos_add, sin_add]
  congr 1
  apply sh_vec_eq <;> ring

private theorem sh_col3 (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraChain l₁ l₂).spatialJacobian θ 3 = ⟨vec 0 0 1, vec 0 0 0⟩ := by
  simp only [SerialChain.spatialJacobian, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero]
  simp only [scaraChain]
  simp
  simp only [Twist.adjoint_prismatic, sh_exp_z_applyVector_zAxis]
  apply Twist.ext <;> ext i <;> fin_cases i <;> simp [Twist.prismatic, Rotation.zAxis, vec]

/-- **The spatial Jacobian of the SCARA finger is the printed one** (MLS §5.3, printed p. 240,
"the Jacobian is that given in Example 3.8"; eq. (3.54), p. 116), computed from the joint twists
of `scaraChain` for every configuration. -/
theorem scaraChain_spatialJacobianMatrix (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraChain l₁ l₂).spatialJacobianMatrix θ = scaraPrintedSpatialJacobian l₁ l₂ θ := by
  ext r k
  fin_cases k <;> rcases r with i | i <;> fin_cases i <;>
    simp [SerialChain.spatialJacobianMatrix, scaraPrintedSpatialJacobian, sh_col0, sh_col1,
      sh_col2, sh_col3, Twist.coordinates, vec]

/-- **The contact frames `g_{sᵢcᵢ} = g_{sᵢp} g_{po} g_{ocᵢ}` of MLS printed p. 241**:
`R_{s₁c₁} = R_{c₁}`, `p_{s₁c₁} = (0, b - r, a)`; `R_{s₂c₂} = R_{c₂}`, `p_{s₂c₂} = (0, -b + r, a)`, at the
object configuration of Figure 5.17. -/
theorem scaraHand_contactFrame (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).contactFrame (scaraObjectPose a) 0 =
        ⟨boxRotation₁, vec 0 (b - r) a⟩ ∧
      (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).contactFrame (scaraObjectPose a) 1 =
        ⟨boxRotation₂, vec 0 (-b + r) a⟩ := by
  constructor <;> ext i
  all_goals simp [HandGrasp.contactFrame, scaraHand, scaraObjectPose, boxSpatialGrasp,
    boxHandBase, boxFrame]
  all_goals fin_cases i <;> simp [vec]
  all_goals ring

/-- The block `J₁₁` as printed in MLS §5.3, printed p. 242. -/
def scaraPrintedJ₁₁ (r b l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 1;
    -b + r, -b + r + l₁ * cos (θ 0), -b + r + l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1), 0;
    0, l₁ * sin (θ 0), l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1), 0;
    0, 0, 0, 0]

/-- The block `J₂₂` as printed in MLS §5.3, printed p. 242 (finger 2's links `l₃, l₄` and angles
`θ₃, θ₄`, here Lean `θ 0, θ 1` of finger 2). -/
def scaraPrintedJ₂₂ (r b l₃ l₄ : ℝ) (θ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![b - r, b - r + l₃ * cos (θ 0), b - r + l₃ * cos (θ 0) + l₄ * cos (θ 0 + θ 1), 0;
    0, 0, 0, 1;
    0, -l₃ * sin (θ 0), -l₃ * sin (θ 0) - l₄ * sin (θ 0 + θ 1), 0;
    0, 0, 0, 0]

/-! ### Private helpers: the soft-finger constraint in the contact frames, and matrix entries -/

/-- `B_cᵀ Ad_{g⁻¹} (v, ω)` for the soft-finger basis and `g = (R_{c₁}, (p, q, s))`:
`Rᵀ (v - p × ω)` read in `x, y, z`, and the normal component of `Rᵀ ω`. -/
private theorem sh_soft_adjoint_frame₁ (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
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

/-- `B_cᵀ Ad_{g⁻¹} (v, ω)` for the soft-finger basis and `g = (R_{c₂}, (p, q, s))`. -/
private theorem sh_soft_adjoint_frame₂ (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
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

/-- Entry `(j, k)` of the block of eq. (5.13) is coefficient `j` of `B_cᵀ Ad⁻¹_{g_{sc}}` applied to
column `k` of the spatial Jacobian. -/
private theorem sh_fingerJacobianMatrix_apply {ι : Type*} [Fintype ι] {m n : ι → ℕ}
    (h : HandGrasp ι m n) (xo : RigidTransform) (i : ι) (θi : Fin (n i) → ℝ) (j : Fin (m i))
    (k : Fin (n i)) :
    h.fingerJacobianMatrix xo i θi j k = (h.grasp.model i).constraint
      (Twist.adjoint (h.contactFrame xo i)⁻¹ ((h.finger i).spatialJacobian θi k)) j := by
  have := congrFun (h.fingerJacobianMatrix_mulVec xo i θi (Pi.single k 1)) j
  rw [Matrix.mulVec_single_one, HandGrasp.fingerJacobian_apply] at this
  simpa [Pi.single_apply] using this

/-- **The block `J₁₁` of MLS printed p. 242 is the computed one**: the block
`B_{c₁}ᵀ Ad⁻¹_{g_{s₁c₁}} J^s_{s₁f₁}(θ_{f₁})` of eq. (5.13), computed from the SCARA chain, the
soft-finger basis and the frames, equals the printed `J₁₁` for every finger configuration. -/
theorem scaraHand_fingerJacobianMatrix_zero (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).fingerJacobianMatrix (scaraObjectPose a) 0 θi =
      scaraPrintedJ₁₁ r b l₁ l₂ θi := by
  ext j k
  rw [sh_fingerJacobianMatrix_apply, (scaraHand_contactFrame μ γ r b l₁ l₂ l₃ l₄ a hμ hγ).1]
  change (ContactModel.softFinger μ γ hμ hγ).constraint
    (Twist.adjoint (⟨boxRotation₁, vec 0 (b - r) a⟩ : RigidTransform)⁻¹
      ((scaraChain l₁ l₂).spatialJacobian θi k)) j = _
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, SerialChain.spatialJacobian_zero,
      sh_col0, sh_col1, sh_col2, sh_col3, sh_soft_adjoint_frame₁] <;>
    fin_cases j <;> simp [scaraPrintedJ₁₁] <;> ring

/-- **The block `J₂₂` of MLS printed p. 242 is the computed one**, for every configuration of
finger 2. -/
theorem scaraHand_fingerJacobianMatrix_one (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).fingerJacobianMatrix (scaraObjectPose a) 1 θi =
      scaraPrintedJ₂₂ r b l₃ l₄ θi := by
  ext j k
  rw [sh_fingerJacobianMatrix_apply, (scaraHand_contactFrame μ γ r b l₁ l₂ l₃ l₄ a hμ hγ).2]
  change (ContactModel.softFinger μ γ hμ hγ).constraint
    (Twist.adjoint (⟨boxRotation₂, vec 0 (-b + r) a⟩ : RigidTransform)⁻¹
      ((scaraChain l₃ l₄).spatialJacobian θi k)) j = _
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, SerialChain.spatialJacobian_zero,
      sh_col0, sh_col1, sh_col2, sh_col3, sh_soft_adjoint_frame₂] <;>
    fin_cases j <;> simp [scaraPrintedJ₂₂] <;> ring

/-- **The third joint of finger 1 is an internal motion exactly at the contact configurations**
(MLS printed p. 242, `θ̇_{N₁} = e₃`): the third column of `J₁₁` vanishes if and only if
`l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) = b - r` and `l₁ sin θ₁ + l₂ sin(θ₁ + θ₂) = 0`, i.e. the third joint's
axis passes through the contact point `(0, b - r)` of the base plane of finger 1. -/
theorem scaraHand_fingerJacobian_zero_single_two_eq_zero_iff (μ γ r b l₁ l₂ l₃ l₄ a : ℝ)
    (hμ : 0 < μ) (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).fingerJacobian (scaraObjectPose a) 0 θi
        (Pi.single 2 1) = 0 ↔
      l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) = b - r ∧
        l₁ * sin (θi 0) + l₂ * sin (θi 0 + θi 1) = 0 := by
  rw [← HandGrasp.fingerJacobianMatrix_mulVec, scaraHand_fingerJacobianMatrix_zero,
    Matrix.mulVec_single_one]
  constructor
  · intro h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [scaraPrintedJ₁₁] at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    funext j
    fin_cases j <;> simp [scaraPrintedJ₁₁] <;> linarith

/-- **The third joint of finger 2 is an internal motion exactly at the contact configurations**
(MLS printed p. 242, `θ̇_{N₂} = e₇`): the third column of `J₂₂` vanishes if and only if
`l₃ cos θ₃ + l₄ cos(θ₃ + θ₄) = -(b - r)` and `l₃ sin θ₃ + l₄ sin(θ₃ + θ₄) = 0`. -/
theorem scaraHand_fingerJacobian_one_single_two_eq_zero_iff (μ γ r b l₁ l₂ l₃ l₄ a : ℝ)
    (hμ : 0 < μ) (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).fingerJacobian (scaraObjectPose a) 1 θi
        (Pi.single 2 1) = 0 ↔
      l₃ * cos (θi 0) + l₄ * cos (θi 0 + θi 1) = -(b - r) ∧
        l₃ * sin (θi 0) + l₄ * sin (θi 0 + θi 1) = 0 := by
  rw [← HandGrasp.fingerJacobianMatrix_mulVec, scaraHand_fingerJacobianMatrix_one,
    Matrix.mulVec_single_one]
  constructor
  · intro h
    have h1 := congrFun h 0
    have h2 := congrFun h 2
    simp [scaraPrintedJ₂₂] at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    funext j
    fin_cases j <;> simp [scaraPrintedJ₂₂] <;> linarith

/-- **The printed internal motions of MLS printed p. 242**, `θ̇_{N₁} = e₃` and `θ̇_{N₂} = e₇`
(Lean: joint `2` of finger `0` and joint `2` of finger `1`), are internal motions (`N(J_h)`) at
every contact configuration of both fingers. -/
theorem scaraHand_isInternalMotion (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ : Fin 2 → Fin 4 → ℝ)
    (h₁ : l₁ * cos (θ 0 0) + l₂ * cos (θ 0 0 + θ 0 1) = b - r)
    (h₁' : l₁ * sin (θ 0 0) + l₂ * sin (θ 0 0 + θ 0 1) = 0)
    (h₂ : l₃ * cos (θ 1 0) + l₄ * cos (θ 1 0 + θ 1 1) = -(b - r))
    (h₂' : l₃ * sin (θ 1 0) + l₄ * sin (θ 1 0 + θ 1 1) = 0) :
    ((scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).toMultifingeredGrasp θ
        (scaraObjectPose a)).IsInternalMotion (Pi.single 0 (Pi.single 2 1)) ∧
      ((scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).toMultifingeredGrasp θ
        (scaraObjectPose a)).IsInternalMotion (Pi.single 1 (Pi.single 2 1)) := by
  constructor
  · change (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a)
      (Pi.single 0 (Pi.single 2 1)) = 0
    rw [HandGrasp.handJacobian_single,
      (scaraHand_fingerJacobian_zero_single_two_eq_zero_iff μ γ r b l₁ l₂ l₃ l₄ a hμ hγ
        (θ 0)).mpr ⟨h₁, h₁'⟩, Pi.single_zero]
  · change (scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a)
      (Pi.single 1 (Pi.single 2 1)) = 0
    rw [HandGrasp.handJacobian_single,
      (scaraHand_fingerJacobian_one_single_two_eq_zero_iff μ γ r b l₁ l₂ l₃ l₄ a hμ hγ
        (θ 1)).mpr ⟨h₂, h₂'⟩, Pi.single_zero]

/-- **The printed product of MLS printed p. 242**: `Gᵀ (0, 0, 0, 0, 1, 0)ᵀ = (0, 0, 0, 1, 0, 0, 0, -1)ᵀ`,
the contact velocities of a unit rotation of the object about its `y`-axis (twist `(v, ω)` with
`v = 0`, `ω = (0, 1, 0)`), for the grasp of Example 5.2. -/
theorem boxSpatialGrasp_graspTranspose_rotY (μ γ r : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    (boxSpatialGrasp μ γ r hμ hγ).graspTranspose ⟨0, vec 0 1 0⟩ = ![![0, 0, 0, 1], ![0, 0, 0, -1]] := by
  have h0 : (0 : Vec3) = vec 0 0 0 := by
    ext i
    fin_cases i <;> rfl
  funext i
  fin_cases i
  · change (ContactModel.softFinger μ γ hμ hγ).constraint
      (Twist.adjoint (⟨boxRotation₁, vec 0 (-r) 0⟩ : RigidTransform)⁻¹ ⟨0, vec 0 1 0⟩) = _
    rw [h0, sh_soft_adjoint_frame₁]
    funext j
    fin_cases j <;> simp
  · change (ContactModel.softFinger μ γ hμ hγ).constraint
      (Twist.adjoint (⟨boxRotation₂, vec 0 r 0⟩ : RigidTransform)⁻¹ ⟨0, vec 0 1 0⟩) = _
    rw [h0, sh_soft_adjoint_frame₂]
    funext j
    fin_cases j <;> simp

/-- MLS printed p. 242: `Gᵀ (0, 0, 0, 0, 1, 0)ᵀ ∉ R(J_h)` for the two-SCARA hand at the object
configuration of Figure 5.17 and every finger configuration: the fourth row of `J₁₁` (rotation
about the contact normal of contact 1) is zero, while the fourth contact velocity of the
printed product is `1`. -/
theorem scaraHand_graspTranspose_rotY_not_mem_range (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) :
    (boxSpatialGrasp μ γ r hμ hγ).graspTranspose ⟨0, vec 0 1 0⟩ ∉
      Set.range ((scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).handJacobian θ (scaraObjectPose a)) := by
  rintro ⟨θ', hθ'⟩
  have h := congrFun (congrFun hθ' 0) 3
  rw [HandGrasp.handJacobian_apply, ← HandGrasp.fingerJacobianMatrix_mulVec,
    scaraHand_fingerJacobianMatrix_zero, boxSpatialGrasp_graspTranspose_rotY] at h
  simp [scaraPrintedJ₁₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h

/-- **The conclusion of the SCARA example of MLS §5.3, printed p. 242**: the two-SCARA grasp is not
manipulable (Definition 5.5) at the object configuration of Figure 5.17, for every finger
configuration (MLS states it for "the particular configuration shown"). Its grasp is that of
Example 5.2, which is force-closure for `r ≠ 0` (`boxSpatialGrasp_isForceClosure`). -/
theorem scaraHand_not_isManipulable (μ γ r b l₁ l₂ l₃ l₄ a : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (θ : Fin 2 → Fin 4 → ℝ) :
    ¬ ((scaraHand μ γ r b l₁ l₂ l₃ l₄ hμ hγ).toMultifingeredGrasp θ
      (scaraObjectPose a)).IsManipulable := by
  intro hm
  obtain ⟨θ', hθ'⟩ := hm ⟨0, vec 0 1 0⟩
  exact scaraHand_graspTranspose_rotY_not_mem_range μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θ ⟨θ', hθ'⟩

end RoboLean.Examples
