import RoboLean.Examples.ScaraKinematics
import RoboLean.Grasp.ScaraFingertip

/-!
# Two SCARA fingers with a fingertip length grasping a box (MLS Chapter 5, Exercises 11–12)

MLS Chapter 5, Exercise 11, printed p. 261: "Calculate the contact constraints for the grasp shown
in Figure 5.17 with `l₃ > 0`." The example of §5.3 (pp. 240–242) takes the fingertip length
`l₃ = 0` and remarks that for `l₃ ≠ 0` "we must recompute the Jacobian to include the additional
displacement (see Exercise 11)" (p. 240) and that "the internal motion still exists but all three
revolute joints will have nonzero instantaneous velocities" (p. 242).

Figure reading (Figure 5.17, p. 241, rendered): the fingertip of length `l₃` is horizontal, at the
foot of the vertical rod carried by the third revolute joint and the prismatic joint, and points
from the joint axis towards the contact. In the joint coordinates of MLS Example 3.1 (arm along
`+y` at `θ = 0`) the fingertip chain has the SCARA joint twists and the reference tool pose
`g_st(0) = (I, (0, l₁ + l₂ + l₃, l₀))` (`scaraFingertipChain`).

**Formalized.**

* The forward kinematics of the fingertip chain as a product of exponentials:
  `g_st(θ) = (Rz(θ₁ + θ₂ + θ₃), (−l₁s₁ − l₂s₁₂ − l₃s₁₂₃, l₁c₁ + l₂c₁₂ + l₃c₁₂₃, l₀ + θ₄))`
  (`scaraFingertipChain_fk`).
* The hand of Figure 5.17 with fingertip length `d` on both fingers (`scaraFingertipHand`; the
  book's `l₃` of p. 240, renamed because `l₃, l₄` are finger 2's links in the printed `J₂₂`). Its
  hand Jacobian is the printed one for every finger configuration
  (`scaraFingertipHand_fingerJacobianMatrix_zero`, `scaraFingertipHand_fingerJacobianMatrix_one`):
  the spatial Jacobian depends only on the joint twists, so the fingertip length enters the
  contact constraint `J_h θ̇ = Gᵀ V^b_{po}` only through the configurations at which the fingertip
  meets the contact point (`scaraFingertipHand_location_zero_iff`).
* At such a configuration with `d ≠ 0` the third joint is no longer an internal motion
  (`scaraFingertipHand_not_isInternalMotion_single_two`); the vector
  `scaraFingertipInternalMotion` is an internal motion at every configuration
  (`scaraFingertipHand_isInternalMotion`), at a contact configuration its revolute components are
  `(d((b − r) sin θ₁₂₃ − l₁ sin θ₂₃), −(b − r) d sin θ₁₂₃, −(b − r) l₁ sin θ₁)`
  (`scaraFingertipInternalMotion_of_location`), all three nonzero under the stated nonvanishing
  conditions, and proportional to the printed `e₃` when `d = 0`. The grasp is still not
  manipulable (`scaraFingertipHand_not_isManipulable`).
* Exercise 12: equating the fingertip location with the contact location and differentiating
  gives the translational rows of the contact constraint; this is proved for every hand
  (`HandGrasp.linear_adjoint_spatialJacobian_eq_of_location` and its converse), so it applies to
  `scaraFingertipHand` and to the hand of the printed example (`d = 0`) alike.

Reading (derivation). "Recompute the Jacobian" (p. 240) is not needed for the spatial Jacobian
`J^s_{sᵢfᵢ}` of eq. (5.13), which does not depend on the tool frame; what changes with `l₃` is
the set of contact configurations, at which the hand Jacobian is evaluated. These are statements
about the coordinate model; nothing here concerns a physical hand.
-/

noncomputable section

namespace RoboLean.Examples

open Matrix Grasp Real

/-- The SCARA finger with a fingertip of length `l₃` (MLS Chapter 5, Exercise 11, p. 261, and
Figure 5.17, p. 241): the joint twists of `scaraChain l₁ l₂` (MLS Examples 3.1 and 3.8) and the
reference tool pose `g_st(0) = (I, (0, l₁ + l₂ + l₃, l₀))`, the fingertip pointing along the last
link at `θ = 0`. -/
def scaraFingertipChain (l₀ l₁ l₂ l₃ : ℝ) : SerialChain 4 :=
  { scaraChain l₁ l₂ with toolRef := ⟨1, vec 0 (l₁ + l₂ + l₃) l₀⟩ }

/-- **The forward kinematics of the SCARA finger with a fingertip** (MLS Exercise 11, p. 261, by
the product of exponentials, eq. (3.3), p. 87):
`g_st(θ) = (Rz(θ₁ + θ₂ + θ₃), (−l₁s₁ − l₂s₁₂ − l₃s₁₂₃, l₁c₁ + l₂c₁₂ + l₃c₁₂₃, l₀ + θ₄))`. -/
theorem scaraFingertipChain_fk (l₀ l₁ l₂ l₃ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraFingertipChain l₀ l₁ l₂ l₃).fk θ =
      ⟨Rotation.zRotation (θ 0 + θ 1 + θ 2),
        vec (-l₁ * sin (θ 0) - l₂ * sin (θ 0 + θ 1) - l₃ * sin (θ 0 + θ 1 + θ 2))
          (l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1) + l₃ * cos (θ 0 + θ 1 + θ 2)) (l₀ + θ 3)⟩ := by
  have htool : (⟨1, vec 0 (l₁ + l₂ + l₃) l₀⟩ : RigidTransform) =
      ⟨1, vec 0 (l₁ + l₂) l₀⟩ * ⟨1, vec 0 l₃ 0⟩ := by
    apply RigidTransform.ext
    · simp
    · rw [RigidTransform.mul_translation]
      ext i
      fin_cases i
      all_goals simp [vec]
      ring
  have h : (scaraFingertipChain l₀ l₁ l₂ l₃).fk θ =
      (scaraKinematicChain l₀ l₁ l₂).fk θ * ⟨1, vec 0 l₃ 0⟩ := by
    rw [SerialChain.fk, SerialChain.fk, mul_assoc]
    change (scaraKinematicChain l₀ l₁ l₂).poe θ *
      (⟨1, vec 0 (l₁ + l₂ + l₃) l₀⟩ : RigidTransform) = _
    rw [htool]
    rfl
  rw [h, scaraKinematicChain_fk]
  apply RigidTransform.ext
  · simp
  · rw [RigidTransform.mul_translation]
    ext i
    fin_cases i <;>
      simp [vec, Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;> ring

/-- The two-SCARA hand of MLS Figure 5.17 (p. 241) with a fingertip of length `d` on both
fingers (MLS Exercise 11, p. 261; the book's `l₃` of p. 240): the soft-finger box grasp of Example
5.2, finger 1 with links `l₁, l₂`, finger 2 with links `l₃, l₄` (the names of the printed `J₂₂`),
both fingers based at height `l₀` below the reference tool, and the finger bases
`g_{ps₁} = (I, (0, −b, 0))`, `g_{ps₂} = (I, (0, b, 0))`. -/
def scaraFingertipHand (μ γ r b l₀ l₁ l₂ l₃ l₄ d : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    HandGrasp (Fin 2) (fun _ => 4) fun _ => 4 :=
  ⟨boxSpatialGrasp μ γ r hμ hγ, ![scaraFingertipChain l₀ l₁ l₂ d, scaraFingertipChain l₀ l₃ l₄ d],
    boxHandBase b⟩

/-- **MLS Exercise 11, p. 261: the block `J₁₁` with a fingertip** is the printed `J₁₁` of p. 242,
for every finger configuration and every fingertip length. -/
theorem scaraFingertipHand_fingerJacobianMatrix_zero (μ γ r b l₀ l₁ l₂ l₃ l₄ d a : ℝ)
    (hμ : 0 < μ) (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    (scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).fingerJacobianMatrix (scaraObjectPose a) 0
      θi = scaraPrintedJ₁₁ r b l₁ l₂ θi := by
  rw [← scaraHand_fingerJacobianMatrix_zero μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θi]
  rfl

/-- **MLS Exercise 11, p. 261: the block `J₂₂` with a fingertip** is the printed `J₂₂` of p. 242,
for every finger configuration and every fingertip length. -/
theorem scaraFingertipHand_fingerJacobianMatrix_one (μ γ r b l₀ l₁ l₂ l₃ l₄ d a : ℝ)
    (hμ : 0 < μ) (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    (scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).fingerJacobianMatrix (scaraObjectPose a) 1
      θi = scaraPrintedJ₂₂ r b l₃ l₄ θi := by
  rw [← scaraHand_fingerJacobianMatrix_one μ γ r b l₁ l₂ l₃ l₄ a hμ hγ θi]
  rfl

/-- **The contact configurations of finger 1 with a fingertip** (MLS Exercise 11, p. 261, Figure
5.17): at the object configuration of p. 241 the fingertip of finger 1 is at the contact point
exactly when `l₁s₁ + l₂s₁₂ + ds₁₂₃ = 0`, `l₁c₁ + l₂c₁₂ + dc₁₂₃ = b − r` and `l₀ + θ₄ = a`. -/
theorem scaraFingertipHand_location_zero_iff (μ γ r b l₀ l₁ l₂ l₃ l₄ d a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θi : Fin 4 → ℝ) :
    ((scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).base 0 *
        ((scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).finger 0).fk θi).translation =
      (scaraObjectPose a * (scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).grasp.frame 0
        ).translation ↔
      l₁ * sin (θi 0) + l₂ * sin (θi 0 + θi 1) + d * sin (θi 0 + θi 1 + θi 2) = 0 ∧
        l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) + d * cos (θi 0 + θi 1 + θi 2) = b - r ∧
        l₀ + θi 3 = a := by
  change ((boxHandBase b 0) * (scaraFingertipChain l₀ l₁ l₂ d).fk θi).translation =
    (scaraObjectPose a * boxFrame r 0).translation ↔ _
  rw [scaraFingertipChain_fk]
  have hL : ((boxHandBase b 0) * (⟨Rotation.zRotation (θi 0 + θi 1 + θi 2),
      vec (-l₁ * sin (θi 0) - l₂ * sin (θi 0 + θi 1) - d * sin (θi 0 + θi 1 + θi 2))
        (l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) + d * cos (θi 0 + θi 1 + θi 2))
        (l₀ + θi 3)⟩ : RigidTransform)).translation =
      vec (-l₁ * sin (θi 0) - l₂ * sin (θi 0 + θi 1) - d * sin (θi 0 + θi 1 + θi 2))
        (l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) + d * cos (θi 0 + θi 1 + θi 2) - b)
        (l₀ + θi 3) := by
    rw [RigidTransform.mul_translation]
    ext i
    fin_cases i
    all_goals simp [vec, boxHandBase]
    ring
  have hR : (scaraObjectPose a * boxFrame r 0).translation = vec 0 (-r) a := by
    rw [RigidTransform.mul_translation]
    ext i
    fin_cases i <;> simp [vec, scaraObjectPose, boxFrame]
  rw [hL, hR]
  constructor
  · intro h
    have h0 := congrArg (fun v : Vec3 => v 0) h
    have h1 := congrArg (fun v : Vec3 => v 1) h
    have h2 := congrArg (fun v : Vec3 => v 2) h
    simp [vec] at h0 h1 h2
    exact ⟨by linarith, by linarith, h2⟩
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;> simp [vec] <;> linarith

/-- The internal motion of finger 1 (MLS p. 242 and Exercise 11, p. 261), the cross product of the
second and third rows of `J₁₁` in the three revolute rates, with zero prismatic rate. -/
def scaraFingertipInternalMotion (r b l₁ l₂ : ℝ) (θi : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(-b + r + l₁ * cos (θi 0)) * (l₁ * sin (θi 0) + l₂ * sin (θi 0 + θi 1)) -
      (-b + r + l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1)) * (l₁ * sin (θi 0)),
    (b - r) * (l₁ * sin (θi 0) + l₂ * sin (θi 0 + θi 1)),
    -(b - r) * (l₁ * sin (θi 0)), 0]

/-- **The internal motion of finger 1** (MLS p. 242, "the internal motion still exists", and
Exercise 11, p. 261): `scaraFingertipInternalMotion` on finger 1 and zero rates on finger 2 is
an internal motion of the hand (`N(J_h)`) at every configuration and every fingertip length. -/
theorem scaraFingertipHand_isInternalMotion (μ γ r b l₀ l₁ l₂ l₃ l₄ d a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) :
    ((scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).toMultifingeredGrasp θ
        (scaraObjectPose a)).IsInternalMotion
      (Pi.single 0 (scaraFingertipInternalMotion r b l₁ l₂ (θ 0))) := by
  change (scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).handJacobian θ (scaraObjectPose a)
    (Pi.single 0 (scaraFingertipInternalMotion r b l₁ l₂ (θ 0))) = 0
  rw [HandGrasp.handJacobian_single, ← HandGrasp.fingerJacobianMatrix_mulVec,
    scaraFingertipHand_fingerJacobianMatrix_zero]
  have h0 : scaraPrintedJ₁₁ r b l₁ l₂ (θ 0) *ᵥ scaraFingertipInternalMotion r b l₁ l₂ (θ 0) = 0 := by
    funext j
    fin_cases j <;>
      simp [scaraPrintedJ₁₁, scaraFingertipInternalMotion, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] <;> ring
  rw [h0, Pi.single_zero]

/-- **The internal motion at a contact configuration** (MLS p. 242 and Exercise 11, p. 261): when
the fingertip of finger 1 is at the contact point, its revolute rates are
`(d((b − r) sin θ₁₂₃ − l₁ sin θ₂₃), −(b − r) d sin θ₁₂₃, −(b − r) l₁ sin θ₁)`; for `d = 0` this is
a multiple of the printed `θ̇_{N₁} = e₃`. -/
theorem scaraFingertipInternalMotion_of_location (r b l₁ l₂ d : ℝ) (θi : Fin 4 → ℝ)
    (hs : l₁ * sin (θi 0) + l₂ * sin (θi 0 + θi 1) + d * sin (θi 0 + θi 1 + θi 2) = 0)
    (hc : l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) + d * cos (θi 0 + θi 1 + θi 2) = b - r) :
    scaraFingertipInternalMotion r b l₁ l₂ θi =
      ![d * ((b - r) * sin (θi 0 + θi 1 + θi 2) - l₁ * sin (θi 1 + θi 2)),
        -(b - r) * d * sin (θi 0 + θi 1 + θi 2), -(b - r) * (l₁ * sin (θi 0)), 0] := by
  have hY : l₁ * sin (θi 0) + l₂ * sin (θi 0 + θi 1) = -(d * sin (θi 0 + θi 1 + θi 2)) := by
    linarith
  have hX : l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) = b - r - d * cos (θi 0 + θi 1 + θi 2) := by
    linarith
  have h23 : sin (θi 1 + θi 2) = sin (θi 0 + θi 1 + θi 2) * cos (θi 0) -
      cos (θi 0 + θi 1 + θi 2) * sin (θi 0) := by
    rw [show θi 1 + θi 2 = (θi 0 + θi 1 + θi 2) - θi 0 by ring, sin_sub]
  funext j
  fin_cases j
  · simp only [scaraFingertipInternalMotion, Fin.zero_eta, Matrix.cons_val_zero]
    rw [hY, show -b + r + l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1) =
      -b + r + (l₁ * cos (θi 0) + l₂ * cos (θi 0 + θi 1)) by ring, hX, h23]
    ring
  · simp only [scaraFingertipInternalMotion, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hY]
    ring
  · simp [scaraFingertipInternalMotion]
  · simp [scaraFingertipInternalMotion]

/-- **With a fingertip the third joint is not an internal motion** (MLS Exercise 11, p. 261,
against `θ̇_{N₁} = e₃` of p. 242 for `l₃ = 0`): at a contact configuration of finger 1 with
`d ≠ 0`, the third column of `J₁₁` is `(0, −d c₁₂₃, −d s₁₂₃, 0) ≠ 0`. -/
theorem scaraFingertipHand_not_isInternalMotion_single_two (μ γ r b l₀ l₁ l₂ l₃ l₄ d a : ℝ)
    (hμ : 0 < μ) (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) (hd : d ≠ 0)
    (hs : l₁ * sin (θ 0 0) + l₂ * sin (θ 0 0 + θ 0 1) + d * sin (θ 0 0 + θ 0 1 + θ 0 2) = 0)
    (hc : l₁ * cos (θ 0 0) + l₂ * cos (θ 0 0 + θ 0 1) + d * cos (θ 0 0 + θ 0 1 + θ 0 2) = b - r) :
    ¬ ((scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).toMultifingeredGrasp θ
        (scaraObjectPose a)).IsInternalMotion (Pi.single 0 (Pi.single 2 1)) := by
  intro hint
  change (scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).handJacobian θ (scaraObjectPose a)
    (Pi.single 0 (Pi.single 2 1)) = 0 at hint
  have h := congrFun hint 0
  rw [HandGrasp.handJacobian_single, Pi.single_eq_same, ← HandGrasp.fingerJacobianMatrix_mulVec,
    scaraFingertipHand_fingerJacobianMatrix_zero, Matrix.mulVec_single_one] at h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [scaraPrintedJ₁₁] at h1 h2
  have hc' : d * cos (θ 0 0 + θ 0 1 + θ 0 2) = 0 := by linarith
  have hs' : d * sin (θ 0 0 + θ 0 1 + θ 0 2) = 0 := by linarith
  have hcs := sin_sq_add_cos_sq (θ 0 0 + θ 0 1 + θ 0 2)
  have hcz : cos (θ 0 0 + θ 0 1 + θ 0 2) = 0 := (mul_eq_zero.mp hc').resolve_left hd
  have hsz : sin (θ 0 0 + θ 0 1 + θ 0 2) = 0 := (mul_eq_zero.mp hs').resolve_left hd
  rw [hcz, hsz] at hcs
  norm_num at hcs

/-- MLS p. 242 with a fingertip (Exercise 11, p. 261): the two-SCARA grasp with fingertip length
`d` is not manipulable at the object configuration of Figure 5.17, for every finger
configuration. -/
theorem scaraFingertipHand_not_isManipulable (μ γ r b l₀ l₁ l₂ l₃ l₄ d a : ℝ) (hμ : 0 < μ)
    (hγ : 0 < γ) (θ : Fin 2 → Fin 4 → ℝ) :
    ¬ ((scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).toMultifingeredGrasp θ
      (scaraObjectPose a)).IsManipulable := by
  intro hm
  obtain ⟨θ', hθ'⟩ := hm ⟨0, vec 0 1 0⟩
  have h := congrFun (congrFun hθ' 0) 3
  change (scaraFingertipHand μ γ r b l₀ l₁ l₂ l₃ l₄ d hμ hγ).handJacobian θ (scaraObjectPose a)
    θ' 0 3 = (boxSpatialGrasp μ γ r hμ hγ).graspTranspose ⟨0, vec 0 1 0⟩ 0 3 at h
  rw [HandGrasp.handJacobian_apply, ← HandGrasp.fingerJacobianMatrix_mulVec,
    scaraFingertipHand_fingerJacobianMatrix_zero, boxSpatialGrasp_graspTranspose_rotY] at h
  simp [scaraPrintedJ₁₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h

end RoboLean.Examples
