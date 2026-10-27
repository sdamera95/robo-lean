import RoboLean.Grasp.RollingHand
import RoboLean.Examples.HandGrasp
import RoboLean.Examples.RollingContact

/-!
# Two spherical fingertips rolling on a box (MLS §6.3 with Example 5.2)

MLS Chapter 5, §6.3, printed pp. 253–255 (eqs. (5.40)–(5.41), Proposition 5.12), applied to the
two-fingered grasp of the box of Example 5.2 (p. 221) by the Cartesian fingers of the hand examples
of §5, with the spherical fingertip of Example 5.7 (p. 253).

**The hand.** `rollingBoxHand` is the rolling hand of the soft-finger box hand (`softHand`: soft
fingers with `μ, γ > 0`, contact frames `boxFrame r` on the faces `y = ∓r`, Cartesian fingers with
bases `(0, ∓b, 0)`), with the fingertip of each finger a sphere of radius `ρ > 0` centred at the
fingertip frame, charted by `sphereChart ρ (−1)` (the outward chart of Example 5.7), and with each
face charted by the tangent plane of its contact frame (`tangentPlaneChart`, curvature `0`).

**The grasp.** With the box at the palm (`x_o = 1`) and the joints `θ₁ = (0, b − r − ρ, 0)`,
`θ₂ = (0, r + ρ − b, 0)`, each sphere touches its face at the face's contact point, with contact
coordinates `η₁ = ((0, −π/2), 0, 0)` and `η₂ = ((0, π/2), 0, π/2)` (`rollingBoxHand_fingerPose`). At
these coordinates the rolling hand is the soft-finger box hand itself
(`rollingBoxHand_toHandGrasp`), so it is force-closure and not manipulable, as in §5.

**Rolling.** The relative curvature form of each contact is `(1/ρ) I`, so Proposition 5.12 applies
and the first line of (5.40) is (5.41) with the contact coordinates read from the finger poses
(`rollingBoxHand_graspingConstraintOfPose`). Along every motion that keeps both contacts (contact
coordinates with derivatives, sphere coordinates in the chart domain), the first line of (5.40)
holds exactly when both fingertips roll (`rollingBoxHand_graspingConstraint_iff`). The motion in
which the box and both fingers translate together along `x` keeps both contacts at fixed contact
coordinates and satisfies every hypothesis (`rollingBoxHand_coTranslation`).

Concrete hands and motions are convention checks for the general theorems; they say nothing about a
physical hand, contact forces or the persistence of contact.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Surface Rolling

/-- **The box hand of MLS Example 5.2 (p. 221) with rolling spherical fingertips (MLS §6.3, p. 254,
Example 5.7, p. 253):** the soft-finger box hand `softHand μ γ r b` as a rolling hand, each
fingertip the sphere `sphereChart ρ (−1)` of radius `ρ` in its fingertip frame, each face charted by
the tangent plane of its contact frame. -/
def rollingBoxHand (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    RollingHand (Fin 2) (fun _ => 4) fun _ => 3 :=
  RollingHand.ofHandGrasp (softHand μ γ r b hμ hγ) fun _ => sphereChart ρ (-1)

/-- The fingertip charts of `rollingBoxHand` are the sphere charts of MLS Example 5.7, p. 253. -/
@[simp] theorem rollingBoxHand_fingerChart (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (i : Fin 2) :
    (rollingBoxHand μ γ r b ρ hμ hγ).fingerChart i = sphereChart ρ (-1) := rfl

/-- The face charts of `rollingBoxHand` are the tangent planes of the contact frames of MLS Example
5.2, p. 221. -/
@[simp] theorem rollingBoxHand_objectChart (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (i : Fin 2) :
    (rollingBoxHand μ γ r b ρ hμ hγ).objectChart i = tangentPlaneChart (boxFrame r i) := rfl

/-- **The contact coordinates of the grasp (MLS p. 249, `η = (α_f, α_o, ψ)`):**
`η₁ = ((0, −π/2), 0, 0)` and `η₂ = ((0, π/2), 0, π/2)`. -/
def rollingBoxContact : Fin 2 → ContactCoords :=
  ![(![0, -(π / 2)], 0, 0), (![0, π / 2], 0, π / 2)]

/-- **The joint angles of the grasp (MLS p. 236):** `θ₁ = (0, b − r − ρ, 0)` and
`θ₂ = (0, r + ρ − b, 0)`, which put the sphere centres at `(0, ∓(r + ρ), 0)`. -/
def rollingBoxJoints (r b ρ : ℝ) : Fin 2 → Fin 3 → ℝ :=
  ![![0, b - r - ρ, 0], ![0, r + ρ - b, 0]]

/-- **At contact coordinates on the contact points of the faces, the rolling box hand is the
soft-finger box hand (MLS p. 254 with Example 5.2, p. 221).** -/
theorem rollingBoxHand_toHandGrasp (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    {η : Fin 2 → ContactCoords} (hη : ∀ i, (η i).2.1 = 0) :
    (rollingBoxHand μ γ r b ρ hμ hγ).toHandGrasp η = softHand μ γ r b hμ hγ :=
  RollingHand.toHandGrasp_ofHandGrasp _ _ hη

/-- **"All of the definitions and properties which held for fixed contact grasps also hold for
moving contact grasps" (MLS p. 255), on the box (p. 242):** at contact coordinates on the contact
points of the faces, the rolling box hand is force-closure for `r ≠ 0` and is not manipulable, at
every configuration `(θ, x_o)`. -/
theorem rollingBoxHand_isForceClosure_not_isManipulable (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (hr : r ≠ 0) (θ : Fin 2 → Fin 3 → ℝ) (xo : RigidTransform) {η : Fin 2 → ContactCoords}
    (hη : ∀ i, (η i).2.1 = 0) :
    (((rollingBoxHand μ γ r b ρ hμ hγ).toHandGrasp η).toMultifingeredGrasp θ xo).IsForceClosure ∧
      ¬ (((rollingBoxHand μ γ r b ρ hμ hγ).toHandGrasp η).toMultifingeredGrasp θ
        xo).IsManipulable := by
  rw [rollingBoxHand_toHandGrasp μ γ r b ρ hμ hγ hη]
  exact ⟨softHand_isForceClosure μ γ r b hμ hγ hr θ xo,
    softHand_not_isManipulable μ γ r b hμ hγ θ xo⟩

/-- The forward kinematics of a Cartesian finger with reference pose the identity is the translation
by the joint vector (supporting lemma for MLS p. 87, prismatic twists, and p. 236). -/
private theorem cartesianFinger_one_fk (θ : Fin 3 → ℝ) :
    (cartesianFinger 1).fk θ = ⟨1, WithLp.toLp 2 ![θ 0, θ 1, θ 2]⟩ := by
  simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, cartesianFinger, List.ofFn_succ,
    Twist.exp_prismatic]
  apply RigidTransform.ext
  · simp
  · ext i
    fin_cases i <;> simp [Rotation.xAxis, Rotation.yAxis, Rotation.zAxis]

/-- The contact frame of the outward sphere chart of MLS Example 5.7 (p. 253) on its equator: at
`(0, v)`, `c_f = (ρ cos v, −ρ sin v, 0)` and the normalized Gauss frame has columns `x = e_z`,
`y = (−sin v, −cos v, 0)` and `n = (cos v, −sin v, 0)` (MLS eq. (5.22), p. 245). -/
private theorem contactFrame_sphereChart_equator {ρ v : ℝ} (hρ : 0 < ρ)
    (hv : (![0, v] : Fin 2 → ℝ) ∈ sphereDomain) :
    (gaussFrame (sphereChart ρ (-1)) ![0, v]).val =
        !![0, -sin v, cos v; 0, -cos v, -sin v; 1, 0, 0] ∧
      (contactFrame (sphereChart ρ (-1)) ![0, v]).translation =
        WithLp.toLp 2 ![ρ * cos v, -(ρ * sin v), 0] := by
  have hO := isOrthogonalChartOn_sphereChart hρ (show (-1 : ℝ) ^ 2 = 1 by norm_num)
  have hM := metricTensor_sphereChart hρ (show (-1 : ℝ) ^ 2 = 1 by norm_num) hv
  have hu : ‖partialU (sphereChart ρ (-1)) ![0, v]‖ = ρ := by
    simpa [metricTensor] using congrFun (congrFun hM 0) 0
  have hvv : ‖partialV (sphereChart ρ (-1)) ![0, v]‖ = ρ := by
    simpa [metricTensor] using congrFun (congrFun hM 1) 1
  constructor
  · rw [gaussFrame_val (hO.orthogonal _ hv) (hO.partialU_ne_zero hv)
      (hO.partialV_ne_zero hv), gaussFrameMatrix, frameX, frameY, hu, hvv,
      gaussNormal_sphereChart hρ (show (-1 : ℝ) ^ 2 = 1 by norm_num) hv, partialU_sphereChart,
      partialV_sphereChart]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sphereChart] <;> field_simp
  · simp [sphereChart]

/-- **Both spheres touch their faces (MLS p. 249, `g_of ∈ W`):** with the box at the palm and the
joints `rollingBoxJoints`, the relative pose of finger `i` is the contact pose `g_of(ηᵢ)` of its
sphere chart and face chart at the contact coordinates `rollingBoxContact`, for `ρ > 0`. -/
theorem rollingBoxHand_fingerPose (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (i : Fin 2) :
    (rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i (rollingBoxJoints r b ρ i) 1 =
      relativePoseMap (sphereChart ρ (-1)) (tangentPlaneChart (boxFrame r i))
        (rollingBoxContact i) := by
  have hD0 : (![0, -(π / 2)] : Fin 2 → ℝ) ∈ sphereDomain := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [pi_pos]
  have hD1 : (![0, π / 2] : Fin 2 → ℝ) ∈ sphereDomain := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [pi_pos]
  simp only [RollingHand.fingerPose, rollingBoxHand, RollingHand.ofHandGrasp, softHand, boxHand,
    relativePoseMap, relativePose]
  rw [contactFrame_mul_contactOffset, inwardContactFrame_tangentPlaneChart]
  fin_cases i
  · obtain ⟨hR, hp⟩ := contactFrame_sphereChart_equator hρ hD0
    simp only [rollingBoxContact, rollingBoxJoints, boxHandBase, boxFrame, Fin.zero_eta,
      Fin.isValue, Matrix.cons_val_zero]
    rw [cartesianFinger_one_fk]
    apply RigidTransform.ext
    · apply Subtype.ext
      simp only [RigidTransform.mul_rotation, RigidTransform.inv_rotation, Submonoid.coe_mul,
        Rotation.inv_val, contactFrame_rotation, hR, Rotation.zRotation_val]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [boxRotation₁, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
    · simp only [RigidTransform.mul_translation, RigidTransform.inv_translation,
        RigidTransform.inv_rotation, hp]
      ext k
      fin_cases k <;>
        simp [Rotation.act_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hR,
          boxRotation₁, Rotation.zRotation_val]
      ring
  · obtain ⟨hR, hp⟩ := contactFrame_sphereChart_equator hρ hD1
    simp only [rollingBoxContact, rollingBoxJoints, boxHandBase, boxFrame, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [cartesianFinger_one_fk]
    apply RigidTransform.ext
    · apply Subtype.ext
      simp only [RigidTransform.mul_rotation, RigidTransform.inv_rotation, Submonoid.coe_mul,
        Rotation.inv_val, contactFrame_rotation, hR, Rotation.zRotation_val]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [boxRotation₂, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
    · simp only [RigidTransform.mul_translation, RigidTransform.inv_translation,
        RigidTransform.inv_rotation, hp]
      ext k
      fin_cases k <;>
        simp [Rotation.act_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hR,
          boxRotation₂, Rotation.zRotation_val]
      ring

/-- The linear part of a tangent-plane chart, `γ ↦ R (γ₀, −γ₁, 0)` (supporting lemma for MLS p. 246,
the flat case). -/
private def tangentPlaneLinear (g : RigidTransform) : (Fin 2 → ℝ) →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun γ => g.rotation.act (WithLp.toLp 2 ![γ 0, -γ 1, 0])
      map_add' := fun γ δ => by
        rw [← map_add]
        congr 1
        ext i
        fin_cases i <;> simp
        ring
      map_smul' := fun c γ => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext i
        fin_cases i <;> simp }

/-- A tangent-plane chart is affine (supporting lemma for MLS p. 246, the flat case). -/
private theorem tangentPlaneChart_eq_affine (g : RigidTransform) :
    tangentPlaneChart g = fun γ => g.translation + tangentPlaneLinear g γ := by
  funext γ
  rw [tangentPlaneChart, RigidTransform.applyPoint, add_comm]
  rfl

/-- **The relative curvature form of each contact is `(1/ρ) I` (MLS p. 250),** invertible for
`ρ > 0`: the hypothesis of Theorem 5.11 and Proposition 5.12 holds at every contact coordinate with
the sphere coordinates in the chart domain. -/
theorem rollingBoxHand_relativeCurvature (r ρ : ℝ) (hρ : 0 < ρ) (i : Fin 2) {η : ContactCoords}
    (hη : η.1 ∈ sphereDomain) :
    relativeCurvature (curvatureTensor (sphereChart ρ (-1)) η.1)
        (curvatureTensor (tangentPlaneChart (boxFrame r i)) η.2.1) η.2.2 = !![1 / ρ, 0; 0, 1 / ρ] ∧
      IsUnit (relativeCurvature (curvatureTensor (sphereChart ρ (-1)) η.1)
        (curvatureTensor (tangentPlaneChart (boxFrame r i)) η.2.1) η.2.2).det := by
  have hK : relativeCurvature (curvatureTensor (sphereChart ρ (-1)) η.1)
      (curvatureTensor (tangentPlaneChart (boxFrame r i)) η.2.1) η.2.2 =
        !![1 / ρ, 0; 0, 1 / ρ] := by
    rw [curvatureTensor_sphereChart hρ (by norm_num) hη, tangentPlaneChart_eq_affine,
      curvatureTensor_affine]
    ext a c
    fin_cases a <;> fin_cases c <;> simp [relativeCurvature, rotatedCurvature]
  refine ⟨hK, ?_⟩
  rw [hK, isUnit_iff_ne_zero, Matrix.det_fin_two_of]
  have : (1 / ρ) ≠ 0 := by positivity
  simpa using this

/-- The contact coordinates of the grasp lie in the domain of the sphere chart (supporting lemma for
MLS Example 5.7, p. 253). -/
private theorem rollingBoxContact_mem (i : Fin 2) : (rollingBoxContact i).1 ∈ sphereDomain := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [rollingBoxContact] <;> linarith [pi_pos]

/-- **MLS eq. (5.41), p. 255, for the rolling box hand at its grasp:** there are readouts `Ψᵢ`, `C¹`
at the contact poses (Proposition 5.12, p. 254), such that at the grasp (`θ = rollingBoxJoints`,
`x_o = 1`, `η = rollingBoxContact`) the first line of (5.40) holds for joint rates `θ̇` and an
object twist `V` exactly when (5.41) does with the contact coordinates read as `Ψᵢ(g_{ofᵢ})`. -/
theorem rollingBoxHand_graspingConstraintOfPose (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (hρ : 0 < ρ) :
    ∃ Ψ : Fin 2 → PoseCoords → ContactCoords,
      (∀ i, ContDiffAt ℝ 1 (Ψ i) (poseCoords (relativePoseMap (sphereChart ρ (-1))
        (tangentPlaneChart (boxFrame r i)) (rollingBoxContact i)))) ∧
      ∀ (θ' : Fin 2 → Fin 3 → ℝ) (V : Twist),
        (rollingBoxHand μ γ r b ρ hμ hγ).GraspingConstraint (rollingBoxJoints r b ρ) 1
            rollingBoxContact θ' V ↔
          (rollingBoxHand μ γ r b ρ hμ hγ).GraspingConstraintOfPose
            (fun i g => Ψ i (poseCoords g)) (rollingBoxJoints r b ρ) 1 θ' V := by
  obtain ⟨N, Ψ, hN, hC, H⟩ := RollingHand.exists_graspingConstraint_iff_graspingConstraintOfPose
    (rollingBoxHand μ γ r b ρ hμ hγ) (Uf := fun _ => sphereDomain) (Uo := fun _ => Set.univ)
    (fun _ => isOrthogonalChartOn_sphereChart hρ (by norm_num))
    (fun i => isOrthogonalChartOn_tangentPlaneChart (boxFrame r i)) (η₀ := rollingBoxContact)
    rollingBoxContact_mem (fun _ => Set.mem_univ _)
    (fun i => (rollingBoxHand_relativeCurvature r ρ hρ i (rollingBoxContact_mem i)).2)
  exact ⟨Ψ, hC, fun θ' V => H _ _ _ (fun i => mem_of_mem_nhds (hN i))
    (fun i => rollingBoxHand_fingerPose μ γ r b ρ hμ hγ hρ i) θ' V⟩

/-- **MLS eq. (5.40), p. 254, for the rolling box hand: the first line holds exactly when both
fingertips roll.** Along joint and object trajectories with actual derivatives that keep both
contacts near `t` (`g_{ofᵢ}(s) = g_of(ηᵢ(s))`, contact coordinates with actual derivatives, sphere
coordinates in the chart domain), `J_h(θ, x_o, η) θ̇ = Gᵀ(η) V^b_{po}` holds at `t` exactly when
both relative twists `V_{l_o l_f}` are pure rollings (MLS p. 249). -/
theorem rollingBoxHand_graspingConstraint_iff (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (hρ : 0 < ρ) {θ : ℝ → Fin 2 → Fin 3 → ℝ} {θ' : Fin 2 → Fin 3 → ℝ} {xo : ℝ → RigidTransform}
    {Do : HomogeneousMatrix} {η : ℝ → Fin 2 → ContactCoords} {η' : Fin 2 → ContactCoords} {t : ℝ}
    (hθ : ∀ i l, HasDerivAt (fun s => θ s i l) (θ' i l) t)
    (ho : HasDerivAt (fun s => (xo s).toHomogeneous) Do t)
    (hη : ∀ i, HasDerivAt (fun s => η s i) (η' i) t) (hηf : ∀ i, (η t i).1 ∈ sphereDomain)
    (hg : ∀ i, ∀ᶠ s in 𝓝 t, (rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i (θ s i) (xo s) =
      relativePoseMap (sphereChart ρ (-1)) (tangentPlaneChart (boxFrame r i)) (η s i))
    {E : Fin 2 → HomogeneousMatrix}
    (hE : ∀ i, HasDerivAt
      (fun s => ((rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i (θ s i) (xo s)).toHomogeneous)
      (E i) t) :
    (rollingBoxHand μ γ r b ρ hμ hγ).GraspingConstraint (θ t) (xo t) (η t) θ'
        (RigidTransform.bodyVelocity xo Do t ho) ↔
      ∀ i, IsRolling (Twist.adjoint (contactFrame (sphereChart ρ (-1)) (η t i).1)⁻¹
        (RigidTransform.bodyVelocity
          (fun s => (rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i (θ s i) (xo s)) (E i) t
          (hE i))) :=
  RollingHand.softFinger_graspingConstraint_iff μ γ hμ hγ (rollingBoxHand μ γ r b ρ hμ hγ)
    (fun _ => rfl) (Uf := fun _ => sphereDomain) (Uo := fun _ => Set.univ)
    (fun _ => isOrthogonalChartOn_sphereChart hρ (by norm_num))
    (fun i => isOrthogonalChartOn_tangentPlaneChart (boxFrame r i)) hθ ho hη hηf
    (fun _ => Set.mem_univ _) hg hE

/-- **The box and both fingers translating together along `x` (instance of MLS eq. (5.40), p.
254):** the object pose `(I, (s, 0, 0))` and the joints `rollingBoxJoints + (s, 0, 0)`. -/
def coTranslationObject (s : ℝ) : RigidTransform := ⟨1, WithLp.toLp 2 ![s, 0, 0]⟩

/-- **The joints of the co-translation (instance of MLS eq. (5.40), p. 254):**
`θᵢ(s) = rollingBoxJoints ᵢ + (s, 0, 0)`. -/
def coTranslationJoints (r b ρ s : ℝ) : Fin 2 → Fin 3 → ℝ :=
  fun i => rollingBoxJoints r b ρ i + ![s, 0, 0]

/-- A pose curve with zero homogeneous derivative has zero body velocity (supporting lemma for MLS
eq. (2.60), p. 55). -/
private theorem bodyVelocity_zero {g : ℝ → RigidTransform} {t : ℝ}
    (hD : HasDerivAt (fun s => (g s).toHomogeneous) 0 t) :
    RigidTransform.bodyVelocity g 0 t hD = 0 := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_bodyVelocity, Matrix.mul_zero, Twist.hat_zero]

/-- **A motion satisfying every hypothesis of `rollingBoxHand_graspingConstraint_iff` (MLS eq.
(5.40), p. 254):** in the co-translation both contacts are kept at the fixed contact coordinates
`rollingBoxContact` for every `s`, the joint rates are `(1, 0, 0)`, the object twist is
`V^b_{po} = ((1, 0, 0), 0)`, and the first line of (5.40) holds at `t = 0` (both fingertips have
zero relative twist, a pure rolling). -/
theorem rollingBoxHand_coTranslation (μ γ r b ρ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) (hρ : 0 < ρ) :
    ∃ (Do : HomogeneousMatrix)
      (ho : HasDerivAt (fun s => (coTranslationObject s).toHomogeneous) Do 0),
      (∀ i s, (rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i (coTranslationJoints r b ρ s i)
          (coTranslationObject s) =
        relativePoseMap (sphereChart ρ (-1)) (tangentPlaneChart (boxFrame r i))
          (rollingBoxContact i)) ∧
      RigidTransform.bodyVelocity coTranslationObject Do 0 ho = ⟨WithLp.toLp 2 ![1, 0, 0], 0⟩ ∧
      (rollingBoxHand μ γ r b ρ hμ hγ).GraspingConstraint (coTranslationJoints r b ρ 0)
        (coTranslationObject 0) rollingBoxContact (fun _ => ![1, 0, 0])
        (RigidTransform.bodyVelocity coTranslationObject Do 0 ho) := by
  have hR : HasDerivAt (fun s => (coTranslationObject s).rotation.val) 0 0 :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => by
      simpa [coTranslationObject] using
        hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
  have hp : HasDerivAt (fun s => (coTranslationObject s).translation)
      (WithLp.toLp 2 ![1, 0, 0]) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const (WithLp.toLp 2 ![1, 0, 0] : Vec3)
    convert h using 1
    · funext s
      apply WithLp.ofLp_injective
      funext k
      fin_cases k <;> simp [coTranslationObject]
    · simp
  have ho := Surface.hasDerivAt_toHomogeneous_of hR hp
  have hfp : ∀ i s, (rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i
      (coTranslationJoints r b ρ s i) (coTranslationObject s) =
        relativePoseMap (sphereChart ρ (-1)) (tangentPlaneChart (boxFrame r i))
          (rollingBoxContact i) := by
    intro i s
    rw [← rollingBoxHand_fingerPose μ γ r b ρ hμ hγ hρ i]
    simp only [RollingHand.fingerPose, rollingBoxHand, RollingHand.ofHandGrasp, softHand, boxHand,
      cartesianFinger_one_fk]
    apply RigidTransform.ext
    · simp [coTranslationObject]
    · ext k
      fin_cases i <;> fin_cases k <;>
        simp [coTranslationObject, coTranslationJoints, rollingBoxJoints, boxHandBase]
  refine ⟨_, ho, hfp, ?_, ?_⟩
  · have h0 : coTranslationObject 0 = 1 := by
      apply RigidTransform.ext
      · rfl
      · ext k
        fin_cases k <;> rfl
    apply Twist.hat_injective
    rw [RigidTransform.hat_bodyVelocity, h0, RigidTransform.toHomogeneous_one, inv_one,
      Matrix.one_mul, Twist.hat]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Vec3.hat]
  · have hθ : ∀ i l, HasDerivAt (fun s => coTranslationJoints r b ρ s i l)
        ((fun _ => ![1, 0, 0] : Fin 2 → Fin 3 → ℝ) i l) 0 := by
      intro i l
      fin_cases l
      · simpa [coTranslationJoints] using
          (hasDerivAt_id' (0 : ℝ)).const_add (rollingBoxJoints r b ρ i 0)
      · simpa [coTranslationJoints] using hasDerivAt_const (0 : ℝ) (rollingBoxJoints r b ρ i 1)
      · simpa [coTranslationJoints] using hasDerivAt_const (0 : ℝ) (rollingBoxJoints r b ρ i 2)
    have hE : ∀ i, HasDerivAt (fun s => ((rollingBoxHand μ γ r b ρ hμ hγ).fingerPose i
        (coTranslationJoints r b ρ s i) (coTranslationObject s)).toHomogeneous) 0 0 := by
      intro i
      refine hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun c => ?_
      simpa [hfp] using hasDerivAt_const (0 : ℝ) ((relativePoseMap (sphereChart ρ (-1))
        (tangentPlaneChart (boxFrame r i)) (rollingBoxContact i)).toHomogeneous a c)
    refine (rollingBoxHand_graspingConstraint_iff μ γ r b ρ hμ hγ hρ
      (θ := fun s => coTranslationJoints r b ρ s) (η := fun _ => rollingBoxContact) (η' := 0)
      hθ ho (fun i => hasDerivAt_const (0 : ℝ) (rollingBoxContact i)) rollingBoxContact_mem
      (fun i => Filter.Eventually.of_forall fun s => hfp i s) hE).mpr fun i => ?_
    rw [bodyVelocity_zero, Twist.adjoint_zero]
    exact ⟨by simp, by simp, by simp⟩

end Examples
end RoboLean
