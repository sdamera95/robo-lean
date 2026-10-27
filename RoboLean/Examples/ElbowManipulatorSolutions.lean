import RoboLean.Examples.ElbowManipulator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Set.Card

/-!
# The eight solutions of the elbow manipulator's inverse kinematics

MLS Example 3.5, printed pp. 104–106: after the four subproblem steps, "θ₁ through θ₆ are
determined. There are a maximum of eight possible solutions, due to multiple solutions for
equations (3.33), (3.34), and (3.36)." This module states and proves that count for the elbow
manipulator `Examples.elbowManipulator l₀ l₁ l₂` of Example 3.2.

Solutions are counted modulo `2π` in each joint angle (real-lift convention, ledger K01): the
solution set is read in `Fin 6 → Real.Angle` (`elbowSolutionAngles`).

The candidates. With `g₁ = g_d g_st(0)⁻¹` (eq. (3.30)), the wrist centre `p_w`, the shoulder point
`p_b`, and three binary choices `b₁ b₂ b₃ : Bool`:

* Step 1, eq. (3.33): `θ₃ = θ₀ ± cos⁻¹ κ` (`elbowAngle₃`, sign `b₁`), the two angles of
  Subproblem 3 (eq. (3.29)), `κ = elbowKappa`;
* Step 2, eq. (3.34): Subproblem 2 for the shoulder axes with `p = e^{ξ̂₃θ₃} p_w` and
  `q = g₁ p_w`; its intermediate point `c = p_b + z` with `z` the candidate of eq. (3.24) for
  `γ = ±√Γ` (`elbowShoulderMid`, sign `b₂`), then `θ₂` and `θ₁` by the Subproblem 1 formula
  `atan2` (`PadenKahan.planeAngle`) from `p` to `c` and from `c` to `q`;
* Step 3, eq. (3.36): Subproblem 2 for the wrist axes 4 and 5 at the point `p = p_w + e_y` of
  the sixth axis and `q = g₂ p`, `g₂ = e^{-ξ̂₃θ₃} e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g₁` (eq. (3.35)), with the
  intermediate point for `γ = ±√Γ` (sign `b₃`), then `θ₅` and `θ₄`;
* Step 4, eq. (3.37): `θ₆` by the Subproblem 1 formula at the point `p′ = p_w + e_x` off the
  sixth axis.

Genericity hypotheses (the book states none): `l₁ ≠ 0`, `l₂ ≠ 0` (as in Step 1); the target of the
wrist centre is not on the first joint axis (`elbowShoulderRegular`: otherwise `θ₁` is free, the
shoulder singularity); for each of the four arm branches, the image of the sixth axis is not along
the fourth axis (`elbowWristRegular`: otherwise only `θ₄ + θ₆` is determined, the wrist
singularity). Under these, every solution is congruent modulo `2π` to one of the eight
candidates, so there are at most eight solutions modulo `2π`
(`ncard_elbowSolutionAngles_le_eight`). If moreover `-1 < κ < 1` (the target of the wrist centre
is strictly inside the annulus the elbow can reach), the eight candidates are solutions and are
pairwise distinct modulo `2π`, so there are exactly eight (`ncard_elbowSolutionAngles_eq_eight`).
If `|κ| > 1` there is no solution. These are statements about the coordinate model, not about a
physical arm or a numerical solver; joint limits are not modelled.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

/-- The target `g₁ p_w` of the wrist centre in MLS eq. (3.31), p. 105, with
`g₁ = g_d g_st(0)⁻¹` (eq. (3.30)). -/
def elbowTarget (l₀ l₁ l₂ : ℝ) (g : RigidTransform) : Vec3 :=
  (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂)

/-- The argument `κ` of `cos⁻¹` in MLS eq. (3.29), p. 103, for Step 1 of Example 3.5 (p. 105):
Subproblem 3 for the third axis (`ω = -x` through `(0, l₁, l₀)`) with `p = p_w`, `q = p_b` and
`δ = ‖g₁ p_w - p_b‖`. -/
def elbowKappa (l₀ l₁ l₂ : ℝ) (g : RigidTransform) : ℝ :=
  PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀) (elbowWrist l₀ l₁ l₂) (elbowShoulder l₀)
    ‖elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀‖

/-- **Step 1 (MLS eq. (3.33), p. 105, with eq. (3.29), p. 103): the two elbow angles**
`θ₃ = θ₀ + cos⁻¹ κ` (`b₁ = true`) and `θ₃ = θ₀ - cos⁻¹ κ` (`b₁ = false`). -/
def elbowAngle₃ (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ : Bool) : ℝ :=
  if b₁ then
    PadenKahan.planeAngle (-xAxis) (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
        (elbowShoulder l₀ - vec 0 l₁ l₀) + Real.arccos (elbowKappa l₀ l₁ l₂ g)
  else
    PadenKahan.planeAngle (-xAxis) (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
        (elbowShoulder l₀ - vec 0 l₁ l₀) - Real.arccos (elbowKappa l₀ l₁ l₂ g)

/-- The point `p = e^{ξ̂₃θ₃} p_w` of Step 2 (MLS eq. (3.34), p. 105) for the elbow angle of
branch `b₁`. -/
def elbowArmSource (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ : Bool) : Vec3 :=
  (Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (elbowAngle₃ l₀ l₁ l₂ g b₁)).applyPoint
    (elbowWrist l₀ l₁ l₂)

/-- **Step 2 (MLS eq. (3.34), p. 105, with eqs. (3.21)–(3.24), pp. 101–102): the intermediate
point** `c = p_b + αω₁ + βω₂ + γ(ω₁ × ω₂)` of Subproblem 2 for the shoulder axes `ω₁ = +z`,
`ω₂ = -x` through `p_b`, with `γ = √Γ` (`b₂ = true`) or `γ = -√Γ` (`b₂ = false`). -/
def elbowShoulderMid (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ : Bool) : Vec3 :=
  elbowShoulder l₀ +
    PadenKahan.subproblemTwoPoint zAxis (-xAxis)
      (elbowArmSource l₀ l₁ l₂ g b₁ - elbowShoulder l₀) (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀)
      (if b₂ then
        √(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis)
          (elbowArmSource l₀ l₁ l₂ g b₁ - elbowShoulder l₀)
          (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀))
      else
        -√(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis)
          (elbowArmSource l₀ l₁ l₂ g b₁ - elbowShoulder l₀)
          (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀)))

/-- **Step 2 (MLS p. 102): the angle `θ₂`**, by the Subproblem 1 formula (p. 100) about the
second axis from `p = e^{ξ̂₃θ₃} p_w` to the intermediate point `c`. -/
def elbowAngle₂ (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ : Bool) : ℝ :=
  PadenKahan.planeAngle (-xAxis) (elbowArmSource l₀ l₁ l₂ g b₁ - elbowShoulder l₀)
    (elbowShoulderMid l₀ l₁ l₂ g b₁ b₂ - elbowShoulder l₀)

/-- **Step 2 (MLS p. 102): the angle `θ₁`**, by the Subproblem 1 formula (p. 100) about the
first axis from the intermediate point `c` to `q = g₁ p_w`. -/
def elbowAngle₁ (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ : Bool) : ℝ :=
  PadenKahan.planeAngle zAxis (elbowShoulderMid l₀ l₁ l₂ g b₁ b₂ - elbowShoulder l₀)
    (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀)

/-- The rigid motion `g₂ = e^{-ξ̂₃θ₃} e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g_d g_st(0)⁻¹` of MLS eq. (3.35),
p. 106, for the arm angles of branch `(b₁, b₂)`. -/
def elbowWristTransform (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ : Bool) : RigidTransform :=
  Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-elbowAngle₃ l₀ l₁ l₂ g b₁) *
    Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-elbowAngle₂ l₀ l₁ l₂ g b₁ b₂) *
    Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-elbowAngle₁ l₀ l₁ l₂ g b₁ b₂) *
    (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)

/-- The point `p = p_w + e_y` on the axis of `ξ₆` and not on the `ξ₄`, `ξ₅` axes, used in Step 3
(MLS p. 106). -/
def elbowWristProbe (l₀ l₁ l₂ : ℝ) : Vec3 := elbowWrist l₀ l₁ l₂ + yAxis

/-- The point `q = g₂ p` of Step 3 (MLS eq. (3.36), p. 106), for the arm branch `(b₁, b₂)`. -/
def elbowWristTarget (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ : Bool) : Vec3 :=
  (elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWristProbe l₀ l₁ l₂)

/-- **Step 3 (MLS eq. (3.36), p. 106, with eqs. (3.21)–(3.24)): the intermediate point** of
Subproblem 2 for the wrist axes `ω₁ = +z`, `ω₂ = -x` through `p_w`, with `γ = √Γ`
(`b₃ = true`) or `γ = -√Γ` (`b₃ = false`). -/
def elbowWristMid (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) : Vec3 :=
  elbowWrist l₀ l₁ l₂ +
    PadenKahan.subproblemTwoPoint zAxis (-xAxis)
      (elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂)
      (elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂)
      (if b₃ then
        √(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis)
          (elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂)
          (elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂))
      else
        -√(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis)
          (elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂)
          (elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂)))

/-- **Step 3 (MLS p. 106): the angle `θ₅`**, by the Subproblem 1 formula about the fifth axis from
`p` to the wrist intermediate point. -/
def elbowAngle₅ (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) : ℝ :=
  PadenKahan.planeAngle (-xAxis) (elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂)
    (elbowWristMid l₀ l₁ l₂ g b₁ b₂ b₃ - elbowWrist l₀ l₁ l₂)

/-- **Step 3 (MLS p. 106): the angle `θ₄`**, by the Subproblem 1 formula about the fourth axis
from the wrist intermediate point to `q = g₂ p`. -/
def elbowAngle₄ (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) : ℝ :=
  PadenKahan.planeAngle zAxis (elbowWristMid l₀ l₁ l₂ g b₁ b₂ b₃ - elbowWrist l₀ l₁ l₂)
    (elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂)

/-- The point `p′ = p_w + e_x`, not on the axis of `ξ₆`, used in Step 4 (MLS p. 106). -/
def elbowToolProbe (l₀ l₁ l₂ : ℝ) : Vec3 := elbowWrist l₀ l₁ l₂ + xAxis

/-- **Step 4 (MLS eq. (3.37), p. 106): the angle `θ₆`**, by the Subproblem 1 formula about the
sixth axis from `p′` to `q = e^{-ξ̂₅θ₅} e^{-ξ̂₄θ₄} g₂ p′`. -/
def elbowAngle₆ (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) : ℝ :=
  PadenKahan.planeAngle yAxis (elbowToolProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂)
    ((Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4) (-elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃) *
        elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowToolProbe l₀ l₁ l₂) -
      elbowWrist l₀ l₁ l₂)

/-- **The eight candidate solutions of MLS Example 3.5 (pp. 104–106)**, indexed by the three
binary branches `(b₁, b₂, b₃)` of eqs. (3.33), (3.34) and (3.36); Lean joint `i` is the book's
joint `i + 1`. -/
def elbowCandidate (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b : Bool × Bool × Bool) : Fin 6 → ℝ :=
  ![elbowAngle₁ l₀ l₁ l₂ g b.1 b.2.1, elbowAngle₂ l₀ l₁ l₂ g b.1 b.2.1, elbowAngle₃ l₀ l₁ l₂ g b.1,
    elbowAngle₄ l₀ l₁ l₂ g b.1 b.2.1 b.2.2, elbowAngle₅ l₀ l₁ l₂ g b.1 b.2.1 b.2.2,
    elbowAngle₆ l₀ l₁ l₂ g b.1 b.2.1 b.2.2]

/-- The solution set of `g_st(θ) = g_d` for the elbow manipulator (MLS Example 3.5, p. 104), read
modulo `2π` in each joint angle: the image of `{θ | g_st(θ) = g_d}` in `Fin 6 → Real.Angle`. -/
def elbowSolutionAngles (l₀ l₁ l₂ : ℝ) (g : RigidTransform) : Set (Fin 6 → Real.Angle) :=
  (fun θ : Fin 6 → ℝ => fun i => (θ i : Real.Angle)) '' {θ | (elbowManipulator l₀ l₁ l₂).fk θ = g}

/-- The eight candidates read modulo `2π` (MLS Example 3.5, p. 106). -/
def elbowCandidateAngles (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b : Bool × Bool × Bool) :
    Fin 6 → Real.Angle :=
  fun i => (elbowCandidate l₀ l₁ l₂ g b i : Real.Angle)

/-- **Shoulder regularity (a hypothesis MLS does not state):** the target `g₁ p_w` of the wrist
centre is not on the first joint axis (the vertical line through `p_b`). On that axis
Subproblem 2's first rotation is free and `θ₁` is undetermined (MLS p. 127: "if the arm of the
elbow manipulator ... is held vertically over the base"). -/
def elbowShoulderRegular (l₀ l₁ l₂ : ℝ) (g : RigidTransform) : Prop :=
  Vec3.perp zAxis (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀) ≠ 0

/-- **Wrist regularity (a hypothesis MLS does not state):** for every arm branch `(b₁, b₂)`, the
point `q = g₂ p` of Step 3 is not on the fourth axis through `p_w`, so the sixth axis is not
carried onto the fourth one; otherwise only `θ₄ + θ₆` is determined (MLS Example 3.5, Step 3,
p. 106). -/
def elbowWristRegular (l₀ l₁ l₂ : ℝ) (g : RigidTransform) : Prop :=
  ∀ b₁ b₂ : Bool, Vec3.perp zAxis (elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂) ≠ 0

/-- The first joint axis `+z` is a unit vector. -/
private theorem norm_zAxis' : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

/-- The axis `-x` of joints 2, 3 and 5 is a unit vector. -/
private theorem norm_neg_xAxis' : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

/-- The real-lift form of equality in `Real.Angle`. -/
private theorem coe_eq_coe_iff {θ c : ℝ} :
    (θ : Real.Angle) = c ↔ ∃ k : ℤ, θ = c + k * (2 * Real.pi) := by
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

/-- The value `γ²` of Subproblem 2 for the axes `+z`, `-x`. -/
private theorem gammaSq_eq (u v : Vec3) :
    PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) u v =
      ‖u‖ ^ 2 - inner ℝ zAxis v ^ 2 - inner ℝ xAxis u ^ 2 := by
  have h0 : inner ℝ zAxis (-xAxis) = (0 : ℝ) := by
    simp [zAxis, xAxis, PiLp.inner_apply, Fin.sum_univ_three]
  have h1 : ‖Vec3.cross zAxis (-xAxis)‖ = 1 := by
    have : Vec3.cross zAxis (-xAxis) = -yAxis := by
      ext i
      fin_cases i <;> simp [Vec3.cross, cross_apply, xAxis, yAxis, zAxis]
    rw [this, norm_neg, Rotation.norm_yAxis]
  simp only [PadenKahan.subproblemTwoGammaSq, PadenKahan.subproblemTwoAlpha,
    PadenKahan.subproblemTwoBeta, h0, h1, inner_neg_left]
  ring

/-- A revolute joint motion fixes the axis point it is built from. -/
private theorem exp_rev_self {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint q = q :=
  Twist.exp_revolute_applyPoint_of_mem_axisLine ω q hω t (AffineSubspace.self_mem_mk' _ _)

/-- With `xᵀu = 0` and `‖u‖ = ‖v‖`, the value `γ²` for the axes `+z`, `-x` is `‖v′‖²`. -/
private theorem gammaSq_eq_perp {u v : Vec3} (hx : inner ℝ xAxis u = 0) (hn : ‖u‖ = ‖v‖) :
    PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) u v = ‖Vec3.perp zAxis v‖ ^ 2 := by
  rw [gammaSq_eq, Vec3.norm_perp_sq norm_zAxis', hx, hn]
  ring

/-- The signed square root squares back to its argument. -/
private theorem sq_signed_sqrt {Γ : ℝ} (hΓ : 0 ≤ Γ) (b : Bool) :
    (if b then √Γ else -√Γ) ^ 2 = Γ := by
  cases b <;> simp [Real.sq_sqrt hΓ]

/-- Subproblem 2 for the axes `+z`, `-x` meeting at `r`: the atan2 angles through an
admissible intermediate point solve both rotations. -/
private theorem sp2_exists {r p q c : Vec3} {γ : ℝ} (hn : ‖p - r‖ = ‖q - r‖)
    (hγ : γ ^ 2 = PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r))
    (hc : c = r + PadenKahan.subproblemTwoPoint zAxis (-xAxis) (p - r) (q - r) γ) :
    (Twist.exp (Twist.revolute (-xAxis) r)
        (PadenKahan.planeAngle (-xAxis) (p - r) (c - r))).applyPoint p = c ∧
      (Twist.exp (Twist.revolute zAxis r)
        (PadenKahan.planeAngle zAxis (c - r) (q - r))).applyPoint c = q := by
  obtain ⟨θ₁, θ₂, h₂, h₁⟩ := PadenKahan.subproblemTwo_exists_of_sq_eq norm_zAxis'
    norm_neg_xAxis' elbowManipulator_shoulder_axes_cross_ne_zero hn hγ
  have hcr : c - r = PadenKahan.subproblemTwoPoint zAxis (-xAxis) (p - r) (q - r) γ := by
    rw [hc, add_sub_cancel_left]
  rw [← hcr] at h₁ h₂
  obtain ⟨a₂, b₂⟩ := (PadenKahan.exists_exp_act_eq_iff norm_neg_xAxis' _ _).mp ⟨θ₂, h₂⟩
  obtain ⟨a₁, b₁⟩ := (PadenKahan.exists_exp_act_eq_iff norm_zAxis' _ _).mp ⟨θ₁, h₁⟩
  exact ⟨PadenKahan.subproblemOne_planeAngle norm_neg_xAxis' a₂ b₂,
    PadenKahan.subproblemOne_planeAngle norm_zAxis' a₁ b₁⟩

/-- Subproblem 2 for the axes `+z`, `-x` meeting at `r`: every solution passes through one of
the two intermediate points, and its angles are the atan2 angles modulo `2π`, provided
`xᵀ(p - r) = 0` and `q` is off the first axis. -/
private theorem sp2_contain {r p q : Vec3} {t₁ t₂ : ℝ} (hx : inner ℝ xAxis (p - r) = 0)
    (hq : Vec3.perp zAxis (q - r) ≠ 0)
    (h : (Twist.exp (Twist.revolute zAxis r) t₁ *
      Twist.exp (Twist.revolute (-xAxis) r) t₂).applyPoint p = q) :
    ∃ b : Bool,
      (∃ k : ℤ, t₂ = PadenKahan.planeAngle (-xAxis) (p - r)
        ((r + PadenKahan.subproblemTwoPoint zAxis (-xAxis) (p - r) (q - r)
          (if b then √(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r))
          else -√(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r)))) - r) +
          k * (2 * Real.pi)) ∧
      (∃ k : ℤ, t₁ = PadenKahan.planeAngle zAxis
        ((r + PadenKahan.subproblemTwoPoint zAxis (-xAxis) (p - r) (q - r)
          (if b then √(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r))
          else -√(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r)))) - r)
          (q - r) + k * (2 * Real.pi)) := by
  have hu : Vec3.perp (-xAxis) (p - r) ≠ 0 := by
    intro h0
    have hpr : p - r = 0 := by
      rw [← h0, Vec3.perp, inner_neg_left, hx, neg_zero, zero_smul, sub_zero]
    rw [sub_eq_zero] at hpr
    subst hpr
    rw [RigidTransform.mul_applyPoint, exp_rev_self norm_neg_xAxis', exp_rev_self norm_zAxis'] at h
    subst h
    simp [Vec3.perp] at hq
  have key : ∀ c : Vec3, (Twist.exp (Twist.revolute (-xAxis) r) t₂).applyPoint p = c →
      (∃ k : ℤ, t₂ = PadenKahan.planeAngle (-xAxis) (p - r) (c - r) + k * (2 * Real.pi)) ∧
      (∃ k : ℤ, t₁ = PadenKahan.planeAngle zAxis (c - r) (q - r) + k * (2 * Real.pi)) := by
    intro c h₂
    have h₁ : (Twist.exp (Twist.revolute zAxis r) t₁).applyPoint c = q := by
      rw [← h₂, ← RigidTransform.mul_applyPoint]
      exact h
    obtain ⟨a₂, b₂⟩ := PadenKahan.subproblemOne_necessary norm_neg_xAxis' h₂
    obtain ⟨a₁, b₁⟩ := PadenKahan.subproblemOne_necessary norm_zAxis' h₁
    have hc : Vec3.perp zAxis (c - r) ≠ 0 := by
      rw [← norm_ne_zero_iff, b₁, norm_ne_zero_iff]
      exact hq
    exact ⟨(PadenKahan.subproblemOne_iff norm_neg_xAxis' a₂ b₂ hu t₂).mp h₂,
      (PadenKahan.subproblemOne_iff norm_zAxis' a₁ b₁ hc t₁).mp h₁⟩
  rcases PadenKahan.subproblemTwo_intermediate norm_zAxis' norm_neg_xAxis'
      elbowManipulator_shoulder_axes_cross_ne_zero h with h₂ | h₂
  · exact ⟨true, key _ h₂⟩
  · exact ⟨false, key _ h₂⟩

/-- A revolute joint motion at angle `-θ` depends on `θ` only modulo `2π`. -/
private theorem exp_neg_congr {ξ : Twist} (hξ : ξ.IsRevoluteJoint) {θ c : ℝ}
    (h : ∃ k : ℤ, θ = c + k * (2 * Real.pi)) : Twist.exp ξ (-θ) = Twist.exp ξ (-c) := by
  obtain ⟨k, rfl⟩ := h
  have : -(c + k * (2 * Real.pi)) = -c + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [this, hξ.exp_add_int_mul_two_pi]

/-- A revolute joint motion depends on its angle only modulo `2π`. -/
private theorem exp_congr {ξ : Twist} (hξ : ξ.IsRevoluteJoint) {θ c : ℝ}
    (h : ∃ k : ℤ, θ = c + k * (2 * Real.pi)) : Twist.exp ξ θ = Twist.exp ξ c := by
  obtain ⟨k, rfl⟩ := h
  exact hξ.exp_add_int_mul_two_pi c k

/-- Step 1: the wrist centre is off the third axis when `l₂ ≠ 0`. -/
private theorem step1_hu {l₀ l₁ l₂ : ℝ} (hl₂ : l₂ ≠ 0) :
    Vec3.perp (-xAxis) (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun v : Vec3 => v 1) h0
  exact hl₂ (by simpa [Vec3.perp, elbowWrist, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three]
    using h1)

/-- Step 1: the shoulder point is off the third axis when `l₁ ≠ 0`. -/
private theorem step1_hv {l₀ l₁ : ℝ} (hl₁ : l₁ ≠ 0) :
    Vec3.perp (-xAxis) (elbowShoulder l₀ - vec 0 l₁ l₀) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun v : Vec3 => v 1) h0
  exact hl₁ (by simpa [Vec3.perp, elbowShoulder, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three]
    using h1)

/-- The point `e^{ξ̂₃θ₃} p_w` has the `x`-coordinate of the shoulder point. -/
private theorem inner_xAxis_arm (l₀ l₁ l₂ t : ℝ) :
    inner ℝ xAxis ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) t).applyPoint
      (elbowWrist l₀ l₁ l₂) - elbowShoulder l₀) = 0 := by
  rw [Twist.exp_revolute_applyPoint _ _ norm_neg_xAxis', add_sub_assoc, inner_add_right]
  have h := Rotation.inner_exp_act_axis norm_neg_xAxis' t (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
  simp only [inner_neg_left, neg_inj] at h
  rw [h]
  simp [xAxis, vec, elbowWrist, elbowShoulder, PiLp.inner_apply, Fin.sum_univ_three]

/-- The probe `p_w + e_y` of Step 3 has the `x`-coordinate of the wrist centre. -/
private theorem inner_xAxis_probe (l₀ l₁ l₂ : ℝ) :
    inner ℝ xAxis (elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂) = 0 := by
  simp [elbowWristProbe, xAxis, yAxis, PiLp.inner_apply, Fin.sum_univ_three]

/-- Step 1: for each branch, `‖e^{ξ̂₃θ₃} p_w - p_b‖ = ‖g₁ p_w - p_b‖`. -/
private theorem armSource_norm {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g) (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1)
    (b₁ : Bool) :
    ‖elbowArmSource l₀ l₁ l₂ g b₁ - elbowShoulder l₀‖ =
      ‖elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀‖ := by
  have h := (PadenKahan.subproblemThree_iff norm_neg_xAxis'
    (norm_nonneg (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀)) (step1_hu hl₂) (step1_hv hl₁)
    hκ₁ hκ₂ (elbowAngle₃ l₀ l₁ l₂ g b₁)).mpr
    ⟨0, by cases b₁ <;> simp [elbowAngle₃, elbowKappa]⟩
  rw [norm_sub_rev]
  exact h

/-- Step 2 for each branch: the atan2 angles `θ₂`, `θ₁` move `e^{ξ̂₃θ₃} p_w` through the
intermediate point to `g₁ p_w`. -/
private theorem arm_steps {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g) (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1)
    (b₁ b₂ : Bool) :
    (Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀))
        (elbowAngle₂ l₀ l₁ l₂ g b₁ b₂)).applyPoint (elbowArmSource l₀ l₁ l₂ g b₁) =
        elbowShoulderMid l₀ l₁ l₂ g b₁ b₂ ∧
      (Twist.exp (Twist.revolute zAxis (elbowShoulder l₀))
        (elbowAngle₁ l₀ l₁ l₂ g b₁ b₂)).applyPoint (elbowShoulderMid l₀ l₁ l₂ g b₁ b₂) =
        elbowTarget l₀ l₁ l₂ g := by
  have hn := armSource_norm hl₁ hl₂ hκ₁ hκ₂ b₁
  have hΓ := gammaSq_eq_perp (inner_xAxis_arm l₀ l₁ l₂ (elbowAngle₃ l₀ l₁ l₂ g b₁)) hn
  exact sp2_exists hn (sq_signed_sqrt (hΓ ▸ sq_nonneg _) b₂) rfl

/-- The motion `g₂` of eq. (3.35) fixes the wrist centre, for each arm branch. -/
private theorem wristTransform_applyPoint_wrist {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g) (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1)
    (b₁ b₂ : Bool) :
    (elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWrist l₀ l₁ l₂) =
      elbowWrist l₀ l₁ l₂ := by
  obtain ⟨h₂, h₁⟩ := arm_steps hl₁ hl₂ hκ₁ hκ₂ b₁ b₂
  have h₂' : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1)
      (elbowAngle₂ l₀ l₁ l₂ g b₁ b₂)).applyPoint
      ((Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (elbowAngle₃ l₀ l₁ l₂ g b₁)).applyPoint
        (elbowWrist l₀ l₁ l₂)) = elbowShoulderMid l₀ l₁ l₂ g b₁ b₂ := h₂
  have h₁' : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0)
      (elbowAngle₁ l₀ l₁ l₂ g b₁ b₂)).applyPoint (elbowShoulderMid l₀ l₁ l₂ g b₁ b₂) =
      g.applyPoint ((elbowManipulator l₀ l₁ l₂).toolRef⁻¹.applyPoint (elbowWrist l₀ l₁ l₂)) := by
    rw [← RigidTransform.mul_applyPoint]
    exact h₁
  simp only [elbowWristTransform, Twist.exp_neg, RigidTransform.mul_applyPoint]
  rw [← h₁', ← h₂']
  simp only [RigidTransform.inv_applyPoint_applyPoint]

/-- Step 3: `‖p - p_w‖ = ‖g₂ p - p_w‖` for the probe `p = p_w + e_y`. -/
private theorem wristTarget_norm {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g) (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1)
    (b₁ b₂ : Bool) :
    ‖elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂‖ =
      ‖elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂‖ := by
  have hfix := wristTransform_applyPoint_wrist hl₁ hl₂ hκ₁ hκ₂ b₁ b₂
  calc ‖elbowWristProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂‖
      = ‖(elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWristProbe l₀ l₁ l₂) -
          (elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWrist l₀ l₁ l₂)‖ := by
        rw [RigidTransform.applyPoint_sub_applyPoint, RigidTransform.norm_applyVector]
    _ = ‖elbowWristTarget l₀ l₁ l₂ g b₁ b₂ - elbowWrist l₀ l₁ l₂‖ := by
        rw [hfix]
        rfl

/-- Step 3 for each branch: the atan2 angles `θ₅`, `θ₄` move the probe through the wrist
intermediate point to `g₂ p`. -/
private theorem wrist_steps {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g) (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1)
    (b₁ b₂ b₃ : Bool) :
    (Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂))
        (elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint (elbowWristProbe l₀ l₁ l₂) =
        elbowWristMid l₀ l₁ l₂ g b₁ b₂ b₃ ∧
      (Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂))
        (elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint (elbowWristMid l₀ l₁ l₂ g b₁ b₂ b₃) =
        elbowWristTarget l₀ l₁ l₂ g b₁ b₂ := by
  have hn := wristTarget_norm hl₁ hl₂ hκ₁ hκ₂ b₁ b₂
  have hΓ := gammaSq_eq_perp (inner_xAxis_probe l₀ l₁ l₂) hn
  exact sp2_exists hn (sq_signed_sqrt (hΓ ▸ sq_nonneg _) b₃) rfl

/-- Step 4: if a rigid motion `H` fixes `p_w` and `p_w + e_y`, the atan2 angle about the axis
`+y` through `p_w` carries `p_w + e_x` to `H (p_w + e_x)`. -/
private theorem step4 {H : RigidTransform} {w : Vec3} (h₀ : H.applyPoint w = w)
    (h₁ : H.applyPoint (w + yAxis) = w + yAxis) :
    (Twist.exp (Twist.revolute yAxis w)
        (PadenKahan.planeAngle yAxis (w + xAxis - w) (H.applyPoint (w + xAxis) - w))).applyPoint
        (w + xAxis) = H.applyPoint (w + xAxis) := by
  have hRy : H.rotation.act yAxis = yAxis := by
    have := H.applyPoint_sub_applyPoint (w + yAxis) w
    rw [h₁, h₀, add_sub_cancel_left] at this
    exact this.symm
  have hv : H.applyPoint (w + xAxis) - w = H.rotation.act xAxis := by
    rw [show H.applyPoint (w + xAxis) - w = H.applyPoint (w + xAxis) - H.applyPoint w by
      rw [h₀], H.applyPoint_sub_applyPoint, add_sub_cancel_left]
    rfl
  have hyx : inner ℝ yAxis xAxis = (0 : ℝ) := by
    simp [xAxis, yAxis, PiLp.inner_apply, Fin.sum_univ_three]
  have hi : inner ℝ yAxis (H.rotation.act xAxis) = 0 := by
    rw [← hRy, Rotation.inner_act, hyx]
  refine PadenKahan.subproblemOne_planeAngle Rotation.norm_yAxis ?_ ?_
  · rw [add_sub_cancel_left, hv, hi, hyx]
  · rw [add_sub_cancel_left, hv, Vec3.perp, Vec3.perp, hi, hyx, zero_smul, sub_zero,
      sub_zero, Rotation.norm_act]

/-- The entries of a candidate: joint 0. -/
private theorem elbowCandidate_zero (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) :
    elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) 0 = elbowAngle₁ l₀ l₁ l₂ g b₁ b₂ := by
  simp only [elbowCandidate, Matrix.cons_val]

/-- The entries of a candidate: joint 1. -/
private theorem elbowCandidate_one (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) :
    elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) 1 = elbowAngle₂ l₀ l₁ l₂ g b₁ b₂ := by
  simp only [elbowCandidate, Matrix.cons_val]

/-- The entries of a candidate: joint 2. -/
private theorem elbowCandidate_two (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) :
    elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) 2 = elbowAngle₃ l₀ l₁ l₂ g b₁ := by
  simp only [elbowCandidate, Matrix.cons_val]

/-- The entries of a candidate: joint 3. -/
private theorem elbowCandidate_three (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) :
    elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) 3 = elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃ := by
  simp only [elbowCandidate, Matrix.cons_val]

/-- The entries of a candidate: joint 4. -/
private theorem elbowCandidate_four (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) :
    elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) 4 = elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃ := by
  simp only [elbowCandidate, Matrix.cons_val]

/-- The entries of a candidate: joint 5. -/
private theorem elbowCandidate_five (l₀ l₁ l₂ : ℝ) (g : RigidTransform) (b₁ b₂ b₃ : Bool) :
    elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) 5 = elbowAngle₆ l₀ l₁ l₂ g b₁ b₂ b₃ := by
  simp only [elbowCandidate, Matrix.cons_val]

/-- The two signs of `±√Γ` differ when `Γ > 0`. -/
private theorem signed_sqrt_injective {Γ : ℝ} (hΓ : 0 < Γ) {b b' : Bool}
    (h : (if b then √Γ else -√Γ) = (if b' then √Γ else -√Γ)) : b = b' := by
  have hs := Real.sqrt_pos.mpr hΓ
  cases b <;> cases b' <;> simp at h ⊢ <;> linarith

/-- Subproblem 2 for the axes `+z`, `-x` meeting at `r`: when `q` is off the first axis, the
two branches give second angles that differ modulo `2π`. -/
private theorem branch_eq_of_angle {r p q : Vec3} (hx : inner ℝ xAxis (p - r) = 0)
    (hn : ‖p - r‖ = ‖q - r‖) (hq : Vec3.perp zAxis (q - r) ≠ 0) (b b' : Bool)
    (h : ∃ k : ℤ,
      PadenKahan.planeAngle (-xAxis) (p - r)
        ((r + PadenKahan.subproblemTwoPoint zAxis (-xAxis) (p - r) (q - r)
          (if b then √(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r))
          else -√(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r)))) - r) =
      PadenKahan.planeAngle (-xAxis) (p - r)
        ((r + PadenKahan.subproblemTwoPoint zAxis (-xAxis) (p - r) (q - r)
          (if b' then √(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r))
          else -√(PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r)))) - r) +
        k * (2 * Real.pi)) : b = b' := by
  have hΓ : 0 < PadenKahan.subproblemTwoGammaSq zAxis (-xAxis) (p - r) (q - r) := by
    rw [gammaSq_eq_perp hx hn]
    exact pow_pos (norm_pos_iff.mpr hq) 2
  have e := (sp2_exists hn (sq_signed_sqrt hΓ.le b) rfl).1
  have e' := (sp2_exists hn (sq_signed_sqrt hΓ.le b') rfl).1
  rw [exp_congr ⟨-xAxis, r, norm_neg_xAxis', rfl⟩ h] at e
  have hc := add_left_cancel (e.symm.trans e')
  exact signed_sqrt_injective hΓ
    (PadenKahan.subproblemTwoPoint_injective elbowManipulator_shoulder_axes_cross_ne_zero _ _ hc)

/-- **MLS Example 3.5, p. 106: every solution is one of the eight candidates modulo `2π`.**
Under `l₁ ≠ 0`, `l₂ ≠ 0`, shoulder regularity and wrist regularity, every joint vector `θ` with
`g_st(θ) = g_d` agrees modulo `2π` in each angle with `elbowCandidate l₀ l₁ l₂ g b` for some branch
`b`. -/
theorem elbowManipulator_fk_eq_imp_candidate {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hs : elbowShoulderRegular l₀ l₁ l₂ g)
    (hw : elbowWristRegular l₀ l₁ l₂ g) {θ : Fin 6 → ℝ}
    (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) :
    ∃ b : Bool × Bool × Bool, ∀ i : Fin 6,
      ∃ k : ℤ, θ i = elbowCandidate l₀ l₁ l₂ g b i + k * (2 * Real.pi) := by
  have hR := elbowManipulator_isRevoluteJoint l₀ l₁ l₂
  -- Step 1: the elbow angle
  obtain ⟨b₁, k₂, hk₂⟩ : ∃ b₁ : Bool, ∃ k : ℤ,
      θ 2 = elbowAngle₃ l₀ l₁ l₂ g b₁ + k * (2 * Real.pi) := by
    obtain ⟨k, hk⟩ := elbowManipulator_elbow_angle hl₁ hl₂ h
    rcases hk with hk | hk
    · exact ⟨true, k, hk⟩
    · exact ⟨false, k, hk⟩
  -- Step 2: the shoulder angles
  have hsh := elbowManipulator_subproblemTwo_shoulder h
  rw [exp_congr (ξ := Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (hR 2) ⟨k₂, hk₂⟩] at hsh
  obtain ⟨b₂, ⟨k₁, hk₁⟩, ⟨k₀, hk₀⟩⟩ := sp2_contain (inner_xAxis_arm l₀ l₁ l₂ _) hs hsh
  have hk₁' : θ 1 = elbowAngle₂ l₀ l₁ l₂ g b₁ b₂ + k₁ * (2 * Real.pi) := hk₁
  have hk₀' : θ 0 = elbowAngle₁ l₀ l₁ l₂ g b₁ b₂ + k₀ * (2 * Real.pi) := hk₀
  -- Step 3: two wrist angles
  have hp : elbowWristProbe l₀ l₁ l₂ ∈ axisLine (elbowWrist l₀ l₁ l₂) yAxis :=
    (mem_axisLine_iff _ _ _).mpr ⟨1, by simp [elbowWristProbe]⟩
  have hwr := elbowManipulator_subproblemTwo_wrist h hp
  rw [exp_neg_congr (hR 2) ⟨k₂, hk₂⟩, exp_neg_congr (hR 1) ⟨k₁, hk₁'⟩,
    exp_neg_congr (hR 0) ⟨k₀, hk₀'⟩] at hwr
  have hwr' : (Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂)) (θ 3) *
      Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂)) (θ 4)).applyPoint
        (elbowWristProbe l₀ l₁ l₂) = elbowWristTarget l₀ l₁ l₂ g b₁ b₂ := hwr
  obtain ⟨b₃, ⟨k₄, hk₄⟩, ⟨k₃, hk₃⟩⟩ := sp2_contain (inner_xAxis_probe l₀ l₁ l₂) (hw b₁ b₂) hwr'
  have hk₄' : θ 4 = elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃ + k₄ * (2 * Real.pi) := hk₄
  have hk₃' : θ 3 = elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃ + k₃ * (2 * Real.pi) := hk₃
  -- Step 4: the last wrist angle
  have htool := elbowManipulator_subproblemOne h (elbowToolProbe l₀ l₁ l₂)
  rw [exp_neg_congr (hR 4) ⟨k₄, hk₄'⟩, exp_neg_congr (hR 3) ⟨k₃, hk₃'⟩,
    exp_neg_congr (hR 2) ⟨k₂, hk₂⟩, exp_neg_congr (hR 1) ⟨k₁, hk₁'⟩,
    exp_neg_congr (hR 0) ⟨k₀, hk₀'⟩,
    show ∀ A B C D E F : RigidTransform, A * B * C * D * E * F = A * B * (C * D * E * F) from
      fun _ _ _ _ _ _ => by simp only [mul_assoc]] at htool
  obtain ⟨a₅, n₅⟩ := PadenKahan.subproblemOne_necessary Rotation.norm_yAxis htool
  have hu : Vec3.perp yAxis (elbowToolProbe l₀ l₁ l₂ - elbowWrist l₀ l₁ l₂) ≠ 0 := by
    have hyx : inner ℝ yAxis xAxis = (0 : ℝ) := by
      simp [xAxis, yAxis, PiLp.inner_apply, Fin.sum_univ_three]
    rw [elbowToolProbe, add_sub_cancel_left, Vec3.perp, hyx, zero_smul, sub_zero]
    intro h0
    simpa [h0] using Rotation.norm_xAxis
  obtain ⟨k₅, hk₅⟩ := (PadenKahan.subproblemOne_iff Rotation.norm_yAxis a₅ n₅ hu (θ 5)).mp htool
  refine ⟨(b₁, b₂, b₃), fun i => ?_⟩
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, elbowCandidate_zero, elbowCandidate_one,
      elbowCandidate_two, elbowCandidate_three, elbowCandidate_four, elbowCandidate_five]
  · exact ⟨k₀, hk₀'⟩
  · exact ⟨k₁, hk₁'⟩
  · exact ⟨k₂, hk₂⟩
  · exact ⟨k₃, hk₃'⟩
  · exact ⟨k₄, hk₄'⟩
  · exact ⟨k₅, hk₅⟩

/-- The solution set modulo `2π` lies in the range of the eight candidates (MLS Example 3.5,
p. 106), under the hypotheses of `elbowManipulator_fk_eq_imp_candidate`. -/
theorem elbowSolutionAngles_subset_range {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hs : elbowShoulderRegular l₀ l₁ l₂ g)
    (hw : elbowWristRegular l₀ l₁ l₂ g) :
    elbowSolutionAngles l₀ l₁ l₂ g ⊆ Set.range (elbowCandidateAngles l₀ l₁ l₂ g) := by
  rintro x ⟨θ, hθ, rfl⟩
  obtain ⟨b, hb⟩ := elbowManipulator_fk_eq_imp_candidate hl₁ hl₂ hs hw hθ
  exact ⟨b, funext fun i => (coe_eq_coe_iff.mpr (hb i)).symm⟩

/-- **MLS Example 3.5, p. 106: "a maximum of eight possible solutions".** Under `l₁ ≠ 0`,
`l₂ ≠ 0`, shoulder regularity and wrist regularity, the solutions of `g_st(θ) = g_d` modulo `2π`
form a finite set with at most eight elements. -/
theorem ncard_elbowSolutionAngles_le_eight {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hs : elbowShoulderRegular l₀ l₁ l₂ g)
    (hw : elbowWristRegular l₀ l₁ l₂ g) :
    (elbowSolutionAngles l₀ l₁ l₂ g).Finite ∧ (elbowSolutionAngles l₀ l₁ l₂ g).ncard ≤ 8 := by
  have hsub := elbowSolutionAngles_subset_range hl₁ hl₂ hs hw
  have hfin : (Set.range (elbowCandidateAngles l₀ l₁ l₂ g)).Finite := Set.finite_range _
  refine ⟨hfin.subset hsub, ?_⟩
  calc (elbowSolutionAngles l₀ l₁ l₂ g).ncard
      ≤ (Set.range (elbowCandidateAngles l₀ l₁ l₂ g)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (Set.univ : Set (Bool × Bool × Bool)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le Set.finite_univ
    _ = 8 := by simp [Set.ncard_univ]

/-- **MLS Example 3.5, pp. 105–106: each candidate is a solution when the elbow can reach.** If
`l₁ ≠ 0`, `l₂ ≠ 0` and `-1 ≤ κ ≤ 1` (Step 1 is solvable), then for every branch `b` the candidate
`elbowCandidate l₀ l₁ l₂ g b` solves `g_st(θ) = g_d`; no regularity hypothesis is needed. -/
theorem elbowManipulator_fk_elbowCandidate {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g) (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1)
    (b : Bool × Bool × Bool) :
    (elbowManipulator l₀ l₁ l₂).fk (elbowCandidate l₀ l₁ l₂ g b) = g := by
  obtain ⟨b₁, b₂, b₃⟩ := b
  obtain ⟨hA₂, hA₁⟩ := arm_steps hl₁ hl₂ hκ₁ hκ₂ b₁ b₂
  obtain ⟨hW₅, hW₄⟩ := wrist_steps hl₁ hl₂ hκ₁ hκ₂ b₁ b₂ b₃
  have hfix := wristTransform_applyPoint_wrist hl₁ hl₂ hκ₁ hκ₂ b₁ b₂
  have hp : elbowWristProbe l₀ l₁ l₂ ∈ axisLine (elbowWrist l₀ l₁ l₂) yAxis :=
    (mem_axisLine_iff _ _ _).mpr ⟨1, by simp [elbowWristProbe]⟩
  have hpw : elbowWristProbe l₀ l₁ l₂ ≠ elbowWrist l₀ l₁ l₂ := by
    intro h
    have hy : yAxis = 0 := by simpa [elbowWristProbe] using h
    simpa [hy] using Rotation.norm_yAxis
  have hp' : elbowToolProbe l₀ l₁ l₂ ∉ axisLine (elbowWrist l₀ l₁ l₂) yAxis := by
    rw [mem_axisLine_iff]
    rintro ⟨s, hs⟩
    have h0 := congrArg (fun v : Vec3 => v 0) hs
    simp [elbowToolProbe, xAxis, yAxis] at h0
  -- the motion left for the last joint fixes `p_w` and the probe `p_w + e_y`
  have hW₅' : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4)
      (elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint (elbowWristProbe l₀ l₁ l₂) =
      elbowWristMid l₀ l₁ l₂ g b₁ b₂ b₃ := hW₅
  have hW₄' : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3)
      (elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint (elbowWristMid l₀ l₁ l₂ g b₁ b₂ b₃) =
      (elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWristProbe l₀ l₁ l₂) := hW₄
  have hH₀ : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4)
      (-elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃) *
      Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃) *
      elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWrist l₀ l₁ l₂) =
      elbowWrist l₀ l₁ l₂ := by
    rw [RigidTransform.mul_applyPoint, RigidTransform.mul_applyPoint, hfix]
    exact (congrArg _ (exp_rev_self norm_zAxis' _ _)).trans (exp_rev_self norm_neg_xAxis' _ _)
  have hH₁ : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4)
      (-elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃) *
      Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃) *
      elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowWristProbe l₀ l₁ l₂) =
      elbowWristProbe l₀ l₁ l₂ := by
    rw [RigidTransform.mul_applyPoint, RigidTransform.mul_applyPoint, ← hW₄', ← hW₅',
      Twist.exp_neg, Twist.exp_neg, RigidTransform.inv_applyPoint_applyPoint,
      RigidTransform.inv_applyPoint_applyPoint]
  have h₆ : (Twist.exp (Twist.revolute yAxis (elbowWrist l₀ l₁ l₂))
      (elbowAngle₆ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint (elbowToolProbe l₀ l₁ l₂) =
      (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4) (-elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃) *
        elbowWristTransform l₀ l₁ l₂ g b₁ b₂).applyPoint (elbowToolProbe l₀ l₁ l₂) :=
    step4 hH₀ hH₁
  refine elbowManipulator_fk_eq_of_subproblems ?_ hp hpw ?_ hp' ?_ <;>
    simp only [elbowCandidate_zero, elbowCandidate_one, elbowCandidate_two, elbowCandidate_three,
      elbowCandidate_four, elbowCandidate_five]
  · rw [RigidTransform.mul_applyPoint]
    change (Twist.exp (Twist.revolute zAxis (elbowShoulder l₀))
      (elbowAngle₁ l₀ l₁ l₂ g b₁ b₂)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀))
          (elbowAngle₂ l₀ l₁ l₂ g b₁ b₂)).applyPoint (elbowArmSource l₀ l₁ l₂ g b₁)) =
      elbowTarget l₀ l₁ l₂ g
    rw [hA₂, hA₁]
  · rw [RigidTransform.mul_applyPoint]
    change (Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂))
      (elbowAngle₄ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂))
          (elbowAngle₅ l₀ l₁ l₂ g b₁ b₂ b₃)).applyPoint (elbowWristProbe l₀ l₁ l₂)) =
      elbowWristTarget l₀ l₁ l₂ g b₁ b₂
    rw [hW₅, hW₄]
  · rw [show ∀ A B C D E F : RigidTransform, A * B * C * D * E * F = A * B * (C * D * E * F) from
      fun _ _ _ _ _ _ => by simp only [mul_assoc]]
    exact h₆

/-- **MLS p. 103, applied to Step 1: no solution when `|κ| > 1`.** If `l₁ ≠ 0`, `l₂ ≠ 0` and
`|κ| > 1` (the target of the wrist centre is outside the annulus the elbow can reach), then
`g_st(θ) = g_d` has no solution. -/
theorem elbowManipulator_fk_ne_of_one_lt_abs_kappa {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hκ : 1 < |elbowKappa l₀ l₁ l₂ g|) (θ : Fin 6 → ℝ) :
    (elbowManipulator l₀ l₁ l₂).fk θ ≠ g := by
  intro h
  exact PadenKahan.subproblemThree_no_solution norm_neg_xAxis'
    (norm_nonneg (elbowTarget l₀ l₁ l₂ g - elbowShoulder l₀)) (step1_hu hl₂) (step1_hv hl₁) hκ
    (θ 2) (elbowManipulator_subproblemThree h)

/-- **The eight candidates are distinct modulo `2π` in the generic case (MLS p. 106).** Under
`l₁ ≠ 0`, `l₂ ≠ 0`, shoulder and wrist regularity and `-1 < κ < 1`, distinct branches give
joint vectors that differ modulo `2π` in some angle. -/
theorem elbowCandidateAngles_injective {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hs : elbowShoulderRegular l₀ l₁ l₂ g)
    (hw : elbowWristRegular l₀ l₁ l₂ g) (hκ₁ : -1 < elbowKappa l₀ l₁ l₂ g)
    (hκ₂ : elbowKappa l₀ l₁ l₂ g < 1) :
    Function.Injective (elbowCandidateAngles l₀ l₁ l₂ g) := by
  rintro ⟨b₁, b₂, b₃⟩ ⟨b₁', b₂', b₃'⟩ hb
  have hc : ∀ i, ∃ k : ℤ, elbowCandidate l₀ l₁ l₂ g (b₁, b₂, b₃) i =
      elbowCandidate l₀ l₁ l₂ g (b₁', b₂', b₃') i + k * (2 * Real.pi) :=
    fun i => coe_eq_coe_iff.mp (congrFun hb i)
  have h₁ := hc 1
  have h₂ := hc 2
  have h₄ := hc 4
  simp only [elbowCandidate_one, elbowCandidate_two, elbowCandidate_four] at h₁ h₂ h₄
  have key : ∀ k : ℤ,
      elbowAngle₃ l₀ l₁ l₂ g true ≠ elbowAngle₃ l₀ l₁ l₂ g false + k * (2 * Real.pi) :=
    fun k hk => PadenKahan.subproblemThree_branches_ne_of_abs_lt_one _ _ hκ₁ hκ₂ ⟨k, hk⟩
  obtain rfl : b₁ = b₁' := by
    obtain ⟨k, hk⟩ := h₂
    cases b₁ <;> cases b₁'
    · rfl
    · exact absurd (by push_cast; linarith) (key (-k))
    · exact absurd hk (key k)
    · rfl
  obtain rfl : b₂ = b₂' :=
    branch_eq_of_angle (inner_xAxis_arm l₀ l₁ l₂ _) (armSource_norm hl₁ hl₂ hκ₁.le hκ₂.le b₁)
      hs b₂ b₂' h₁
  obtain rfl : b₃ = b₃' :=
    branch_eq_of_angle (inner_xAxis_probe l₀ l₁ l₂)
      (wristTarget_norm hl₁ hl₂ hκ₁.le hκ₂.le b₁ b₂) (hw b₁ b₂) b₃ b₃' h₄
  rfl

/-- The solution set modulo `2π` is exactly the range of the eight candidates (MLS Example 3.5,
pp. 104–106) under `l₁ ≠ 0`, `l₂ ≠ 0`, shoulder and wrist regularity and `-1 ≤ κ ≤ 1`. -/
theorem elbowSolutionAngles_eq_range {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hs : elbowShoulderRegular l₀ l₁ l₂ g)
    (hw : elbowWristRegular l₀ l₁ l₂ g) (hκ₁ : -1 ≤ elbowKappa l₀ l₁ l₂ g)
    (hκ₂ : elbowKappa l₀ l₁ l₂ g ≤ 1) :
    elbowSolutionAngles l₀ l₁ l₂ g = Set.range (elbowCandidateAngles l₀ l₁ l₂ g) := by
  refine (elbowSolutionAngles_subset_range hl₁ hl₂ hs hw).antisymm ?_
  rintro x ⟨b, rfl⟩
  exact ⟨elbowCandidate l₀ l₁ l₂ g b, elbowManipulator_fk_elbowCandidate hl₁ hl₂ hκ₁ hκ₂ b, rfl⟩

/-- **MLS Example 3.5, p. 106: exactly eight solutions in the generic case.** Under `l₁ ≠ 0`,
`l₂ ≠ 0`, shoulder regularity, wrist regularity and `-1 < κ < 1`, the solutions of
`g_st(θ) = g_d` modulo `2π` are exactly eight. -/
theorem ncard_elbowSolutionAngles_eq_eight {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {g : RigidTransform} (hs : elbowShoulderRegular l₀ l₁ l₂ g)
    (hw : elbowWristRegular l₀ l₁ l₂ g) (hκ₁ : -1 < elbowKappa l₀ l₁ l₂ g)
    (hκ₂ : elbowKappa l₀ l₁ l₂ g < 1) :
    (elbowSolutionAngles l₀ l₁ l₂ g).ncard = 8 := by
  rw [elbowSolutionAngles_eq_range hl₁ hl₂ hs hw hκ₁.le hκ₂.le,
    Set.ncard_range_of_injective (elbowCandidateAngles_injective hl₁ hl₂ hs hw hκ₁ hκ₂)]
  simp

end RoboLean.Examples
