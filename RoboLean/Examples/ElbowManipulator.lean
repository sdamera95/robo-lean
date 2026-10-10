import RoboLean.Kinematics.PadenKahan
import RoboLean.Kinematics.Singularity
import RoboLean.Examples.RigidTransform

/-!
# The elbow manipulator: forward kinematics and the inverse-kinematics decomposition

MLS Chapter 3. Example 3.2 (printed pp. 89–91, Figure 3.4) defines the six-joint elbow
manipulator: two intersecting shoulder axes, an elbow, and a spherical wrist of three
intersecting axes, with the fully extended reference configuration `θ = 0`. Example 3.5
(pp. 104–106, Figure 3.11) solves its inverse kinematics with the Paden–Kahan subproblems in
four steps.

Frame and data (Example 3.2, as printed). The base frame `S` has the first axis along `+z`;
the arm extends along `+y` at height `l₀`. The twists, in the library order `(v, ω)`, are
`ξᵢ = (-ωᵢ × qᵢ, ωᵢ)` with axis directions `ω₁ = ω₄ = (0, 0, 1)`, `ω₂ = ω₃ = ω₅ = (-1, 0, 0)`,
`ω₆ = (0, 1, 0)` and axis points `q₁ = q₂ = (0, 0, l₀)` (p. 90 uses `q₁ = (0, 0, l₀)`),
`(0, l₁, l₀)` for joint 3 and the wrist centre `(0, l₁ + l₂, l₀)` for joints 4–6;
`g_st(0) = (I, (0, l₁ + l₂, l₀))`. The printed six-vectors of the twists are theorems
(`elbowManipulator_twist_zero` … `_five`). Lean joint `i` is the book's joint `i + 1`.

Contents:

* `elbowManipulator l₀ l₁ l₂`, the chain of Example 3.2, and its forward kinematics as printed on
  pp. 90–91: the rotation `R(θ)` with entries `r₁₁ … r₃₃` (`elbowManipulator_fk_rotation`) and the
  position `p(θ)` (`elbowManipulator_fk_translation`), for all real link lengths and angles;
* the inverse-kinematics decomposition of Example 3.5: for every joint vector `θ` with
  `g_st(θ) = g_d`, with `g₁ = g_d g_st(0)⁻¹` (eq. (3.30)), the wrist centre `p_w` and the shoulder
  point `p_b`:
  - Step 1, eqs. (3.31)–(3.33): `θ₃` solves Subproblem 3 with `p = p_w`, `q = p_b`,
    `δ = ‖g₁ p_w - p_b‖` (`elbowManipulator_subproblemThree`), hence `θ₃` is one of the two
    angles of eq. (3.29) modulo `2π` (`elbowManipulator_elbow_angle`);
  - Step 2, eq. (3.34): `(θ₁, θ₂)` solves Subproblem 2 with `p = e^{ξ̂₃θ₃} p_w`, `q = g₁ p_w`
    (`elbowManipulator_subproblemTwo_shoulder`);
  - Step 3, eqs. (3.35)–(3.36): `(θ₄, θ₅)` solves Subproblem 2 for every point `p` of the sixth
    axis, with `g₂ = e^{-ξ̂₃θ₃} e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g₁` (`elbowManipulator_subproblemTwo_wrist`);
  - Step 4, eq. (3.37): `θ₆` solves Subproblem 1 for every point `p`
    (`elbowManipulator_subproblemOne`);
* the converse, so that the four steps find every solution: for a point `p ≠ p_w` of the sixth
  axis and a point `p′` off it, `g_st(θ) = g_d` holds exactly when `θ` satisfies (3.34), (3.36)
  at `p` and (3.37) at `p′` (`elbowManipulator_fk_eq_of_subproblems`,
  `elbowManipulator_fk_eq_iff`); the proof uses that a rigid motion fixing three points not on
  one line is the identity;
* Example 3.12's remark (p. 126): the elbow manipulator is singular in its reference
  configuration, because axes 2, 3 and 5 are parallel and coplanar
  (`elbowManipulator_isSingular_zero`).

What is not proved: the count "a maximum of eight possible solutions" (p. 106), and the
conditions under which each subproblem has finitely many solutions (the book chooses `p` on the
sixth axis "but not on the `ξ₄`, `ξ₅` axes" and, in Step 4, "not on the axis of `ξ₆`"; the
necessary conditions hold for every point, and the converse needs only `p ≠ p_w` on the sixth
axis and `p′` off it). These are statements about the coordinate model, not about a physical arm
or a numerical solver.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

private theorem norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem act_negX (t x y z : ℝ) :
    (Rotation.exp (-xAxis) t).act (vec x y z) =
      vec x (Real.cos t * y + Real.sin t * z) (-(Real.sin t * y) + Real.cos t * z) := by
  rw [Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem act_Z (t x y z : ℝ) :
    (Rotation.exp zAxis t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

/-- A revolute joint motion fixes the axis point it is built from. -/
private theorem exp_revolute_applyPoint_self {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint q = q :=
  Twist.exp_revolute_applyPoint_of_mem_axisLine ω q hω t (AffineSubspace.self_mem_mk' _ _)

/-- The shoulder point `p_b = (0, 0, l₀)` of MLS Example 3.5, p. 105, Figure 3.11: the intersection
of the first two joint axes of the elbow manipulator. -/
def elbowShoulder (l₀ : ℝ) : Vec3 := vec 0 0 l₀

/-- The wrist centre `p_w = (0, l₁ + l₂, l₀)` of MLS Example 3.5, p. 105: the common point of the
three wrist axes of the elbow manipulator, and the tool origin at `θ = 0` (Example 3.2, p. 89). -/
def elbowWrist (l₀ l₁ l₂ : ℝ) : Vec3 := vec 0 (l₁ + l₂) l₀

/-- **MLS Example 3.2, pp. 89–90, Figure 3.4: the elbow manipulator.** Six revolute joints with
base-frame twists `ξᵢ = (-ωᵢ × qᵢ, ωᵢ)` (order `(v, ω)`): `ω₁ = +z` through `(0, 0, l₀)`,
`ω₂ = -x` through `(0, 0, l₀)`, `ω₃ = -x` through `(0, l₁, l₀)`, `ω₄ = +z`, `ω₅ = -x` and
`ω₆ = +y` through the wrist centre `(0, l₁ + l₂, l₀)`; reference tool pose
`g_st(0) = (I, (0, l₁ + l₂, l₀))` (p. 89); unrestricted joint space. -/
def elbowManipulator (l₀ l₁ l₂ : ℝ) : SerialChain 6 where
  twist := ![Twist.revolute zAxis (elbowShoulder l₀), Twist.revolute (-xAxis) (elbowShoulder l₀),
    Twist.revolute (-xAxis) (vec 0 l₁ l₀), Twist.revolute zAxis (elbowWrist l₀ l₁ l₂),
    Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂), Twist.revolute yAxis (elbowWrist l₀ l₁ l₂)]
  toolRef := ⟨1, elbowWrist l₀ l₁ l₂⟩

/-! ### The printed twists (MLS pp. 89–90) -/

/-- MLS p. 89: `ξ₁ = (0, 0, 0, 0, 0, 1)`. -/
theorem elbowManipulator_twist_zero (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 0 = ⟨vec 0 0 0, vec 0 0 1⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [elbowManipulator, elbowShoulder, elbowWrist, Twist.revolute, Vec3.cross, cross_apply,
        xAxis, yAxis, zAxis, vec]
  · ext i
    fin_cases i <;> simp [elbowManipulator, Twist.revolute, xAxis, yAxis, zAxis, vec]

/-- MLS p. 89: `ξ₂ = (0, -l₀, 0, -1, 0, 0)`. -/
theorem elbowManipulator_twist_one (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 1 = ⟨vec 0 (-l₀) 0, vec (-1) 0 0⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [elbowManipulator, elbowShoulder, elbowWrist, Twist.revolute, Vec3.cross, cross_apply,
        xAxis, yAxis, zAxis, vec]
  · ext i
    fin_cases i <;> simp [elbowManipulator, Twist.revolute, xAxis, yAxis, zAxis, vec]

/-- MLS p. 90: `ξ₃ = (0, -l₀, l₁, -1, 0, 0)`. -/
theorem elbowManipulator_twist_two (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 2 = ⟨vec 0 (-l₀) l₁, vec (-1) 0 0⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [elbowManipulator, elbowShoulder, elbowWrist, Twist.revolute, Vec3.cross, cross_apply,
        xAxis, yAxis, zAxis, vec]
  · ext i
    fin_cases i <;> simp [elbowManipulator, Twist.revolute, xAxis, yAxis, zAxis, vec]

/-- MLS p. 90: `ξ₄ = (l₁ + l₂, 0, 0, 0, 0, 1)`. -/
theorem elbowManipulator_twist_three (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 3 = ⟨vec (l₁ + l₂) 0 0, vec 0 0 1⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [elbowManipulator, elbowShoulder, elbowWrist, Twist.revolute, Vec3.cross, cross_apply,
        xAxis, yAxis, zAxis, vec]
  · ext i
    fin_cases i <;> simp [elbowManipulator, Twist.revolute, xAxis, yAxis, zAxis, vec]

/-- MLS p. 90: `ξ₅ = (0, -l₀, l₁ + l₂, -1, 0, 0)`. -/
theorem elbowManipulator_twist_four (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 4 = ⟨vec 0 (-l₀) (l₁ + l₂), vec (-1) 0 0⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [elbowManipulator, elbowShoulder, elbowWrist, Twist.revolute, Vec3.cross, cross_apply,
        xAxis, yAxis, zAxis, vec]
  · ext i
    fin_cases i <;> simp [elbowManipulator, Twist.revolute, xAxis, yAxis, zAxis, vec]

/-- MLS p. 90: `ξ₆ = (-l₀, 0, 0, 0, 1, 0)`. -/
theorem elbowManipulator_twist_five (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 5 = ⟨vec (-l₀) 0 0, vec 0 1 0⟩ := by
  apply Twist.ext
  · ext i
    fin_cases i <;>
      simp [elbowManipulator, elbowShoulder, elbowWrist, Twist.revolute, Vec3.cross, cross_apply,
        xAxis, yAxis, zAxis, vec]
  · ext i
    fin_cases i <;> simp [elbowManipulator, Twist.revolute, xAxis, yAxis, zAxis, vec]

/-- Every joint of the elbow manipulator is a revolute joint with a unit axis in the sense of
MLS p. 87 (Example 3.2, p. 89: all six joints are revolute). -/
theorem elbowManipulator_isRevoluteJoint (l₀ l₁ l₂ : ℝ) (i : Fin 6) :
    ((elbowManipulator l₀ l₁ l₂).twist i).IsRevoluteJoint := by
  fin_cases i
  · exact ⟨zAxis, elbowShoulder l₀, norm_zAxis, rfl⟩
  · exact ⟨-xAxis, elbowShoulder l₀, norm_neg_xAxis, rfl⟩
  · exact ⟨-xAxis, vec 0 l₁ l₀, norm_neg_xAxis, rfl⟩
  · exact ⟨zAxis, elbowWrist l₀ l₁ l₂, norm_zAxis, rfl⟩
  · exact ⟨-xAxis, elbowWrist l₀ l₁ l₂, norm_neg_xAxis, rfl⟩
  · exact ⟨yAxis, elbowWrist l₀ l₁ l₂, Rotation.norm_yAxis, rfl⟩

/-! ### Forward kinematics as printed (MLS pp. 90–91) -/

/-- The rotation `R(θ)` printed on MLS p. 91 (Example 3.2), with `cᵢ = cos θᵢ`, `sᵢ = sin θᵢ`,
`c₂₃ = cos(θ₂ + θ₃)`, `s₂₃ = sin(θ₂ + θ₃)`; the book's `θᵢ` is Lean's `θ (i - 1)`. -/
def elbowRotationMatrix (θ : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let c₁ := Real.cos (θ 0)
  let s₁ := Real.sin (θ 0)
  let c₄ := Real.cos (θ 3)
  let s₄ := Real.sin (θ 3)
  let c₅ := Real.cos (θ 4)
  let s₅ := Real.sin (θ 4)
  let c₆ := Real.cos (θ 5)
  let s₆ := Real.sin (θ 5)
  let c₂₃ := Real.cos (θ 1 + θ 2)
  let s₂₃ := Real.sin (θ 1 + θ 2)
  !![c₆ * (c₁ * c₄ - s₁ * c₂₃ * s₄) + s₆ * (s₁ * s₂₃ * c₅ + s₁ * c₂₃ * c₄ * s₅ + c₁ * s₄ * s₅),
      -c₅ * (s₁ * c₂₃ * c₄ + c₁ * s₄) + s₁ * s₂₃ * s₅,
      c₆ * (-c₅ * s₁ * s₂₃ - (c₂₃ * c₄ * s₁ + c₁ * s₄) * s₅) + (c₁ * c₄ - c₂₃ * s₁ * s₄) * s₆;
    c₆ * (c₄ * s₁ + c₁ * c₂₃ * s₄) - (c₁ * c₅ * s₂₃ + (c₁ * c₂₃ * c₄ - s₁ * s₄) * s₅) * s₆,
      c₅ * (c₁ * c₂₃ * c₄ - s₁ * s₄) - c₁ * s₂₃ * s₅,
      c₆ * (c₁ * c₅ * s₂₃ + (c₁ * c₂₃ * c₄ - s₁ * s₄) * s₅) + (c₄ * s₁ + c₁ * c₂₃ * s₄) * s₆;
    -(c₆ * s₂₃ * s₄) - (c₂₃ * c₅ - c₄ * s₂₃ * s₅) * s₆,
      -(c₄ * c₅ * s₂₃) - c₂₃ * s₅,
      c₆ * (c₂₃ * c₅ - c₄ * s₂₃ * s₅) - s₂₃ * s₄ * s₆]

/-- The product of exponentials with the six revolute twists written out. -/
private theorem elbowManipulator_poe_revolute (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (elbowManipulator l₀ l₁ l₂).poe θ =
      Twist.exp (Twist.revolute zAxis (elbowShoulder l₀)) (θ 0) *
        Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀)) (θ 1) *
        Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 2) *
        Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂)) (θ 3) *
        Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂)) (θ 4) *
        Twist.exp (Twist.revolute yAxis (elbowWrist l₀ l₁ l₂)) (θ 5) := by
  simp only [SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- **MLS Example 3.2, p. 91: the rotation of the elbow manipulator.** The rotation part of
`g_st(θ) = e^{ξ̂₁θ₁} ⋯ e^{ξ̂₆θ₆} g_st(0)` (eq. (3.3)) is the printed matrix `R(θ)`, for all real
link lengths and joint angles. Proved by evaluating the six revolute exponentials, not from a
closed form placed in the definition. -/
theorem elbowManipulator_fk_rotation (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((elbowManipulator l₀ l₁ l₂).fk θ).rotation.val = elbowRotationMatrix θ := by
  have hR : ((elbowManipulator l₀ l₁ l₂).fk θ).rotation =
      Rotation.exp zAxis (θ 0) * Rotation.exp (-xAxis) (θ 1 + θ 2) * Rotation.exp zAxis (θ 3) *
        Rotation.exp (-xAxis) (θ 4) * Rotation.exp yAxis (θ 5) := by
    rw [SerialChain.fk, elbowManipulator_poe_revolute]
    simp only [RigidTransform.mul_rotation, Twist.exp_revolute _ _ norm_zAxis,
      Twist.exp_revolute _ _ norm_neg_xAxis, Twist.exp_revolute _ _ Rotation.norm_yAxis]
    rw [Rotation.exp_add, show (elbowManipulator l₀ l₁ l₂).toolRef.rotation = 1 from rfl, mul_one,
      ← mul_assoc]
  rw [hR]
  simp only [Submonoid.coe_mul, Rotation.exp_neg_axis, Rotation.exp_xAxis_val,
    Rotation.exp_yAxis_val, Rotation.exp_zAxis_val, Rotation.xMatrix, Rotation.yMatrix,
    Rotation.zMatrix, Matrix.mul_fin_three, Real.cos_neg, Real.sin_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elbowRotationMatrix] <;> ring

/-- **MLS Example 3.2, p. 90: the position of the elbow manipulator.** The translation part of
`g_st(θ)` (eq. (3.3)) is the printed
`p(θ) = (-sin θ₁ (l₁ cos θ₂ + l₂ cos(θ₂ + θ₃)), cos θ₁ (l₁ cos θ₂ + l₂ cos(θ₂ + θ₃)),
l₀ - l₁ sin θ₂ - l₂ sin(θ₂ + θ₃))`, for all real link lengths and joint angles. -/
theorem elbowManipulator_fk_translation (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((elbowManipulator l₀ l₁ l₂).fk θ).translation =
      vec (-Real.sin (θ 0) * (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)))
        (Real.cos (θ 0) * (l₁ * Real.cos (θ 1) + l₂ * Real.cos (θ 1 + θ 2)))
        (l₀ - l₁ * Real.sin (θ 1) - l₂ * Real.sin (θ 1 + θ 2)) := by
  have hfk : ((elbowManipulator l₀ l₁ l₂).fk θ).translation =
      ((elbowManipulator l₀ l₁ l₂).poe θ).applyPoint (elbowWrist l₀ l₁ l₂) := rfl
  rw [hfk, elbowManipulator_poe_revolute]
  simp only [RigidTransform.mul_applyPoint, exp_revolute_applyPoint_self norm_zAxis,
    exp_revolute_applyPoint_self norm_neg_xAxis, exp_revolute_applyPoint_self Rotation.norm_yAxis]
  rw [Twist.exp_revolute_applyPoint _ _ norm_neg_xAxis,
    Twist.exp_revolute_applyPoint _ _ norm_neg_xAxis, Twist.exp_revolute_applyPoint _ _ norm_zAxis]
  simp only [elbowWrist, elbowShoulder, vec_sub, act_negX, vec_add, act_Z]
  rw [Real.cos_add, Real.sin_add]
  ext i
  fin_cases i <;> simp only [vec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    ring

/-- The six joint twists of the elbow manipulator as revolute twists. -/
private theorem elbowManipulator_twist_revolute (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).twist 0 = Twist.revolute zAxis (elbowShoulder l₀) ∧
      (elbowManipulator l₀ l₁ l₂).twist 1 = Twist.revolute (-xAxis) (elbowShoulder l₀) ∧
      (elbowManipulator l₀ l₁ l₂).twist 2 = Twist.revolute (-xAxis) (vec 0 l₁ l₀) ∧
      (elbowManipulator l₀ l₁ l₂).twist 3 = Twist.revolute zAxis (elbowWrist l₀ l₁ l₂) ∧
      (elbowManipulator l₀ l₁ l₂).twist 4 = Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Example 3.5: the inverse-kinematics decomposition (MLS pp. 104–106) -/

/-- The product of exponentials of the elbow manipulator, written out:
`e^{ξ̂₁θ₁} ⋯ e^{ξ̂₆θ₆}` (MLS eq. (3.3), p. 87; the left side of eq. (3.30), p. 105). -/
theorem elbowManipulator_poe (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (elbowManipulator l₀ l₁ l₂).poe θ =
      Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (θ 0) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (θ 2) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (θ 3) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4) (θ 4) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 5) (θ 5) := by
  simp only [SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- **MLS eq. (3.31), p. 105.** If `g_st(θ) = g_d`, applying both sides of eq. (3.30) to the wrist
centre `p_w`, which the three wrist motions fix, gives
`e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} e^{ξ̂₃θ₃} p_w = g₁ p_w` with `g₁ = g_d g_st(0)⁻¹`. -/
theorem elbowManipulator_wrist_eq {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) :
    (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (θ 0) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (θ 2)).applyPoint (elbowWrist l₀ l₁ l₂) =
      (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂) := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, elbowManipulator_poe_revolute]
  simp only [RigidTransform.mul_applyPoint, exp_revolute_applyPoint_self norm_zAxis,
    exp_revolute_applyPoint_self norm_neg_xAxis, exp_revolute_applyPoint_self Rotation.norm_yAxis]
  rfl

/-- **MLS Example 3.5, Step 1, eq. (3.33), p. 105: the elbow angle solves Subproblem 3.** If
`g_st(θ) = g_d`, then `‖p_b - e^{ξ̂₃θ₃} p_w‖ = ‖g₁ p_w - p_b‖`: Subproblem 3 (eq. (3.26)) for the
third joint twist `ξ₃ = (-ω₃ × q₃, ω₃)`, `ω₃ = -x`, `q₃ = (0, l₁, l₀)`, with `p = p_w`, `q = p_b`
and `δ = ‖g₁ p_w - p_b‖`, `g₁ = g_d g_st(0)⁻¹`. The first two motions fix `p_b` and preserve
distances. -/
theorem elbowManipulator_subproblemThree {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) :
    ‖elbowShoulder l₀ -
        (Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 2)).applyPoint
          (elbowWrist l₀ l₁ l₂)‖ =
      ‖(g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂) -
        elbowShoulder l₀‖ := by
  have hb : (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (θ 0) *
      Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (θ 1)).applyPoint (elbowShoulder l₀) =
      elbowShoulder l₀ := by
    simp only [RigidTransform.mul_applyPoint]
    exact (congrArg _ (exp_revolute_applyPoint_self norm_neg_xAxis _ _)).trans
      (exp_revolute_applyPoint_self norm_zAxis _ _)
  rw [← elbowManipulator_wrist_eq h, RigidTransform.mul_applyPoint]
  nth_rewrite 2 [← hb]
  rw [RigidTransform.applyPoint_sub_applyPoint, RigidTransform.norm_applyVector, norm_sub_rev]
  rfl

/-- **MLS Example 3.5, Step 1, with eq. (3.29), p. 103: the elbow angle is one of the two
Subproblem 3 angles.** If `g_st(θ) = g_d` and `l₁ ≠ 0`, `l₂ ≠ 0` (so that neither `p_w` nor `p_b`
lies on the third axis; hypotheses the book does not state), then
`θ₃ = θ₀ ± cos⁻¹ κ` modulo `2π`, where `θ₀` (eq. (3.28)) and `κ` (the argument of `cos⁻¹` in
eq. (3.29)) are those of Subproblem 3 with `ω = -x`, `r = (0, l₁, l₀)`, `p = p_w`, `q = p_b` and
`δ = ‖g₁ p_w - p_b‖`. -/
theorem elbowManipulator_elbow_angle {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {θ : Fin 6 → ℝ} {g : RigidTransform} (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) :
    ∃ k : ℤ,
      θ 2 = PadenKahan.planeAngle (-xAxis) (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
            (elbowShoulder l₀ - vec 0 l₁ l₀) +
          Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀)
            (elbowWrist l₀ l₁ l₂) (elbowShoulder l₀)
            ‖(g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂) -
              elbowShoulder l₀‖) + k * (2 * Real.pi) ∨
      θ 2 = PadenKahan.planeAngle (-xAxis) (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
            (elbowShoulder l₀ - vec 0 l₁ l₀) -
          Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀)
            (elbowWrist l₀ l₁ l₂) (elbowShoulder l₀)
            ‖(g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂) -
              elbowShoulder l₀‖) + k * (2 * Real.pi) := by
  have hsub := elbowManipulator_subproblemThree h
  have hu : PadenKahan.perp (-xAxis) (elbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [PadenKahan.perp, elbowWrist, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₂ h1
  have hv : PadenKahan.perp (-xAxis) (elbowShoulder l₀ - vec 0 l₁ l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [PadenKahan.perp, elbowShoulder, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₁ h1
  have hcos := (PadenKahan.subproblemThree_iff_cos norm_neg_xAxis (norm_nonneg _) hu hv
    (θ 2)).mp hsub
  exact (PadenKahan.subproblemThree_iff norm_neg_xAxis (norm_nonneg _) hu hv
    (hcos ▸ Real.neg_one_le_cos _) (hcos ▸ Real.cos_le_one _) (θ 2)).mp hsub

/-- **MLS Example 3.5, Step 2, eq. (3.34), p. 105: the shoulder angles solve Subproblem 2.** If
`g_st(θ) = g_d`, then `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` with `p = e^{ξ̂₃θ₃} p_w` and `q = g₁ p_w`: Subproblem 2
(eq. (3.20)) for the unit twists `ξ₁ = (-ω₁ × p_b, ω₁)`, `ω₁ = +z`, and `ξ₂ = (-ω₂ × p_b, ω₂)`,
`ω₂ = -x`, whose axes meet at `p_b`; the axes are not parallel (`ω₁ × ω₂ ≠ 0`,
`elbowManipulator_shoulder_axes_cross_ne_zero`), as `PadenKahan.subproblemTwo_iff` requires. -/
theorem elbowManipulator_subproblemTwo_shoulder {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ}
    {g : RigidTransform} (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) :
    (Twist.exp (Twist.revolute zAxis (elbowShoulder l₀)) (θ 0) *
        Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀)) (θ 1)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 2)).applyPoint
          (elbowWrist l₀ l₁ l₂)) =
      (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂) := by
  rw [← RigidTransform.mul_applyPoint]
  exact elbowManipulator_wrist_eq h

/-- The shoulder axes `+z` and `-x` of the elbow manipulator (and equally the wrist axes of
joints 4 and 5) are not parallel: `(+z) × (-x) ≠ 0`, the non-parallel hypothesis of
Subproblem 2 (MLS p. 101). -/
theorem elbowManipulator_shoulder_axes_cross_ne_zero : Vec3.cross zAxis (-xAxis) ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Vec3 => v 1) h
  simp [Vec3.cross, cross_apply, xAxis, zAxis] at h1

/-- **MLS Example 3.5, Step 3, eqs. (3.35)–(3.36), p. 106: two wrist angles solve
Subproblem 2.** If `g_st(θ) = g_d`, then for every point `p` on the axis of `ξ₆` (the line
through `p_w` along `+y`), `e^{ξ̂₄θ₄} e^{ξ̂₅θ₅} p = g₂ p` with
`g₂ = e^{-ξ̂₃θ₃} e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g_d g_st(0)⁻¹`: Subproblem 2 for the unit twists through `p_w`
with axes `+z` and `-x`. The book takes `p` "not on the `ξ₄`, `ξ₅` axes" so that the subproblem is
informative; the equation holds for every point of the sixth axis. -/
theorem elbowManipulator_subproblemTwo_wrist {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ}
    {g : RigidTransform} (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) {p : Vec3}
    (hp : p ∈ axisLine (elbowWrist l₀ l₁ l₂) yAxis) :
    (Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂)) (θ 3) *
        Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂)) (θ 4)).applyPoint p =
      (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-θ 2) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-θ 0) *
        (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, elbowManipulator_poe_revolute]
  simp only [elbowManipulator_twist_revolute, Twist.exp_neg, mul_assoc, inv_mul_cancel_left,
    RigidTransform.mul_applyPoint,
    Twist.exp_revolute_applyPoint_of_mem_axisLine yAxis _ Rotation.norm_yAxis _ hp]

/-- **MLS Example 3.5, Step 4, eq. (3.37), p. 106: the last wrist angle solves Subproblem 1.** If
`g_st(θ) = g_d`, then for every point `p`,
`e^{ξ̂₆θ₆} p = e^{-ξ̂₅θ₅} e^{-ξ̂₄θ₄} ⋯ e^{-ξ̂₁θ₁} g_d g_st(0)⁻¹ p`: Subproblem 1 (eq. (3.17)) for the
unit twist through `p_w` with axis `+y`. The book takes `p` not on the sixth axis, for which
Subproblem 1 determines `θ₆` modulo `2π` (`PadenKahan.subproblemOne_iff`). -/
theorem elbowManipulator_subproblemOne {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (elbowManipulator l₀ l₁ l₂).fk θ = g) (p : Vec3) :
    (Twist.exp (Twist.revolute yAxis (elbowWrist l₀ l₁ l₂)) (θ 5)).applyPoint p =
      (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4) (-θ 4) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-θ 3) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-θ 2) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-θ 0) *
        (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, elbowManipulator_poe_revolute]
  simp only [elbowManipulator_twist_revolute, Twist.exp_neg, mul_assoc, inv_mul_cancel_left]

/-! ### Example 3.5: the four steps determine every solution -/

private theorem cross_self_eq_zero (u : Vec3) : Vec3.cross u u = 0 := by
  apply WithLp.ofLp_injective
  simp [Vec3.cross_coordinates, cross_self]

private theorem linearIndependent_cross {u v : Vec3} (h : Vec3.cross u v ≠ 0) :
    LinearIndependent ℝ ![u, v, Vec3.cross u v] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hc
  have h2 : c 2 = 0 := by
    have := congrArg (fun x => inner ℝ x (Vec3.cross u v)) hc
    simp only [inner_add_left, real_inner_smul_left, Vec3.inner_cross_left,
      Vec3.inner_cross_right, inner_zero_left, mul_zero, zero_add] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd (inner_self_eq_zero.mp h') h
  rw [h2, zero_smul, add_zero] at hc
  have h0 : c 0 = 0 := by
    have := congrArg (fun x => Vec3.cross x v) hc
    simp only [Vec3.add_cross, Vec3.smul_cross, cross_self_eq_zero, smul_zero, add_zero,
      Vec3.zero_cross] at this
    exact (smul_eq_zero.mp this).resolve_right h
  have h1 : c 1 = 0 := by
    have := congrArg (fun x => Vec3.cross u x) hc
    simp only [Vec3.cross_add, Vec3.cross_smul, cross_self_eq_zero, smul_zero, zero_add,
      Vec3.cross_zero] at this
    exact (smul_eq_zero.mp this).resolve_right h
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem rotation_eq_one_of_act_eq {R : Rotation} {u v : Vec3}
    (huv : Vec3.cross u v ≠ 0) (hu : R.act u = u) (hv : R.act v = v) : R = 1 := by
  have hspan := (linearIndependent_cross huv).span_eq_top_of_card_eq_finrank' (by simp)
  have hact : R.act = (1 : Rotation).act := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
    · simp [Rotation.act_cross, hu, hv]
  exact Subtype.ext (Matrix.toEuclideanLin.injective hact)

private theorem eq_one_of_applyPoint_eq {g : RigidTransform} {p₀ p₁ p₂ : Vec3}
    (h : Vec3.cross (p₁ - p₀) (p₂ - p₀) ≠ 0) (h₀ : g.applyPoint p₀ = p₀)
    (h₁ : g.applyPoint p₁ = p₁) (h₂ : g.applyPoint p₂ = p₂) : g = 1 := by
  have hR : g.rotation = 1 := by
    apply rotation_eq_one_of_act_eq h
    · have := g.applyPoint_sub_applyPoint p₁ p₀
      rw [h₁, h₀] at this
      exact this.symm
    · have := g.applyPoint_sub_applyPoint p₂ p₀
      rw [h₂, h₀] at this
      exact this.symm
  have ht : g.translation = 0 := by
    simpa [RigidTransform.applyPoint, hR] using h₀
  exact RigidTransform.ext hR ht

/-- **MLS Example 3.5, pp. 105–106: the subproblem equations determine the solutions.** Conversely
to Steps 2–4, let `p ≠ p_w` be a point of the sixth axis and `p′` a point off it (the points the
book prescribes in Steps 3 and 4). If `θ` satisfies the Subproblem 2 equation (3.34) of Step 2,
the Subproblem 2 equation (3.36) of Step 3 at `p`, and the Subproblem 1 equation (3.37) of Step 4
at `p′`, then `g_st(θ) = g_d`. The proof: the rigid motion
`e^{-ξ̂₆θ₆} ⋯ e^{-ξ̂₁θ₁} g_d g_st(0)⁻¹` fixes `p_w`, `p` and `p′`, three points not on one line, so
it is the identity. The equation (3.33) of Step 1 follows from (3.34). -/
theorem elbowManipulator_fk_eq_of_subproblems {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ}
    {g : RigidTransform}
    (h₁₂ : (Twist.exp (Twist.revolute zAxis (elbowShoulder l₀)) (θ 0) *
        Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀)) (θ 1)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 2)).applyPoint
          (elbowWrist l₀ l₁ l₂)) =
      (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂))
    {p : Vec3} (hp : p ∈ axisLine (elbowWrist l₀ l₁ l₂) yAxis) (hpw : p ≠ elbowWrist l₀ l₁ l₂)
    (h₄₅ : (Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂)) (θ 3) *
        Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂)) (θ 4)).applyPoint p =
      (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-θ 2) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-θ 0) *
        (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)).applyPoint p)
    {p' : Vec3} (hp' : p' ∉ axisLine (elbowWrist l₀ l₁ l₂) yAxis)
    (h₆ : (Twist.exp (Twist.revolute yAxis (elbowWrist l₀ l₁ l₂)) (θ 5)).applyPoint p' =
      (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4) (-θ 4) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-θ 3) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-θ 2) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-θ 0) *
        (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)).applyPoint p') :
    (elbowManipulator l₀ l₁ l₂).fk θ = g := by
  have hP := elbowManipulator_poe_revolute l₀ l₁ l₂ θ
  set g₁ := g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹
  simp only [elbowManipulator_twist_revolute, Twist.exp_neg, RigidTransform.mul_applyPoint]
    at h₁₂ h₄₅ h₆
  set A₁ := Twist.exp (Twist.revolute zAxis (elbowShoulder l₀)) (θ 0)
  set A₂ := Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀)) (θ 1)
  set A₃ := Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 2)
  set A₄ := Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂)) (θ 3)
  set A₅ := Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂)) (θ 4)
  set A₆ := Twist.exp (Twist.revolute yAxis (elbowWrist l₀ l₁ l₂)) (θ 5)
  set pw := elbowWrist l₀ l₁ l₂
  have hM : ∀ x, ((elbowManipulator l₀ l₁ l₂).poe θ)⁻¹.applyPoint (g₁.applyPoint x) =
      A₆⁻¹.applyPoint (A₅⁻¹.applyPoint (A₄⁻¹.applyPoint
        (A₃⁻¹.applyPoint (A₂⁻¹.applyPoint (A₁⁻¹.applyPoint (g₁.applyPoint x)))))) := by
    intro x
    simp only [hP, mul_inv_rev, RigidTransform.mul_applyPoint]
  have h₆p : A₆.applyPoint p = p :=
    Twist.exp_revolute_applyPoint_of_mem_axisLine yAxis _ Rotation.norm_yAxis _ hp
  have h₆inv : A₆⁻¹.applyPoint p = p := by
    conv_lhs => rw [← h₆p]
    exact RigidTransform.inv_applyPoint_applyPoint _ _
  have hfix : ∀ {ω : Vec3}, ‖ω‖ = 1 → ∀ t : ℝ,
      (Twist.exp (Twist.revolute ω pw) t).applyPoint pw = pw :=
    fun hω t => exp_revolute_applyPoint_self hω pw t
  have hcross : Vec3.cross (p - pw) (p' - pw) ≠ 0 := by
    obtain ⟨s, rfl⟩ := (mem_axisLine_iff _ _ _).mp hp
    have hs : s ≠ 0 := by
      rintro rfl
      simp at hpw
    rw [add_sub_cancel_left, Vec3.smul_cross]
    intro hc
    have hc' := (smul_eq_zero.mp hc).resolve_left hs
    have h0 := congrArg (fun v : Vec3 => v 0) hc'
    have h2 := congrArg (fun v : Vec3 => v 2) hc'
    simp [Vec3.cross, cross_apply, yAxis] at h0 h2
    apply hp'
    rw [mem_axisLine_iff]
    refine ⟨p' 1 - pw 1, ?_⟩
    ext i
    fin_cases i <;> simp [yAxis] <;> linarith
  have hM1 : ((elbowManipulator l₀ l₁ l₂).poe θ)⁻¹ * g₁ = 1 := by
    refine eq_one_of_applyPoint_eq hcross ?_ ?_ ?_
    · have h₄w : A₄.applyPoint pw = pw := hfix norm_zAxis _
      have h₅w : A₅.applyPoint pw = pw := hfix norm_neg_xAxis _
      have h₆w : A₆.applyPoint pw = pw := hfix Rotation.norm_yAxis _
      have hPw : ((elbowManipulator l₀ l₁ l₂).poe θ).applyPoint pw = g₁.applyPoint pw := by
        rw [← h₁₂, hP]
        simp only [RigidTransform.mul_applyPoint]
        rw [h₆w, h₅w, h₄w]
      rw [RigidTransform.mul_applyPoint, ← hPw, RigidTransform.inv_applyPoint_applyPoint]
    · rw [RigidTransform.mul_applyPoint, hM, ← h₄₅, RigidTransform.inv_applyPoint_applyPoint,
        RigidTransform.inv_applyPoint_applyPoint, h₆inv]
    · rw [RigidTransform.mul_applyPoint, hM, ← h₆, RigidTransform.inv_applyPoint_applyPoint]
  exact (SerialChain.fk_eq_iff_poe_eq _ _ _).mpr (inv_mul_eq_one.mp hM1)

/-- **MLS Example 3.5, pp. 104–106: all solutions of the elbow inverse kinematics.** For a point
`p ≠ p_w` of the sixth axis and a point `p′` off it, a joint vector `θ` solves `g_st(θ) = g_d`
exactly when it satisfies the Subproblem 2 equation (3.34) (Step 2), the Subproblem 2 equation
(3.36) at `p` (Step 3) and the Subproblem 1 equation (3.37) at `p′` (Step 4). Step 1, eq. (3.33),
is a consequence (`elbowManipulator_subproblemThree`). The count "a maximum of eight possible
solutions" (p. 106) is not formalized. -/
theorem elbowManipulator_fk_eq_iff {l₀ l₁ l₂ : ℝ} {p p' : Vec3}
    (hp : p ∈ axisLine (elbowWrist l₀ l₁ l₂) yAxis) (hpw : p ≠ elbowWrist l₀ l₁ l₂)
    (hp' : p' ∉ axisLine (elbowWrist l₀ l₁ l₂) yAxis) (θ : Fin 6 → ℝ) (g : RigidTransform) :
    (elbowManipulator l₀ l₁ l₂).fk θ = g ↔
      (Twist.exp (Twist.revolute zAxis (elbowShoulder l₀)) (θ 0) *
          Twist.exp (Twist.revolute (-xAxis) (elbowShoulder l₀)) (θ 1)).applyPoint
          ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 2)).applyPoint
            (elbowWrist l₀ l₁ l₂)) =
        (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹).applyPoint (elbowWrist l₀ l₁ l₂) ∧
      (Twist.exp (Twist.revolute zAxis (elbowWrist l₀ l₁ l₂)) (θ 3) *
          Twist.exp (Twist.revolute (-xAxis) (elbowWrist l₀ l₁ l₂)) (θ 4)).applyPoint p =
        (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-θ 2) *
          Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-θ 1) *
          Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-θ 0) *
          (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)).applyPoint p ∧
      (Twist.exp (Twist.revolute yAxis (elbowWrist l₀ l₁ l₂)) (θ 5)).applyPoint p' =
        (Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 4) (-θ 4) *
          Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 3) (-θ 3) *
          Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 2) (-θ 2) *
          Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 1) (-θ 1) *
          Twist.exp ((elbowManipulator l₀ l₁ l₂).twist 0) (-θ 0) *
          (g * (elbowManipulator l₀ l₁ l₂).toolRef⁻¹)).applyPoint p' := by
  constructor
  · intro h
    exact ⟨elbowManipulator_subproblemTwo_shoulder h, elbowManipulator_subproblemTwo_wrist h hp,
      elbowManipulator_subproblemOne h p'⟩
  · rintro ⟨h₁₂, h₄₅, h₆⟩
    exact elbowManipulator_fk_eq_of_subproblems h₁₂ hp hpw h₄₅ hp' h₆

/-! ### The reference configuration is singular (MLS p. 126) -/

/-- **MLS p. 126, after Example 3.12: "The elbow manipulator exhibits this singularity in its
reference configuration."** At `θ = 0` the spatial Jacobian columns of joints 2, 3 and 5 are the
reference twists, with parallel axes `-x` through `(0, 0, l₀)`, `(0, l₁, l₀)`, `(0, l₁ + l₂, l₀)`,
all in the plane `z = l₀` with unit normal `+z`; by Example 3.12
(`SerialChain.isSingular_of_three_parallel_coplanar_revolute`) the configuration is singular,
for all real link lengths. -/
theorem elbowManipulator_isSingular_zero (l₀ l₁ l₂ : ℝ) :
    (elbowManipulator l₀ l₁ l₂).IsSingular 0 := by
  refine SerialChain.isSingular_of_three_parallel_coplanar_revolute _ 0 le_rfl ![1, 2, 4]
    (by decide) (fun _ => -xAxis) ![elbowShoulder l₀, vec 0 l₁ l₀, elbowWrist l₀ l₁ l₂] ?_
    (fun _ _ => Or.inl rfl) zAxis norm_zAxis ?_ ?_
  · intro k
    have hJ : ∀ i, (elbowManipulator l₀ l₁ l₂).spatialJacobian 0 i =
        (elbowManipulator l₀ l₁ l₂).twist i := by
      intro i
      fin_cases i <;> simp [SerialChain.spatialJacobian, SerialChain.jointMotions]
    rw [hJ]
    fin_cases k <;> rfl
  · intro i
    simp [zAxis, xAxis, PiLp.inner_apply, Fin.sum_univ_three]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [zAxis, elbowShoulder, elbowWrist, vec, PiLp.inner_apply, Fin.sum_univ_three]

end RoboLean.Examples
