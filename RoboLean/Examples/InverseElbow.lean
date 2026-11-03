import RoboLean.Kinematics.PadenKahan
import RoboLean.Kinematics.Jacobian
import RoboLean.Examples.RigidTransform

/-!
# The inverse elbow manipulator of MLS Figure 3.24(ii): Exercise 4(a)–(c)

MLS Chapter 3, Exercise 4, printed pp. 146–147, Figure 3.24(ii). The figure is drawn in the style
of the elbow manipulator of Figure 3.4 (p. 90): vertical cylinders are joints about `+z`, cylinders
drawn along the arm are joints about `+y`, and cylinders drawn in the depth direction are joints
about `-x`, the directions Example 3.2 (p. 89) assigns to the same drawing. Read in that style, the
inverse elbow has a base joint about `+z`, a joint about `+y` and a joint about `-x` whose axes are
drawn through one point `p_b`, two further joints about `-x` (the elbow and the first wrist joint),
and a last joint about `+y` drawn through the axis of the fifth joint. The figure has no dimensions;
`l₀` (height of `p_b`), `l₁` (from `p_b` to the elbow axis) and `l₂` (from the elbow axis to the
point `w` where axes 5 and 6 meet) are recorded symbols. That the first three axes meet at `p_b`
and that axes 5 and 6 meet at `w` are readings of the drawing, which makes the arm the elbow
manipulator with the order of its joint groups reversed.

Frame and data: base frame with `z` along the first axis and `y` along the arm at `θ = 0`, as in
Example 3.2; `p_b = (0, 0, l₀)`, the elbow axis through `(0, l₁, l₀)`, `w = (0, l₁ + l₂, l₀)`, and
`g_st(0) = (I, w)`. Twists `ξᵢ = (-ωᵢ × qᵢ, ωᵢ)` in the library order `(v, ω)`; Lean joint `k` is
the book's joint `k + 1`.

Contents: the chain; the forward kinematics as the product of exponentials (eq. (3.3), p. 87), its
rotation and tool position in closed form; the spatial Jacobian (eq. (3.54), p. 116); and the
inverse-kinematics decomposition by the Paden–Kahan subproblems (pp. 99–104) in the manner of
Example 3.5 (pp. 104–106), with every step a necessary condition on a solution:

* the elbow angle `θ₄` solves Subproblem 3 with `p = w`, `q = p_b`, `δ = ‖g₁ w - p_b‖`,
  `g₁ = g_d g_st(0)⁻¹`, and is one of the two angles of eq. (3.29) modulo `2π`;
* `(θ₆, θ₅)` solve Subproblem 2 for the inverse motions about the two axes through `w`, applied to
  `e^{-ξ̂₄θ₄} p_b`, with target `g₁⁻¹ p_b`;
* `(θ₁, θ₂)` solve Subproblem 2 for every point of the third axis;
* `θ₃` solves Subproblem 1.

Not covered here: Exercise 4(d) and 4(e) (singular configurations, workspaces and solution counts)
and the converse that the four steps find every solution. These are statements about the
coordinate model, not about a physical arm.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)
open Real

/-! ### Private coordinate helpers -/

private theorem ie_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem ie_norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem ie_act_negX (t x y z : ℝ) :
    (Rotation.exp (-xAxis) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem ie_act_Z (t x y z : ℝ) :
    (Rotation.exp zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem ie_act_Y (t x y z : ℝ) :
    (Rotation.exp yAxis t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem ie_act_Z' (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z :=
  ie_act_Z t x y z

private theorem ie_act_Y' (t x y z : ℝ) :
    (Rotation.exp (vec 0 1 0) t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) :=
  ie_act_Y t x y z

private theorem ie_act_negX' (t x y z : ℝ) :
    (Rotation.exp (vec (-1) 0 0) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [show vec (-1) 0 0 = -xAxis from by ext i; fin_cases i <;> simp [vec, xAxis]]
  exact ie_act_negX t x y z

private theorem ie_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem ie_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem ie_vec_neg (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem ie_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem ie_xAxis : xAxis = vec 1 0 0 := rfl
private theorem ie_yAxis : yAxis = vec 0 1 0 := rfl
private theorem ie_zAxis : zAxis = vec 0 0 1 := rfl

private theorem ie_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem ie_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem ie_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem ie_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem ie_tool_applyPoint (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform).applyPoint (vec 0 0 0) = vec a b c := by
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

private theorem ie_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint q = q :=
  Twist.exp_revolute_applyPoint_of_mem_axisLine ω q hω t (AffineSubspace.self_mem_mk' _ _)

private theorem ie_inv_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t)⁻¹.applyPoint q = q := by
  rw [← Twist.exp_neg]
  exact ie_fix hω q (-t)

/-- The base point `p_b = (0, 0, l₀)` of the inverse elbow manipulator of MLS Figure 3.24(ii),
p. 147 (Exercise 4): the point where the first three joint axes meet, under the recorded reading
of the figure. -/
def inverseElbowBase (l₀ : ℝ) : Vec3 := vec 0 0 l₀

/-- The point `w = (0, l₁ + l₂, l₀)` where the fifth and sixth joint axes of the inverse elbow
manipulator of MLS Figure 3.24(ii), p. 147, meet; the tool origin at `θ = 0` (recorded reading). -/
def inverseElbowWrist (l₀ l₁ l₂ : ℝ) : Vec3 := vec 0 (l₁ + l₂) l₀

/-- **MLS Figure 3.24(ii), p. 147 (Exercise 4): the inverse elbow manipulator**, under the
recorded reading: revolute joints about `+z`, `+y` and `-x` through `p_b = (0, 0, l₀)`, about `-x`
through `(0, l₁, l₀)`, and about `-x` and `+y` through `w = (0, l₁ + l₂, l₀)`; reference tool pose
`g_st(0) = (I, w)` (p. 87); twists `(-ω × q, ω)`, order `(v, ω)`; unrestricted joint space. -/
def inverseElbow (l₀ l₁ l₂ : ℝ) : SerialChain 6 where
  twist := ![Twist.revolute zAxis (inverseElbowBase l₀), Twist.revolute yAxis (inverseElbowBase l₀),
    Twist.revolute (-xAxis) (inverseElbowBase l₀), Twist.revolute (-xAxis) (vec 0 l₁ l₀),
    Twist.revolute (-xAxis) (inverseElbowWrist l₀ l₁ l₂),
    Twist.revolute yAxis (inverseElbowWrist l₀ l₁ l₂)]
  toolRef := ⟨1, inverseElbowWrist l₀ l₁ l₂⟩

/-- Every joint of the inverse elbow manipulator of MLS Figure 3.24(ii), p. 147, is a revolute
joint with a unit axis (MLS p. 87). -/
theorem inverseElbow_isRevoluteJoint (l₀ l₁ l₂ : ℝ) (i : Fin 6) :
    ((inverseElbow l₀ l₁ l₂).twist i).IsRevoluteJoint := by
  fin_cases i
  · exact ⟨zAxis, inverseElbowBase l₀, ie_norm_zAxis, rfl⟩
  · exact ⟨yAxis, inverseElbowBase l₀, Rotation.norm_yAxis, rfl⟩
  · exact ⟨-xAxis, inverseElbowBase l₀, ie_norm_neg_xAxis, rfl⟩
  · exact ⟨-xAxis, vec 0 l₁ l₀, ie_norm_neg_xAxis, rfl⟩
  · exact ⟨-xAxis, inverseElbowWrist l₀ l₁ l₂, ie_norm_neg_xAxis, rfl⟩
  · exact ⟨yAxis, inverseElbowWrist l₀ l₁ l₂, Rotation.norm_yAxis, rfl⟩

/-- **MLS Exercise 4(a), p. 146, for Figure 3.24(ii): the rotation of the forward kinematics**
(eq. (3.3), p. 87): `R(θ) = Rz(θ₁) Ry(θ₂) R₋ₓ(θ₃ + θ₄ + θ₅) Ry(θ₆)`, the three parallel joints
about `-x` adding their angles. -/
theorem inverseElbow_fk_rotation (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((inverseElbow l₀ l₁ l₂).fk θ).rotation =
      Rotation.exp zAxis (θ 0) * Rotation.exp yAxis (θ 1) *
        Rotation.exp (-xAxis) (θ 2 + θ 3 + θ 4) * Rotation.exp yAxis (θ 5) := by
  rw [Rotation.exp_add, Rotation.exp_add]
  simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    inverseElbow, Twist.revolute, mul_assoc]

/-- **MLS Exercise 4(a), p. 146, for Figure 3.24(ii): the tool position of the forward
kinematics** (eq. (3.3), p. 87): with `Y = l₁ c₃ + l₂ c₃₄` and `Z = -(l₁ s₃ + l₂ s₃₄)`, the tool
origin is `(c₁ s₂ Z - s₁ Y, s₁ s₂ Z + c₁ Y, l₀ + c₂ Z)`; the last two joints do not move it. -/
theorem inverseElbow_fk_translation (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((inverseElbow l₀ l₁ l₂).fk θ).translation =
      vec (cos (θ 0) * sin (θ 1) * (-(l₁ * sin (θ 2) + l₂ * sin (θ 2 + θ 3))) -
          sin (θ 0) * (l₁ * cos (θ 2) + l₂ * cos (θ 2 + θ 3)))
        (sin (θ 0) * sin (θ 1) * (-(l₁ * sin (θ 2) + l₂ * sin (θ 2 + θ 3))) +
          cos (θ 0) * (l₁ * cos (θ 2) + l₂ * cos (θ 2 + θ 3)))
        (l₀ + cos (θ 1) * (-(l₁ * sin (θ 2) + l₂ * sin (θ 2 + θ 3)))) := by
  rw [ie_translation]
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
  change (Twist.exp (Twist.revolute zAxis (inverseElbowBase l₀)) (θ 0)).applyPoint
    ((Twist.exp (Twist.revolute yAxis (inverseElbowBase l₀)) (θ 1)).applyPoint
      ((Twist.exp (Twist.revolute (-xAxis) (inverseElbowBase l₀)) (θ 2)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 3)).applyPoint
          ((Twist.exp (Twist.revolute (-xAxis) (inverseElbowWrist l₀ l₁ l₂)) (θ 4)).applyPoint
            ((Twist.exp (Twist.revolute yAxis (inverseElbowWrist l₀ l₁ l₂)) (θ 5)).applyPoint
              ((⟨1, inverseElbowWrist l₀ l₁ l₂⟩ : RigidTransform).applyPoint (vec 0 0 0))))))) = _
  rw [inverseElbowWrist, ie_tool_applyPoint, ie_fix Rotation.norm_yAxis, ie_fix ie_norm_neg_xAxis,
    ie_applyPoint_rev ie_norm_neg_xAxis, ie_applyPoint_rev ie_norm_neg_xAxis,
    ie_applyPoint_rev Rotation.norm_yAxis, ie_applyPoint_rev ie_norm_zAxis, inverseElbowBase]
  simp only [ie_vec_sub, ie_vec_add, ie_act_negX, ie_act_Y, ie_act_Z]
  apply ie_vec_eq <;> simp only [cos_add, sin_add] <;> ring

/-- **MLS Exercise 4(c), p. 147, for Figure 3.24(ii): the spatial Jacobian** (eq. (3.54),
p. 116), order `(v, ω)`: `ξ₁′ = (0, e_z)`; `ξ₂′` the revolute twist about `(-s₁, c₁, 0)` through
`p_b`; `ξ₃′`, `ξ₄′`, `ξ₅′` revolute twists about `(-c₁c₂, -s₁c₂, s₂)` through `p_b`, through the
moved elbow point `(-l₁(c₁s₂s₃ + s₁c₃), l₁(c₁c₃ - s₁s₂s₃), l₀ - l₁c₂s₃)` and through the moved
point `w`, the tool position of `inverseElbow_fk_translation`; and `ξ₆′` the revolute twist about
`(-(c₁s₂s₃₄₅ + s₁c₃₄₅), c₁c₃₄₅ - s₁s₂s₃₄₅, -c₂s₃₄₅)` through the moved `w`. -/
theorem inverseElbow_spatialJacobian (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (inverseElbow l₀ l₁ l₂).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩,
        Twist.revolute (vec (-sin (θ 0)) (cos (θ 0)) 0) (vec 0 0 l₀),
        Twist.revolute (vec (-(cos (θ 0) * cos (θ 1))) (-(sin (θ 0) * cos (θ 1))) (sin (θ 1)))
          (vec 0 0 l₀),
        Twist.revolute (vec (-(cos (θ 0) * cos (θ 1))) (-(sin (θ 0) * cos (θ 1))) (sin (θ 1)))
          (vec (-(l₁ * (cos (θ 0) * sin (θ 1) * sin (θ 2) + sin (θ 0) * cos (θ 2))))
            (l₁ * (cos (θ 0) * cos (θ 2) - sin (θ 0) * sin (θ 1) * sin (θ 2)))
            (l₀ - l₁ * (cos (θ 1) * sin (θ 2)))),
        Twist.revolute (vec (-(cos (θ 0) * cos (θ 1))) (-(sin (θ 0) * cos (θ 1))) (sin (θ 1)))
          ((inverseElbow l₀ l₁ l₂).fk θ).translation,
        Twist.revolute
          (vec (-(cos (θ 0) * sin (θ 1) * sin (θ 2 + θ 3 + θ 4) +
              sin (θ 0) * cos (θ 2 + θ 3 + θ 4)))
            (cos (θ 0) * cos (θ 2 + θ 3 + θ 4) - sin (θ 0) * sin (θ 1) * sin (θ 2 + θ 3 + θ 4))
            (-(cos (θ 1) * sin (θ 2 + θ 3 + θ 4))))
          ((inverseElbow l₀ l₁ l₂).fk θ).translation] := by
  rw [inverseElbow_fk_translation]
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, inverseElbow, List.ofFn_succ,
      Twist.adjoint_revolute, ie_applyPoint_rev ie_norm_zAxis,
      ie_applyPoint_rev Rotation.norm_yAxis, ie_applyPoint_rev ie_norm_neg_xAxis,
      ie_applyVector_rev] <;>
    simp [ie_xAxis, ie_yAxis, ie_zAxis, ie_vec_sub, ie_vec_add, ie_vec_neg, ie_act_Z', ie_act_Y',
      ie_act_negX', ie_revolute_vec, inverseElbowBase, inverseElbowWrist]
  all_goals first
    | (refine ⟨?_, ?_⟩ <;> apply ie_vec_eq <;> (try simp only [cos_add, sin_add]) <;> ring)
    | (apply ie_vec_eq <;> (try simp only [cos_add, sin_add]) <;> ring)

/-! ### Exercise 4(b): the inverse-kinematics decomposition -/

/-- The product of exponentials of the inverse elbow manipulator written out,
`e^{ξ̂₁θ₁} ⋯ e^{ξ̂₆θ₆}` (MLS eq. (3.3), p. 87; the left side of eq. (3.30), p. 105). -/
theorem inverseElbow_poe (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (inverseElbow l₀ l₁ l₂).poe θ =
      Twist.exp ((inverseElbow l₀ l₁ l₂).twist 0) (θ 0) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 2) (θ 2) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 3) (θ 3) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 4) (θ 4) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 5) (θ 5) := by
  simp only [SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(ii), first step (as eq. (3.31), p. 105):** if
`g_st(θ) = g_d`, applying both sides of eq. (3.30) to `w`, which the last two joint motions fix,
gives `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} e^{ξ̂₃θ₃} e^{ξ̂₄θ₄} w = g₁ w` with `g₁ = g_d g_st(0)⁻¹`. -/
theorem inverseElbow_wrist_eq {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (inverseElbow l₀ l₁ l₂).fk θ = g) :
    (Twist.exp ((inverseElbow l₀ l₁ l₂).twist 0) (θ 0) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 2) (θ 2) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 3) (θ 3)).applyPoint
          (inverseElbowWrist l₀ l₁ l₂) =
      (g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹).applyPoint (inverseElbowWrist l₀ l₁ l₂) := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, inverseElbow_poe]
  simp only [RigidTransform.mul_applyPoint]
  rw [show (inverseElbow l₀ l₁ l₂).twist 5 = Twist.revolute yAxis (inverseElbowWrist l₀ l₁ l₂)
      from rfl, ie_fix Rotation.norm_yAxis,
    show (inverseElbow l₀ l₁ l₂).twist 4 = Twist.revolute (-xAxis) (inverseElbowWrist l₀ l₁ l₂)
      from rfl, ie_fix ie_norm_neg_xAxis]

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(ii): the elbow angle solves Subproblem 3** (as
eq. (3.33), p. 105). If `g_st(θ) = g_d`, then `‖p_b - e^{ξ̂₄θ₄} w‖ = ‖g₁ w - p_b‖`: Subproblem 3
(eq. (3.26), p. 102) for the fourth joint twist (axis `-x` through `(0, l₁, l₀)`) with `p = w`,
`q = p_b`, `δ = ‖g₁ w - p_b‖`. The first three motions fix `p_b` and preserve distances. -/
theorem inverseElbow_subproblemThree {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (inverseElbow l₀ l₁ l₂).fk θ = g) :
    ‖inverseElbowBase l₀ -
        (Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 3)).applyPoint
          (inverseElbowWrist l₀ l₁ l₂)‖ =
      ‖(g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹).applyPoint (inverseElbowWrist l₀ l₁ l₂) -
        inverseElbowBase l₀‖ := by
  have hb : (Twist.exp ((inverseElbow l₀ l₁ l₂).twist 0) (θ 0) *
      Twist.exp ((inverseElbow l₀ l₁ l₂).twist 1) (θ 1) *
      Twist.exp ((inverseElbow l₀ l₁ l₂).twist 2) (θ 2)).applyPoint (inverseElbowBase l₀) =
      inverseElbowBase l₀ := by
    simp only [RigidTransform.mul_applyPoint]
    rw [show (inverseElbow l₀ l₁ l₂).twist 2 = Twist.revolute (-xAxis) (inverseElbowBase l₀)
        from rfl, ie_fix ie_norm_neg_xAxis,
      show (inverseElbow l₀ l₁ l₂).twist 1 = Twist.revolute yAxis (inverseElbowBase l₀)
        from rfl, ie_fix Rotation.norm_yAxis,
      show (inverseElbow l₀ l₁ l₂).twist 0 = Twist.revolute zAxis (inverseElbowBase l₀)
        from rfl, ie_fix ie_norm_zAxis]
  rw [← inverseElbow_wrist_eq h, RigidTransform.mul_applyPoint]
  nth_rewrite 2 [← hb]
  rw [RigidTransform.applyPoint_sub_applyPoint, RigidTransform.norm_applyVector, norm_sub_rev]
  rfl

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(ii), with eq. (3.29), p. 103: the elbow angle is
one of the two Subproblem 3 angles.** If `g_st(θ) = g_d` and `l₁ ≠ 0`, `l₂ ≠ 0` (so that neither
`w` nor `p_b` lies on the elbow axis; hypotheses the book does not state), then
`θ₄ = θ₀ ± cos⁻¹ κ` modulo `2π`, with `θ₀` (eq. (3.28)) and `κ` those of Subproblem 3 for the axis
`-x` through `(0, l₁, l₀)`, `p = w`, `q = p_b` and `δ = ‖g₁ w - p_b‖`. -/
theorem inverseElbow_elbow_angle {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {θ : Fin 6 → ℝ} {g : RigidTransform} (h : (inverseElbow l₀ l₁ l₂).fk θ = g) :
    ∃ k : ℤ,
      θ 3 = PadenKahan.planeAngle (-xAxis) (inverseElbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
            (inverseElbowBase l₀ - vec 0 l₁ l₀) +
          Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀)
            (inverseElbowWrist l₀ l₁ l₂) (inverseElbowBase l₀)
            ‖(g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹).applyPoint (inverseElbowWrist l₀ l₁ l₂) -
              inverseElbowBase l₀‖) + k * (2 * Real.pi) ∨
      θ 3 = PadenKahan.planeAngle (-xAxis) (inverseElbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
            (inverseElbowBase l₀ - vec 0 l₁ l₀) -
          Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀)
            (inverseElbowWrist l₀ l₁ l₂) (inverseElbowBase l₀)
            ‖(g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹).applyPoint (inverseElbowWrist l₀ l₁ l₂) -
              inverseElbowBase l₀‖) + k * (2 * Real.pi) := by
  have hsub := inverseElbow_subproblemThree h
  have hu : Vec3.perp (-xAxis) (inverseElbowWrist l₀ l₁ l₂ - vec 0 l₁ l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [Vec3.perp, inverseElbowWrist, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₂ h1
  have hv : Vec3.perp (-xAxis) (inverseElbowBase l₀ - vec 0 l₁ l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [Vec3.perp, inverseElbowBase, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₁ h1
  have hcos := (PadenKahan.subproblemThree_iff_cos ie_norm_neg_xAxis (norm_nonneg _) hu hv
    (θ 3)).mp hsub
  exact (PadenKahan.subproblemThree_iff ie_norm_neg_xAxis (norm_nonneg _) hu hv
    (hcos ▸ Real.neg_one_le_cos _) (hcos ▸ Real.cos_le_one _) (θ 3)).mp hsub

/-- The axes `+z`, `+y` (joints 1 and 2) and `+y`, `-x` (joints 6 and 5) of the inverse elbow
manipulator of MLS Figure 3.24(ii) are not parallel: the non-parallel hypothesis of Subproblem 2
(MLS p. 101) for the second and third steps of Exercise 4(b). -/
theorem inverseElbow_axes_cross_ne_zero :
    Vec3.cross zAxis yAxis ≠ 0 ∧ Vec3.cross yAxis (-xAxis) ≠ 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun v : Vec3 => v 0) h
    simp [Vec3.cross, cross_apply, yAxis, zAxis] at h1
  · intro h
    have h1 := congrArg (fun v : Vec3 => v 2) h
    simp [Vec3.cross, cross_apply, xAxis, yAxis] at h1

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(ii): the last two angles solve Subproblem 2.**
If `g_st(θ) = g_d`, then `e^{-ξ̂₆θ₆} e^{-ξ̂₅θ₅} p = q` with `p = e^{-ξ̂₄θ₄} p_b` and
`q = g₁⁻¹ p_b`, `g₁ = g_d g_st(0)⁻¹`: Subproblem 2 (eq. (3.20), p. 100) for the unit twists about
`+y` and `-x` through `w`, with the angles `-θ₆`, `-θ₅`. The inverse of eq. (3.30) applied to
`p_b`, which the first three motions fix. -/
theorem inverseElbow_subproblemTwo_wrist {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (inverseElbow l₀ l₁ l₂).fk θ = g) :
    (Twist.exp (Twist.revolute yAxis (inverseElbowWrist l₀ l₁ l₂)) (-θ 5) *
        Twist.exp (Twist.revolute (-xAxis) (inverseElbowWrist l₀ l₁ l₂)) (-θ 4)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (-θ 3)).applyPoint
          (inverseElbowBase l₀)) =
      (g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹)⁻¹.applyPoint (inverseElbowBase l₀) := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, inverseElbow_poe]
  simp only [mul_inv_rev, RigidTransform.mul_applyPoint, Twist.exp_neg]
  rw [show (inverseElbow l₀ l₁ l₂).twist 0 = Twist.revolute zAxis (inverseElbowBase l₀)
      from rfl, ie_inv_fix ie_norm_zAxis,
    show (inverseElbow l₀ l₁ l₂).twist 1 = Twist.revolute yAxis (inverseElbowBase l₀)
      from rfl, ie_inv_fix Rotation.norm_yAxis,
    show (inverseElbow l₀ l₁ l₂).twist 2 = Twist.revolute (-xAxis) (inverseElbowBase l₀)
      from rfl, ie_inv_fix ie_norm_neg_xAxis]
  rfl

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(ii): the first two angles solve Subproblem 2.**
If `g_st(θ) = g_d`, then for every point `p` of the third axis (the line through `p_b` along
`-x`), `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = g₂ p` with `g₂ = g₁ e^{-ξ̂₆θ₆} e^{-ξ̂₅θ₅} e^{-ξ̂₄θ₄}`: Subproblem 2
for the unit twists about `+z` and `+y` through `p_b`. A point off `p_b` makes it informative; the
equation holds for every point of the axis. -/
theorem inverseElbow_subproblemTwo_base {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (inverseElbow l₀ l₁ l₂).fk θ = g) {p : Vec3}
    (hp : p ∈ axisLine (inverseElbowBase l₀) (-xAxis)) :
    (Twist.exp (Twist.revolute zAxis (inverseElbowBase l₀)) (θ 0) *
        Twist.exp (Twist.revolute yAxis (inverseElbowBase l₀)) (θ 1)).applyPoint p =
      (g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹ *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 5) (-θ 5) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 4) (-θ 4) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 3) (-θ 3)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, inverseElbow_poe]
  simp only [Twist.exp_neg, mul_assoc, mul_inv_cancel, mul_one, RigidTransform.mul_applyPoint]
  rw [show (inverseElbow l₀ l₁ l₂).twist 2 = Twist.revolute (-xAxis) (inverseElbowBase l₀)
      from rfl, Twist.exp_revolute_applyPoint_of_mem_axisLine _ _ ie_norm_neg_xAxis _ hp]
  rfl

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(ii): the third angle solves Subproblem 1.** If
`g_st(θ) = g_d`, then for every point `p`,
`e^{ξ̂₃θ₃} p = e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g₁ e^{-ξ̂₆θ₆} e^{-ξ̂₅θ₅} e^{-ξ̂₄θ₄} p`: Subproblem 1
(eq. (3.17), p. 99) for the unit twist about `-x` through `p_b`; a point off that axis determines
`θ₃` modulo `2π` (`PadenKahan.subproblemOne_iff`). -/
theorem inverseElbow_subproblemOne {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (inverseElbow l₀ l₁ l₂).fk θ = g) (p : Vec3) :
    (Twist.exp (Twist.revolute (-xAxis) (inverseElbowBase l₀)) (θ 2)).applyPoint p =
      (Twist.exp ((inverseElbow l₀ l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 0) (-θ 0) *
        (g * (inverseElbow l₀ l₁ l₂).toolRef⁻¹) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 5) (-θ 5) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 4) (-θ 4) *
        Twist.exp ((inverseElbow l₀ l₁ l₂).twist 3) (-θ 3)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, inverseElbow_poe]
  simp only [Twist.exp_neg, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  rfl

end RoboLean.Examples
