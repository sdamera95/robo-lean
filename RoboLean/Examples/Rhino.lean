import RoboLean.Kinematics.PadenKahan
import RoboLean.Kinematics.Jacobian
import RoboLean.Examples.RigidTransform

/-!
# The Rhino robot of MLS Figure 3.24(iv): Exercise 4(a)–(c)

MLS Chapter 3, Exercise 4, printed pp. 146–147, Figure 3.24(iv). The figure (drawn in the style of
the elbow manipulator of Figure 3.4, p. 90, whose directions Example 3.2, p. 89, fixes: vertical
cylinders about `+z`, cylinders along the arm about `+y`, cylinders in the depth direction about
`-x`) shows a prismatic joint at the base (a box on the ground, translating along the drawn arm
direction, read as `+y`), a revolute joint about `+z` whose axis is drawn into the first of three
parallel joints about `-x`, and a last joint about `+y` along the arm, drawn through the axis of
the third `-x` joint. The figure has no dimensions; `l₀` (height of the shoulder point `p_s` where
the `+z` axis meets the first `-x` axis), `l₁` (from `p_s` to the elbow axis) and `l₂` (from the
elbow axis to the point `w` where the last two axes meet) are recorded symbols, and the meeting
points are readings of the drawing.

Frame and data: base frame with `z` along the vertical axis and `y` along the slide and the arm at
`θ = 0`; `p_s = (0, 0, l₀)`, the elbow axis through `(0, l₁, l₀)`, `w = (0, l₁ + l₂, l₀)`,
`g_st(0) = (I, w)`. Twists in the library order `(v, ω)`: the slide `(e_y, 0)` (p. 87) and the
revolute twists `(-ω × q, ω)`; Lean joint `k` is the book's joint `k + 1`.

Contents: the chain; the forward kinematics as the product of exponentials (eq. (3.3), p. 87), its
rotation and tool position in closed form; the spatial Jacobian (eq. (3.54), p. 116); and the
inverse-kinematics steps of Exercise 4(b), each a necessary condition on a solution, with
`g₁ = g_d g_st(0)⁻¹`:

* `(θ₂, θ₃ + θ₄ + θ₅)` solve Subproblem 2 (p. 100) for the rotations about `+z` and `-x` applied to
  `e_y`, with target `R₁ e_y` (the rotation fixes the heading and the summed pitch);
* `θ₆` solves Subproblem 1 (p. 99) for the rotation about `+y` applied to `e_x`;
* the slide satisfies the linear relation `θ₁ sin θ₂ = c₂ x + s₂ y` with `(x, y, z) = g₁ w` (the
  moved arm plane contains the moved shoulder point); this step is not a Paden–Kahan subproblem,
  and it determines `θ₁` exactly when `sin θ₂ ≠ 0`;
* the elbow angle `θ₄` solves Subproblem 3 (p. 102) with `p = w`, `q = p_s` and
  `δ = ‖g₁ w - (p_s + θ₁ e_y)‖`, and is one of the two angles of eq. (3.29) modulo `2π`;
* `θ₃` solves Subproblem 1 for the rotation about the shoulder axis.

Not covered here: Exercise 4(d) and 4(e) and the converse that the steps find every solution. These
are statements about the coordinate model, not about the commercial arm the figure names.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)
open Real

/-! ### Private coordinate helpers -/

private theorem rh_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem rh_norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

/-- The shoulder point `p_s = (0, 0, l₀)` of the Rhino robot of MLS Figure 3.24(iv), p. 147
(Exercise 4): where the vertical axis meets the first `-x` axis at `θ = 0`, under the recorded
reading of the figure. -/
def rhinoShoulder (l₀ : ℝ) : Vec3 := vec 0 0 l₀

/-- The point `w = (0, l₁ + l₂, l₀)` where the last two joint axes of the Rhino robot of MLS
Figure 3.24(iv), p. 147, meet; the tool origin at `θ = 0` (recorded reading). -/
def rhinoWrist (l₀ l₁ l₂ : ℝ) : Vec3 := vec 0 (l₁ + l₂) l₀

/-- **MLS Figure 3.24(iv), p. 147 (Exercise 4): the Rhino robot**, under the recorded reading: a
prismatic joint along `+y`, revolute joints about `+z` and `-x` through `p_s = (0, 0, l₀)`, about
`-x` through `(0, l₁, l₀)`, and about `-x` and `+y` through `w = (0, l₁ + l₂, l₀)`; reference tool
pose `g_st(0) = (I, w)` (p. 87); order `(v, ω)`; unrestricted joint space. -/
def rhino (l₀ l₁ l₂ : ℝ) : SerialChain 6 where
  twist := ![Twist.prismatic yAxis, Twist.revolute zAxis (rhinoShoulder l₀),
    Twist.revolute (-xAxis) (rhinoShoulder l₀), Twist.revolute (-xAxis) (vec 0 l₁ l₀),
    Twist.revolute (-xAxis) (rhinoWrist l₀ l₁ l₂), Twist.revolute yAxis (rhinoWrist l₀ l₁ l₂)]
  toolRef := ⟨1, rhinoWrist l₀ l₁ l₂⟩

private theorem rh_act_negX (t x y z : ℝ) :
    (Rotation.exp (-xAxis) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem rh_act_Z (t x y z : ℝ) :
    (Rotation.exp zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem rh_act_Y (t x y z : ℝ) :
    (Rotation.exp yAxis t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem rh_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem rh_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem rh_vec_neg (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem rh_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem rh_xAxis : xAxis = vec 1 0 0 := rfl
private theorem rh_yAxis : yAxis = vec 0 1 0 := rfl
private theorem rh_zAxis : zAxis = vec 0 0 1 := rfl

private theorem rh_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem rh_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem rh_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem rh_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem rh_tool_applyPoint (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform).applyPoint (vec 0 0 0) = vec a b c := by
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

private theorem rh_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint q = q :=
  Twist.exp_revolute_applyPoint_of_mem_axisLine ω q hω t (AffineSubspace.self_mem_mk' _ _)

private theorem rh_inv_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t)⁻¹.applyPoint q = q := by
  rw [← Twist.exp_neg]
  exact rh_fix hω q (-t)

private theorem rh_vec_smul (r a b c : ℝ) : r • vec a b c = vec (r * a) (r * b) (r * c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem rh_applyPoint_pri (u : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyPoint x = x + t • u := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyPoint]

private theorem rh_applyVector_pri (u : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyVector v = v := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyVector]

private theorem rh_act_Z' (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z :=
  rh_act_Z t x y z

private theorem rh_act_negX' (t x y z : ℝ) :
    (Rotation.exp (vec (-1) 0 0) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [show vec (-1) 0 0 = -xAxis from by ext i; fin_cases i <;> simp [vec, xAxis]]
  exact rh_act_negX t x y z

private theorem rh_poe (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (rhino l₀ l₁ l₂).poe θ =
      Twist.exp ((rhino l₀ l₁ l₂).twist 0) (θ 0) * Twist.exp ((rhino l₀ l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((rhino l₀ l₁ l₂).twist 2) (θ 2) * Twist.exp ((rhino l₀ l₁ l₂).twist 3) (θ 3) *
        Twist.exp ((rhino l₀ l₁ l₂).twist 4) (θ 4) * Twist.exp ((rhino l₀ l₁ l₂).twist 5) (θ 5) := by
  simp only [SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

private theorem rh_g₁_vector {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) (v : Vec3) :
    (g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyVector v = ((rhino l₀ l₁ l₂).fk θ).rotation.act v := by
  subst h
  simp [RigidTransform.applyVector, rhino]

private theorem rh_g₁_wrist {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) :
    (g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) =
      ((rhino l₀ l₁ l₂).fk θ).translation := by
  subst h
  have hw : rhinoWrist l₀ l₁ l₂ = (rhino l₀ l₁ l₂).toolRef.applyPoint 0 := by
    simp [rhino, RigidTransform.applyPoint]
  rw [RigidTransform.mul_applyPoint, hw, RigidTransform.inv_applyPoint_applyPoint]
  simp [RigidTransform.applyPoint]

/-- **MLS Exercise 4(a), p. 146, for Figure 3.24(iv): the rotation of the forward kinematics**
(eq. (3.3), p. 87): `R(θ) = Rz(θ₂) R₋ₓ(θ₃ + θ₄ + θ₅) Ry(θ₆)`; the slide does not rotate the tool
and the three parallel joints add their angles. -/
theorem rhino_fk_rotation (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((rhino l₀ l₁ l₂).fk θ).rotation =
      Rotation.exp zAxis (θ 1) * Rotation.exp (-xAxis) (θ 2 + θ 3 + θ 4) *
        Rotation.exp yAxis (θ 5) := by
  rw [Rotation.exp_add, Rotation.exp_add]
  simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, rhino,
    Twist.revolute, Twist.exp_prismatic, mul_assoc]

/-- **MLS Exercise 4(a), p. 146, for Figure 3.24(iv): the tool position of the forward
kinematics** (eq. (3.3), p. 87): with `Y = l₁ c₃ + l₂ c₃₄` and `Z = -(l₁ s₃ + l₂ s₃₄)`, the tool
origin is `(-s₂ Y, θ₁ + c₂ Y, l₀ + Z)`; the last two joints do not move it. -/
theorem rhino_fk_translation (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((rhino l₀ l₁ l₂).fk θ).translation =
      vec (-(sin (θ 1) * (l₁ * cos (θ 2) + l₂ * cos (θ 2 + θ 3))))
        (θ 0 + cos (θ 1) * (l₁ * cos (θ 2) + l₂ * cos (θ 2 + θ 3)))
        (l₀ - (l₁ * sin (θ 2) + l₂ * sin (θ 2 + θ 3))) := by
  rw [rh_translation]
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
  change (Twist.exp (Twist.prismatic yAxis) (θ 0)).applyPoint
    ((Twist.exp (Twist.revolute zAxis (rhinoShoulder l₀)) (θ 1)).applyPoint
      ((Twist.exp (Twist.revolute (-xAxis) (rhinoShoulder l₀)) (θ 2)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 3)).applyPoint
          ((Twist.exp (Twist.revolute (-xAxis) (rhinoWrist l₀ l₁ l₂)) (θ 4)).applyPoint
            ((Twist.exp (Twist.revolute yAxis (rhinoWrist l₀ l₁ l₂)) (θ 5)).applyPoint
              ((⟨1, rhinoWrist l₀ l₁ l₂⟩ : RigidTransform).applyPoint (vec 0 0 0))))))) = _
  rw [rhinoWrist, rh_tool_applyPoint, rh_fix Rotation.norm_yAxis, rh_fix rh_norm_neg_xAxis,
    rh_applyPoint_rev rh_norm_neg_xAxis, rh_applyPoint_rev rh_norm_neg_xAxis,
    rh_applyPoint_rev rh_norm_zAxis, rh_applyPoint_pri, rhinoShoulder]
  simp only [rh_vec_sub, rh_vec_add, rh_act_negX, rh_act_Z, rh_yAxis, rh_vec_smul]
  apply rh_vec_eq <;> simp only [cos_add, sin_add] <;> ring

/-- **MLS Exercise 4(c), p. 147, for Figure 3.24(iv): the spatial Jacobian** (eq. (3.54),
p. 116), order `(v, ω)`: `ξ₁′ = (e_y, 0)`; `ξ₂′` the revolute twist about `+z` through the moved
shoulder point `(0, θ₁, l₀)`; `ξ₃′`, `ξ₄′`, `ξ₅′` revolute twists about `(-c₂, -s₂, 0)` through
`(0, θ₁, l₀)`, through the moved elbow point `(-l₁ s₂ c₃, θ₁ + l₁ c₂ c₃, l₀ - l₁ s₃)` and through
the moved `w`, the tool position of `rhino_fk_translation`; and `ξ₆′` the revolute twist about
`(-s₂ c₃₄₅, c₂ c₃₄₅, -s₃₄₅)` through the moved `w`. -/
theorem rhino_spatialJacobian (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (rhino l₀ l₁ l₂).spatialJacobian θ =
      ![⟨vec 0 1 0, vec 0 0 0⟩,
        Twist.revolute (vec 0 0 1) (vec 0 (θ 0) l₀),
        Twist.revolute (vec (-cos (θ 1)) (-sin (θ 1)) 0) (vec 0 (θ 0) l₀),
        Twist.revolute (vec (-cos (θ 1)) (-sin (θ 1)) 0)
          (vec (-(l₁ * (sin (θ 1) * cos (θ 2)))) (θ 0 + l₁ * (cos (θ 1) * cos (θ 2)))
            (l₀ - l₁ * sin (θ 2))),
        Twist.revolute (vec (-cos (θ 1)) (-sin (θ 1)) 0) ((rhino l₀ l₁ l₂).fk θ).translation,
        Twist.revolute
          (vec (-(sin (θ 1) * cos (θ 2 + θ 3 + θ 4))) (cos (θ 1) * cos (θ 2 + θ 3 + θ 4))
            (-sin (θ 2 + θ 3 + θ 4)))
          ((rhino l₀ l₁ l₂).fk θ).translation] := by
  rw [rhino_fk_translation]
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, rhino, List.ofFn_succ,
      Twist.adjoint_revolute, Twist.adjoint_prismatic, rh_applyPoint_rev rh_norm_zAxis,
      rh_applyPoint_rev rh_norm_neg_xAxis, rh_applyVector_rev, rh_applyPoint_pri, rh_applyVector_pri] <;>
    simp [rh_xAxis, rh_yAxis, rh_zAxis, rh_vec_sub, rh_vec_add, rh_vec_neg, rh_vec_smul, rh_act_Z',
      rh_act_negX', rh_revolute_vec, rhinoShoulder, rhinoWrist]
  all_goals first
    | (refine ⟨?_, ?_⟩ <;> apply rh_vec_eq <;> (try simp only [cos_add, sin_add]) <;> ring)
    | (apply rh_vec_eq <;> (try simp only [cos_add, sin_add]) <;> ring)
    | (simp only [Twist.prismatic]
       apply Twist.ext <;> ext i <;> fin_cases i <;> simp [vec])

/-! ### Exercise 4(b): the inverse-kinematics steps -/

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(iv): the heading and the summed pitch solve
Subproblem 2.** If `g_st(θ) = g_d`, then `e^{ξ̂_zθ₂} e^{ξ̂₋ₓ(θ₃ + θ₄ + θ₅)} e_y = R₁ e_y` with
`R₁` the rotation of `g₁ = g_d g_st(0)⁻¹`: Subproblem 2 (eq. (3.20), p. 100) for the unit twists
about `+z` and `-x` through the origin, whose axes meet there and are not parallel. The rotation
about `+y` fixes `e_y`. -/
theorem rhino_subproblemTwo_orientation {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) :
    (Twist.exp (Twist.revolute zAxis 0) (θ 1) *
        Twist.exp (Twist.revolute (-xAxis) 0) (θ 2 + θ 3 + θ 4)).applyPoint yAxis =
      (g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyVector yAxis := by
  rw [rh_g₁_vector h, rhino_fk_rotation]
  simp only [RigidTransform.mul_applyPoint, rh_applyPoint_rev rh_norm_zAxis,
    rh_applyPoint_rev rh_norm_neg_xAxis, sub_zero, add_zero, Rotation.act_mul,
    Rotation.exp_act_unit_axis yAxis Rotation.norm_yAxis]

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(iv): the roll angle solves Subproblem 1.** If
`g_st(θ) = g_d`, then `e^{ξ̂_yθ₆} e_x = e^{-ξ̂₋ₓ(θ₃ + θ₄ + θ₅)} e^{-ξ̂_zθ₂} R₁ e_x`: Subproblem 1
(eq. (3.17), p. 99) for the unit twist about `+y` through the origin; `e_x` is off that axis, so
the equation determines `θ₆` modulo `2π` (`PadenKahan.subproblemOne_iff`). -/
theorem rhino_subproblemOne_roll {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) :
    (Twist.exp (Twist.revolute yAxis 0) (θ 5)).applyPoint xAxis =
      (Twist.exp (Twist.revolute (-xAxis) 0) (-(θ 2 + θ 3 + θ 4)) *
        Twist.exp (Twist.revolute zAxis 0) (-θ 1)).applyPoint
          ((g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyVector xAxis) := by
  rw [rh_g₁_vector h, rhino_fk_rotation]
  simp only [RigidTransform.mul_applyPoint, rh_applyPoint_rev rh_norm_zAxis,
    rh_applyPoint_rev rh_norm_neg_xAxis, rh_applyPoint_rev Rotation.norm_yAxis, sub_zero, add_zero,
    Rotation.exp_neg, ← Rotation.act_mul, mul_assoc, inv_mul_cancel_left]

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(iv): the slide.** If `g_st(θ) = g_d` and
`(x, y, z) = g₁ w` with `g₁ = g_d g_st(0)⁻¹`, then `θ₁ sin θ₂ = x cos θ₂ + y sin θ₂`: the moved
arm plane, through the moved shoulder `(0, θ₁, l₀)` and normal to `(c₂, s₂, 0)`, contains `g₁ w`.
A linear equation, not a Paden–Kahan subproblem; it determines `θ₁` exactly when `sin θ₂ ≠ 0`. -/
theorem rhino_slide {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) :
    θ 0 * sin (θ 1) =
      (g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) 0 * cos (θ 1) +
        (g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) 1 * sin (θ 1) := by
  rw [rh_g₁_wrist h, rhino_fk_translation]
  simp only [vec]
  simp
  ring

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(iv): the elbow angle solves Subproblem 3.** If
`g_st(θ) = g_d`, then `‖p_s - e^{ξ̂₄θ₄} w‖ = ‖g₁ w - (p_s + θ₁ e_y)‖`: Subproblem 3 (eq. (3.26),
p. 102) for the fourth joint twist (axis `-x` through `(0, l₁, l₀)`) with `p = w`, `q = p_s`; the
slide moves `p_s` to `(0, θ₁, l₀)` and the next two motions fix it. -/
theorem rhino_subproblemThree {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) :
    ‖rhinoShoulder l₀ -
        (Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 3)).applyPoint
          (rhinoWrist l₀ l₁ l₂)‖ =
      ‖(g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) - vec 0 (θ 0) l₀‖ := by
  have hw : (g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) =
      (Twist.exp ((rhino l₀ l₁ l₂).twist 0) (θ 0) * Twist.exp ((rhino l₀ l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((rhino l₀ l₁ l₂).twist 2) (θ 2)).applyPoint
          ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 3)).applyPoint
            (rhinoWrist l₀ l₁ l₂)) := by
    rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, rh_poe]
    simp only [RigidTransform.mul_applyPoint]
    rw [show (rhino l₀ l₁ l₂).twist 5 = Twist.revolute yAxis (rhinoWrist l₀ l₁ l₂) from rfl,
      rh_fix Rotation.norm_yAxis,
      show (rhino l₀ l₁ l₂).twist 4 = Twist.revolute (-xAxis) (rhinoWrist l₀ l₁ l₂) from rfl,
      rh_fix rh_norm_neg_xAxis]
    rfl
  have hb : (Twist.exp ((rhino l₀ l₁ l₂).twist 0) (θ 0) *
      Twist.exp ((rhino l₀ l₁ l₂).twist 1) (θ 1) *
      Twist.exp ((rhino l₀ l₁ l₂).twist 2) (θ 2)).applyPoint (rhinoShoulder l₀) =
      vec 0 (θ 0) l₀ := by
    simp only [RigidTransform.mul_applyPoint]
    rw [show (rhino l₀ l₁ l₂).twist 2 = Twist.revolute (-xAxis) (rhinoShoulder l₀) from rfl,
      rh_fix rh_norm_neg_xAxis,
      show (rhino l₀ l₁ l₂).twist 1 = Twist.revolute zAxis (rhinoShoulder l₀) from rfl,
      rh_fix rh_norm_zAxis,
      show (rhino l₀ l₁ l₂).twist 0 = Twist.prismatic yAxis from rfl, rh_applyPoint_pri,
      rhinoShoulder, rh_yAxis, rh_vec_smul, rh_vec_add]
    apply rh_vec_eq <;> ring
  rw [hw, ← hb, RigidTransform.applyPoint_sub_applyPoint, RigidTransform.norm_applyVector,
    norm_sub_rev]

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(iv), with eq. (3.29), p. 103: the elbow angle is
one of the two Subproblem 3 angles.** If `g_st(θ) = g_d` and `l₁ ≠ 0`, `l₂ ≠ 0` (hypotheses the
book does not state), then `θ₄ = θ₀ ± cos⁻¹ κ` modulo `2π`, with `θ₀` (eq. (3.28)) and `κ` those
of Subproblem 3 for the axis `-x` through `(0, l₁, l₀)`, `p = w`, `q = p_s` and
`δ = ‖g₁ w - (0, θ₁, l₀)‖`. -/
theorem rhino_elbow_angle {l₀ l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {θ : Fin 6 → ℝ} {g : RigidTransform} (h : (rhino l₀ l₁ l₂).fk θ = g) :
    ∃ k : ℤ,
      θ 3 = PadenKahan.planeAngle (-xAxis) (rhinoWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
            (rhinoShoulder l₀ - vec 0 l₁ l₀) +
          Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀)
            (rhinoWrist l₀ l₁ l₂) (rhinoShoulder l₀)
            ‖(g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) -
              vec 0 (θ 0) l₀‖) + k * (2 * Real.pi) ∨
      θ 3 = PadenKahan.planeAngle (-xAxis) (rhinoWrist l₀ l₁ l₂ - vec 0 l₁ l₀)
            (rhinoShoulder l₀ - vec 0 l₁ l₀) -
          Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 l₁ l₀)
            (rhinoWrist l₀ l₁ l₂) (rhinoShoulder l₀)
            ‖(g * (rhino l₀ l₁ l₂).toolRef⁻¹).applyPoint (rhinoWrist l₀ l₁ l₂) -
              vec 0 (θ 0) l₀‖) + k * (2 * Real.pi) := by
  have hsub := rhino_subproblemThree h
  have hu : Vec3.perp (-xAxis) (rhinoWrist l₀ l₁ l₂ - vec 0 l₁ l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [Vec3.perp, rhinoWrist, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₂ h1
  have hv : Vec3.perp (-xAxis) (rhinoShoulder l₀ - vec 0 l₁ l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [Vec3.perp, rhinoShoulder, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₁ h1
  have hcos := (PadenKahan.subproblemThree_iff_cos rh_norm_neg_xAxis (norm_nonneg _) hu hv
    (θ 3)).mp hsub
  exact (PadenKahan.subproblemThree_iff rh_norm_neg_xAxis (norm_nonneg _) hu hv
    (hcos ▸ Real.neg_one_le_cos _) (hcos ▸ Real.cos_le_one _) (θ 3)).mp hsub

/-- **MLS Exercise 4(b), p. 147, for Figure 3.24(iv): the shoulder angle solves Subproblem 1.** If
`g_st(θ) = g_d`, then `e^{ξ̂₃θ₃} p = q` with `p = e^{ξ̂₄θ₄} w` and
`q = e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g₁ w`: Subproblem 1 (eq. (3.17), p. 99) for the unit twist about `-x`
through `p_s`. -/
theorem rhino_subproblemOne_shoulder {l₀ l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (rhino l₀ l₁ l₂).fk θ = g) :
    (Twist.exp (Twist.revolute (-xAxis) (rhinoShoulder l₀)) (θ 2)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 3)).applyPoint
          (rhinoWrist l₀ l₁ l₂)) =
      (Twist.exp ((rhino l₀ l₁ l₂).twist 1) (-θ 1) * Twist.exp ((rhino l₀ l₁ l₂).twist 0) (-θ 0) *
        (g * (rhino l₀ l₁ l₂).toolRef⁻¹)).applyPoint (rhinoWrist l₀ l₁ l₂) := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, rh_poe]
  simp only [Twist.exp_neg, mul_assoc, inv_mul_cancel_left, RigidTransform.mul_applyPoint]
  rw [show (rhino l₀ l₁ l₂).twist 5 = Twist.revolute yAxis (rhinoWrist l₀ l₁ l₂) from rfl,
    rh_fix Rotation.norm_yAxis,
    show (rhino l₀ l₁ l₂).twist 4 = Twist.revolute (-xAxis) (rhinoWrist l₀ l₁ l₂) from rfl,
    rh_fix rh_norm_neg_xAxis]
  rfl

end RoboLean.Examples
