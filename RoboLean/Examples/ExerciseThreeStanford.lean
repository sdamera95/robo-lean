import RoboLean.Examples.StanfordArm
import RoboLean.Kinematics.PadenKahan

/-!
# The Stanford arm of MLS Figure 3.24(iii): Exercise 4(a) and 4(b)

MLS Chapter 3, Exercise 4, printed pp. 146–147, for the Stanford manipulator of Figure 3.24(iii),
read as the idealized Stanford arm of Example 3.9 (Figure 3.14, p. 119), `stanfordArm l₀ l₁`,
whose spatial Jacobian Example 3.9 prints (`stanfordArm_spatialJacobian`). Figure 3.24(iii) draws
the three wrist joints in the order `-x`, `+z`, `+y`, while Figure 3.14 has `+z`, `-x`, `+y`; both
are spherical wrists through the wrist centre, and the book notes that some parts of Exercise 4
"have already been solved in the examples", so the arm of Example 3.9 is the one treated here.
Frames and twists are those of `stanfordArm`: revolute joints about `+z` and `-x` through
`q₁ = (0, 0, l₀)`, a prismatic joint along `+y`, wrist joints about `+z`, `-x`, `+y` through the wrist
centre `q_w = (0, l₁, l₀)`, `g_st(0) = (I, q_w)`; order `(v, ω)`; Lean joint `k` is the book's joint
`k + 1`.

Contents: the forward kinematics (eq. (3.3), p. 87), its rotation and its tool position, which is
the moved wrist centre `q_w′` printed in Example 3.9; and the inverse kinematics of Exercise 4(b)
by the Paden–Kahan subproblems, each step a necessary condition on a solution, with
`g₁ = g_d g_st(0)⁻¹`: the prismatic extension solves Subproblem 5 (Exercise 7, p. 148) with
`p = q_w`, `q = q₁` and `δ = ‖g₁ q_w - q₁‖`, so `θ₃ = -l₁ ± δ`; `(θ₁, θ₂)` solve Subproblem 2;
`(θ₄, θ₅)` solve Subproblem 2 for every point of the sixth axis; `θ₆` solves Subproblem 1.
Statements about the coordinate model, not about a physical arm.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)
open Real

/-! ### Private coordinate helpers -/

private theorem sf_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem sf_norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem sf_act_negX (t x y z : ℝ) :
    (Rotation.exp (-xAxis) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem sf_act_Z (t x y z : ℝ) :
    (Rotation.exp zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem sf_act_Y (t x y z : ℝ) :
    (Rotation.exp yAxis t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem sf_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem sf_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem sf_vec_neg (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem sf_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem sf_xAxis : xAxis = vec 1 0 0 := rfl
private theorem sf_yAxis : yAxis = vec 0 1 0 := rfl
private theorem sf_zAxis : zAxis = vec 0 0 1 := rfl

private theorem sf_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem sf_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem sf_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem sf_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem sf_tool_applyPoint (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform).applyPoint (vec 0 0 0) = vec a b c := by
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

private theorem sf_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint q = q :=
  Twist.exp_revolute_applyPoint_of_mem_axisLine ω q hω t (AffineSubspace.self_mem_mk' _ _)

private theorem sf_inv_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t)⁻¹.applyPoint q = q := by
  rw [← Twist.exp_neg]
  exact sf_fix hω q (-t)

private theorem sf_vec_smul (r a b c : ℝ) : r • vec a b c = vec (r * a) (r * b) (r * c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem sf_applyPoint_pri (u : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.prismatic u) t).applyPoint x = x + t • u := by
  rw [Twist.exp_prismatic]
  simp [RigidTransform.applyPoint]

private theorem sf_twist (l₀ l₁ : ℝ) :
    (stanfordArm l₀ l₁).twist 0 = Twist.revolute zAxis (vec 0 0 l₀) ∧
      (stanfordArm l₀ l₁).twist 1 = Twist.revolute (-xAxis) (vec 0 0 l₀) ∧
      (stanfordArm l₀ l₁).twist 2 = Twist.prismatic yAxis ∧
      (stanfordArm l₀ l₁).twist 3 = Twist.revolute zAxis (vec 0 l₁ l₀) ∧
      (stanfordArm l₀ l₁).twist 4 = Twist.revolute (-xAxis) (vec 0 l₁ l₀) ∧
      (stanfordArm l₀ l₁).twist 5 = Twist.revolute yAxis (vec 0 l₁ l₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem sf_poe (l₀ l₁ : ℝ) (θ : Fin 6 → ℝ) :
    (stanfordArm l₀ l₁).poe θ =
      Twist.exp ((stanfordArm l₀ l₁).twist 0) (θ 0) * Twist.exp ((stanfordArm l₀ l₁).twist 1) (θ 1) *
        Twist.exp ((stanfordArm l₀ l₁).twist 2) (θ 2) *
        Twist.exp ((stanfordArm l₀ l₁).twist 3) (θ 3) *
        Twist.exp ((stanfordArm l₀ l₁).twist 4) (θ 4) *
        Twist.exp ((stanfordArm l₀ l₁).twist 5) (θ 5) := by
  simp only [SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- **MLS Exercise 4(a), p. 146, for Figure 3.24(iii) read as Example 3.9: the rotation of the
Stanford arm's forward kinematics** (eq. (3.3), p. 87):
`R(θ) = Rz(θ₁) R₋ₓ(θ₂) Rz(θ₄) R₋ₓ(θ₅) Ry(θ₆)`; the prismatic joint does not rotate the tool. -/
theorem stanfordArm_fk_rotation (l₀ l₁ : ℝ) (θ : Fin 6 → ℝ) :
    ((stanfordArm l₀ l₁).fk θ).rotation =
      Rotation.exp zAxis (θ 0) * Rotation.exp (-xAxis) (θ 1) * Rotation.exp zAxis (θ 3) *
        Rotation.exp (-xAxis) (θ 4) * Rotation.exp yAxis (θ 5) := by
  simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, stanfordArm,
    Twist.revolute, Twist.exp_prismatic, mul_assoc]

/-- **MLS Exercise 4(a), p. 146, for Figure 3.24(iii) read as Example 3.9: the tool position of
the Stanford arm** (eq. (3.3), p. 87): the moved wrist centre
`q_w′ = (-(l₁ + θ₃) s₁ c₂, (l₁ + θ₃) c₁ c₂, l₀ - (l₁ + θ₃) s₂)` printed in Example 3.9, p. 119. -/
theorem stanfordArm_fk_translation (l₀ l₁ : ℝ) (θ : Fin 6 → ℝ) :
    ((stanfordArm l₀ l₁).fk θ).translation =
      vec (-((l₁ + θ 2) * sin (θ 0) * cos (θ 1))) ((l₁ + θ 2) * cos (θ 0) * cos (θ 1))
        (l₀ - (l₁ + θ 2) * sin (θ 1)) := by
  rw [sf_translation]
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
  change (Twist.exp (Twist.revolute zAxis (vec 0 0 l₀)) (θ 0)).applyPoint
    ((Twist.exp (Twist.revolute (-xAxis) (vec 0 0 l₀)) (θ 1)).applyPoint
      ((Twist.exp (Twist.prismatic yAxis) (θ 2)).applyPoint
        ((Twist.exp (Twist.revolute zAxis (vec 0 l₁ l₀)) (θ 3)).applyPoint
          ((Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 4)).applyPoint
            ((Twist.exp (Twist.revolute yAxis (vec 0 l₁ l₀)) (θ 5)).applyPoint
              ((⟨1, vec 0 l₁ l₀⟩ : RigidTransform).applyPoint (vec 0 0 0))))))) = _
  rw [sf_tool_applyPoint, sf_fix Rotation.norm_yAxis, sf_fix sf_norm_neg_xAxis,
    sf_fix sf_norm_zAxis, sf_applyPoint_pri, sf_applyPoint_rev sf_norm_neg_xAxis,
    sf_applyPoint_rev sf_norm_zAxis]
  simp only [sf_yAxis, sf_vec_smul, sf_vec_add, sf_vec_sub, sf_act_negX, sf_act_Z]
  apply sf_vec_eq <;> ring

/-- **MLS Exercise 4(b), p. 147, for the Stanford arm (as eq. (3.31), p. 105):** if
`g_st(θ) = g_d`, the wrist motions fix `q_w`, so `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} e^{ξ̂₃θ₃} q_w = g₁ q_w`. -/
theorem stanfordArm_wrist_eq {l₀ l₁ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (stanfordArm l₀ l₁).fk θ = g) :
    (Twist.exp ((stanfordArm l₀ l₁).twist 0) (θ 0) * Twist.exp ((stanfordArm l₀ l₁).twist 1) (θ 1) *
        Twist.exp ((stanfordArm l₀ l₁).twist 2) (θ 2)).applyPoint (vec 0 l₁ l₀) =
      (g * (stanfordArm l₀ l₁).toolRef⁻¹).applyPoint (vec 0 l₁ l₀) := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, sf_poe]
  obtain ⟨-, -, -, h₃, h₄, h₅⟩ := sf_twist l₀ l₁
  simp only [RigidTransform.mul_applyPoint, h₃, h₄, h₅, sf_fix Rotation.norm_yAxis,
    sf_fix sf_norm_neg_xAxis, sf_fix sf_norm_zAxis]

/-- **MLS Exercise 4(b), p. 147, for the Stanford arm: the extension solves Subproblem 5**
(Exercise 7, p. 148). If `g_st(θ) = g_d`, then `‖q₁ - e^{ξ̂₃θ₃} q_w‖ = ‖g₁ q_w - q₁‖`: Subproblem 5
for the unit prismatic twist along `+y` with `p = q_w`, `q = q₁ = (0, 0, l₀)`, the point where the
first two axes meet, which their motions fix. -/
theorem stanfordArm_subproblemFive {l₀ l₁ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (stanfordArm l₀ l₁).fk θ = g) :
    ‖vec 0 0 l₀ - (Twist.exp (Twist.prismatic yAxis) (θ 2)).applyPoint (vec 0 l₁ l₀)‖ =
      ‖(g * (stanfordArm l₀ l₁).toolRef⁻¹).applyPoint (vec 0 l₁ l₀) - vec 0 0 l₀‖ := by
  obtain ⟨h₀, h₁, -⟩ := sf_twist l₀ l₁
  have hb : (Twist.exp ((stanfordArm l₀ l₁).twist 0) (θ 0) *
      Twist.exp ((stanfordArm l₀ l₁).twist 1) (θ 1)).applyPoint (vec 0 0 l₀) = vec 0 0 l₀ := by
    rw [RigidTransform.mul_applyPoint, h₁, sf_fix sf_norm_neg_xAxis, h₀, sf_fix sf_norm_zAxis]
  rw [← stanfordArm_wrist_eq h, RigidTransform.mul_applyPoint]
  nth_rewrite 2 [← hb]
  rw [RigidTransform.applyPoint_sub_applyPoint, RigidTransform.norm_applyVector, norm_sub_rev]
  rfl

/-- **MLS Exercise 4(b), p. 147, for the Stanford arm: the two extensions.** If `g_st(θ) = g_d`,
then `θ₃ = -l₁ + δ` or `θ₃ = -l₁ - δ` with `δ = ‖g₁ q_w - q₁‖`: the two roots `vᵀ(q - p) ± √D` of
Subproblem 5, here with `vᵀ(q - p) = -l₁` and `D = δ²`. -/
theorem stanfordArm_extension {l₀ l₁ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (stanfordArm l₀ l₁).fk θ = g) :
    θ 2 = -l₁ + ‖(g * (stanfordArm l₀ l₁).toolRef⁻¹).applyPoint (vec 0 l₁ l₀) - vec 0 0 l₀‖ ∨
      θ 2 = -l₁ - ‖(g * (stanfordArm l₀ l₁).toolRef⁻¹).applyPoint (vec 0 l₁ l₀) - vec 0 0 l₀‖ := by
  have hsub := stanfordArm_subproblemFive h
  have hn : ‖vec 0 0 l₀ - (Twist.exp (Twist.prismatic yAxis) (θ 2)).applyPoint (vec 0 l₁ l₀)‖ =
      |l₁ + θ 2| := by
    rw [sf_applyPoint_pri, sf_yAxis, sf_vec_smul, sf_vec_add, sf_vec_sub, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three, vec, Real.sqrt_sq_eq_abs]
    rw [← abs_neg]
    ring_nf
  rw [hn] at hsub
  rcases (abs_eq (norm_nonneg _)).mp hsub with h1 | h1
  · left
    linarith
  · right
    linarith

/-- **MLS Exercise 4(b), p. 147, for the Stanford arm: the shoulder angles solve Subproblem 2.**
If `g_st(θ) = g_d`, then `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` with `p = e^{ξ̂₃θ₃} q_w` and `q = g₁ q_w`:
Subproblem 2 (eq. (3.20), p. 100) for the axes `+z` and `-x` through `q₁`. -/
theorem stanfordArm_subproblemTwo_shoulder {l₀ l₁ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (stanfordArm l₀ l₁).fk θ = g) :
    (Twist.exp (Twist.revolute zAxis (vec 0 0 l₀)) (θ 0) *
        Twist.exp (Twist.revolute (-xAxis) (vec 0 0 l₀)) (θ 1)).applyPoint
        ((Twist.exp (Twist.prismatic yAxis) (θ 2)).applyPoint (vec 0 l₁ l₀)) =
      (g * (stanfordArm l₀ l₁).toolRef⁻¹).applyPoint (vec 0 l₁ l₀) := by
  rw [← RigidTransform.mul_applyPoint]
  exact stanfordArm_wrist_eq h

/-- **MLS Exercise 4(b), p. 147, for the Stanford arm: two wrist angles solve Subproblem 2** (as
eqs. (3.35)–(3.36), p. 106). If `g_st(θ) = g_d`, then for every point `p` of the sixth axis,
`e^{ξ̂₄θ₄} e^{ξ̂₅θ₅} p = e^{-ξ̂₃θ₃} e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g₁ p`, for the wrist axes `+z` and `-x`
through `q_w`. -/
theorem stanfordArm_subproblemTwo_wrist {l₀ l₁ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (stanfordArm l₀ l₁).fk θ = g) {p : Vec3} (hp : p ∈ axisLine (vec 0 l₁ l₀) yAxis) :
    (Twist.exp (Twist.revolute zAxis (vec 0 l₁ l₀)) (θ 3) *
        Twist.exp (Twist.revolute (-xAxis) (vec 0 l₁ l₀)) (θ 4)).applyPoint p =
      (Twist.exp ((stanfordArm l₀ l₁).twist 2) (-θ 2) *
        Twist.exp ((stanfordArm l₀ l₁).twist 1) (-θ 1) *
        Twist.exp ((stanfordArm l₀ l₁).twist 0) (-θ 0) *
        (g * (stanfordArm l₀ l₁).toolRef⁻¹)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, sf_poe]
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := sf_twist l₀ l₁
  simp only [h₀, h₁, h₂, h₃, h₄, h₅, Twist.exp_neg, mul_assoc, inv_mul_cancel_left,
    RigidTransform.mul_applyPoint,
    Twist.exp_revolute_applyPoint_of_mem_axisLine yAxis _ Rotation.norm_yAxis _ hp]

/-- **MLS Exercise 4(b), p. 147, for the Stanford arm: the last wrist angle solves Subproblem 1**
(as eq. (3.37), p. 106): if `g_st(θ) = g_d`, then for every point `p`,
`e^{ξ̂₆θ₆} p = e^{-ξ̂₅θ₅} ⋯ e^{-ξ̂₁θ₁} g₁ p`. -/
theorem stanfordArm_subproblemOne {l₀ l₁ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (stanfordArm l₀ l₁).fk θ = g) (p : Vec3) :
    (Twist.exp (Twist.revolute yAxis (vec 0 l₁ l₀)) (θ 5)).applyPoint p =
      (Twist.exp ((stanfordArm l₀ l₁).twist 4) (-θ 4) *
        Twist.exp ((stanfordArm l₀ l₁).twist 3) (-θ 3) *
        Twist.exp ((stanfordArm l₀ l₁).twist 2) (-θ 2) *
        Twist.exp ((stanfordArm l₀ l₁).twist 1) (-θ 1) *
        Twist.exp ((stanfordArm l₀ l₁).twist 0) (-θ 0) *
        (g * (stanfordArm l₀ l₁).toolRef⁻¹)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, sf_poe]
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := sf_twist l₀ l₁
  simp only [h₀, h₁, h₂, h₃, h₄, h₅, Twist.exp_neg, mul_assoc, inv_mul_cancel_left]

end RoboLean.Examples
