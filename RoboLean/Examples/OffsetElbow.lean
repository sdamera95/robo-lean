import RoboLean.Kinematics.PadenKahanVariants
import RoboLean.Examples.RigidTransform

/-!
# The elbow manipulator with non-intersecting shoulder axes: MLS Exercise 5

MLS Chapter 3, Exercise 5, printed p. 147: solve Subproblem 2 when the two axes do not intersect
(Subproblem 2′, `PadenKahan.subproblemTwoPrime_exists_iff`), and "use this subproblem to solve the
inverse kinematics for the elbow manipulator in Example 3.5 when the first two joints do not
intersect at a point".

Reading. The elbow manipulator of Example 3.2 (p. 89) has its first axis along `+z` and its second
along `-x`, both through `(0, 0, l₀)`. Moving the second axis along its own direction or along `z`
leaves the two axes meeting; they fail to meet exactly when the second axis is moved along `y`.
The offset elbow is therefore read with the second axis through `(0, d, l₀)`, `d ≠ 0` (a recorded
symbol, the length of the common perpendicular), and the rest of the arm moved with it: the elbow
axis through `(0, d + l₁, l₀)` and the wrist centre `w = (0, d + l₁ + l₂, l₀)`, with the wrist axes
`+z`, `-x`, `+y` through `w` and `g_st(0) = (I, w)` as in Example 3.2. Twists `(-ω × q, ω)`, order
`(v, ω)`; Lean joint `k` is the book's joint `k + 1`.

Elimination. Step 1 of Example 3.5 (eq. (3.33), p. 105) measures the distance from the shoulder
point, which both shoulder motions fix; with skew shoulder axes no such point exists. The
replacement used here: the elbow and the second joint keep the wrist centre in the plane `x = 0`,
and the first joint rotates that plane about the `z` axis, so the moved wrist centre `q = g₁ w`
(`g₁ = g_d g_st(0)⁻¹`) has height `q_z = P_z` and distance `√(q_x² + q_y²) = |P_y|` from the first
axis, where `P` is the wrist centre before the first rotation. The second motion fixes the point
`(0, d, l₀)` of its axis, so the elbow angle solves Subproblem 3 with
`δ = √((σ - d)² + (q_z - l₀)²)` for one of the two values `σ = ±√(q_x² + q_y²)`. Then `(θ₁, θ₂)`
solve Subproblem 2′ and the wrist angles are found as in Example 3.5. Every step is a necessary
condition on a solution; the converse is not proved here. Statements about the coordinate model,
not about a physical arm.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)
open Real

/-! ### Private coordinate helpers -/

private theorem oe_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem oe_norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem oe_act_negX (t x y z : ℝ) :
    (Rotation.exp (-xAxis) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem oe_act_Z (t x y z : ℝ) :
    (Rotation.exp zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem oe_act_Y (t x y z : ℝ) :
    (Rotation.exp yAxis t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem oe_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem oe_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem oe_vec_neg (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem oe_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem oe_xAxis : xAxis = vec 1 0 0 := rfl
private theorem oe_yAxis : yAxis = vec 0 1 0 := rfl
private theorem oe_zAxis : zAxis = vec 0 0 1 := rfl

private theorem oe_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem oe_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem oe_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem oe_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem oe_tool_applyPoint (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform).applyPoint (vec 0 0 0) = vec a b c := by
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

private theorem oe_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint q = q :=
  Twist.exp_revolute_applyPoint_of_mem_axisLine ω q hω t (AffineSubspace.self_mem_mk' _ _)

private theorem oe_inv_fix {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t)⁻¹.applyPoint q = q := by
  rw [← Twist.exp_neg]
  exact oe_fix hω q (-t)

/-- The wrist centre `w = (0, d + l₁ + l₂, l₀)` of the elbow manipulator with offset shoulder
axes read from MLS Exercise 5, p. 147 (Example 3.2, p. 89, with the second axis moved by `d`). -/
def offsetElbowWrist (l₀ d l₁ l₂ : ℝ) : Vec3 := vec 0 (d + l₁ + l₂) l₀

/-- **MLS Exercise 5, p. 147: the elbow manipulator of Example 3.2 (p. 89) with non-intersecting
shoulder axes**, under the recorded reading: revolute joints about `+z` through `(0, 0, l₀)`, about
`-x` through `(0, d, l₀)` and `(0, d + l₁, l₀)`, and about `+z`, `-x`, `+y` through the wrist centre
`w = (0, d + l₁ + l₂, l₀)`; `g_st(0) = (I, w)`; twists `(-ω × q, ω)`, order `(v, ω)`. -/
def offsetElbow (l₀ d l₁ l₂ : ℝ) : SerialChain 6 where
  twist := ![Twist.revolute zAxis (vec 0 0 l₀), Twist.revolute (-xAxis) (vec 0 d l₀),
    Twist.revolute (-xAxis) (vec 0 (d + l₁) l₀), Twist.revolute zAxis (offsetElbowWrist l₀ d l₁ l₂),
    Twist.revolute (-xAxis) (offsetElbowWrist l₀ d l₁ l₂),
    Twist.revolute yAxis (offsetElbowWrist l₀ d l₁ l₂)]
  toolRef := ⟨1, offsetElbowWrist l₀ d l₁ l₂⟩

private theorem oe_twist_revolute (l₀ d l₁ l₂ : ℝ) :
    (offsetElbow l₀ d l₁ l₂).twist 0 = Twist.revolute zAxis (vec 0 0 l₀) ∧
      (offsetElbow l₀ d l₁ l₂).twist 1 = Twist.revolute (-xAxis) (vec 0 d l₀) ∧
      (offsetElbow l₀ d l₁ l₂).twist 2 = Twist.revolute (-xAxis) (vec 0 (d + l₁) l₀) ∧
      (offsetElbow l₀ d l₁ l₂).twist 3 = Twist.revolute zAxis (offsetElbowWrist l₀ d l₁ l₂) ∧
      (offsetElbow l₀ d l₁ l₂).twist 4 = Twist.revolute (-xAxis) (offsetElbowWrist l₀ d l₁ l₂) ∧
      (offsetElbow l₀ d l₁ l₂).twist 5 = Twist.revolute yAxis (offsetElbowWrist l₀ d l₁ l₂) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem oe_poe (l₀ d l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (offsetElbow l₀ d l₁ l₂).poe θ =
      Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 0) (θ 0) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 2) (θ 2) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 3) (θ 3) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 4) (θ 4) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 5) (θ 5) := by
  simp only [SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

private theorem oe_g₁_wrist {l₀ d l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) :
    (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) =
      ((offsetElbow l₀ d l₁ l₂).fk θ).translation := by
  subst h
  have hw : offsetElbowWrist l₀ d l₁ l₂ = (offsetElbow l₀ d l₁ l₂).toolRef.applyPoint 0 := by
    simp [offsetElbow, RigidTransform.applyPoint]
  rw [RigidTransform.mul_applyPoint, hw, RigidTransform.inv_applyPoint_applyPoint]
  simp [RigidTransform.applyPoint]

/-- **MLS Exercise 5, p. 147: the shoulder axes do not intersect.** For `d ≠ 0` the first axis
(through `(0, 0, l₀)` along `+z`) and the second (through `(0, d, l₀)` along `-x`) of
`offsetElbow` have no common point, so Subproblem 2 (p. 100) does not apply to them. -/
theorem offsetElbow_shoulder_axes_disjoint {l₀ d : ℝ} (hd : d ≠ 0) (x : Vec3)
    (h₁ : x ∈ axisLine (vec 0 0 l₀) zAxis) : x ∉ axisLine (vec 0 d l₀) (-xAxis) := by
  intro h₂
  obtain ⟨r, rfl⟩ := (mem_axisLine_iff _ _ _).mp h₁
  obtain ⟨s, hs⟩ := (mem_axisLine_iff _ _ _).mp h₂
  have h := congrArg (fun v : Vec3 => v 1) hs
  simp [vec, zAxis, xAxis] at h
  exact hd h.symm

/-- **The tool position of the offset elbow** (MLS eq. (3.3), p. 87; the arm of Exercise 5,
p. 147): with `P_y = d + l₁ c₂ + l₂ c₂₃` and `P_z = l₀ - (l₁ s₂ + l₂ s₂₃)`, the tool origin is
`(-s₁ P_y, c₁ P_y, P_z)`; the wrist joints do not move it. -/
theorem offsetElbow_fk_translation (l₀ d l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    ((offsetElbow l₀ d l₁ l₂).fk θ).translation =
      vec (-(sin (θ 0) * (d + l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2))))
        (cos (θ 0) * (d + l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)))
        (l₀ - (l₁ * sin (θ 1) + l₂ * sin (θ 1 + θ 2))) := by
  rw [oe_translation]
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
  change (Twist.exp (Twist.revolute zAxis (vec 0 0 l₀)) (θ 0)).applyPoint
    ((Twist.exp (Twist.revolute (-xAxis) (vec 0 d l₀)) (θ 1)).applyPoint
      ((Twist.exp (Twist.revolute (-xAxis) (vec 0 (d + l₁) l₀)) (θ 2)).applyPoint
        ((Twist.exp (Twist.revolute zAxis (offsetElbowWrist l₀ d l₁ l₂)) (θ 3)).applyPoint
          ((Twist.exp (Twist.revolute (-xAxis) (offsetElbowWrist l₀ d l₁ l₂)) (θ 4)).applyPoint
            ((Twist.exp (Twist.revolute yAxis (offsetElbowWrist l₀ d l₁ l₂)) (θ 5)).applyPoint
              ((⟨1, offsetElbowWrist l₀ d l₁ l₂⟩ : RigidTransform).applyPoint (vec 0 0 0))))))) = _
  rw [offsetElbowWrist, oe_tool_applyPoint, oe_fix Rotation.norm_yAxis, oe_fix oe_norm_neg_xAxis,
    oe_fix oe_norm_zAxis, oe_applyPoint_rev oe_norm_neg_xAxis, oe_applyPoint_rev oe_norm_neg_xAxis,
    oe_applyPoint_rev oe_norm_zAxis]
  simp only [oe_vec_sub, oe_vec_add, oe_act_negX, oe_act_Z]
  apply oe_vec_eq <;> simp only [cos_add, sin_add] <;> ring

/-- **MLS Exercise 5, p. 147, with eq. (3.31), p. 105:** if `g_st(θ) = g_d`, the wrist motions fix
`w`, so `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} e^{ξ̂₃θ₃} w = g₁ w` with `g₁ = g_d g_st(0)⁻¹`. -/
theorem offsetElbow_wrist_eq {l₀ d l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) :
    (Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 0) (θ 0) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 1) (θ 1) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 2) (θ 2)).applyPoint
          (offsetElbowWrist l₀ d l₁ l₂) =
      (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, oe_poe]
  obtain ⟨-, -, -, h₃, h₄, h₅⟩ := oe_twist_revolute l₀ d l₁ l₂
  simp only [RigidTransform.mul_applyPoint, h₃, h₄, h₅, oe_fix Rotation.norm_yAxis,
    oe_fix oe_norm_neg_xAxis, oe_fix oe_norm_zAxis]

/-- **MLS Exercise 5, p. 147: the elbow angle solves Subproblem 3 without a common shoulder
point.** If `g_st(θ) = g_d` and `q = g₁ w` with `g₁ = g_d g_st(0)⁻¹`, then for some `σ` with
`σ² = q_x² + q_y²` (the signed distance of the wrist centre from the first axis),
`‖(0, d, l₀) - e^{ξ̂₃θ₃} w‖ = √((σ - d)² + (q_z - l₀)²)`: Subproblem 3 (eq. (3.26), p. 102) for
the elbow twist with `p = w`, `q = (0, d, l₀)` on the second axis, and one of the two distances. -/
theorem offsetElbow_subproblemThree {l₀ d l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) :
    ∃ σ : ℝ,
      σ ^ 2 = (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) 0 ^ 2 +
          (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) 1 ^ 2 ∧
        ‖vec 0 d l₀ -
            (Twist.exp (Twist.revolute (-xAxis) (vec 0 (d + l₁) l₀)) (θ 2)).applyPoint
              (offsetElbowWrist l₀ d l₁ l₂)‖ =
          √((σ - d) ^ 2 +
            ((g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint
              (offsetElbowWrist l₀ d l₁ l₂) 2 - l₀) ^ 2) := by
  rw [oe_g₁_wrist h, offsetElbow_fk_translation]
  refine ⟨d + l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2), ?_, ?_⟩
  · simp only [vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(d + l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)) ^ 2) * sin_sq_add_cos_sq (θ 0)
  · rw [oe_applyPoint_rev oe_norm_neg_xAxis, offsetElbowWrist, oe_vec_sub, oe_act_negX, oe_vec_add,
      oe_vec_sub, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, vec, cos_add, sin_add]
    linear_combination (-(l₁ ^ 2 + 2 * l₁ * l₂ * cos (θ 2) +
      l₂ ^ 2 * (cos (θ 2) ^ 2 + sin (θ 2) ^ 2))) * sin_sq_add_cos_sq (θ 1)

/-- **MLS Exercise 5, p. 147, with eq. (3.29), p. 103: the elbow angle is one of at most four
Subproblem 3 angles.** If `g_st(θ) = g_d` and `l₁ ≠ 0`, `l₂ ≠ 0` (hypotheses the book does not
state), then for some `σ` with `σ² = q_x² + q_y²`, `q = g₁ w`, the elbow angle is `θ₀ ± cos⁻¹ κ`
modulo `2π`, with `θ₀` (eq. (3.28)) and `κ` those of Subproblem 3 for the elbow axis, `p = w`,
`q = (0, d, l₀)` and `δ = √((σ - d)² + (q_z - l₀)²)`. -/
theorem offsetElbow_elbow_angle {l₀ d l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    {θ : Fin 6 → ℝ} {g : RigidTransform} (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) :
    ∃ σ : ℝ,
      σ ^ 2 = (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) 0 ^ 2 +
          (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) 1 ^ 2 ∧
        ∃ k : ℤ,
          θ 2 = PadenKahan.planeAngle (-xAxis) (offsetElbowWrist l₀ d l₁ l₂ - vec 0 (d + l₁) l₀)
                (vec 0 d l₀ - vec 0 (d + l₁) l₀) +
              Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 (d + l₁) l₀)
                (offsetElbowWrist l₀ d l₁ l₂) (vec 0 d l₀)
                √((σ - d) ^ 2 + ((g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint
                  (offsetElbowWrist l₀ d l₁ l₂) 2 - l₀) ^ 2)) + k * (2 * Real.pi) ∨
          θ 2 = PadenKahan.planeAngle (-xAxis) (offsetElbowWrist l₀ d l₁ l₂ - vec 0 (d + l₁) l₀)
                (vec 0 d l₀ - vec 0 (d + l₁) l₀) -
              Real.arccos (PadenKahan.subproblemThreeCos (-xAxis) (vec 0 (d + l₁) l₀)
                (offsetElbowWrist l₀ d l₁ l₂) (vec 0 d l₀)
                √((σ - d) ^ 2 + ((g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint
                  (offsetElbowWrist l₀ d l₁ l₂) 2 - l₀) ^ 2)) + k * (2 * Real.pi) := by
  obtain ⟨σ, hσ, hsub⟩ := offsetElbow_subproblemThree h
  refine ⟨σ, hσ, ?_⟩
  have hu : Vec3.perp (-xAxis) (offsetElbowWrist l₀ d l₁ l₂ - vec 0 (d + l₁) l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [Vec3.perp, offsetElbowWrist, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₂ (by linarith)
  have hv : Vec3.perp (-xAxis) (vec 0 d l₀ - vec 0 (d + l₁) l₀) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 1) h0
    simp [Vec3.perp, vec, xAxis, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hl₁ (by linarith)
  have hcos := (PadenKahan.subproblemThree_iff_cos oe_norm_neg_xAxis (Real.sqrt_nonneg _) hu hv
    (θ 2)).mp hsub
  exact (PadenKahan.subproblemThree_iff oe_norm_neg_xAxis (Real.sqrt_nonneg _) hu hv
    (hcos ▸ Real.neg_one_le_cos _) (hcos ▸ Real.cos_le_one _) (θ 2)).mp hsub

/-- **MLS Exercise 5, p. 147: the shoulder angles solve Subproblem 2′.** If `g_st(θ) = g_d`, then
`e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} p = q` with `p = e^{ξ̂₃θ₃} w` and `q = g₁ w`, for the non-intersecting axes of
the first two joints; `PadenKahan.subproblemTwoPrime_exists_iff` gives its solvability through
the intermediate point `e^{ξ̂₂θ₂} p`. -/
theorem offsetElbow_subproblemTwoPrime {l₀ d l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) :
    (Twist.exp (Twist.revolute zAxis (vec 0 0 l₀)) (θ 0) *
        Twist.exp (Twist.revolute (-xAxis) (vec 0 d l₀)) (θ 1)).applyPoint
        ((Twist.exp (Twist.revolute (-xAxis) (vec 0 (d + l₁) l₀)) (θ 2)).applyPoint
          (offsetElbowWrist l₀ d l₁ l₂)) =
      (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹).applyPoint (offsetElbowWrist l₀ d l₁ l₂) := by
  rw [← RigidTransform.mul_applyPoint]
  exact offsetElbow_wrist_eq h

/-- **MLS Exercise 5, p. 147, with Example 3.5, Step 3, eqs. (3.35)–(3.36), p. 106:** if
`g_st(θ) = g_d`, then for every point `p` of the sixth axis,
`e^{ξ̂₄θ₄} e^{ξ̂₅θ₅} p = e^{-ξ̂₃θ₃} e^{-ξ̂₂θ₂} e^{-ξ̂₁θ₁} g₁ p`: Subproblem 2 for the wrist axes `+z`
and `-x` through `w`, unchanged by the shoulder offset. -/
theorem offsetElbow_subproblemTwo_wrist {l₀ d l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) {p : Vec3}
    (hp : p ∈ axisLine (offsetElbowWrist l₀ d l₁ l₂) yAxis) :
    (Twist.exp (Twist.revolute zAxis (offsetElbowWrist l₀ d l₁ l₂)) (θ 3) *
        Twist.exp (Twist.revolute (-xAxis) (offsetElbowWrist l₀ d l₁ l₂)) (θ 4)).applyPoint p =
      (Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 2) (-θ 2) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 0) (-θ 0) *
        (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, oe_poe]
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := oe_twist_revolute l₀ d l₁ l₂
  simp only [h₀, h₁, h₂, h₃, h₄, h₅, Twist.exp_neg, mul_assoc, inv_mul_cancel_left,
    RigidTransform.mul_applyPoint,
    Twist.exp_revolute_applyPoint_of_mem_axisLine yAxis _ Rotation.norm_yAxis _ hp]

/-- **MLS Exercise 5, p. 147, with Example 3.5, Step 4, eq. (3.37), p. 106:** if `g_st(θ) = g_d`,
then for every point `p`, `e^{ξ̂₆θ₆} p = e^{-ξ̂₅θ₅} ⋯ e^{-ξ̂₁θ₁} g₁ p`: Subproblem 1 for the last
wrist axis. -/
theorem offsetElbow_subproblemOne {l₀ d l₁ l₂ : ℝ} {θ : Fin 6 → ℝ} {g : RigidTransform}
    (h : (offsetElbow l₀ d l₁ l₂).fk θ = g) (p : Vec3) :
    (Twist.exp (Twist.revolute yAxis (offsetElbowWrist l₀ d l₁ l₂)) (θ 5)).applyPoint p =
      (Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 4) (-θ 4) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 3) (-θ 3) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 2) (-θ 2) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 1) (-θ 1) *
        Twist.exp ((offsetElbow l₀ d l₁ l₂).twist 0) (-θ 0) *
        (g * (offsetElbow l₀ d l₁ l₂).toolRef⁻¹)).applyPoint p := by
  rw [← (SerialChain.fk_eq_iff_poe_eq _ _ _).mp h, oe_poe]
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩ := oe_twist_revolute l₀ d l₁ l₂
  simp only [h₀, h₁, h₂, h₃, h₄, h₅, Twist.exp_neg, mul_assoc, inv_mul_cancel_left]

end RoboLean.Examples
