import RoboLean.Examples.FigureManipulatorInclined
import RoboLean.Kinematics.PadenKahan

/-!
# The manipulator of MLS Figure 3.23(ii): the body Jacobian and the inverse kinematics

MLS Chapter 3, Exercise 3(b) and 3(c), printed p. 146, for the manipulator of Figure 3.23(ii)
with an inclined third axis, `figureManipulatorInclined a l γ` (the figure reading, frames and
symbols are those of `RoboLean.Examples.FigureManipulatorInclined`: revolute joints about `+z` and
`+y` through the base origin and about `(cos γ, 0, sin γ)` through `(a, 0, 0)`, tool frame at
`(l, 0, 0)` parallel to the base frame).

Contents:

* the tool point after the third joint, `inclinedToolPoint a l γ θ₃`, by Rodrigues' formula (2.14);
* Exercise 3(c): the body Jacobian through its definition (eq. (3.55), p. 117), with the inverse
  third rotation written out by Rodrigues' formula;
* Exercise 3(b) by the Paden–Kahan subproblems at the level of tool positions (three joints do not
  reach every pose): the first two axes meet at the origin, so the third angle solves Subproblem 3
  (p. 102) with `q` the origin and `δ = ‖p‖`, and is one of the two angles of eq. (3.29) when
  `l ≠ a`, `a ≠ 0` and `sin γ ≠ 0`; the first two angles then solve Subproblem 2 (p. 100) for the
  axes `+z` and `+y`; and some `θ₁, θ₂` put the tool at `p` with third angle `θ₃` exactly when
  `‖p‖ = ‖P‖` and `p_z² + P_y² ≤ ‖P‖²` for `P = inclinedToolPoint a l γ θ₃` (the existence
  condition of Subproblem 2: the value of `γ²` on p. 102 is nonnegative).

Statements about the coordinate model, not about a physical arm.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

/-! ### Private coordinate helpers -/

private theorem fv_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem fv_norm_inclined (γ : ℝ) : ‖inclinedAxis γ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [inclinedAxis, vec, Fin.sum_univ_succ]

private theorem fv_act_Z (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, show vec 0 0 1 = zAxis from rfl, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem fv_act_Y (t x y z : ℝ) :
    (Rotation.exp (vec 0 1 0) t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, show vec 0 1 0 = yAxis from rfl, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem fv_act_inclined (γ t x y z : ℝ) :
    (Rotation.exp (inclinedAxis γ) t).act (vec x y z) =
      vec (x * cos t - sin γ * y * sin t + cos γ * (cos γ * x + sin γ * z) * (1 - cos t))
        (y * cos t + (sin γ * x - cos γ * z) * sin t)
        (z * cos t + cos γ * y * sin t + sin γ * (cos γ * x + sin γ * z) * (1 - cos t)) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_val, Vec3.exp_hat_of_norm_eq_one _ (fv_norm_inclined γ)]
  fin_cases i <;>
    simp [Vec3.hat, inclinedAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two, vec,
      Matrix.one_apply]
  all_goals first
    | ring1
    | linear_combination (-(1 - cos t) * x) * sin_sq_add_cos_sq γ
    | linear_combination ((1 - cos t) * x) * sin_sq_add_cos_sq γ
    | linear_combination (-(1 - cos t) * y) * sin_sq_add_cos_sq γ
    | linear_combination ((1 - cos t) * y) * sin_sq_add_cos_sq γ
    | linear_combination (-(1 - cos t) * z) * sin_sq_add_cos_sq γ

private theorem fv_act_inclined' (γ t x y z : ℝ) :
    (Rotation.exp (vec (cos γ) 0 (sin γ)) t).act (vec x y z) =
      vec (x * cos t - sin γ * y * sin t + cos γ * (cos γ * x + sin γ * z) * (1 - cos t))
        (y * cos t + (sin γ * x - cos γ * z) * sin t)
        (z * cos t + cos γ * y * sin t + sin γ * (cos γ * x + sin γ * z) * (1 - cos t)) :=
  fv_act_inclined γ t x y z

private theorem fv_act_Z_inv (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t)⁻¹.act (vec x y z) =
      vec (cos t * x + sin t * y) (-(sin t * x) + cos t * y) z := by
  rw [← Rotation.exp_neg, fv_act_Z, cos_neg, sin_neg]
  congr 1 <;> ring

private theorem fv_act_Y_inv (t x y z : ℝ) :
    (Rotation.exp (vec 0 1 0) t)⁻¹.act (vec x y z) =
      vec (cos t * x - sin t * z) y (sin t * x + cos t * z) := by
  rw [← Rotation.exp_neg, fv_act_Y, cos_neg, sin_neg]
  congr 1 <;> ring

private theorem fv_act_inclined_inv (γ t x y z : ℝ) :
    (Rotation.exp (vec (cos γ) 0 (sin γ)) t)⁻¹.act (vec x y z) =
      vec (x * cos t + sin γ * y * sin t + cos γ * (cos γ * x + sin γ * z) * (1 - cos t))
        (y * cos t - (sin γ * x - cos γ * z) * sin t)
        (z * cos t - cos γ * y * sin t + sin γ * (cos γ * x + sin γ * z) * (1 - cos t)) := by
  rw [← Rotation.exp_neg, fv_act_inclined', cos_neg, sin_neg]
  congr 1 <;> ring

private theorem fv_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fv_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fv_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem fv_vec_zero : (vec 0 0 0 : Vec3) = 0 := by
  ext i
  fin_cases i <;> rfl

private theorem fv_yAxis : yAxis = vec 0 1 0 := rfl
private theorem fv_zAxis : zAxis = vec 0 0 1 := rfl

private theorem fv_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem fv_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem fv_inv_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t)⁻¹.applyPoint x = (Rotation.exp ω (-t)).act (x - q) + q := by
  rw [← Twist.exp_neg]
  exact Twist.exp_revolute_applyPoint ω q hω (-t) x

private theorem fv_inv_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t)⁻¹.applyVector v = (Rotation.exp ω (-t)).act v := by
  rw [← Twist.exp_neg]
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem fv_tool_inv_applyPoint (l : ℝ) (x : Vec3) :
    (⟨1, vec l 0 0⟩ : RigidTransform)⁻¹.applyPoint x = x - vec l 0 0 := by
  conv_lhs => rw [show x = (⟨1, vec l 0 0⟩ : RigidTransform).applyPoint (x - vec l 0 0) from by
    simp [RigidTransform.applyPoint]]
  exact RigidTransform.inv_applyPoint_applyPoint _ _

private theorem fv_tool_inv_applyVector (l : ℝ) (v : Vec3) :
    (⟨1, vec l 0 0⟩ : RigidTransform)⁻¹.applyVector v = v := by
  simp [RigidTransform.applyVector]

private theorem fv_inner_z (v : Vec3) : inner ℝ zAxis v = v 2 := by
  simp [zAxis, PiLp.inner_apply, Fin.sum_univ_three]

private theorem fv_inner_y (v : Vec3) : inner ℝ yAxis v = v 1 := by
  simp [yAxis, PiLp.inner_apply, Fin.sum_univ_three]

private theorem fv_cross_zy : Vec3.cross zAxis yAxis = -xAxis := by
  ext i
  fin_cases i <;> simp [Vec3.cross, cross_apply, xAxis, yAxis, zAxis]

private theorem fv_tool_eq (a l γ : ℝ) (θ : Fin 3 → ℝ) :
    ((figureManipulatorInclined a l γ).fk θ).translation =
      (Twist.exp (Twist.revolute zAxis (vec 0 0 0)) (θ 0) *
        Twist.exp (Twist.revolute yAxis (vec 0 0 0)) (θ 1)).applyPoint
        ((Twist.exp (Twist.revolute (inclinedAxis γ) (vec a 0 0)) (θ 2)).applyPoint
          (vec l 0 0)) := by
  have ht : ((figureManipulatorInclined a l γ).fk θ).translation =
      ((figureManipulatorInclined a l γ).fk θ).applyPoint 0 := by
    simp [RigidTransform.applyPoint]
  rw [ht]
  simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
  congr 3
  simp [figureManipulatorInclined, RigidTransform.applyPoint]

/-- The tool point `(l, 0, 0)` of MLS Figure 3.23(ii), p. 146, rotated by `θ₃` about the inclined
third axis through `(a, 0, 0)`: `(a + (l - a)(c₃ + (1 - c₃) cos² γ), (l - a) s₃ sin γ,
(l - a)(1 - c₃) cos γ sin γ)` (Rodrigues' formula, eq. (2.14), p. 28). -/
def inclinedToolPoint (a l γ θ₃ : ℝ) : Vec3 :=
  vec (a + (l - a) * (cos θ₃ + (1 - cos θ₃) * cos γ ^ 2)) ((l - a) * (sin θ₃ * sin γ))
    ((l - a) * ((1 - cos θ₃) * (cos γ * sin γ)))

/-- MLS Figure 3.23(ii), p. 146: the third joint motion carries the reference tool point
`(l, 0, 0)` to `inclinedToolPoint a l γ θ₃` (eq. (2.40), p. 47, with Rodrigues' formula (2.14)). -/
theorem figureManipulatorInclined_applyPoint_tool (a l γ θ₃ : ℝ) :
    (Twist.exp (Twist.revolute (inclinedAxis γ) (vec a 0 0)) θ₃).applyPoint (vec l 0 0) =
      inclinedToolPoint a l γ θ₃ := by
  rw [fv_applyPoint_rev (fv_norm_inclined γ), fv_vec_sub, fv_act_inclined, fv_vec_add,
    inclinedToolPoint]
  apply fv_vec_eq <;> ring

/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(ii): the body Jacobian** (eq. (3.55), p. 117),
order `(v, ω)`: with `c₃ = cos θ₃`, `s₃ = sin θ₃`, all three columns are revolute twists through
the point `(a - l - a(c₃ + (1 - c₃) cos² γ), a s₃ sin γ, -a(1 - c₃) cos γ sin γ)` except the third,
through `(a - l, 0, 0)`; their axes are
`ξ₁†`: `(-s₂c₃ + cos γ sin(γ - θ₂)(1 - c₃), cos(θ₂ - γ) s₃, c₂c₃ + sin γ sin(γ - θ₂)(1 - c₃))`,
`ξ₂†`: `(s₃ sin γ, c₃, -s₃ cos γ)` and `ξ₃†`: `(cos γ, 0, sin γ)`. -/
theorem figureManipulatorInclined_bodyJacobian (a l γ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorInclined a l γ).bodyJacobian θ =
      ![Twist.revolute
          (vec (-(sin (θ 1) * cos (θ 2)) + cos γ * sin (γ - θ 1) * (1 - cos (θ 2)))
            (cos (θ 1 - γ) * sin (θ 2))
            (cos (θ 1) * cos (θ 2) + sin γ * sin (γ - θ 1) * (1 - cos (θ 2))))
          (vec (a - l - a * (cos (θ 2) + (1 - cos (θ 2)) * cos γ ^ 2)) (a * (sin (θ 2) * sin γ))
            (-(a * ((1 - cos (θ 2)) * (cos γ * sin γ))))),
        Twist.revolute (vec (sin (θ 2) * sin γ) (cos (θ 2)) (-(sin (θ 2) * cos γ)))
          (vec (a - l - a * (cos (θ 2) + (1 - cos (θ 2)) * cos γ ^ 2)) (a * (sin (θ 2) * sin γ))
            (-(a * ((1 - cos (θ 2)) * (cos γ * sin γ))))),
        Twist.revolute (inclinedAxis γ) (vec (a - l) 0 0)] := by
  funext i
  fin_cases i <;>
    simp [SerialChain.bodyJacobian, SerialChain.jointMotions, figureManipulatorInclined,
      List.ofFn_succ, Twist.adjoint_revolute, mul_inv_rev, fv_inv_applyPoint_rev fv_norm_zAxis,
      fv_inv_applyPoint_rev Rotation.norm_yAxis, fv_inv_applyPoint_rev (fv_norm_inclined _),
      fv_inv_applyVector_rev, fv_tool_inv_applyPoint, fv_tool_inv_applyVector] <;>
    simp [fv_yAxis, fv_zAxis, fv_vec_sub, fv_vec_add, fv_act_Z_inv, fv_act_Y_inv,
      fv_act_inclined_inv, fv_revolute_vec, inclinedAxis]
  all_goals first
    | (refine ⟨?_, ?_⟩ <;> apply fv_vec_eq <;> (try simp only [sin_sub, cos_sub]) <;> ring1)
    | (refine ⟨?_, ?_⟩ <;> apply fv_vec_eq <;> first
        | ring1
        | linear_combination ((a - l) * sin γ * (cos (θ 2) - 1)) * sin_sq_add_cos_sq γ
        | linear_combination (cos γ * (1 - cos (θ 2))) * sin_sq_add_cos_sq γ
        | linear_combination (sin γ * (1 - cos (θ 2))) * sin_sq_add_cos_sq γ)

/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(ii): the third angle solves Subproblem 3.** If the
tool is at `p`, then `‖0 - e^{ξ̂₃θ₃} (l, 0, 0)‖ = ‖p‖`: Subproblem 3 (eq. (3.26), p. 102) for the
third joint twist with the tool point and `q` the origin, where the first two axes meet; the first
two motions fix the origin and preserve distances. -/
theorem figureManipulatorInclined_subproblemThree {a l γ : ℝ} {θ : Fin 3 → ℝ} {p : Vec3}
    (h : ((figureManipulatorInclined a l γ).fk θ).translation = p) :
    ‖vec 0 0 0 - (Twist.exp (Twist.revolute (inclinedAxis γ) (vec a 0 0)) (θ 2)).applyPoint
        (vec l 0 0)‖ = ‖p‖ := by
  have h0 : (Twist.exp (Twist.revolute zAxis (vec 0 0 0)) (θ 0) *
      Twist.exp (Twist.revolute yAxis (vec 0 0 0)) (θ 1)).applyPoint (vec 0 0 0) = vec 0 0 0 := by
    rw [RigidTransform.mul_applyPoint, fv_applyPoint_rev Rotation.norm_yAxis, sub_self,
      fv_applyPoint_rev fv_norm_zAxis, fv_vec_zero]
    simp
  rw [← h, fv_tool_eq]
  set E := Twist.exp (Twist.revolute zAxis (vec 0 0 0)) (θ 0) *
    Twist.exp (Twist.revolute yAxis (vec 0 0 0)) (θ 1) with hE
  set X := (Twist.exp (Twist.revolute (inclinedAxis γ) (vec a 0 0)) (θ 2)).applyPoint (vec l 0 0)
  have h1 : ‖E.applyPoint X‖ = ‖E.applyPoint X - E.applyPoint (vec 0 0 0)‖ := by
    rw [h0, fv_vec_zero, sub_zero]
  rw [h1, RigidTransform.applyPoint_sub_applyPoint, RigidTransform.norm_applyVector, norm_sub_rev]

/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(ii), with eq. (3.29), p. 103: the third angle is
one of the two Subproblem 3 angles.** If the tool is at `p`, `l ≠ a`, `a ≠ 0` and `sin γ ≠ 0`
(neither the tool point nor the origin lies on the third axis; hypotheses the book does not
state), then `θ₃ = θ₀ ± cos⁻¹ κ` modulo `2π`, with `θ₀` (eq. (3.28)) and `κ` those of
Subproblem 3 for the third axis, the tool point, `q` the origin and `δ = ‖p‖`. -/
theorem figureManipulatorInclined_third_angle {a l γ : ℝ} (hla : l ≠ a) (ha : a ≠ 0)
    (hγ : sin γ ≠ 0) {θ : Fin 3 → ℝ} {p : Vec3}
    (h : ((figureManipulatorInclined a l γ).fk θ).translation = p) :
    ∃ k : ℤ,
      θ 2 = PadenKahan.planeAngle (inclinedAxis γ) (vec l 0 0 - vec a 0 0) (vec 0 0 0 - vec a 0 0) +
          Real.arccos (PadenKahan.subproblemThreeCos (inclinedAxis γ) (vec a 0 0) (vec l 0 0)
            (vec 0 0 0) ‖p‖) + k * (2 * Real.pi) ∨
      θ 2 = PadenKahan.planeAngle (inclinedAxis γ) (vec l 0 0 - vec a 0 0) (vec 0 0 0 - vec a 0 0) -
          Real.arccos (PadenKahan.subproblemThreeCos (inclinedAxis γ) (vec a 0 0) (vec l 0 0)
            (vec 0 0 0) ‖p‖) + k * (2 * Real.pi) := by
  have hsub := figureManipulatorInclined_subproblemThree h
  have key : ∀ c : ℝ, c * (1 - cos γ ^ 2) = 0 → c = 0 := by
    intro c hc
    have h2 : c * sin γ ^ 2 = 0 := by linear_combination hc + c * sin_sq_add_cos_sq γ
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h3) hγ
  have hu : Vec3.perp (inclinedAxis γ) (vec l 0 0 - vec a 0 0) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 0) h0
    simp [Vec3.perp, inclinedAxis, vec, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact hla (sub_eq_zero.mp (key (l - a) (by linear_combination h1)))
  have hv : Vec3.perp (inclinedAxis γ) (vec 0 0 0 - vec a 0 0) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 0) h0
    simp [Vec3.perp, inclinedAxis, vec, PiLp.inner_apply, Fin.sum_univ_three] at h1
    exact ha (neg_eq_zero.mp (key (-a) (by linear_combination h1)))
  have hcos := (PadenKahan.subproblemThree_iff_cos (fv_norm_inclined γ) (norm_nonneg _) hu hv
    (θ 2)).mp hsub
  exact (PadenKahan.subproblemThree_iff (fv_norm_inclined γ) (norm_nonneg _) hu hv
    (hcos ▸ Real.neg_one_le_cos _) (hcos ▸ Real.cos_le_one _) (θ 2)).mp hsub

/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(ii): the first two angles solve Subproblem 2.** If
the tool is at `p`, then `e^{ξ̂₁θ₁} e^{ξ̂₂θ₂} P = p` with `P = e^{ξ̂₃θ₃}(l, 0, 0)`: Subproblem 2
(eq. (3.20), p. 100) for the unit twists about `+z` and `+y` through the origin. -/
theorem figureManipulatorInclined_subproblemTwo {a l γ : ℝ} {θ : Fin 3 → ℝ} {p : Vec3}
    (h : ((figureManipulatorInclined a l γ).fk θ).translation = p) :
    (Twist.exp (Twist.revolute zAxis (vec 0 0 0)) (θ 0) *
        Twist.exp (Twist.revolute yAxis (vec 0 0 0)) (θ 1)).applyPoint
        ((Twist.exp (Twist.revolute (inclinedAxis γ) (vec a 0 0)) (θ 2)).applyPoint (vec l 0 0)) =
      p := by
  rw [← h, fv_tool_eq]

/-- **MLS Exercise 3(b), p. 146, for Figure 3.23(ii): which tool positions the first two joints
reach.** For every third angle `θ₃` and point `p`, some `θ₁, θ₂` put the tool at `p` exactly when
`‖p‖ = ‖P‖` and `p_z² + P_y² ≤ ‖P‖²`, where `P = inclinedToolPoint a l γ θ₃`: the existence
condition of Subproblem 2 for the axes `+z`, `+y` (`PadenKahan.subproblemTwo_exists_iff`), whose
`γ²` on p. 102 is `‖P‖² - p_z² - P_y²` here. -/
theorem figureManipulatorInclined_exists_translation_eq_iff (a l γ θ₃ : ℝ) (p : Vec3) :
    (∃ θ₁ θ₂ : ℝ, ((figureManipulatorInclined a l γ).fk ![θ₁, θ₂, θ₃]).translation = p) ↔
      ‖p‖ = ‖inclinedToolPoint a l γ θ₃‖ ∧
        p 2 ^ 2 + inclinedToolPoint a l γ θ₃ 1 ^ 2 ≤ ‖inclinedToolPoint a l γ θ₃‖ ^ 2 := by
  have hn : Vec3.cross zAxis yAxis ≠ 0 := by
    rw [fv_cross_zy, neg_ne_zero]
    intro h0
    have h1 := congrArg (fun v : Vec3 => v 0) h0
    simp [xAxis] at h1
  have hiff : (∃ θ₁ θ₂ : ℝ, ((figureManipulatorInclined a l γ).fk ![θ₁, θ₂, θ₃]).translation = p) ↔
      ∃ θ₁ θ₂ : ℝ, (Twist.exp (Twist.revolute zAxis (vec 0 0 0)) θ₁ *
        Twist.exp (Twist.revolute yAxis (vec 0 0 0)) θ₂).applyPoint
          (inclinedToolPoint a l γ θ₃) = p := by
    refine exists_congr fun θ₁ => exists_congr fun θ₂ => ?_
    rw [fv_tool_eq, ← figureManipulatorInclined_applyPoint_tool]
    rfl
  rw [hiff, PadenKahan.subproblemTwo_exists_iff fv_norm_zAxis Rotation.norm_yAxis hn, fv_vec_zero,
    sub_zero, sub_zero]
  simp only [PadenKahan.subproblemTwoGammaSq, PadenKahan.subproblemTwoAlpha,
    PadenKahan.subproblemTwoBeta, fv_inner_z, fv_inner_y, fv_cross_zy, norm_neg,
    Rotation.norm_xAxis]
  have hzy : yAxis 2 = 0 := by simp [yAxis]
  rw [hzy]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    norm_num at h2
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    norm_num
    linarith

end Examples

end RoboLean
