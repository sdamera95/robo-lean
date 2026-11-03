import RoboLean.Kinematics.Jacobian
import RoboLean.Examples.RigidTransform
import RoboLean.Geometry.ElementaryRotations
import RoboLean.Geometry.Rodrigues

/-!
# The manipulator of MLS Figure 3.23(ii): Exercise 3(a) and the spatial Jacobian of 3(c)

MLS Chapter 3, Exercise 3, printed p. 146, Figure 3.23(ii). The figure (oblique projection, `x` to
the right, `z` up, depth `y` drawn at `45°`) shows revolute joints about the vertical axis of `θ₁`
and the depth axis of `θ₂`, meeting at the marked shoulder point, and a third cylinder whose axis
is drawn at `45°` up and to the right through a second marked point on the axis of `θ₁` below the
shoulder. The end caps of the third cylinder are drawn as ellipses, unlike the circles of the
cylinders along the depth direction, so its axis is read as lying in the vertical plane of the arm,
inclined at an angle `γ` (drawn as `45°`) to the arm, and crossing the arm's line at `(a, 0, 0)`
(it then meets the axis of `θ₁` at `(0, 0, -a tan γ)` when `cos γ ≠ 0`). The gripper is on the arm's
line at `(l, 0, 0)`. The figure has no dimensions; `a`, `l` and `γ` are recorded symbols. Base frame
at the shoulder point, `z` along the axis of `θ₁`, `y` along the drawn axis of `θ₂`, `x` along the
arm, reference tool frame parallel to the base frame.

Contents: the forward kinematics as a product of exponentials (eq. (3.3), p. 87), with the third
rotation evaluated by Rodrigues' formula (2.14), and the spatial Jacobian (eq. (3.54), p. 116).
Conventions: twists `(v, ω)`, Lean joint `k` is the book's joint `k + 1`.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

open RoboLean.Rotation (xAxis yAxis zAxis)

/-! ### Private coordinate helpers -/

private theorem fi_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem fi_act_Z (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, show vec 0 0 1 = zAxis from rfl, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem fi_act_Y (t x y z : ℝ) :
    (Rotation.exp (vec 0 1 0) t).act (vec x y z) =
      vec (cos t * x + sin t * z) y (-(sin t * x) + cos t * z) := by
  ext i
  rw [Rotation.act_apply, show vec 0 1 0 = yAxis from rfl, Rotation.exp_yAxis_val]
  fin_cases i <;> simp [Rotation.yMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem fi_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fi_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem fi_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem fi_yAxis : yAxis = vec 0 1 0 := rfl
private theorem fi_zAxis : zAxis = vec 0 0 1 := rfl

private theorem fi_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem fi_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem fi_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

private theorem fi_translation (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem fi_tool_applyPoint (a b c : ℝ) :
    (⟨1, vec a b c⟩ : RigidTransform).applyPoint (vec 0 0 0) = vec a b c := by
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, vec]

/-- The unit direction `(cos γ, 0, sin γ)` of the inclined third axis of MLS Figure 3.23(ii),
p. 146 (in the vertical plane of the arm, at angle `γ` to the arm). -/
def inclinedAxis (γ : ℝ) : Vec3 := vec (cos γ) 0 (sin γ)

private theorem fi_norm_inclined (γ : ℝ) : ‖inclinedAxis γ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [inclinedAxis, vec, Fin.sum_univ_succ]

private theorem fi_act_inclined (γ t x : ℝ) :
    (Rotation.exp (inclinedAxis γ) t).act (vec x 0 0) =
      vec (x * (cos t + (1 - cos t) * cos γ ^ 2)) (x * (sin t * sin γ))
        (x * ((1 - cos t) * (cos γ * sin γ))) := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_val, Vec3.exp_hat_of_norm_eq_one _ (fi_norm_inclined γ)]
  fin_cases i <;>
    simp [Vec3.hat, inclinedAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two, vec]
  all_goals first
    | ring1
    | linear_combination (cos t * x - x) * sin_sq_add_cos_sq γ

/-- **MLS Figure 3.23(ii), p. 146: the manipulator with an inclined third axis**, revolute joints
about `+z` and `+y` through the base origin and about `inclinedAxis γ` through `(a, 0, 0)`;
reference tool pose `(I, (l, 0, 0))`. Twists `(-ω × q, ω)`, order `(v, ω)`. -/
def figureManipulatorInclined (a l γ : ℝ) : SerialChain 3 where
  twist := ![Twist.revolute zAxis (vec 0 0 0), Twist.revolute yAxis (vec 0 0 0),
    Twist.revolute (inclinedAxis γ) (vec a 0 0)]
  toolRef := ⟨1, vec l 0 0⟩

/-- **MLS Exercise 3(a), p. 146, for Figure 3.23(ii): the forward kinematics** (eq. (3.3), p. 87):
the rotation is `Rz(θ₁) Ry(θ₂) e^{ω̂₃θ₃}` and the tool position is `Rz(θ₁) Ry(θ₂)` applied to
`(a + (l - a)(c₃ + (1 - c₃) cos² γ), (l - a) s₃ sin γ, (l - a)(1 - c₃) cos γ sin γ)`, the tool point
rotated about the inclined axis by Rodrigues' formula (2.14). -/
theorem figureManipulatorInclined_fk (a l γ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorInclined a l γ).fk θ =
      ⟨Rotation.exp zAxis (θ 0) * Rotation.exp yAxis (θ 1) * Rotation.exp (inclinedAxis γ) (θ 2),
        (Rotation.exp zAxis (θ 0) * Rotation.exp yAxis (θ 1)).act
          (vec (a + (l - a) * (cos (θ 2) + (1 - cos (θ 2)) * cos γ ^ 2))
            ((l - a) * (sin (θ 2) * sin γ)) ((l - a) * ((1 - cos (θ 2)) * (cos γ * sin γ))))⟩ := by
  apply RigidTransform.ext
  · simp [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      figureManipulatorInclined, Twist.revolute, mul_assoc]
  · rw [fi_translation]
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, RigidTransform.mul_applyPoint]
    change (Twist.exp (Twist.revolute zAxis (vec 0 0 0)) (θ 0)).applyPoint
      ((Twist.exp (Twist.revolute yAxis (vec 0 0 0)) (θ 1)).applyPoint
        ((Twist.exp (Twist.revolute (inclinedAxis γ) (vec a 0 0)) (θ 2)).applyPoint
          ((⟨1, vec l 0 0⟩ : RigidTransform).applyPoint (vec 0 0 0)))) = _
    rw [fi_tool_applyPoint, fi_applyPoint_rev (fi_norm_inclined γ), fi_vec_sub, sub_self,
      fi_act_inclined, fi_vec_add, fi_applyPoint_rev Rotation.norm_yAxis, fi_vec_sub,
      fi_applyPoint_rev fi_norm_zAxis, Rotation.act_mul]
    simp only [sub_zero, add_zero]
    rw [show (Rotation.exp yAxis (θ 1)).act _ + vec 0 0 0 - vec 0 0 0 =
      (Rotation.exp yAxis (θ 1)).act _ from by rw [add_sub_cancel_right]]
    rw [show (vec 0 0 0 : Vec3) = 0 from by ext i; fin_cases i <;> rfl, add_zero]
    congr 2
    apply fi_vec_eq <;> ring

/-- **MLS Exercise 3(c), p. 146, for Figure 3.23(ii): the spatial Jacobian** (eq. (3.54), p. 116),
order `(v, ω)`: `ξ₁ = (0, 0, 0, 0, 0, 1)`, `ξ₂′ = (0, 0, 0, -s₁, c₁, 0)`, and `ξ₃′` the revolute
twist about the moved axis `Rz(θ₁) Ry(θ₂) ω₃ = (c₁ cos(θ₂ - γ), s₁ cos(θ₂ - γ), sin(γ - θ₂))`
through the moved point `(a c₁c₂, a s₁c₂, -a s₂)`. -/
theorem figureManipulatorInclined_spatialJacobian (a l γ : ℝ) (θ : Fin 3 → ℝ) :
    (figureManipulatorInclined a l γ).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩, ⟨vec 0 0 0, vec (-sin (θ 0)) (cos (θ 0)) 0⟩,
        Twist.revolute
          (vec (cos (θ 0) * cos (θ 1 - γ)) (sin (θ 0) * cos (θ 1 - γ)) (sin (γ - θ 1)))
          (vec (a * (cos (θ 0) * cos (θ 1))) (a * (sin (θ 0) * cos (θ 1)))
            (-(a * sin (θ 1))))] := by
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, figureManipulatorInclined,
      List.ofFn_succ, Twist.adjoint_revolute, fi_applyPoint_rev fi_norm_zAxis,
      fi_applyPoint_rev Rotation.norm_yAxis, fi_applyVector_rev] <;>
    simp [fi_yAxis, fi_zAxis, fi_vec_sub, fi_vec_add, fi_act_Z, fi_act_Y, fi_revolute_vec,
      inclinedAxis]
  simp only [sin_sub, cos_sub]
  constructor <;> apply fi_vec_eq <;> ring

end Examples

end RoboLean
