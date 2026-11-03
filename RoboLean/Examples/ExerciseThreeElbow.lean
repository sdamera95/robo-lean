import RoboLean.Examples.ElbowManipulator
import RoboLean.Kinematics.Jacobian

/-!
# The elbow manipulator of MLS Figure 3.24(i): the spatial Jacobian of Exercise 4(c)

MLS Chapter 3, Exercise 4, printed pp. 146–147, for the elbow manipulator of Figure 3.24(i), read
as the elbow manipulator of Example 3.2 (Figure 3.4, p. 90), `elbowManipulator l₀ l₁ l₂`, whose
forward kinematics (Example 3.2) and inverse kinematics (Example 3.5, with the count of eight
solutions) the library already has. Figure 3.24(i) draws the wrist joints in the order `-x`, `+z`,
`+y`, while Figure 3.4 has `+z`, `-x`, `+y`; both are spherical wrists through the wrist centre, and
the arm of Example 3.2 is the one treated. Exercise 4(c) asks in addition for the Jacobians; this
module gives the spatial Jacobian (eq. (3.54), p. 116). Twists in the order `(v, ω)`; Lean joint
`k` is the book's joint `k + 1`. A statement about the coordinate model.
-/

noncomputable section

namespace RoboLean.Examples

open RoboLean.Rotation (xAxis yAxis zAxis)
open Real

private theorem ej_norm_zAxis : ‖zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [zAxis, Fin.sum_univ_succ]

private theorem ej_norm_neg_xAxis : ‖-xAxis‖ = 1 := by
  rw [norm_neg, Rotation.norm_xAxis]

private theorem ej_act_Z (t x y z : ℝ) :
    (Rotation.exp (vec 0 0 1) t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, show vec 0 0 1 = zAxis from rfl, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem ej_act_negX (t x y z : ℝ) :
    (Rotation.exp (vec (-1) 0 0) t).act (vec x y z) =
      vec x (cos t * y + sin t * z) (-(sin t * y) + cos t * z) := by
  rw [show vec (-1) 0 0 = -xAxis from by ext i; fin_cases i <;> simp [vec, xAxis],
    Rotation.exp_neg_axis]
  ext i
  rw [Rotation.act_apply, Rotation.exp_xAxis_val]
  fin_cases i <;> simp [Rotation.xMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec]

private theorem ej_vec_sub (a b c d e f : ℝ) :
    vec a b c - vec d e f = vec (a - d) (b - e) (c - f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem ej_vec_add (a b c d e f : ℝ) :
    vec a b c + vec d e f = vec (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem ej_vec_neg (a b c : ℝ) : -vec a b c = vec (-a) (-b) (-c) := by
  ext i
  fin_cases i <;> simp [vec]

private theorem ej_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem ej_xAxis : xAxis = vec 1 0 0 := rfl
private theorem ej_yAxis : yAxis = vec 0 1 0 := rfl
private theorem ej_zAxis : zAxis = vec 0 0 1 := rfl

private theorem ej_revolute_vec (a b c x y z : ℝ) :
    Twist.revolute (vec a b c) (vec x y z) =
      ⟨vec (-(b * z - c * y)) (-(c * x - a * z)) (-(a * y - b * x)), vec a b c⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, vec]

private theorem ej_applyPoint_rev {ω : Vec3} (hω : ‖ω‖ = 1) (q : Vec3) (t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyPoint x = (Rotation.exp ω t).act (x - q) + q :=
  Twist.exp_revolute_applyPoint ω q hω t x

private theorem ej_applyVector_rev (ω q : Vec3) (t : ℝ) (v : Vec3) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  simp [RigidTransform.applyVector, Twist.revolute]

/-- **MLS Exercise 4(c), p. 147, for Figure 3.24(i) read as Example 3.2: the spatial Jacobian of the
elbow manipulator** (eq. (3.54), p. 116), order `(v, ω)`: `ξ₁′ = (0, e_z)`; `ξ₂′` the revolute twist
about `(-c₁, -s₁, 0)` through the shoulder `(0, 0, l₀)`; `ξ₃′` about the same direction through the
moved elbow point `(-l₁ s₁ c₂, l₁ c₁ c₂, l₀ - l₁ s₂)`; and the wrist twists through the moved wrist
centre `p(θ) = (-s₁(l₁c₂ + l₂c₂₃), c₁(l₁c₂ + l₂c₂₃), l₀ - l₁s₂ - l₂s₂₃)` printed on p. 90, about
`ω₄′ = (-s₁ s₂₃, c₁ s₂₃, c₂₃)`, `ω₅′ = (-c₁c₄ + s₁c₂₃s₄, -s₁c₄ - c₁c₂₃s₄, s₂₃s₄)` and
`ω₆′ = (-c₅(s₁c₂₃c₄ + c₁s₄) + s₁s₂₃s₅, c₅(c₁c₂₃c₄ - s₁s₄) - c₁s₂₃s₅, -s₂₃c₄c₅ - c₂₃s₅)`, the
wrist directions of the Stanford arm in Example 3.9 (eq. (3.58), p. 120) with `θ₂ + θ₃` in place of
`θ₂`. -/
theorem elbowManipulator_spatialJacobian (l₀ l₁ l₂ : ℝ) (θ : Fin 6 → ℝ) :
    (elbowManipulator l₀ l₁ l₂).spatialJacobian θ =
      ![⟨vec 0 0 0, vec 0 0 1⟩,
        Twist.revolute (vec (-cos (θ 0)) (-sin (θ 0)) 0) (vec 0 0 l₀),
        Twist.revolute (vec (-cos (θ 0)) (-sin (θ 0)) 0)
          (vec (-(l₁ * sin (θ 0) * cos (θ 1))) (l₁ * cos (θ 0) * cos (θ 1)) (l₀ - l₁ * sin (θ 1))),
        Twist.revolute
          (vec (-(sin (θ 0) * sin (θ 1 + θ 2))) (cos (θ 0) * sin (θ 1 + θ 2)) (cos (θ 1 + θ 2)))
          (vec (-(sin (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2))))
            (cos (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)))
            (l₀ - l₁ * sin (θ 1) - l₂ * sin (θ 1 + θ 2))),
        Twist.revolute
          (vec (-(cos (θ 0) * cos (θ 3)) + sin (θ 0) * cos (θ 1 + θ 2) * sin (θ 3))
            (-(sin (θ 0) * cos (θ 3)) - cos (θ 0) * cos (θ 1 + θ 2) * sin (θ 3))
            (sin (θ 1 + θ 2) * sin (θ 3)))
          (vec (-(sin (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2))))
            (cos (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)))
            (l₀ - l₁ * sin (θ 1) - l₂ * sin (θ 1 + θ 2))),
        Twist.revolute
          (vec (-(cos (θ 4) * (sin (θ 0) * cos (θ 1 + θ 2) * cos (θ 3) + cos (θ 0) * sin (θ 3))) +
              sin (θ 0) * sin (θ 1 + θ 2) * sin (θ 4))
            (cos (θ 4) * (cos (θ 0) * cos (θ 1 + θ 2) * cos (θ 3) - sin (θ 0) * sin (θ 3)) -
              cos (θ 0) * sin (θ 1 + θ 2) * sin (θ 4))
            (-(sin (θ 1 + θ 2) * cos (θ 3) * cos (θ 4)) - cos (θ 1 + θ 2) * sin (θ 4)))
          (vec (-(sin (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2))))
            (cos (θ 0) * (l₁ * cos (θ 1) + l₂ * cos (θ 1 + θ 2)))
            (l₀ - l₁ * sin (θ 1) - l₂ * sin (θ 1 + θ 2)))] := by
  funext i
  fin_cases i <;>
    simp [SerialChain.spatialJacobian, SerialChain.jointMotions, elbowManipulator, List.ofFn_succ,
      Twist.adjoint_revolute, ej_applyPoint_rev ej_norm_zAxis,
      ej_applyPoint_rev ej_norm_neg_xAxis, ej_applyVector_rev] <;>
    simp [ej_xAxis, ej_yAxis, ej_zAxis, ej_vec_sub, ej_vec_add, ej_vec_neg, ej_act_Z, ej_act_negX,
      ej_revolute_vec, elbowShoulder, elbowWrist]
  all_goals try simp only [cos_add, sin_add]
  all_goals first
    | (refine ⟨?_, ?_⟩ <;> apply ej_vec_eq <;> ring1)
    | (apply ej_vec_eq <;> ring1)

end RoboLean.Examples
