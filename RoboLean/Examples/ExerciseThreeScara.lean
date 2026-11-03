import RoboLean.Examples.ScaraKinematics

/-!
# MLS Chapter 3, Exercise 7 for the SCARA: the prismatic extension

MLS Chapter 3, Exercise 7, printed p. 148: Subproblem 5 (translation to a given distance) asks for
`θ` with `‖q - e^{ξ̂θ} p‖ = δ` for a unit prismatic twist `ξ` (solved in
`RoboLean.Kinematics.PadenKahanVariants`), and the exercise says to "use this subproblem to solve
for the extension of the prismatic joint in the SCARA robot in Example 3.6" (pp. 106–107, the SCARA
of Example 3.1, `scaraKinematicChain l₀ l₁ l₂`).

Reading. In the book's inverse kinematics the distance `δ` of a subproblem is computed from the
target through a point that the remaining joints fix (the shoulder point of Example 3.5, eq. (3.32),
p. 105). For the SCARA the remaining joints are the three revolute joints, whose axes are parallel
vertical lines through `(0, 0)`, `(0, l₁)` and `(0, l₁ + l₂)`; for `l₁ ≠ 0` no point is fixed by
every motion of the first two of them (`scaraKinematicChain_exists_applyPoint_ne`), so Subproblem 5
cannot be fed in that way. The route that works is the one of Example 3.6: rotations about vertical
axes keep heights, so `θ₄ = z - l₀` for every target with height `z`
(`scaraKinematicChain_prismatic_eq`). Once the height is known, Subproblem 5 does apply to the point
`q = (δ, l₁ + l₂, z)` at horizontal distance `δ` from the prismatic line through the reference tool
point, and its two roots coincide in `θ₄ = z - l₀` (`scaraKinematicChain_subproblemFive_iff`): it
restates the height and adds nothing. Statements about the coordinate model.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

private theorem es_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem es_vec_self (q : Vec3) : q = vec (q 0) (q 1) (q 2) := by
  ext i
  fin_cases i <;> rfl

private theorem es_act_Z (t x y z : ℝ) :
    (Rotation.exp Rotation.zAxis t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  rw [Rotation.act_apply, Rotation.exp_zAxis_val]
  fin_cases i <;>
    simp [Rotation.zMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, vec, sub_eq_add_neg]

private theorem es_exp_z_applyPoint (qx qy qz t x y z : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec qx qy qz)) t).applyPoint (vec x y z) =
      vec (cos t * (x - qx) - sin t * (y - qy) + qx)
        (sin t * (x - qx) + cos t * (y - qy) + qy) z := by
  rw [Twist.exp_revolute_applyPoint _ _ es_norm_zAxis]
  have h : vec x y z - vec qx qy qz = vec (x - qx) (y - qy) (z - qz) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [h, es_act_Z]
  ext i
  fin_cases i <;> simp [vec]

private theorem es_exp_prismatic_applyPoint (t x y z : ℝ) :
    (Twist.exp (Twist.prismatic Rotation.zAxis) t).applyPoint (vec x y z) = vec x y (z + t) := by
  rw [Twist.exp_prismatic]
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, Rotation.zAxis, vec]

/-- **MLS Exercise 7, p. 148: the SCARA's revolute joints fix no common point.** For `l₁ ≠ 0` and
every point `q`, some motion of the first two joints of the SCARA of Example 3.1 (pp. 87–88;
revolute joints about the vertical axes through `(0, 0, 0)` and `(0, l₁, 0)`) moves `q`. So no
distance from such a point to the tool is fixed by the target, as Subproblem 5 would need. -/
theorem scaraKinematicChain_exists_applyPoint_ne (l₀ : ℝ) {l₁ : ℝ} (l₂ : ℝ) (hl₁ : l₁ ≠ 0)
    (q : Vec3) :
    ∃ t₁ t₂ : ℝ, (Twist.exp ((scaraKinematicChain l₀ l₁ l₂).twist 0) t₁ *
        Twist.exp ((scaraKinematicChain l₀ l₁ l₂).twist 1) t₂).applyPoint q ≠ q := by
  by_contra H
  simp only [not_exists, ne_eq, not_not] at H
  have h1 := H π 0
  have h2 := H 0 π
  rw [es_vec_self q] at h1 h2
  simp only [Twist.exp_zero, mul_one, one_mul] at h1 h2
  change (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) π).applyPoint _ = _ at h1
  change (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 l₁ 0)) π).applyPoint _ = _ at h2
  rw [es_exp_z_applyPoint, cos_pi, sin_pi] at h1 h2
  have a1 := congrArg (fun v : Vec3 => v 1) h1
  have a2 := congrArg (fun v : Vec3 => v 1) h2
  simp [vec] at a1 a2
  exact hl₁ (by linarith)

/-- **MLS Exercise 7, p. 148, by the route of Example 3.6 (pp. 106–107): the prismatic extension
is the height.** For every pose `g`, if `g_st(θ) = g` then `θ₄ = z - l₀` with `z` the height of the
position of `g`; the revolute joints rotate about vertical axes and keep heights. -/
theorem scaraKinematicChain_prismatic_eq {l₀ l₁ l₂ : ℝ} {θ : Fin 4 → ℝ} {g : RigidTransform}
    (h : (scaraKinematicChain l₀ l₁ l₂).fk θ = g) : θ 3 = g.translation 2 - l₀ := by
  rw [← h, scaraKinematicChain_fk]
  simp [vec]

/-- **MLS Exercise 7, p. 148: Subproblem 5 once the height is known.** For `δ > 0` (the book's
hypothesis) and every height `z`, the prismatic motion of the SCARA's fourth joint carries the
reference tool point `p = (0, l₁ + l₂, l₀)` to distance `δ` from `q = (δ, l₁ + l₂, z)` exactly when
`t = z - l₀`: the discriminant of Subproblem 5 vanishes and its two roots coincide. -/
theorem scaraKinematicChain_subproblemFive_iff (l₀ l₁ l₂ z : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ‖vec δ (l₁ + l₂) z -
        (Twist.exp ((scaraKinematicChain l₀ l₁ l₂).twist 3) t).applyPoint
          (vec 0 (l₁ + l₂) l₀)‖ = δ ↔ t = z - l₀ := by
  change ‖vec δ (l₁ + l₂) z - (Twist.exp (Twist.prismatic Rotation.zAxis) t).applyPoint
    (vec 0 (l₁ + l₂) l₀)‖ = δ ↔ _
  have hv : vec δ (l₁ + l₂) z - vec 0 (l₁ + l₂) (l₀ + t) = vec δ 0 (z - (l₀ + t)) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [es_exp_prismatic_applyPoint, hv, EuclideanSpace.norm_eq,
    Real.sqrt_eq_iff_eq_sq (by positivity) hδ.le]
  simp [Fin.sum_univ_three, vec]
  constructor <;> intro h <;> linarith

end Examples

end RoboLean
