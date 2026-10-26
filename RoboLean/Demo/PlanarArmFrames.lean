import RoboLean.Examples.PlanarTwoLinkInverseKinematics
import RoboLean.Examples.WorkspaceControl

/-!
# The two frames of the planar two-link arm

The library carries the planar two-link arm in two frames. The kinematic arm
`Examples.planarTwoLink a b` of Chapter 3 (MLS Example 3.1, eq. (3.4), printed pp. 87–89,
specialized) points along `+y` at the zero configuration; its tool position is
`Examples.planarTwoLinkPosition a b q`, and the workspace certificate and the inverse kinematics
are stated for it. The dynamic arm `Examples.planarTwoLinkArm` of Chapter 4 (MLS Figure 4.4,
printed p. 164) points along `+x`, as the book's figures do (Figure 3.7a, p. 97), and its
end-effector map is `Examples.planarArmXY l₁ l₂ q`, the book's
`(l₁ cos θ₁ + l₂ cos(θ₁ + θ₂), l₁ sin θ₁ + l₂ sin(θ₁ + θ₂))`. Both use the same joint
coordinates, `θ₁ = q 0` and `θ₂ = q 1`, and the two frames differ by the rotation `R_z(π/2)`: the
book's point `(x, y)` is the library point `vec (-y) x 0`.

This file proves that relation for every joint vector, so that a joint vector produced by the
kinematic certificate for a target is a set point of the dynamic arm's controller with the same
target in the book's frame. The dynamic arm has no tool point of its own (its tool reference is
the identity); `planarArmXY` with `l₁ = a` and `l₂ = b` is the book's end-effector map for it.
Statements about the coordinate models only.
-/

namespace RoboLean.Demo

open RoboLean.Examples

/-- **Frame bridge.** For every joint vector `q`, the tool position of the kinematic arm
`planarTwoLinkPosition a b q` (zero configuration along `+y`, MLS eq. (3.4), p. 89, specialized)
is the end-effector point `planarArmXY a b q = (x, y)` of the book's frame (zero configuration
along `+x`, MLS p. 97 and Figure 4.4, p. 164) written as the library point `vec (-y) x 0`; the
frames differ by `R_z(π/2)`. -/
theorem planarTwoLinkPosition_eq_vec_planarArmXY (a b : ℝ) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q = vec (-(planarArmXY a b q 1)) (planarArmXY a b q 0) 0 :=
  (planarTwoLinkPosition_eq_vec_iff a b _ _ q).mpr ⟨by simp [planarArmXY], by simp [planarArmXY]⟩

/-- **Frame bridge, target form.** A joint vector `q` puts the tool of the kinematic arm at the
library point `vec (-y) x 0` exactly when it puts the end effector of the book's map
`planarArmXY a b` at the book's point `(x, y)` (MLS p. 97, `θ₁ = q 0`, `θ₂ = q 1`). So the joint
vectors of the workspace certificate and of the inverse kinematics (3.16), p. 98, are set points
of the dynamic arm for the same target. -/
theorem planarTwoLinkPosition_eq_vec_iff_planarArmXY_eq (a b x y : ℝ) (q : Fin 2 → ℝ) :
    planarTwoLinkPosition a b q = vec (-y) x 0 ↔ planarArmXY a b q = ![x, y] := by
  rw [planarTwoLinkPosition_eq_vec_iff]
  constructor
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [planarArmXY, h0, h1]
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [planarArmXY, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨h0, h1⟩

/-- **The elbow-down joint vector of MLS eq. (3.16), p. 98,** for the book's point `(x, y)` at
distance `r = √(x² + y²)`: `θ₁ = atan2(y, x) - β`, `θ₂ = π - α`, with `α`, `β` the angles of
p. 98 (`Examples.planarTwoLinkAlpha`, `Examples.planarTwoLinkBeta`) and `atan2` the library's
`Rotation.atan2`. This is the minus branch of `Examples.planarTwoLink_inverseKinematics_minus`;
with `θ₂ = π - α ∈ [0, π]` the elbow lies on the clockwise side of the segment from the base to
the target, the branch this library calls elbow-down (MLS p. 98 does not name the branches). -/
noncomputable def elbowDown (a b x y : ℝ) : Fin 2 → ℝ :=
  ![Rotation.atan2 y x - planarTwoLinkBeta a b √(x ^ 2 + y ^ 2),
    Real.pi - planarTwoLinkAlpha a b √(x ^ 2 + y ^ 2)]

/-- **The elbow-down solution is a set point of the dynamic arm.** For positive link lengths and
a book's point `(x, y)` with `0 < r` and `|a - b| ≤ r ≤ a + b`, `r = √(x² + y²)`, the elbow-down
joint vector of MLS eq. (3.16), p. 98, puts the end effector of `planarArmXY a b` at `(x, y)`.
From `Examples.planarTwoLink_inverseKinematics_minus` and the frame bridge
`planarTwoLinkPosition_eq_vec_iff_planarArmXY_eq`. The book does not state `0 < a, b` or
`r ≠ 0`. -/
theorem planarArmXY_elbowDown {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr₀ : 0 < √(x ^ 2 + y ^ 2)) (h₁ : |a - b| ≤ √(x ^ 2 + y ^ 2))
    (h₂ : √(x ^ 2 + y ^ 2) ≤ a + b) :
    planarArmXY a b (elbowDown a b x y) = ![x, y] :=
  (planarTwoLinkPosition_eq_vec_iff_planarArmXY_eq a b x y _).mp
    (planarTwoLink_inverseKinematics_minus ha hb rfl hr₀ h₁ h₂)

end RoboLean.Demo
