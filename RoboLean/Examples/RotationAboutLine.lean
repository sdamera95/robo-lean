import RoboLean.Kinematics.SerialChain
import RoboLean.Geometry.Homogeneous
import RoboLean.Geometry.ElementaryRotations

/-!
# Example 2.1: rotation about a line

MLS Chapter 2, Example 2.1, printed pp. 38–39 (Figure 2.4): a rigid body rotated by `θ` about the
line in the `z` direction through `(0, l₁, 0)`. The orientation of frame `B` relative to `A` is
`R_ab = R_z(θ)`, the origin of `B` is `p_ab = (0, l₁, 0)`, and the homogeneous representation is
the printed `4 × 4` matrix `g_ab(θ)`; at `θ = 0` the displacement is a pure translation along `y`.

Also checked here: every point of the body on the line (the `z`-axis of `B`) keeps its
`A`-coordinates `(0, l₁, z)` for every `θ`, and `g_ab(θ) = e^{ξ̂θ} g_ab(0)` for the revolute twist
`ξ = (-ω × q, ω)` with `ω = e_z`, `q = (0, l₁, 0)` (eq. (2.36), p. 42, and Example 2.2's form).
Conventions: `g_ab` takes `B`-coordinates to `A`-coordinates (p. 35); twists `(v, ω)`.
-/

noncomputable section

namespace RoboLean.Examples

open Real

/-- The `z`-axis is a unit vector (MLS p. 31). -/
private theorem norm_zAxis_line : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [Rotation.zAxis, Fin.sum_univ_three]

/-- The configuration `g_ab(θ) = (R_z(θ), (0, l₁, 0))` of MLS Example 2.1, printed pp. 38–39:
rotation by `θ` about the `z`-direction line through `(0, l₁, 0)`. -/
def rotationAboutLine (l₁ θ : ℝ) : RigidTransform :=
  ⟨Rotation.zRotation θ, WithLp.toLp 2 ![0, l₁, 0]⟩

/-- **MLS Example 2.1**, printed p. 39: the homogeneous representation of `g_ab(θ)` is the
printed matrix `[[cos θ, -sin θ, 0, 0], [sin θ, cos θ, 0, l₁], [0, 0, 1, 0], [0, 0, 0, 1]]`
(blocks `R_ab`, `p_ab`, `0`, `1`). -/
theorem rotationAboutLine_toHomogeneous (l₁ θ : ℝ) :
    (rotationAboutLine l₁ θ).toHomogeneous =
      Matrix.fromBlocks !![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1]
        (Matrix.of ![![0], ![l₁], ![0]]) 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rotationAboutLine, RigidTransform.toHomogeneous, Rotation.zRotation_val]

/-- **MLS Example 2.1**, printed p. 39: at `θ = 0`, `g_ab(0)` is the pure translation by
`(0, l₁, 0)` along the `y`-axis. -/
theorem rotationAboutLine_zero (l₁ : ℝ) :
    rotationAboutLine l₁ 0 = ⟨1, WithLp.toLp 2 ![0, l₁, 0]⟩ := by
  simp [rotationAboutLine, Rotation.zRotation]

/-- MLS Example 2.1, printed pp. 38–39 ("rotated about a line"): the points `(0, 0, z)` of the
body on the line keep the `A`-coordinates `(0, l₁, z)` for every rotation angle `θ`. -/
theorem rotationAboutLine_applyPoint_axis (l₁ θ z : ℝ) :
    (rotationAboutLine l₁ θ).applyPoint (WithLp.toLp 2 ![0, 0, z]) =
      WithLp.toLp 2 ![0, l₁, z] := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [rotationAboutLine, RigidTransform.applyPoint, Rotation.act_apply,
    Rotation.zRotation_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- MLS Example 2.1 with eq. (2.36), printed pp. 38–42: `g_ab(θ) = e^{ξ̂θ} g_ab(0)` for the
revolute twist `ξ = (-e_z × q, e_z)` about the line, `q = (0, l₁, 0)`. -/
theorem rotationAboutLine_eq_exp_mul (l₁ θ : ℝ) :
    rotationAboutLine l₁ θ =
      Twist.exp (Twist.revolute Rotation.zAxis (WithLp.toLp 2 ![0, l₁, 0])) θ *
        rotationAboutLine l₁ 0 := by
  rw [rotationAboutLine_zero, Twist.exp_revolute _ _ norm_zAxis_line]
  apply RigidTransform.ext
  · simp [rotationAboutLine, Rotation.zRotation]
  · simp [rotationAboutLine]

end RoboLean.Examples
