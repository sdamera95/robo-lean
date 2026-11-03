import RoboLean.Geometry.Homogeneous
import RoboLean.Geometry.ElementaryRotations

/-!
# Exercise 2.16(a): the two-degree-of-freedom manipulator of Figure 2.17

MLS Chapter 2, Exercise 16, printed pp. 77–78, Figure 2.17 (read as a rendered image): a base
frame `C₀`, a column of height `l₀` carrying frame `C₁` and the first revolute joint about the
vertical axis, a horizontal link of length `l₁` to frame `C₂` and the second revolute joint about
a parallel vertical axis, and a horizontal link of length `l₂` to frame `C₃`; all frames drawn with
the same orientation in the reference configuration. Part (a): "Express the position and
orientation of frame `C₃` relative to frame `C₀` in terms of the joint angle variables and the
link parameters."

Reading of the figure (stated here): joint `i` rotates about the `z`-axis by `θᵢ`; `C₁` sits at
height `l₀` above `C₀` on the first axis, `C₂` at distance `l₁` along the `x`-axis of `C₁` (the
figure dimensions no vertical offset between `C₁` and `C₂`, taken as zero), and `C₃` at distance
`l₂` along the `x`-axis of `C₂`. Then
`g_{C₀C₃} = (R_z(θ₁ + θ₂), (l₁ cos θ₁ + l₂ cos (θ₁ + θ₂), l₁ sin θ₁ + l₂ sin (θ₁ + θ₂), l₀))`.
Parts (b)–(d) (velocities) are not formalized here. Conventions: `g_{ab}` takes `b`-coordinates
to `a`-coordinates and composes as `g_{ac} = g_{ab} g_{bc}` (p. 37).
-/

noncomputable section

namespace RoboLean.Examples

open Real

/-- The relative configuration of `C₁` in `C₀` in MLS Figure 2.17, printed p. 77: rotation by `θ₁`
about the vertical axis, origin at height `l₀`. -/
def twoDofFrame01 (l₀ θ₁ : ℝ) : RigidTransform :=
  ⟨Rotation.zRotation θ₁, WithLp.toLp 2 ![0, 0, l₀]⟩

/-- The relative configuration of `C₂` in `C₁` in MLS Figure 2.17, printed p. 77: rotation by `θ₂`
about the vertical axis, origin at distance `l₁` along `x`. -/
def twoDofFrame12 (l₁ θ₂ : ℝ) : RigidTransform :=
  ⟨Rotation.zRotation θ₂, WithLp.toLp 2 ![l₁, 0, 0]⟩

/-- The relative configuration of `C₃` in `C₂` in MLS Figure 2.17, printed p. 77: a translation by
`l₂` along `x`. -/
def twoDofFrame23 (l₂ : ℝ) : RigidTransform :=
  ⟨1, WithLp.toLp 2 ![l₂, 0, 0]⟩

/-- **MLS Exercise 2.16(a)**, printed pp. 77–78: the configuration of `C₃` relative to `C₀` is
`g_{C₀C₁} g_{C₁C₂} g_{C₂C₃} = (R_z(θ₁ + θ₂), (l₁ cos θ₁ + l₂ cos (θ₁ + θ₂),
l₁ sin θ₁ + l₂ sin (θ₁ + θ₂), l₀))`. -/
theorem twoDofPose_eq (l₀ l₁ l₂ θ₁ θ₂ : ℝ) :
    twoDofFrame01 l₀ θ₁ * twoDofFrame12 l₁ θ₂ * twoDofFrame23 l₂ =
      ⟨Rotation.zRotation (θ₁ + θ₂), WithLp.toLp 2
        ![l₁ * cos θ₁ + l₂ * cos (θ₁ + θ₂), l₁ * sin θ₁ + l₂ * sin (θ₁ + θ₂), l₀]⟩ := by
  apply RigidTransform.ext
  · simp [twoDofFrame01, twoDofFrame12, twoDofFrame23, Rotation.zRotation, Rotation.exp_add]
  · apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [twoDofFrame01, twoDofFrame12, twoDofFrame23, Rotation.act_apply,
      Rotation.zRotation_val, Matrix.mulVec, dotProduct, Fin.sum_univ_three, cos_add, sin_add] <;>
      ring

end RoboLean.Examples
