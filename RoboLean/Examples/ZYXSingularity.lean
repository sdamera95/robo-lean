import RoboLean.Kinematics.EulerSingularity

/-!
# The ZYX singularity remark of MLS p. 33

MLS Chapter 2, printed pp. 32–33: "Both the ZYX and YZX Euler angle parameterizations have the
advantage of not having a singularity at the identity orientation, `R = I`, though they do contain
singularities at other, different, orientations. For example, in the instance of ZYX Euler angles,
we have: `R_ab = R_z(ψ) R_y(θ) R_x(φ) = e^{ẑψ} e^{ŷθ} e^{x̂φ}`, which is singular when
`θ = -π/2`."

Singular is read as in MLS Exercise 3.14 (p. 150): the parameterization as the forward kinematics
of three revolute joints `z, y, x`, with a singular Jacobian. Built on
`SerialChain.isSingular_eulerChain_zyx` (determinant `-cos θ`). Corrected printing: the
parameterization is singular at `θ = π/2` as well as at `θ = -π/2` (both zeros of `cos θ`; the
printed "when `θ = -π/2`" names one of the two). It is not singular at `θ = 0`, which contains the
identity orientation (all three angles `0`).
-/

noncomputable section

namespace RoboLean.Examples

open Real

/-- **MLS p. 33, ZYX Euler angles, corrected printing**: `R_z(ψ) R_y(θ) R_x(φ)` is singular at
`θ = π/2` (for every `ψ`, `φ`; singular in the sense of Exercise 3.14, p. 150). -/
theorem zyx_isSingular_pi_div_two (ψ φ : ℝ) :
    (SerialChain.eulerChain Rotation.zAxis Rotation.yAxis Rotation.xAxis).IsSingular
      ![ψ, π / 2, φ] := by
  rw [(SerialChain.isSingular_eulerChain_zyx _).2]
  simp

/-- **MLS p. 33, ZYX Euler angles, as printed**: `R_z(ψ) R_y(θ) R_x(φ)` is singular at
`θ = -π/2` (for every `ψ`, `φ`; singular in the sense of Exercise 3.14, p. 150). -/
theorem zyx_isSingular_neg_pi_div_two (ψ φ : ℝ) :
    (SerialChain.eulerChain Rotation.zAxis Rotation.yAxis Rotation.xAxis).IsSingular
      ![ψ, -(π / 2), φ] := by
  rw [(SerialChain.isSingular_eulerChain_zyx _).2]
  simp

/-- **MLS pp. 32–33**: ZYX Euler angles are not singular at `θ = 0`, in particular at the
identity orientation `R = I` (all angles `0`; singular in the sense of Exercise 3.14,
p. 150). -/
theorem zyx_not_isSingular_zero (ψ φ : ℝ) :
    ¬ (SerialChain.eulerChain Rotation.zAxis Rotation.yAxis Rotation.xAxis).IsSingular
      ![ψ, 0, φ] := by
  rw [(SerialChain.isSingular_eulerChain_zyx _).2]
  simp

end RoboLean.Examples
