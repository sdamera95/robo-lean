import RoboLean.Geometry.RigidTransform
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A fixed unit axis for every proper three-dimensional rotation

This is an algebraic prerequisite for MLS Proposition 2.5, printed pp. 29–30
(ledger R19), and Euler's axis-angle theorem on p. 31. In odd dimension three,
orthogonality and determinant one force `det (R - I) = 0`. A nonzero kernel
vector then gives a fixed axis, which is normalized using the Euclidean norm.

This argument covers identity and half-turn rotations without dividing by
`sin θ`. It does not yet provide an angle, an exponential representation,
uniqueness, or a continuous choice of axis. The determinant argument is a
separate derivation, not the denominator-based extraction in MLS equation (2.18).
-/

namespace RoboLean
namespace Rotation

open Matrix

/-- In dimension three, every proper rotation has a singular `R - I`. -/
theorem det_sub_one (R : Rotation) : Matrix.det (R.val - 1) = 0 := by
  have hm : R.valᵀ * (R.val - 1) = -(R.val - 1)ᵀ := by
    rw [mul_sub, R.transpose_mul, mul_one, Matrix.transpose_sub,
      Matrix.transpose_one, neg_sub]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_transpose, R.det_eq_one, one_mul,
    Matrix.det_neg, Matrix.det_transpose] at hd
  norm_num at hd
  linarith

/-- Every proper rotation fixes a nonzero Euclidean vector. -/
theorem exists_ne_zero_act_eq_self (R : Rotation) :
    ∃ v : Vec3, v ≠ 0 ∧ R.act v = v := by
  obtain ⟨v, hv, hRv⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := R.val - 1)).mpr R.det_sub_one
  refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
  · intro h
    apply hv
    simpa using congrArg WithLp.ofLp h
  · apply WithLp.ofLp_injective
    change R.val *ᵥ v = v
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hRv

/-- Every proper rotation fixes a unit vector, including identity and half-turns.
The norm here is the Euclidean norm of `Vec3`. -/
theorem exists_unit_axis (R : Rotation) :
    ∃ ω : Vec3, ‖ω‖ = 1 ∧ R.act ω = ω := by
  obtain ⟨v, hv, hRv⟩ := R.exists_ne_zero_act_eq_self
  refine ⟨NormedSpace.normalize v, NormedSpace.norm_normalize hv, ?_⟩
  simp only [NormedSpace.normalize, map_smul, hRv]

end Rotation
end RoboLean
