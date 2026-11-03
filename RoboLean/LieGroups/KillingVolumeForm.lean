import Mathlib.LinearAlgebra.CrossProduct
import RoboLean.LieGroups.HyperbolicKilling

/-!
# The volume form on `so(3)` through the bracket and the Killing form

MLS Appendix A, §3.3, printed p. 431: "a volume form on `SO(3)` can be defined by making use of the
Lie bracket and Killing form on `SO(3)`: `Ω_{SO(3)}(ω̂₁, ω̂₂, ω̂₃) = -¼ ⟨ω̂₁, [ω̂₂, ω̂₃]⟩_K =
ω₁ · ω₂ × ω₃`", which "is equivalent to the volume form defined by using the standard volume on
`ℝ³`". The algebraic content at the identity is stated here.

Source observation (an ambiguity, not an error): the printed equality holds with the Killing form
of `se(3)`, `⟨ξ₁, ξ₂⟩_K = -4 ω₁ · ω₂` of (A.14), evaluated on pure rotations `(0, ω)`, with the
twist bracket of Example A.8 (p. 411). With the Killing form of `so(3)` itself,
`trace(ad_{ω̂₁} ∘ ad_{ω̂₂}) = trace(ω̂₁ ω̂₂) = -2 ω₁ · ω₂` (the bracket of Example A.7 is the cross
product, so `ad_{ω̂} = ω̂`), the same expression is half the triple product.

The value of the volume of `SO(3)` printed on the same page (`8π³ rad³`) is not stated in Lean;
the left invariant extension of this form gives `8π²` (a corrected printing recorded with the
library's conventions, from two hand computations and a numerical check).
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Twist

/-- MLS printed p. 431: `-¼ ⟨ω̂₁, [ω̂₂, ω̂₃]⟩_K = ω₁ · ω₂ × ω₃`, with the Killing form (A.14) of
`se(3)` on pure rotations `(0, ω)` and the twist bracket of Example A.8 (p. 411). -/
theorem neg_quarter_killingForm_bracket (ω₁ ω₂ ω₃ : Vec3) :
    -(1 / 4) * killingForm ⟨0, ω₁⟩ (bracket ⟨0, ω₂⟩ ⟨0, ω₃⟩) =
      inner ℝ ω₁ (Vec3.cross ω₂ ω₃) := by
  rw [killingForm_eq]
  simp only [bracket_angular]
  ring

/-- MLS printed p. 431, "equivalent to the volume form defined by using the standard volume on
`ℝ³`": the triple product `ω₁ · ω₂ × ω₃` is the determinant of the matrix with rows `ω₁, ω₂, ω₃`. -/
theorem inner_cross_eq_det (ω₁ ω₂ ω₃ : Vec3) :
    inner ℝ ω₁ (Vec3.cross ω₂ ω₃) =
      Matrix.det ![WithLp.ofLp ω₁, WithLp.ofLp ω₂, WithLp.ofLp ω₃] := by
  rw [← triple_product_eq_det]
  simp only [Vec3.cross, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The trace form of `so(3)` itself, MLS printed p. 427 (`⟨ξ₁, ξ₂⟩_K = trace(ad_ξ₁ ∘ ad_ξ₂)`)
applied to `so(3) ≅ (ℝ³, ×)` of Example A.7 (p. 411), where `ad_{ω̂}` acts as `ω̂`:
`trace(ω̂₁ ω̂₂) = -2 ω₁ · ω₂`. -/
theorem trace_hat_mul_hat (ω₁ ω₂ : Vec3) :
    (Vec3.hat ω₁ * Vec3.hat ω₂).trace = -2 * inner ℝ ω₁ ω₂ := by
  simp [Matrix.trace, Vec3.hat, Fin.sum_univ_three, PiLp.inner_apply]
  ring

end Twist

end RoboLean
