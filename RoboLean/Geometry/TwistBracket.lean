import RoboLean.Geometry.Twist
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Tactic.Ring

/-!
# Coordinate and matrix brackets of twists

MLS Appendix A, printed pp. 410–411, Examples A.6–A.8: matrix brackets are
commutators, the three-dimensional hat map intertwines cross product and
commutator, and the `se(3)` bracket has linear-first coordinates
`(ω₁ × v₂ - ω₂ × v₁, ω₁ × ω₂)`. No unit or nonzero premise is used.
The algebraic identities below do not construct a tangent bundle or prove a
manifold-level correspondence with left-invariant vector fields.
-/

noncomputable section

open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing

namespace RoboLean

namespace Vec3

/-- MLS Example A.7: cross product corresponds to the independent matrix commutator. -/
theorem hat_cross (u v : Vec3) :
    hat (cross u v) = hat u * hat v - hat v * hat u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hat, cross, cross_apply] <;> ring

end Vec3

namespace Twist

/-- MLS Example A.8, with linear coordinates before angular coordinates. -/
def bracket (ξ η : Twist) : Twist :=
  (Vec3.cross ξ.angular η.linear - Vec3.cross η.angular ξ.linear,
    Vec3.cross ξ.angular η.angular)

@[simp] theorem bracket_linear (ξ η : Twist) :
    (bracket ξ η).linear =
      Vec3.cross ξ.angular η.linear - Vec3.cross η.angular ξ.linear := rfl

@[simp] theorem bracket_angular (ξ η : Twist) :
    (bracket ξ η).angular = Vec3.cross ξ.angular η.angular := rfl

/-- The independently defined coordinate bracket agrees with the homogeneous
matrix commutator, including every translation and zero case. -/
theorem hat_bracket (ξ η : Twist) :
    (bracket ξ η).hat = ξ.hat * η.hat - η.hat * ξ.hat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    fin_cases i <;> fin_cases j <;>
      simp [hat, bracket, linear, angular, Vec3.hat, Vec3.cross, cross_apply, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.fromBlocks] <;> ring

/-- Compatibility with Mathlib's associative matrix Lie bracket. -/
theorem hat_bracket_lie (ξ η : Twist) : (bracket ξ η).hat = ⁅ξ.hat, η.hat⁆ :=
  hat_bracket ξ η

/-- Additivity in the first argument, transported through the faithful hat map. -/
theorem bracket_add_left (ξ η ζ : Twist) :
    bracket (ξ + η) ζ = bracket ξ ζ + bracket η ζ := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_add, add_lie]

/-- Additivity in the second argument. -/
theorem bracket_add_right (ξ η ζ : Twist) :
    bracket ξ (η + ζ) = bracket ξ η + bracket ξ ζ := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_add, lie_add]

/-- Real homogeneity in the first argument. -/
theorem bracket_smul_left (c : ℝ) (ξ η : Twist) :
    bracket (c • ξ) η = c • bracket ξ η := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_smul, smul_lie]

/-- Real homogeneity in the second argument. -/
theorem bracket_smul_right (c : ℝ) (ξ η : Twist) :
    bracket ξ (c • η) = c • bracket ξ η := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_smul, lie_smul]

@[simp] theorem bracket_zero_left (ξ : Twist) : bracket 0 ξ = 0 := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_zero, zero_lie]

@[simp] theorem bracket_zero_right (ξ : Twist) : bracket ξ 0 = 0 := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_zero, lie_zero]

@[simp] theorem bracket_self (ξ : Twist) : bracket ξ ξ = 0 := by
  apply hat_injective
  simp only [hat_bracket_lie, hat_zero, lie_self]

/-- Antisymmetry of the coordinate bracket. -/
theorem bracket_antisymm (ξ η : Twist) : bracket ξ η = -bracket η ξ := by
  apply hat_injective
  rw [hat_bracket_lie, hat_neg, hat_bracket_lie]
  exact (lie_skew ξ.hat η.hat).symm

/-- Jacobi follows from the actual associative matrix commutator identity. -/
theorem bracket_jacobi (ξ η ζ : Twist) :
    bracket ξ (bracket η ζ) + bracket η (bracket ζ ξ) + bracket ζ (bracket ξ η) = 0 := by
  apply hat_injective
  simp only [hat_add, hat_bracket_lie, hat_zero]
  exact lie_jacobi ξ.hat η.hat ζ.hat

/-- The coordinate bracket as a real bilinear map. -/
def bracketBilinear : Twist →ₗ[ℝ] Twist →ₗ[ℝ] Twist where
  toFun ξ :=
    { toFun := bracket ξ
      map_add' := bracket_add_right ξ
      map_smul' := fun c η => bracket_smul_right c ξ η }
  map_add' ξ η := LinearMap.ext (fun ζ => bracket_add_left ξ η ζ)
  map_smul' c ξ := LinearMap.ext (fun η => bracket_smul_left c ξ η)

@[simp] theorem bracketBilinear_apply (ξ η : Twist) :
    bracketBilinear ξ η = bracket ξ η := rfl

end Twist

/-- The independently constrained homogeneous `se(3)` carrier is closed under
matrix commutators; this is not closure by definition of the coordinate bracket. -/
theorem se3_commutator_mem {A B : HomogeneousMatrix}
    (hA : A ∈ se3Submodule) (hB : B ∈ se3Submodule) :
    A * B - B * A ∈ se3Submodule := by
  have h := Twist.hat_mem_se3Submodule (Twist.bracket (Twist.vee A) (Twist.vee B))
  rwa [Twist.hat_bracket, Twist.hat_vee A hA, Twist.hat_vee B hB] at h

end RoboLean
