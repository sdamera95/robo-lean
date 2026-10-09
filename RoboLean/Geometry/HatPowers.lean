import RoboLean.Geometry.Hat
import Mathlib.Tactic.Ring

/-!
# Powers of three-dimensional hat matrices

MLS Lemma 2.3, equations (2.12) and (2.13), uses the Euclidean norm of the
axial vector. The identities hold for every vector, including zero.
-/

open Matrix

namespace RoboLean.Vec3

/-- The outer product of Euclidean coordinate vectors. -/
noncomputable def outer (v w : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.vecMulVec (WithLp.ofLp v) (WithLp.ofLp w)

@[simp] theorem outer_apply (v w : Vec3) (i j : Fin 3) :
    outer v w i j = v i * w j := rfl

/-- A vector is in the kernel of its own hat matrix. -/
@[simp] theorem hat_mulVec_self (v : Vec3) : hat v *ᵥ WithLp.ofLp v = 0 := by
  rw [hat_mulVec, cross_coordinates, cross_self]

/-- MLS equation (2.12), with no normalization hypothesis. -/
theorem hat_sq (v : Vec3) : hat v ^ 2 = outer v v - ‖v‖ ^ 2 • 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, hat, outer, Matrix.mul_apply, Matrix.vecMulVec,
      Fin.sum_univ_succ] <;> ring

/-- MLS equation (2.13), including the zero vector. -/
theorem hat_cube (v : Vec3) : hat v ^ 3 = -(‖v‖ ^ 2) • hat v := by
  rw [pow_succ', hat_sq, mul_sub, outer, Matrix.mul_vecMulVec,
    hat_mulVec_self, Matrix.zero_vecMulVec, Matrix.mul_smul, mul_one,
    zero_sub, neg_smul]

/-- The square identity specialized to a unit axis. -/
theorem hat_sq_of_norm_eq_one (v : Vec3) (hv : ‖v‖ = 1) :
    hat v ^ 2 = outer v v - 1 := by
  simp [hat_sq, hv]

/-- The cubic relation used for a unit-axis Rodrigues formula. -/
theorem hat_cube_of_norm_eq_one (v : Vec3) (hv : ‖v‖ = 1) :
    hat v ^ 3 = -hat v := by
  simp [hat_cube, hv]

end RoboLean.Vec3
