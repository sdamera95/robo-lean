import RoboLean.Geometry.RigidTransform
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Concrete rigid-transform conventions

These coordinate examples use right-handed, active rotations of column vectors.
The product `g * h` applies `h` first. The expected coordinates are stated
explicitly so reversing that convention changes the regression statements.

The rational 3–4–5 rotation also distinguishes the Euclidean norm on `Vec3`
from the supremum norm on a plain function space.
-/

noncomputable section

namespace RoboLean.Examples

/-- A Euclidean vector with explicitly ordered Cartesian coordinates. -/
def vec (x y z : ℝ) : Vec3 := WithLp.toLp 2 ![x, y, z]

/-- The right-handed positive quarter turn about the third coordinate axis. -/
def quarterTurn : Rotation :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    · norm_num [Matrix.det_fin_three]⟩

/-- A quarter turn followed by the translation `(1, 2, 3)`. -/
def g : RigidTransform := ⟨quarterTurn, vec 1 2 3⟩

/-- Translation by `(2, 0, 0)` without rotation. -/
def h : RigidTransform := ⟨1, vec 2 0 0⟩

/-- The same coordinates are used as a point or displacement in separate tests. -/
def q : Vec3 := vec 1 1 1

theorem quarterTurn_act (x y z : ℝ) :
    quarterTurn.act (vec x y z) = vec (-y) x z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, quarterTurn, vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem g_mul_h_translation : (g * h).translation = vec 1 4 3 := by
  change quarterTurn.act (vec 2 0 0) + vec 1 2 3 = _
  rw [quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

theorem h_mul_g_translation : (h * g).translation = vec 3 2 3 := by
  change (1 : Rotation).act (vec 1 2 3) + vec 2 0 0 = _
  ext i
  fin_cases i <;>
    norm_num [Rotation.act_apply, vec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem g_applyPoint_q : g.applyPoint q = vec 0 3 4 := by
  change quarterTurn.act (vec 1 1 1) + vec 1 2 3 = _
  rw [quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

theorem g_applyVector_q : g.applyVector q = vec (-1) 1 1 := by
  exact quarterTurn_act 1 1 1

theorem g_mul_h_applyPoint_q : (g * h).applyPoint q = vec 0 5 4 := by
  change (quarterTurn * 1).act (vec 1 1 1) + (g * h).translation = _
  rw [mul_one, g_mul_h_translation, quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

theorem h_mul_g_applyPoint_q : (h * g).applyPoint q = vec 2 3 4 := by
  change (1 * quarterTurn).act (vec 1 1 1) + (h * g).translation = _
  rw [one_mul, h_mul_g_translation, quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

theorem g_inv_translation : (g⁻¹).translation = vec (-2) 1 (-3) := by
  change -((quarterTurn⁻¹).act (vec 1 2 3)) = _
  ext i
  fin_cases i <;>
    norm_num [Rotation.act_apply, quarterTurn, vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- An exact rational rotation with planar cosine `3/5` and sine `4/5`. -/
def rationalTurn : Rotation :=
  ⟨!![3 / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    · norm_num [Matrix.det_fin_three]⟩

theorem rationalTurn_act_five : rationalTurn.act (vec 5 0 0) = vec 3 4 0 := by
  ext i
  fin_cases i <;>
    norm_num [Rotation.act_apply, rationalTurn, vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem vec_five_norm : ‖vec 5 0 0‖ = 5 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [vec, Fin.sum_univ_succ]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

theorem vec_three_four_norm : ‖vec 3 4 0‖ = 5 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [vec, Fin.sum_univ_succ]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

theorem rationalTurn_act_five_norm : ‖rationalTurn.act (vec 5 0 0)‖ = 5 := by
  rw [rationalTurn_act_five, vec_three_four_norm]

end RoboLean.Examples
