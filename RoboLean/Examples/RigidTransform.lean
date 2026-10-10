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

MLS references (printed pages): the quarter turn is `R_z(π/2)` for the matrix
`R_z` of p. 31; the point action is equation (2.22), p. 35; the vector action
`g_*(v) = R v` is on p. 36; composition (2.24) and the inverse
`g⁻¹ = (-Rᵀp, Rᵀ)` are on p. 37; the Euclidean norm is the one in Proposition
2.2, p. 26. The expected values are derived independently in the exact example of
`research/reports/geometry-conventions.md`. Every theorem here is a convention
check on concrete inputs, not a general result.
-/

noncomputable section

namespace RoboLean.Examples

/-- A Euclidean vector with explicitly ordered Cartesian coordinates `(x, y, z) ∈ ℝ³`,
MLS p. 20. -/
def vec (x y z : ℝ) : Vec3 := WithLp.toLp 2 ![x, y, z]

/-- The right-handed positive quarter turn about the third coordinate axis, `R_z(π/2)` for
the elementary rotation `R_z` of MLS p. 31. -/
def quarterTurn : Rotation :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    · norm_num [Matrix.det_fin_three]⟩

/-- A quarter turn followed by the translation `(1, 2, 3)`: the element
`(p, R) = ((1, 2, 3), R_z(π/2))` of `SE(3)`, MLS equation (2.21), p. 35. -/
def g : RigidTransform := ⟨quarterTurn, vec 1 2 3⟩

/-- Translation by `(2, 0, 0)` without rotation: the element `((2, 0, 0), I)` of `SE(3)`,
MLS equation (2.21), p. 35. -/
def h : RigidTransform := ⟨1, vec 2 0 0⟩

/-- The same coordinates are used as a point or displacement in separate tests: a point
under the action (2.22), MLS p. 35, and a free vector under `g_*(v) = Rv`, MLS p. 36; MLS
p. 21 notes that both are represented by 3-tuples. -/
def q : Vec3 := vec 1 1 1

/-- Convention check: `R_z(π/2)` (MLS p. 31) sends `(x, y, z)` to `(-y, x, z)`. -/
theorem quarterTurn_act (x y z : ℝ) :
    quarterTurn.act (vec x y z) = vec (-y) x z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, quarterTurn, vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- Convention check of composition (2.24), MLS p. 37: the translation of `g * h` is
`R_g p_h + p_g`. -/
theorem g_mul_h_translation : (g * h).translation = vec 1 4 3 := by
  change quarterTurn.act (vec 2 0 0) + vec 1 2 3 = _
  rw [quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

/-- Convention check of composition (2.24), MLS p. 37, with the factors reversed. -/
theorem h_mul_g_translation : (h * g).translation = vec 3 2 3 := by
  change (1 : Rotation).act (vec 1 2 3) + vec 2 0 0 = _
  ext i
  fin_cases i <;>
    norm_num [Rotation.act_apply, vec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Convention check of the point action `g(q) = p + Rq`, MLS equation (2.22), p. 35. -/
theorem g_applyPoint_q : g.applyPoint q = vec 0 3 4 := by
  change quarterTurn.act (vec 1 1 1) + vec 1 2 3 = _
  rw [quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

/-- Convention check of the vector action `g_*(v) = Rv`, MLS p. 36: no translation. -/
theorem g_applyVector_q : g.applyVector q = vec (-1) 1 1 := by
  exact quarterTurn_act 1 1 1

/-- Convention check: `g * h` applies `h` first to a point, MLS equation (2.24), p. 37. -/
theorem g_mul_h_applyPoint_q : (g * h).applyPoint q = vec 0 5 4 := by
  change (quarterTurn * 1).act (vec 1 1 1) + (g * h).translation = _
  rw [mul_one, g_mul_h_translation, quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

/-- Convention check: `h * g` applies `g` first to a point, MLS equation (2.24), p. 37. -/
theorem h_mul_g_applyPoint_q : (h * g).applyPoint q = vec 2 3 4 := by
  change (1 * quarterTurn).act (vec 1 1 1) + (h * g).translation = _
  rw [one_mul, h_mul_g_translation, quarterTurn_act]
  ext i
  fin_cases i <;> norm_num [vec]

/-- Convention check of the inverse translation `-Rᵀp`, MLS p. 37. -/
theorem g_inv_translation : (g⁻¹).translation = vec (-2) 1 (-3) := by
  change -((quarterTurn⁻¹).act (vec 1 2 3)) = _
  ext i
  fin_cases i <;>
    norm_num [Rotation.act_apply, quarterTurn, vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- An exact rational rotation with planar cosine `3/5` and sine `4/5`: a matrix of the
elementary form `R_z(α)` of MLS p. 31 with `cos α = 3/5`, `sin α = 4/5`. -/
def rationalTurn : Rotation :=
  ⟨!![3 / 5, -(4 / 5), 0; 4 / 5, 3 / 5, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    · norm_num [Matrix.det_fin_three]⟩

/-- Convention check: a rotation of the `R_z` form of MLS p. 31 with cosine `3/5` and
sine `4/5` sends `(5, 0, 0)` to `(3, 4, 0)`. -/
theorem rationalTurn_act_five : rationalTurn.act (vec 5 0 0) = vec 3 4 0 := by
  ext i
  fin_cases i <;>
    norm_num [Rotation.act_apply, rationalTurn, vec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- Convention check of the Euclidean norm used in MLS Proposition 2.2, p. 26. -/
theorem vec_five_norm : ‖vec 5 0 0‖ = 5 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [vec, Fin.sum_univ_succ]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- Convention check of the Euclidean norm used in MLS Proposition 2.2, p. 26. -/
theorem vec_three_four_norm : ‖vec 3 4 0‖ = 5 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [vec, Fin.sum_univ_succ]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

/-- Convention check of norm preservation, MLS Proposition 2.2, p. 26, on one input. -/
theorem rationalTurn_act_five_norm : ‖rationalTurn.act (vec 5 0 0)‖ = 5 := by
  rw [rationalTurn_act_five, vec_three_four_norm]

end RoboLean.Examples
