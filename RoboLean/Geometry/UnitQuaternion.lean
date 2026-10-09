import RoboLean.Geometry.CrossProduct
import Mathlib.Analysis.Quaternion
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Scalar-first quaternion coordinates and the unit-quaternion group

MLS printed pp. 33–34 uses `(q₀, (q₁,q₂,q₃))`. Quaternion multiplication,
conjugation, norm, and group structure below reuse Mathlib's real quaternions
and unitary-element group. The scalar/vector multiplication theorem permits
zero quaternions; the group carrier is independently identified by norm one.
-/

noncomputable section

namespace RoboLean
namespace QuaternionCoordinates

/-- The vector component, in the established Euclidean x/y/z coordinates. -/
def vector (q : Quaternion ℝ) : Vec3 := WithLp.toLp 2 ![q.imI, q.imJ, q.imK]

/-- Assemble scalar-first quaternion coordinates using Mathlib's quaternion type. -/
def ofScalarVector (a : ℝ) (v : Vec3) : Quaternion ℝ := ⟨a, v 0, v 1, v 2⟩

@[simp] theorem re_ofScalarVector (a : ℝ) (v : Vec3) : (ofScalarVector a v).re = a := rfl

@[simp] theorem vector_ofScalarVector (a : ℝ) (v : Vec3) : vector (ofScalarVector a v) = v := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem ofScalarVector_re_vector (q : Quaternion ℝ) :
    ofScalarVector q.re (vector q) = q := by
  cases q
  rfl

/-- MLS printed p. 33: the quaternion product in scalar/vector coordinates. -/
theorem mul_formula (q p : Quaternion ℝ) :
    q * p = ofScalarVector (q.re * p.re - inner ℝ (vector q) (vector p))
      (q.re • vector p + p.re • vector q + Vec3.cross (vector q) (vector p)) := by
  ext <;>
    simp [ofScalarVector, vector, EuclideanSpace.inner_eq_star_dotProduct, Vec3.cross,
      cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The vector component of multiplication, for arbitrary real quaternions. -/
theorem vector_mul (q p : Quaternion ℝ) :
    vector (q * p) = q.re • vector p + p.re • vector q + Vec3.cross (vector q) (vector p) := by
  rw [mul_formula, vector_ofScalarVector]

/-- Quaternion norm square is scalar square plus the Euclidean vector norm square. -/
theorem normSq_eq_scalar_vector (q : Quaternion ℝ) :
    Quaternion.normSq q = q.re ^ 2 + ‖vector q‖ ^ 2 := by
  rw [Quaternion.normSq_def', EuclideanSpace.real_norm_sq_eq]
  simp [vector, Fin.sum_univ_succ]
  ring

@[simp] theorem normSq_ofScalarVector (a : ℝ) (v : Vec3) :
    Quaternion.normSq (ofScalarVector a v) = a ^ 2 + ‖v‖ ^ 2 := by
  rw [normSq_eq_scalar_vector, re_ofScalarVector, vector_ofScalarVector]

/-- Conjugation preserves the scalar and negates the vector component. -/
theorem star_ofScalarVector (a : ℝ) (v : Vec3) :
    star (ofScalarVector a v) = ofScalarVector a (-v) := by
  ext <;> simp [ofScalarVector]

end QuaternionCoordinates

/-- The existing unitary-element group of real quaternions. The independent
norm-one characterization is proved below. -/
abbrev UnitQuaternion := unitary (Quaternion ℝ)

/-- Exactly norm-one real quaternions inhabit the reused group carrier. -/
theorem mem_unitQuaternion_iff (q : Quaternion ℝ) :
    q ∈ unitary (Quaternion ℝ) ↔ ‖q‖ = 1 := by
  constructor
  · intro hq
    have h := congrArg (fun a : Quaternion ℝ => a.re) (Unitary.mem_iff.mp hq).1
    have hn : Quaternion.normSq q = 1 := by
      simpa only [Quaternion.star_mul_self, Quaternion.re_coe, Quaternion.re_one] using h
    rw [Quaternion.normSq_eq_norm_mul_self] at hn
    nlinarith [norm_nonneg q]
  · intro hq
    have hn : Quaternion.normSq q = 1 := by rw [Quaternion.normSq_eq_norm_mul_self, hq, one_mul]
    apply Unitary.mem_iff.mpr
    simp only [Quaternion.star_mul_self, Quaternion.self_mul_star, hn, Quaternion.coe_one,
      and_self]

namespace UnitQuaternion

/-- Package independently supplied norm-one quaternion evidence. -/
def ofNormOne (q : Quaternion ℝ) (h : ‖q‖ = 1) : UnitQuaternion :=
  ⟨q, (mem_unitQuaternion_iff q).mpr h⟩

@[simp] theorem ofNormOne_val (q : Quaternion ℝ) (h : ‖q‖ = 1) :
    (ofNormOne q h).val = q := rfl

@[simp] theorem norm_val (q : UnitQuaternion) : ‖q.val‖ = 1 :=
  (mem_unitQuaternion_iff q.val).mp q.property

@[simp] theorem normSq_val (q : UnitQuaternion) : Quaternion.normSq q.val = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, norm_val, one_mul]

/-- The group carrier excludes zero, unlike the full quaternion vector space. -/
theorem val_ne_zero (q : UnitQuaternion) : q.val ≠ 0 := by
  intro h
  have hn := norm_val q
  rw [h, norm_zero] at hn
  norm_num at hn

@[simp] theorem one_val : (1 : UnitQuaternion).val = 1 := rfl

@[simp] theorem mul_val (q p : UnitQuaternion) : (q * p).val = q.val * p.val := rfl

/-- Unit-quaternion inversion is quaternion conjugation. -/
@[simp] theorem inv_val (q : UnitQuaternion) : (q⁻¹).val = star q.val := rfl

@[simp] theorem neg_val (q : UnitQuaternion) : (-q).val = -q.val := rfl

/-- The scalar coordinate of a unit quaternion. -/
def scalar (q : UnitQuaternion) : ℝ := q.val.re

/-- The Euclidean vector coordinate of a unit quaternion. -/
def vector (q : UnitQuaternion) : Vec3 := QuaternionCoordinates.vector q.val

/-- The unit constraint in the stated scalar/vector convention. -/
theorem scalar_sq_add_norm_vector_sq (q : UnitQuaternion) :
    scalar q ^ 2 + ‖vector q‖ ^ 2 = 1 := by
  rw [scalar, vector, ← QuaternionCoordinates.normSq_eq_scalar_vector, normSq_val]

end UnitQuaternion
end RoboLean
