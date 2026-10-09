import RoboLean.Geometry.CrossProduct
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Hat and vee maps in three dimensions

The hat matrix represents the right-handed cross product on column coordinates.
Over the reals, Mathlib's skew-adjoint matrices are exactly the matrices satisfying
`Aᵀ = -A`; hat and vee give a linear equivalence with Euclidean three-space.
-/

open Matrix

namespace RoboLean

/-- Real skew-symmetric three-by-three matrices, with Mathlib's real module structure. -/
abbrev SkewMatrix3 := skewAdjoint (Matrix (Fin 3) (Fin 3) ℝ)

theorem mem_skewMatrix3_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ skewAdjoint (Matrix (Fin 3) (Fin 3) ℝ) ↔ Aᵀ = -A := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

namespace Vec3

/-- The skew matrix representing cross product by `v`, as in MLS equation (2.4). -/
noncomputable def hat (v : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]

/-- Extract axial coordinates. This inverts `hat` on skew-symmetric matrices. -/
noncomputable def vee (A : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  WithLp.toLp 2 ![A 2 1, A 0 2, A 1 0]

@[simp] theorem vee_hat (v : Vec3) : vee (hat v) = v := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> rfl

@[simp] theorem hat_transpose (v : Vec3) : (hat v)ᵀ = -hat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat]

/-- The reverse inverse requires the skew-transpose hypothesis explicitly. -/
theorem hat_vee (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Aᵀ = -A) :
    hat (vee A) = A := by
  have hentry (i j : Fin 3) : A j i = -A i j :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M i j) h
  have hdiag (i : Fin 3) : A i i = 0 := by
    have := hentry i i
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat, vee, hdiag]
  · exact (hentry 1 0).symm
  · exact (hentry 2 1).symm
  · exact (hentry 0 2).symm

@[simp] theorem hat_add (v w : Vec3) : hat (v + w) = hat v + hat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat] <;> exact add_comm _ _

@[simp] theorem hat_smul (c : ℝ) (v : Vec3) : hat (c • v) = c • hat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hat, mul_neg]

/-- Hat is a linear equivalence onto all real skew-symmetric three-by-three matrices. -/
noncomputable def hatLinearEquiv : Vec3 ≃ₗ[ℝ] SkewMatrix3 where
  toFun v := ⟨hat v, (mem_skewMatrix3_iff _).mpr (hat_transpose v)⟩
  invFun A := vee A.val
  left_inv := vee_hat
  right_inv A := Subtype.ext (hat_vee A.val ((mem_skewMatrix3_iff _).mp A.property))
  map_add' v w := Subtype.ext (hat_add v w)
  map_smul' c v := Subtype.ext (hat_smul c v)

@[simp] theorem hatLinearEquiv_apply (v : Vec3) :
    (hatLinearEquiv v).val = hat v := rfl

@[simp] theorem hatLinearEquiv_symm_apply (A : SkewMatrix3) :
    hatLinearEquiv.symm A = vee A.val := rfl

/-- Multiplication by the hat matrix is the cross product, in column coordinates. -/
theorem hat_mulVec (v w : Vec3) :
    hat v *ᵥ WithLp.ofLp w = WithLp.ofLp (cross v w) := by
  ext i
  fin_cases i <;> simp [hat, cross, cross_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg] <;> exact add_comm _ _

/-- Proper rotations act on hat matrices by conjugation. -/
theorem hat_act (R : Rotation) (v : Vec3) :
    hat (R.act v) = R.val * hat v * R.valᵀ := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  let y : Vec3 := WithLp.toLp 2 x
  change hat (R.act v) *ᵥ WithLp.ofLp y =
    (R.val * hat v * R.valᵀ) *ᵥ WithLp.ofLp y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change hat (R.act v) *ᵥ WithLp.ofLp y =
    R.val *ᵥ (hat v *ᵥ WithLp.ofLp ((R⁻¹).act y))
  rw [hat_mulVec, hat_mulVec]
  change WithLp.ofLp (cross (R.act v) y) =
    WithLp.ofLp (R.act (cross v ((R⁻¹).act y)))
  rw [Rotation.act_cross, Rotation.act_inv_act]

end Vec3
end RoboLean
