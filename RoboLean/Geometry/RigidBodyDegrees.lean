import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Prod
import Mathlib.Basic.Real.Basic

/-!
# Degrees of freedom of a rigid body in `ℝⁿ` (MLS Chapter 2, Exercise 7)

MLS Chapter 2, Exercise 7, printed p. 74: "A rigid body moving in `ℝ²` has three degrees of
freedom (two components of translation and one of rotation), a rigid body moving in `ℝ³` has six
degrees of freedom (three each of translation and rotation). Show that a rigid body moving in `ℝⁿ`
will have `½(n + n²)` degrees of freedom. How many are translational and how many are
rotational?"

Reading (stated here): the degrees of freedom are the dimension of the space of rigid velocities,
pairs `(v, ω̂)` of a translational velocity `v ∈ ℝⁿ` and an angular velocity `ω̂ ∈ so(n)`, the
skew-symmetric `n × n` matrices (MLS p. 24 defines `SO(n)` and the tangent space of rotations is
the skew-symmetric matrices, eq. (2.6), p. 27, for `n = 3`). Here `so(n)` is Mathlib's
`LieAlgebra.Orthogonal.so (Fin n) ℝ` (`Aᵀ = -A`); its dimension is `n(n - 1)/2 = n.choose 2`
(rotational), the translational part has dimension `n`, and `n + n(n - 1)/2 = (n + n²)/2`.
The identification of degrees of freedom with this dimension is the modeling step; no manifold
structure on `SE(n)` is used.
-/

noncomputable section

open Module

namespace RoboLean

/-- **MLS Exercise 7**, printed p. 74, rotational part: the skew-symmetric `n × n` real matrices
`so(n)` (`Aᵀ = -A`) have dimension `n(n - 1)/2`, written `n.choose 2`. -/
theorem finrank_so (n : ℕ) :
    finrank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ) = n.choose 2 := by
  let e : LieAlgebra.Orthogonal.so (Fin n) ℝ ≃ₗ[ℝ] ({p : Fin n × Fin n // p.1 < p.2} → ℝ) :=
    { toFun := fun A p => (A : Matrix (Fin n) (Fin n) ℝ) p.1.1 p.1.2
      map_add' := fun A B => by
        ext p
        simp
      map_smul' := fun c A => by
        ext p
        simp
      invFun := fun f => ⟨Matrix.of fun i j =>
          if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0, by
        rw [LieAlgebra.Orthogonal.mem_so]
        ext i j
        simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
        by_cases h1 : i < j
        · have h2 : ¬ j < i := lt_asymm h1
          simp [h1, h2]
        · by_cases h2 : j < i
          · simp [h1, h2]
          · simp [h1, h2]⟩
      left_inv := fun A => by
        have hA := (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ _).1 A.2
        apply Subtype.ext
        ext i j
        have hij := congrFun (congrFun hA i) j
        have hii := congrFun (congrFun hA i) i
        simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij hii
        simp only [Matrix.of_apply]
        by_cases h1 : i < j
        · simp [h1]
        · by_cases h2 : j < i
          · simp [h1, h2, hij]
          · have : i = j := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
            subst this
            simp
            linarith
      right_inv := fun f => by
        ext p
        simp [p.2] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  rw [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- **MLS Exercise 7**, printed p. 74: the rigid velocities `(v, ω̂) ∈ ℝⁿ × so(n)` of a body moving
in `ℝⁿ` form a space of dimension `n + n(n - 1)/2` (`n` translational, `n(n - 1)/2` rotational). -/
theorem finrank_rigidVelocity (n : ℕ) :
    finrank ℝ ((Fin n → ℝ) × LieAlgebra.Orthogonal.so (Fin n) ℝ) = n + n.choose 2 := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, finrank_so]

/-- **MLS Exercise 7**, printed p. 74: `n + n(n - 1)/2 = (n + n²)/2`, the printed count; `3` for
`n = 2` and `6` for `n = 3`. -/
theorem rigidBody_degrees_eq (n : ℕ) : n + n.choose 2 = (n + n ^ 2) / 2 := by
  have h : 2 * (n + n.choose 2) = n + n ^ 2 := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith [ih]
  rw [← h, Nat.mul_div_cancel_left _ two_pos]

end RoboLean
