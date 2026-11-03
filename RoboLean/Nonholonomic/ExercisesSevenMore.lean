import RoboLean.Nonholonomic.Controllability
import RoboLean.Geometry.Hat
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Chapter 7, Exercise 12: the satellite with two rotors at matrix level (MLS pp. 351–352)

MLS Chapter 7, Exercise 12, printed p. 351: a satellite body with two symmetrically attached rotors
whose axes intersect at a point, under conservation of angular momentum. "(a) Assuming that the
initial angular momentum of the system is zero, show that the (body) angular velocity, `ω₁`, of the
satellite body is related to the rotor velocities `(u₁, u₂)` by `ω₁ = b₁u₁ + b₂u₂` (7.21) where
`b₁, b₂ ∈ ℝ³` are constant vectors. Equation (7.21) gives rise to a differential equation in the
rotation group `SO(3)` for the satellite body `Ṙ(t) = R(t)(b̂₁u₁ + b̂₂u₂)` (7.22). (b) Obtain a local
coordinate description of (7.22) using the Euler parameters of `SO(3)` (from Chapter 2) and show
that the resulting system is controllable."

**What is formalized.**
* (a), under a recorded reading of the model: the total angular momentum in the body frame is
  `Mω + u₁c₁ + u₂c₂` with `M` the (invertible) locked inertia and `cᵢ` constant rotor vectors, as
  for rotors of fixed axes; zero momentum gives (7.21) with `bᵢ = −M⁻¹cᵢ`
  (`satellite_bodyVelocity`).
* (7.22) as the drift-free system on the `3 × 3` matrices with the fields `Xᵢ(R) = R b̂ᵢ`
  (`satelliteField`), `Σ uᵢXᵢ(R) = R ω̂₁`.
* (b) at matrix level instead of in Euler parameters: the bracket of the two fields is
  `[X₁, X₂](R) = R (b₁ × b₂)^` (the book's sign, p. 323, with `(a × b)^ = âb̂ − b̂â`), and for
  independent `b₁, b₂` (equivalently `b₁ × b₂ ≠ 0`) the values `R b̂₁`, `R b̂₂`, `R (b₁ × b₂)^`
  span exactly `R · so(3)`, the tangent space of `SO(3)` at a rotation `R` (`satellite_span`).
  This is the rank condition of Theorem 7.5 on `SO(3)`. The passage to the Euler parameters and
  the conclusion "controllable" on the manifold `SO(3)` are not formalized: the library's
  controllability is stated on a normed space, and in the ambient nine-dimensional space of
  matrices the rank is three.

**Conventions.** Vectors are `Fin 3 → ℝ` with Mathlib's cross product `⨯₃`; `hatMat b` is the
book's `b̂` (2.4) (equal to the library's `Vec3.hat`); matrices carry the operator norm of
`Matrix.Norms.Operator` (the bracket does not depend on the norm); the bracket is Mathlib's
`lieBracket`, `[f, g] = (∂g/∂q) f − (∂f/∂q) g` (MLS p. 323).
-/

noncomputable section

open Matrix VectorField
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace Nonholonomic

/-- **MLS eq. (2.4), p. 26, as used in (7.22), p. 351: the skew matrix `b̂`** of a vector
`b ∈ ℝ³`, `b̂ v = b × v`. -/
def hatMat (b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -b 2, b 1; b 2, 0, -b 0; -b 1, b 0, 0]

/-- **MLS eq. (2.4), p. 26:** `hatMat` is the library's hat map `Vec3.hat`. -/
theorem hatMat_eq_hat (b : Fin 3 → ℝ) : hatMat b = Vec3.hat (WithLp.toLp 2 b) := rfl

/-- **MLS eq. (2.4), p. 26:** `b̂` is skew-symmetric. -/
theorem hatMat_transpose (b : Fin 3 → ℝ) : (hatMat b)ᵀ = -hatMat b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hatMat]

/-- **MLS eq. (2.4), p. 26:** the hat map is linear. -/
theorem hatMat_add_smul (a b : Fin 3 → ℝ) (s t : ℝ) :
    hatMat (s • a + t • b) = s • hatMat a + t • hatMat b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hatMat] <;> ring

/-- **MLS Example A.7 (p. 412) and Exercise 12, p. 351: `(a × b)^ = âb̂ − b̂â`.** -/
theorem hatMat_cross (a b : Fin 3 → ℝ) :
    hatMat (a ⨯₃ b) = hatMat a * hatMat b - hatMat b * hatMat a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hatMat, cross_apply] <;> ring

/-- **MLS eq. (2.4), p. 26: every skew-symmetric `3 × 3` matrix is a hat matrix**,
`A = (A₂₁, A₀₂, A₁₀)^`. -/
theorem hatMat_vee {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = -A) :
    hatMat ![A 2 1, A 0 2, A 1 0] = A := by
  have he (i j : Fin 3) : A j i = -A i j := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hA
  have hd (i : Fin 3) : A i i = 0 := by linarith [he i i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hatMat, hd]
  · exact (he 1 0).symm
  · exact (he 2 1).symm
  · exact (he 0 2).symm

/-- **MLS Chapter 7, Exercise 12(a), p. 351, eq. (7.21), under the recorded reading of the
momentum:** if the body-frame angular momentum `Mω + u₁c₁ + u₂c₂` of the satellite and its rotors
vanishes and the locked inertia `M` is invertible, then `ω = b₁u₁ + b₂u₂` with the constant vectors
`bᵢ = −M⁻¹cᵢ`. -/
theorem satellite_bodyVelocity {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsUnit M.det)
    (c₁ c₂ ω : Fin 3 → ℝ) (u₁ u₂ : ℝ) (h : M *ᵥ ω + u₁ • c₁ + u₂ • c₂ = 0) :
    ω = u₁ • -(M⁻¹ *ᵥ c₁) + u₂ • -(M⁻¹ *ᵥ c₂) := by
  have h' : M *ᵥ ω = -(u₁ • c₁ + u₂ • c₂) := by
    rw [← sub_eq_zero, sub_neg_eq_add, ← add_assoc]
    exact h
  have hω : ω = M⁻¹ *ᵥ (M *ᵥ ω) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  rw [hω, h', Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [smul_neg]
  abel

/-- **MLS Chapter 7, Exercise 12, eq. (7.22), p. 351: the field `X_b(R) = R b̂`** on the `3 × 3`
matrices. -/
def satelliteField (b : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  R * hatMat b

/-- **MLS eq. (7.22), p. 351: `Ṙ = R(b̂₁u₁ + b̂₂u₂)`** is the drift-free system with the fields
`(X_{b₁}, X_{b₂})`: `Σ uᵢ X_{bᵢ}(R) = R (u₁b₁ + u₂b₂)^`. -/
theorem satellite_driftFree (b₁ b₂ : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 2 → ℝ) :
    driftFree ![satelliteField b₁, satelliteField b₂] R u = R * hatMat (u 0 • b₁ + u 1 • b₂) := by
  simp [driftFree, Fin.sum_univ_two, satelliteField, hatMat_add_smul, Matrix.mul_add]

/-- The field `X_b` is a continuous linear map (supporting lemma for MLS p. 351). -/
private theorem satelliteField_eq_clm (b : Fin 3 → ℝ) :
    satelliteField b = ⇑((ContinuousLinearMap.mul ℝ (Matrix (Fin 3) (Fin 3) ℝ)).flip (hatMat b)) := by
  funext R
  rfl

/-- **MLS Chapter 7, Exercise 12(b), p. 351, at matrix level: `[X_{b₁}, X_{b₂}](R) = R (b₁ × b₂)^`.**
The bracket of the two fields of (7.22) is the field of the cross product (book's sign, p. 323). -/
theorem satellite_lieBracket (b₁ b₂ : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    lieBracket ℝ (satelliteField b₁) (satelliteField b₂) R = satelliteField (b₁ ⨯₃ b₂) R := by
  rw [lieBracket, satelliteField_eq_clm b₁, satelliteField_eq_clm b₂,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
  rw [satelliteField, hatMat_cross, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]

/-- `b₁, b₂, b₁ × b₂` are independent when `b₁ × b₂ ≠ 0` (supporting lemma for MLS p. 351). -/
private theorem linearIndependent_cross_triple {b₁ b₂ : Fin 3 → ℝ} (hb : b₁ ⨯₃ b₂ ≠ 0) :
    LinearIndependent ℝ ![b₁, b₂, b₁ ⨯₃ b₂] := by
  have hpair := (crossProduct_ne_zero_iff_linearIndependent).1 hb
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have hc : (b₁ ⨯₃ b₂) ⬝ᵥ (b₁ ⨯₃ b₂) ≠ 0 := by
    intro h
    exact hb (dotProduct_self_eq_zero.1 h)
  have h2 : g 2 = 0 := by
    have := congrArg (fun v => (b₁ ⨯₃ b₂) ⬝ᵥ v) hg
    simp only [dotProduct_add, dotProduct_smul, dotProduct_zero, smul_eq_mul] at this
    rw [dotProduct_comm (b₁ ⨯₃ b₂) b₁, dotProduct_comm (b₁ ⨯₃ b₂) b₂, dot_self_cross,
      dot_cross_self] at this
    simp only [mul_zero, zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right hc
  rw [h2, zero_smul, add_zero] at hg
  have h01 := (LinearIndependent.pair_iff.1 hpair) (g 0) (g 1) hg
  intro i
  fin_cases i
  · exact h01.1
  · exact h01.2
  · exact h2

/-- **MLS Chapter 7, Exercise 12(b), p. 351, at matrix level: the rank condition on `SO(3)`.** For
`b₁ × b₂ ≠ 0` (independent `b₁, b₂`), the values `X_{b₁}(R)`, `X_{b₂}(R)` and `[X_{b₁}, X_{b₂}](R)`
span `R · so(3)`: every `R A` with `A` skew-symmetric is in their span, and every element of the span
is such an `R A`. -/
theorem satellite_span {b₁ b₂ : Fin 3 → ℝ} (hb : b₁ ⨯₃ b₂ ≠ 0) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (X : Matrix (Fin 3) (Fin 3) ℝ) :
    X ∈ Submodule.span ℝ {satelliteField b₁ R, satelliteField b₂ R,
      lieBracket ℝ (satelliteField b₁) (satelliteField b₂) R} ↔
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ, Aᵀ = -A ∧ X = R * A := by
  rw [satellite_lieBracket]
  constructor
  · intro hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨hatMat b₁, hatMat_transpose _, rfl⟩
      · exact ⟨hatMat b₂, hatMat_transpose _, rfl⟩
      · exact ⟨hatMat (b₁ ⨯₃ b₂), hatMat_transpose _, rfl⟩
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨A, hA, rfl⟩ := hx
      obtain ⟨B, hB, rfl⟩ := hy
      exact ⟨A + B, by rw [Matrix.transpose_add, hA, hB, neg_add], by rw [Matrix.mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨A, hA, rfl⟩ := hx
      exact ⟨c • A, by rw [Matrix.transpose_smul, hA, smul_neg], by rw [Matrix.mul_smul]⟩
  · rintro ⟨A, hA, rfl⟩
    have htop := (linearIndependent_cross_triple hb).span_eq_top_of_card_eq_finrank'
      (by simp)
    have hv : ![A 2 1, A 0 2, A 1 0] ∈ Submodule.span ℝ (Set.range ![b₁, b₂, b₁ ⨯₃ b₂]) := by
      rw [htop]
      exact Submodule.mem_top
    rw [← hatMat_vee hA]
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union, Set.singleton_union] at hv
    obtain ⟨s, t, r, hst⟩ : ∃ s t r : ℝ, s • b₁ + t • b₂ + r • (b₁ ⨯₃ b₂) =
        ![A 2 1, A 0 2, A 1 0] := by
      rcases Submodule.mem_span_insert.1 hv with ⟨s, y, hy, hsy⟩
      rcases Submodule.mem_span_insert.1 hy with ⟨t, z, hz, htz⟩
      rcases Submodule.mem_span_singleton.1 hz with ⟨r, rfl⟩
      exact ⟨s, t, r, by rw [hsy, htz]; abel⟩
    rw [← hst]
    have hlin : hatMat (s • b₁ + t • b₂ + r • (b₁ ⨯₃ b₂)) =
        s • hatMat b₁ + t • hatMat b₂ + r • hatMat (b₁ ⨯₃ b₂) := by
      rw [show s • b₁ + t • b₂ + r • (b₁ ⨯₃ b₂) = (1 : ℝ) • (s • b₁ + t • b₂) + r • (b₁ ⨯₃ b₂) by
        rw [one_smul], hatMat_add_smul, hatMat_add_smul, one_smul]
    rw [hlin, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [satelliteField]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [satelliteField]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [satelliteField]))

end Nonholonomic
end RoboLean
