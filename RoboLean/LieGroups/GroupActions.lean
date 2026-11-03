import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import RoboLean.Geometry.TwistAdjoint

/-!
# Actions of matrix groups: orbits, conjugation and the adjoint as a derivative

MLS Appendix A, §2.5, printed pp. 415–416.

* Example A.16: `GL(n, ℝ)` acts on `ℝⁿ` by `(A, x) ↦ A x`, and the orbit of `x ≠ 0` is
  `ℝⁿ \ {0}` (printed "`Rⁿ/{0}`").
* Example A.17: conjugation `I_g(h) = g h g⁻¹` is a left action of `SE(3)` on itself,
  `I_e = id` and `I_g ∘ I_h = I_{gh}`.
* Example A.18: for a matrix group, `Ad_g ξ = T_e I_g ξ = g ξ g⁻¹`: the derivative at the identity
  of `M ↦ g M g⁻¹` on `4 × 4` homogeneous matrices (entrywise norm) sends `ξ̂` to the hat of the
  library's coordinate adjoint (2.58) of `ξ`.

The coadjoint action (Example A.19) and the lifted action (Example A.20) of `SE(3)` are the wrench
transformation and the action on vectors already in the library.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace LieGroup

/-- MLS Example A.16, printed p. 415: the orbit of `x ≠ 0` under the action `(A, x) ↦ A x` of
`GL(n, ℝ)` on `ℝⁿ` is `ℝⁿ \ {0}`. Column vectors. -/
theorem range_mulVec_generalLinearGroup {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    Set.range (fun A : GL (Fin n) ℝ => (A : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = {y | y ≠ 0} := by
  ext y
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨A, rfl⟩ h0
    apply hx
    have := congrArg (fun z => ((A⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) h0
    simpa [Matrix.mulVec_mulVec] using this
  · intro hy
    have hpos {w : Fin n → ℝ} (hw : w ≠ 0) : 0 < w ⬝ᵥ w := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i) :
          (0 : ℝ) ≤ w ⬝ᵥ w) with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hw
    have hs := hpos hx
    set c : ℝ := if x ⬝ᵥ y = 0 then 1 else 0
    set z : Fin n → ℝ := (x ⬝ᵥ x)⁻¹ • (x + c • y)
    have hzx : z ⬝ᵥ x = 1 := by
      simp only [z, smul_dotProduct, add_dotProduct, smul_eq_mul]
      by_cases h : x ⬝ᵥ y = 0
      · simp [c, h, dotProduct_comm y x, hs.ne']
      · simp [c, h, hs.ne']
    have hzy : z ⬝ᵥ y ≠ 0 := by
      simp only [z, smul_dotProduct, add_dotProduct, smul_eq_mul]
      by_cases h : x ⬝ᵥ y = 0
      · simp [c, h, hs.ne', (hpos hy).ne']
      · simp [c, h, hs.ne']
    have hdet : (1 + replicateCol (Fin 1) (y - x) * replicateRow (Fin 1) z).det ≠ 0 := by
      have e := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (y - x) z
      intro h0
      have h1 : 1 + z ⬝ᵥ (y - x) = 0 := e.symm.trans h0
      rw [dotProduct_sub, hzx] at h1
      exact hzy (by linarith)
    have hMx : (1 + replicateCol (Fin 1) (y - x) * replicateRow (Fin 1) z) *ᵥ x = y := by
      ext i
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
      rw [← Matrix.mulVec_mulVec]
      simp [Matrix.mulVec, dotProduct, replicateRow, replicateCol]
      have : ∑ j, z j * x j = 1 := by simpa [dotProduct] using hzx
      rw [this]
      ring
    refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)).unit, ?_⟩
    simpa using hMx

/-- MLS Example A.17, printed p. 415: conjugation by the identity is the identity, `I_e = id`, on
`SE(3)`. -/
theorem conj_one (h : RigidTransform) : 1 * h * 1⁻¹ = h := by
  rw [inv_one, one_mul, mul_one]

/-- MLS Example A.17, printed p. 415: `I_g ∘ I_h = I_{gh}` on `SE(3)`, so conjugation is a left
action, `g (h x h⁻¹) g⁻¹ = (g h) x (g h)⁻¹`. -/
theorem conj_conj (g h x : RigidTransform) :
    g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ := by
  rw [_root_.mul_inv_rev]
  simp only [mul_assoc]

section Adjoint

open scoped Matrix.Norms.Elementwise

/-- MLS Example A.18, printed p. 415: `Ad_g = T_e I_g`. The conjugation `M ↦ g M g⁻¹` of `4 × 4`
homogeneous matrices (entrywise norm) has at the identity the derivative `M ↦ g M g⁻¹`, and on
`ξ̂ ∈ se(3)` it gives the hat of the coordinate adjoint `Ad_g ξ` of equation (2.58), p. 55
(`Twist.hat_adjoint`). Coordinates `(v, ω)`. -/
theorem fderiv_conj_hat (g : RigidTransform) (ξ : Twist) :
    fderiv ℝ (fun M : HomogeneousMatrix => g.toHomogeneous * M * (g⁻¹).toHomogeneous) 1 ξ.hat =
      (Twist.adjoint g ξ).hat := by
  let L : HomogeneousMatrix →L[ℝ] HomogeneousMatrix :=
    { toFun := fun M => g.toHomogeneous * M * (g⁻¹).toHomogeneous
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
      cont := by fun_prop }
  have hL : (fun M : HomogeneousMatrix => g.toHomogeneous * M * (g⁻¹).toHomogeneous) = ⇑L := rfl
  rw [hL, L.fderiv, Twist.hat_adjoint, ← RigidTransform.toHomogeneous_inv]
  rfl

end Adjoint

end LieGroup

end RoboLean
