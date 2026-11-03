import RoboLean.Geometry.EulerAngles
import RoboLean.Kinematics.PadenKahan

/-!
# ZYZ Euler angles at the singular endpoints, and three-axis angles onto `SO(3)`

MLS Chapter 2, printed p. 32, after eq. (2.19): "the converse question of whether the map from
`(α, β, γ) → SO(3)` is surjective is an important one. The answer to this question is
affirmative". The library proves the inverse formulas (2.20) where `sin β ≠ 0`
(`Rotation.zyz_inverse`, on the branch `zyzRadial R > 0`). This file supplies the two endpoint
cases the book does not print, `β = 0` and `β = π` (`zyzRadial R = 0`), with explicit angles,
and with them the surjectivity of the ZYZ map with `β ∈ [0, π]`.

It also proves the three-axis form used for a spherical wrist (MLS p. 96): for unit axes `a`, `b`,
`c` with `a ⊥ b` and `b ⊥ c`, every rotation is `e^{âα} e^{b̂β} e^{ĉγ}`. The ZYZ angles are the
case `a = c = z`, `b = y`; three mutually orthogonal axes, the wrist of the elbow manipulator of
MLS Example 3.2 (p. 89), are another case.

Conventions: `zyz α β γ = Rz(α) Ry(β) Rz(γ)` (eq. (2.19)); `atan2` is `Rotation.atan2` with its
branch `(-π, π]`; the matrix entry `R.val i j` is the book's `r_{i+1, j+1}`.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Rotation

private theorem row_two_sq' (R : Rotation) :
    R.val 2 0 ^ 2 + R.val 2 1 ^ 2 + R.val 2 2 ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) R.mul_transpose
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h

private theorem col_two_sq' (R : Rotation) :
    R.val 0 2 ^ 2 + R.val 1 2 ^ 2 + R.val 2 2 ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) R.transpose_mul
  simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h

private theorem atan2_trig_of_unit (y x : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    Real.cos (atan2 y x) = x ∧ Real.sin (atan2 y x) = y := by
  have hs : √(x ^ 2 + y ^ 2) = 1 := by rw [h, Real.sqrt_one]
  have hc := sqrt_mul_cos_atan2 y x
  have hn := sqrt_mul_sin_atan2 y x
  rw [hs, one_mul] at hc hn
  exact ⟨hc, hn⟩

/-- **MLS p. 32, the endpoint cases of (2.20).** When `zyzRadial R = √(r₃₁² + r₃₂²) = 0`, that is
`sin β = 0`, the formulas (2.20) divide by zero and the book prints none. The middle angle
`β = zyzBeta R = atan2(0, r₃₃)` is then `0` (if `r₃₃ = 1`) or `π` (if `r₃₃ = −1`), and with
`α = 0` and `γ = atan2(r₂₁, r₂₂)` the ZYZ product reconstructs `R`. The choice `α = 0` is one
member of the family of solutions (p. 32: infinitely many representations at `β = 0`). -/
theorem zyz_inverse_of_zyzRadial_eq_zero (R : Rotation) (hr : zyzRadial R = 0) :
    zyz 0 (zyzBeta R) (atan2 (R.val 1 0) (R.val 1 1)) = R := by
  have hsq : R.val 2 0 ^ 2 + R.val 2 1 ^ 2 = 0 := by
    unfold zyzRadial at hr
    exact (Real.sqrt_eq_zero (by positivity)).mp hr
  have h20 : R.val 2 0 = 0 := by nlinarith [sq_nonneg (R.val 2 0), sq_nonneg (R.val 2 1)]
  have h21 : R.val 2 1 = 0 := by nlinarith [sq_nonneg (R.val 2 0), sq_nonneg (R.val 2 1)]
  have h22 : R.val 2 2 ^ 2 = 1 := by nlinarith [row_two_sq' R]
  have hc02 : R.val 0 2 ^ 2 + R.val 1 2 ^ 2 = 0 := by nlinarith [col_two_sq' R]
  have h02 : R.val 0 2 = 0 := by nlinarith [sq_nonneg (R.val 0 2), sq_nonneg (R.val 1 2)]
  have h12 : R.val 1 2 = 0 := by nlinarith [sq_nonneg (R.val 0 2), sq_nonneg (R.val 1 2)]
  have hsb : Real.sin (zyzBeta R) = 0 := by rw [sin_zyzBeta, hr]
  have hcb : Real.cos (zyzBeta R) = R.val 2 2 := cos_zyzBeta R
  let T := zyz 0 (zyzBeta R) 0
  have hcol : T.act zAxis = R.act zAxis := by
    apply WithLp.ofLp_injective
    change (zyz 0 (zyzBeta R) 0).val *ᵥ WithLp.ofLp zAxis = R.val *ᵥ WithLp.ofLp zAxis
    rw [zyz_val]
    ext i
    fin_cases i <;>
      simp [zyzMatrix, zAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hsb, hcb, h02, h12]
  let S := T⁻¹ * R
  have hsfix : S.act zAxis = zAxis := by
    change (T⁻¹ * R).act zAxis = zAxis
    rw [act_mul, ← hcol, inv_act_act]
  have hz : ‖zAxis‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [zAxis, Fin.sum_univ_succ]
  obtain ⟨γ, _, _, hγ⟩ := exists_angle_exp_eq_of_fixed_axis S zAxis hz hsfix
  have hrep : zyz 0 (zyzBeta R) γ = R := by
    have hT : zyz 0 (zyzBeta R) γ = T * exp zAxis γ := by
      simp only [T, zyz, zRotation, exp_zero, mul_one, one_mul]
    rw [hT, hγ]
    simp only [S, mul_inv_cancel_left]
  have h10 : Real.sin γ = R.val 1 0 := by
    have h := congrArg (fun Q : Rotation => Q.val 1 0) hrep
    simpa [zyz_val, zyzMatrix] using h
  have h11 : Real.cos γ = R.val 1 1 := by
    have h := congrArg (fun Q : Rotation => Q.val 1 1) hrep
    simpa [zyz_val, zyzMatrix] using h
  obtain ⟨hcγ, hsγ⟩ := atan2_trig_of_unit (R.val 1 0) (R.val 1 1)
    (by rw [← h10, ← h11]; nlinarith [Real.sin_sq_add_cos_sq γ])
  have hzg : zRotation (atan2 (R.val 1 0) (R.val 1 1)) = zRotation γ := by
    apply Subtype.ext
    simp only [zRotation_val, hcγ, hsγ, h10, h11]
  simpa only [zyz, hzg] using hrep

/-- **MLS p. 32: the ZYZ map is onto `SO(3)`** ("The answer to this question is affirmative"),
with the middle angle in `[0, π]`: (2.20) where `sin β ≠ 0` (`zyz_inverse`) and the endpoint
formulas of `zyz_inverse_of_zyzRadial_eq_zero` where `sin β = 0`. -/
theorem zyz_surjective (R : Rotation) :
    ∃ α β γ : ℝ, 0 ≤ β ∧ β ≤ Real.pi ∧ zyz α β γ = R := by
  have hb : 0 ≤ zyzBeta R ∧ zyzBeta R ≤ Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr (Real.sqrt_nonneg _), Complex.arg_le_pi _⟩
  rcases (Real.sqrt_nonneg (R.val 2 0 ^ 2 + R.val 2 1 ^ 2)).lt_or_eq with h | h
  · exact ⟨_, _, _, hb.1, hb.2, zyz_inverse R h⟩
  · exact ⟨_, _, _, hb.1, hb.2, zyz_inverse_of_zyzRadial_eq_zero R h.symm⟩

private theorem gram_aux (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ)
    (hb : b0 * b0 + b1 * b1 + b2 * b2 = 1) (hc : c0 * c0 + c1 * c1 + c2 * c2 = 1)
    (hbc : b0 * c0 + b1 * c1 + b2 * c2 = 0) :
    (a0 * (b1 * c2 - b2 * c1) + a1 * (b2 * c0 - b0 * c2) + a2 * (b0 * c1 - b1 * c0)) ^ 2 =
      (a0 * a0 + a1 * a1 + a2 * a2) - (a0 * b0 + a1 * b1 + a2 * b2) ^ 2 -
        (a0 * c0 + a1 * c1 + a2 * c2) ^ 2 := by
  linear_combination
    ((a0 * a0 + a1 * a1 + a2 * a2) * (c0 * c0 + c1 * c1 + c2 * c2) -
      (a0 * c0 + a1 * c1 + a2 * c2) ^ 2) * hb +
    ((a0 * a0 + a1 * a1 + a2 * a2) - (a0 * b0 + a1 * b1 + a2 * b2) ^ 2) * hc +
    (2 * (a0 * b0 + a1 * b1 + a2 * b2) * (a0 * c0 + a1 * c1 + a2 * c2) -
      (a0 * a0 + a1 * a1 + a2 * a2) * (b0 * c0 + b1 * c1 + b2 * c2)) * hbc

private theorem inner_cross_sq_of_orthonormal (a b c : Vec3) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hbc : inner ℝ b c = 0) :
    inner ℝ a (Vec3.cross b c) ^ 2 = ‖a‖ ^ 2 - inner ℝ a b ^ 2 - inner ℝ a c ^ 2 := by
  have hb2 : ‖b‖ ^ 2 = 1 := by rw [hb, one_pow]
  have hc2 : ‖c‖ ^ 2 = 1 := by rw [hc, one_pow]
  rw [← real_inner_self_eq_norm_sq] at hb2 hc2 ⊢
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    Fin.sum_univ_three, Vec3.cross_coordinates, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    at hb2 hc2 hbc ⊢
  have h := gram_aux (WithLp.ofLp a 0) (WithLp.ofLp a 1) (WithLp.ofLp a 2)
    (WithLp.ofLp b 0) (WithLp.ofLp b 1) (WithLp.ofLp b 2) (WithLp.ofLp c 0) (WithLp.ofLp c 1)
    (WithLp.ofLp c 2) (by linear_combination hb2) (by linear_combination hc2)
    (by linear_combination hbc)
  linear_combination h

/-- **Three-axis angles onto `SO(3)`, the orientation part of a spherical wrist (MLS p. 96).**
For unit axes `a`, `b`, `c` with `a ⊥ b` and `b ⊥ c`, every rotation is
`e^{âα} e^{b̂β} e^{ĉγ}` for some real angles. MLS p. 96 states that "a spherical wrist can be used
to achieve any orientation" for "three orthogonal revolute axes which intersect at a point"; the
proof needs only the two orthogonalities, so it covers the ZYZ case `a = c` and mutually orthogonal
axes alike. Proof: `β` makes `aᵀ e^{b̂β} c = aᵀ R c` (the left side is `cos(β − φ)` for a fixed `φ`),
Subproblem 1 (MLS p. 100) gives `α` with `e^{âα} e^{b̂β} c = R c`, and the remaining rotation fixes
`c`, hence is `e^{ĉγ}`. -/
theorem exists_exp_mul_exp_mul_exp_eq {a b c : Vec3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hab : inner ℝ a b = 0) (hbc : inner ℝ b c = 0) (R : Rotation) :
    ∃ α β γ : ℝ, exp a α * exp b β * exp c γ = R := by
  have hamp : inner ℝ a c ^ 2 + inner ℝ a (Vec3.cross b c) ^ 2 = 1 := by
    have h := inner_cross_sq_of_orthonormal a b c hb hc hbc
    rw [ha, hab] at h
    linarith
  obtain ⟨φ, -, -, hcφ, hsφ⟩ := exists_angle_of_sq_add_sq_eq_one _ _ hamp
  set t := R.act c with ht
  have hk : |inner ℝ a t| ≤ 1 := by
    have h := abs_real_inner_le_norm a t
    rwa [ha, ht, norm_act, hc, one_mul] at h
  set β := φ + Real.arccos (inner ℝ a t) with hβ
  have hp : inner ℝ a ((exp b β).act c) = inner ℝ a t := by
    rw [exp_act_of_inner_eq_zero b c hb hbc, inner_add_right, inner_smul_right,
      inner_smul_right, ← hcφ, ← hsφ]
    have h := Real.cos_sub β φ
    rw [hβ, add_sub_cancel_left, Real.cos_arccos (abs_le.mp hk).1 (abs_le.mp hk).2] at h
    rw [hβ]
    linarith
  have hnp : ‖(exp b β).act c‖ = ‖t‖ := by rw [norm_act, ht, norm_act]
  obtain ⟨α, hα⟩ := (PadenKahan.exists_exp_act_eq_iff ha ((exp b β).act c) t).mpr
    ⟨hp, by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Vec3.norm_perp_sq ha, Vec3.norm_perp_sq ha, hp,
        hnp]⟩
  set X := exp a α * exp b β with hX
  have hfix : (X⁻¹ * R).act c = c := by
    rw [act_mul, ← ht, ← hα]
    have : (exp a α).act ((exp b β).act c) = X.act c := by rw [hX, act_mul]
    rw [this, inv_act_act]
  obtain ⟨γ, -, -, hγ⟩ := exists_angle_exp_eq_of_fixed_axis (X⁻¹ * R) c hc hfix
  exact ⟨α, β, γ, by rw [hγ, mul_inv_cancel_left]⟩

end Rotation
end RoboLean
