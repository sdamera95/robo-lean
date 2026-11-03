import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import RoboLean.LieGroups.ExponentialClosedForms

/-!
# The volume of `SO(3)` in exponential coordinates

MLS Appendix A, §3.3, printed p. 431. A volume form on `SO(3)` is defined from the Lie bracket and
the Killing form, `Ω_SO(3)(ω̂₁, ω̂₂, ω̂₃) = −¼⟨ω̂₁, [ω̂₂, ω̂₃]⟩_K = ω₁ · ω₂ × ω₃`, the triple product
(`RoboLean.Twist.neg_quarter_killingForm_bracket`), extended by left translation; "with this
definition, `SO(3)` has a volume of `8π³ rad³`". Example A.28 (p. 432) uses the same factor in the
bound `V_M ≤ (4/3)π(L_M)³ · 8π³`.

Statements. The matrix `A(ω) = I + ω̂(1 − cos‖ω‖)/‖ω‖² + ω̂²(‖ω‖ − sin‖ω‖)/‖ω‖³` of Example A.12
(p. 413, `Twist.expTranslationMatrix`) has determinant `2(1 − cos‖ω‖)/‖ω‖²` for `ω ≠ 0` and `1` at
`ω = 0`; its integral over the open ball `‖ω‖ < π` of `ℝ³` (Lebesgue measure) is `8π²`.

Reading and limits. `A(ω)` is the left Jacobian of `SO(3)`: the derivative of `ω ↦ exp(ω̂)`,
translated back to the identity, is `A(ω)` or `A(−ω) = A(ω)ᵀ` according to the side, so the
triple-product volume form pulled back to exponential coordinates has the density `det A(ω)`.
That identification of the derivative, and the fact that `exp` maps the ball injectively onto
`SO(3)` up to the rotations by `π` (a null set), are the standard steps from this integral to the
volume of `SO(3)`; neither the derivative identity nor the change of variables on `SO(3)` is
proved here (the injectivity on the ball is `RoboLean.LieGroup.injOn_rotation_exp_ball`). The
integral itself is exact. Corrected printing, through this reading: the volume is `8π²`, not the
printed `8π³ rad³`; the integral `∫ sin β dα dβ dγ = 8π²` over ZYZ Euler angles gives the same
value.
-/

noncomputable section

open Matrix MeasureTheory

namespace RoboLean

namespace LieGroup

/-- The determinant of `I + aω̂ + bω̂²` is `(1 − b‖ω‖²)² + a²‖ω‖²`. -/
private theorem det_one_add_hat (a b : ℝ) (ω : Vec3) :
    (1 + a • Vec3.hat ω + b • Vec3.hat ω ^ 2).det = (1 - b * ‖ω‖ ^ 2) ^ 2 + a ^ 2 * ‖ω‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Matrix.det_fin_three]
  simp [Vec3.hat, sq]
  ring

/-- `det A(ω)` as a function of `r = ‖ω‖`. -/
private def radial (r : ℝ) : ℝ :=
  (1 - (r - Real.sin r) / r ^ 3 * r ^ 2) ^ 2 + ((1 - Real.cos r) / r ^ 2) ^ 2 * r ^ 2

private theorem det_eq_radial (ω : Vec3) : (Twist.expTranslationMatrix ω).det = radial ‖ω‖ := by
  unfold Twist.expTranslationMatrix radial
  rw [det_one_add_hat]

private theorem sq_mul_radial (r : ℝ) (hr : r ≠ 0) : r ^ 2 * radial r = 2 - 2 * Real.cos r := by
  have h1 : 1 - (r - Real.sin r) / r ^ 3 * r ^ 2 = Real.sin r / r := by
    field_simp
    ring
  have h2 : r ^ 2 * radial r = Real.sin r ^ 2 + (1 - Real.cos r) ^ 2 := by
    unfold radial
    rw [h1]
    field_simp
  rw [h2]
  linear_combination Real.sin_sq_add_cos_sq r

/-- **The density of the volume of `SO(3)` in exponential coordinates** (MLS p. 431, with the matrix
`A(ω)` of Example A.12, p. 413): `det A(ω) = 2(1 − cos‖ω‖)/‖ω‖²` for `ω ≠ 0`. -/
theorem det_expTranslationMatrix (ω : Vec3) (hω : ω ≠ 0) :
    (Twist.expTranslationMatrix ω).det = 2 * (1 - Real.cos ‖ω‖) / ‖ω‖ ^ 2 := by
  have hr : ‖ω‖ ≠ 0 := norm_ne_zero_iff.mpr hω
  rw [det_eq_radial, eq_div_iff (pow_ne_zero 2 hr), mul_comm, sq_mul_radial _ hr]
  ring

/-- MLS Example A.12, p. 413: at `ω = 0` the matrix `A(0)` is the identity, with determinant `1`
(the limit of the density at the identity). -/
theorem det_expTranslationMatrix_zero : (Twist.expTranslationMatrix 0).det = 1 := by
  rw [det_eq_radial]
  simp [radial]

/-- **MLS p. 431, corrected printing: the volume of `SO(3)` is `8π²`.** The integral of the density
`det A(ω)` over the ball `‖ω‖ < π` of exponential coordinates is `8π²` (printed `8π³ rad³`). -/
theorem integral_ball_pi_det_expTranslationMatrix :
    ∫ ω in Metric.ball (0 : Vec3) Real.pi, (Twist.expTranslationMatrix ω).det = 8 * Real.pi ^ 2 := by
  let h : ℝ → ℝ := fun r => if r < Real.pi then radial r else 0
  have hind : (Metric.ball (0 : Vec3) Real.pi).indicator
      (fun ω => (Twist.expTranslationMatrix ω).det) = fun ω => h ‖ω‖ := by
    funext ω
    by_cases hω : ‖ω‖ < Real.pi
    · rw [Set.indicator_of_mem (by simpa using hω)]
      simp [h, hω, det_eq_radial]
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      simp [h, hω]
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
    integral_fun_norm_addHaar volume h, finrank_euclideanSpace_fin]
  have hrad : Set.EqOn (fun y : ℝ => y ^ (3 - 1) • h y)
      ((Set.Iio Real.pi).indicator fun y => 2 - 2 * Real.cos y) (Set.Ioi 0) := by
    intro y hy
    simp only [smul_eq_mul, h, Set.indicator_apply, Set.mem_Iio]
    split_ifs with hyπ
    · exact sq_mul_radial y (ne_of_gt hy)
    · simp
  rw [setIntegral_congr_fun measurableSet_Ioi hrad, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_cos.const_mul 2),
    intervalIntegral.integral_const_mul, integral_cos]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Real.sin_pi, Real.sin_zero,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, nsmul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  push_cast
  ring

end LieGroup

end RoboLean
