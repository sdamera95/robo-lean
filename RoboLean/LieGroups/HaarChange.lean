import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.WithDensity
import RoboLean.LieGroups.ExpDerivative

/-!
# The volume of `SO(3)` as a measure in exponential coordinates

MLS Appendix A, §3.3, printed pp. 430–431: the volume of a manifold is defined by integrating a
volume form in local coordinates, where the pull back by a chart is `(det J) Ω` (equation (A.16));
`SO(3)` carries the triple-product volume form and "has a volume of `8π³ rad³`".

**Formalized.** The measure used here is defined, not derived from an intrinsic structure on
`SO(3)`: `so3ExpMeasure` is the image under the exponential chart `ω ↦ e^{ω̂}` of the measure on the
open ball `‖ω‖ < π` of `ℝ³` with density `det J(ω)` with respect to Lebesgue measure, where `J(ω)`
is the spatial Jacobian of the chart (`LieGroup.expSpatialJacobian`, equal to `A(ω)` of Example
A.12 by `LieGroup.expSpatialJacobian_eq`); by `LieGroup.inner_cross_spatial_expHatDeriv` this
density is the triple-product volume form pulled back by the chart, as in equation (A.16). It is
a measure on the `3 × 3` real matrices with the product measurable structure.

* The density is `2(1 − cos‖ω‖)/‖ω‖²` away from `0` and `1` at `0`, and lies in `[0, 1]`
  (`expChartDensity_eq`, `expChartDensity_nonneg`, `expChartDensity_le_one`).
* The measure is concentrated on `SO(3)` (`so3ExpMeasure_compl_specialOrthogonalGroup`) and its
  total mass is `8π²` (`so3ExpMeasure_univ`), the corrected value of the printed `8π³ rad³`.
* The measure is invariant under conjugation `R ↦ Q R Qᵀ` by every rotation `Q`
  (`so3ExpMeasure_map_conj`): conjugation acts on exponential coordinates as `ω ↦ Qω`, which
  preserves Lebesgue measure, the ball and the density.

Limits. The chart is injective on the open ball (`LieGroup.injOn_rotation_exp_ball`) and its
image misses exactly the rotations by `π`, so this is the volume of `SO(3)` in exponential
coordinates; that the measure is a Haar measure of `SO(3)` (invariant under left and right
translation, not only under conjugation) is not proved here, and Mathlib's change-of-variables theorem, which concerns maps
between open sets of one Euclidean space, does not apply to a chart onto a submanifold of the
matrices.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

namespace RoboLean

namespace LieGroup

/-- The density of the volume of `SO(3)` in exponential coordinates (MLS p. 431, equation
(A.16)): the determinant of the spatial Jacobian of `ω ↦ e^{ω̂}`. -/
def expChartDensity (ω : Vec3) : ℝ := (expSpatialJacobian ω).det

/-- The density is `2(1 − cos‖ω‖)/‖ω‖²` away from `0` and `1` at `0` (MLS p. 431 with Example A.12,
p. 413). -/
theorem expChartDensity_eq (ω : Vec3) :
    expChartDensity ω =
      if ‖ω‖ = 0 then 1 else 2 * (1 - Real.cos ‖ω‖) / ‖ω‖ ^ 2 := by
  rw [expChartDensity]
  split_ifs with h
  · rw [norm_eq_zero.mp h, det_expSpatialJacobian_zero]
  · exact det_expSpatialJacobian ω (norm_ne_zero_iff.mp h)

/-- The density is nonnegative (MLS p. 431). -/
theorem expChartDensity_nonneg (ω : Vec3) : 0 ≤ expChartDensity ω := by
  rw [expChartDensity_eq]
  split_ifs
  · exact zero_le_one
  · have := Real.cos_le_one ‖ω‖
    positivity

/-- The density is at most `1`, its value at the identity (MLS p. 431). -/
theorem expChartDensity_le_one (ω : Vec3) : expChartDensity ω ≤ 1 := by
  rw [expChartDensity_eq]
  split_ifs with h
  · exact le_rfl
  · have hc := Real.one_sub_sq_div_two_le_cos (x := ‖ω‖)
    rw [div_le_one (by positivity)]
    linarith

/-- The exponential chart `ω ↦ e^{ω̂}` is measurable into the `3 × 3` matrices with the product
measurable structure (MLS p. 431). -/
theorem measurable_exp_hat : Measurable fun ω : Vec3 => NormedSpace.exp (Vec3.hat ω) := by
  have h (i j : Fin 3) : Continuous fun ω : Vec3 => NormedSpace.exp (Vec3.hat ω) i j :=
    continuous_iff_continuousAt.mpr fun ω => (hasFDerivAt_exp_hat_apply ω i j).continuousAt
  exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => (h i j).measurable

/-- **The volume measure of `SO(3)` in exponential coordinates** (MLS Appendix A, §3.3, p. 431,
equation (A.16)): the image under `ω ↦ e^{ω̂}` of the measure on the open ball `‖ω‖ < π` with
density `det J(ω)` (the spatial Jacobian of the chart) with respect to Lebesgue measure. A
measure on the `3 × 3` real matrices; it is defined here, not an intrinsic Haar measure. -/
def so3ExpMeasure : Measure (Matrix (Fin 3) (Fin 3) ℝ) :=
  Measure.map (fun ω : Vec3 => NormedSpace.exp (Vec3.hat ω))
    ((volume.restrict (Metric.ball (0 : Vec3) Real.pi)).withDensity
      fun ω => ENNReal.ofReal (expChartDensity ω))

/-- `so3ExpMeasure` is concentrated on `SO(3)` (MLS p. 431): the complement of the special
orthogonal group has measure zero. -/
theorem so3ExpMeasure_compl_specialOrthogonalGroup :
    so3ExpMeasure ((Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ))ᶜ) =
      0 := by
  have hclosed : IsClosed
      ((Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ))) := by
    have : ((Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ))) =
        {M | Mᵀ * M = 1} ∩ {M | M.det = 1} := by
      ext M
      simp only [SetLike.mem_coe, Matrix.mem_specialOrthogonalGroup_iff,
        Matrix.mem_orthogonalGroup_iff', Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id)
      continuous_const).inter (isClosed_eq continuous_id.matrix_det continuous_const)
  rw [so3ExpMeasure, Measure.map_apply measurable_exp_hat hclosed.measurableSet.compl]
  have hempty : (fun ω : Vec3 => NormedSpace.exp (Vec3.hat ω)) ⁻¹'
      ((Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ))ᶜ) = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact Rotation.matrix_exp_mem _ (Vec3.hat_transpose ω)
  rw [hempty, measure_empty]

/-- **MLS p. 431, corrected printing: `SO(3)` has volume `8π²` in exponential coordinates.** The
total mass of `so3ExpMeasure` is `8π²` (printed `8π³ rad³`). -/
theorem so3ExpMeasure_univ : so3ExpMeasure Set.univ = ENNReal.ofReal (8 * Real.pi ^ 2) := by
  have hmeas : Measurable expChartDensity := by
    have hf : Measurable fun r : ℝ => if r = 0 then (1 : ℝ) else 2 * (1 - Real.cos r) / r ^ 2 :=
      Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
    have : expChartDensity = (fun r : ℝ => if r = 0 then (1 : ℝ) else
        2 * (1 - Real.cos r) / r ^ 2) ∘ fun ω : Vec3 => ‖ω‖ := by
      funext ω
      exact expChartDensity_eq ω
    rw [this]
    exact hf.comp measurable_norm
  have hint : IntegrableOn expChartDensity (Metric.ball (0 : Vec3) Real.pi) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [expChartDensity_nonneg ω], expChartDensity_le_one ω⟩
  rw [so3ExpMeasure, Measure.map_apply measurable_exp_hat MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => expChartDensity_nonneg ω)]
  congr 1
  rw [← integral_ball_pi_det_expTranslationMatrix]
  refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun ω _ => ?_
  rw [expChartDensity, expSpatialJacobian_eq]

/-- A rotation `ω ↦ Qω` of `ℝ³` as a linear isometry equivalence (supporting definition). -/
private def rotationIsometryEquiv (Q : Rotation) : Vec3 ≃ₗᵢ[ℝ] Vec3 :=
  Q.toLinearIsometry.toLinearIsometryEquiv rfl

private theorem rotationIsometryEquiv_apply (Q : Rotation) (ω : Vec3) :
    rotationIsometryEquiv Q ω = Q.act ω := rfl

/-- `e^{(Qω)^} = Q e^{ω̂} Qᵀ` for a rotation `Q` (MLS Lemma 2.1, eq. (2.7), p. 26, and the conjugation rule of
the matrix exponential; supporting lemma). -/
private theorem exp_hat_act (Q : Rotation) (ω : Vec3) :
    NormedSpace.exp (Vec3.hat (Q.act ω)) = Q.val * NormedSpace.exp (Vec3.hat ω) * Q.valᵀ := by
  have hinv : Q.val⁻¹ = Q.valᵀ := Matrix.inv_eq_left_inv (Rotation.transpose_mul Q)
  have hu : IsUnit Q.val :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by
      have h : (Q.val).det = 1 := Q.property.2
      rw [h]
      exact isUnit_one)
  rw [Vec3.hat_act, ← hinv, Matrix.exp_conj _ _ hu]

/-- **`so3ExpMeasure` is invariant under conjugation by rotations** (MLS Appendix A, §3.3, p. 431;
the conjugation `I_Q(R) = Q R Qᵀ` of Theorem A.8, p. 431, restricted to `SO(3)`): for every
rotation `Q`, the image of `so3ExpMeasure` under `M ↦ Q M Qᵀ` is `so3ExpMeasure`. -/
theorem so3ExpMeasure_map_conj (Q : Rotation) :
    so3ExpMeasure.map (fun M => Q.val * M * Q.valᵀ) = so3ExpMeasure := by
  have hconj : Measurable fun M : Matrix (Fin 3) (Fin 3) ℝ => Q.val * M * Q.valᵀ :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  set e := rotationIsometryEquiv Q
  have he : MeasurePreserving e volume volume := e.measurePreserving
  have hemeas : Measurable e := e.continuous.measurable
  have hcomp : (fun M => Q.val * M * Q.valᵀ) ∘ (fun ω : Vec3 => NormedSpace.exp (Vec3.hat ω)) =
      (fun ω : Vec3 => NormedSpace.exp (Vec3.hat ω)) ∘ e := by
    funext ω
    simp only [Function.comp, e, rotationIsometryEquiv_apply, exp_hat_act]
  rw [so3ExpMeasure, Measure.map_map hconj measurable_exp_hat, hcomp,
    ← Measure.map_map measurable_exp_hat hemeas]
  congr 1
  ext S hS
  rw [Measure.map_apply hemeas hS, withDensity_apply _ (hemeas hS), withDensity_apply _ hS,
    Measure.restrict_restrict (hemeas hS), Measure.restrict_restrict hS]
  have hball : e ⁻¹' Metric.ball (0 : Vec3) Real.pi = Metric.ball 0 Real.pi := by
    ext ω
    simp [e]
  have hρ (ω : Vec3) : expChartDensity (e ω) = expChartDensity ω := by
    rw [expChartDensity_eq, expChartDensity_eq, e.norm_map]
  have key := he.setLIntegral_comp_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun a => ENNReal.ofReal (expChartDensity a)) (S ∩ Metric.ball 0 Real.pi)
  rw [Set.preimage_inter, hball] at key
  simp only [hρ] at key
  exact key

end LieGroup

end RoboLean
