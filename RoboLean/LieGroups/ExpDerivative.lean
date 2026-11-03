import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import RoboLean.LieGroups.Haar
import RoboLean.LieGroups.KillingVolumeForm
import RoboLean.Geometry.Rodrigues
import RoboLean.Geometry.RotationExp

/-!
# The derivative of the exponential chart of `SO(3)`

MLS Appendix A, §3.3, printed pp. 430–431, with the matrix `A(ω)` of Example A.12 (p. 413).
The book defines the pull back of a volume form by a map `F` and states that in local coordinates
`F*Ω = (det J) Ω`, `J` the Jacobian of `F` (equation (A.16), p. 431); it then gives a volume form on
`SO(3)` from the triple product (`Ω_SO(3)(ω̂₁, ω̂₂, ω̂₃) = ω₁ · ω₂ × ω₃`) and its total volume. The
exponential coordinates `ω ↦ e^{ω̂}` are the chart in which that volume is computed.

**Formalized.**

* Duhamel's formula for the matrix exponential, for square real matrices of any size:
  `e^{W + sV} e^{−W} = I + s ∫₀¹ e^{t(W + sV)} V e^{−tW} dt` (`exp_add_smul_mul_exp_neg`), and the
  directional derivative `d/ds e^{W + sV}|_{s=0} = (∫₀¹ e^{tW} V e^{−tW} dt) e^{W}`
  (`hasDerivAt_exp_add_smul`).
* `∫₀¹ e^{tω̂} dt = A(ω)` for every `ω ∈ ℝ³` (`integral_exp_smul_hat`), and
  `∫₀¹ e^{tω̂} v̂ e^{−tω̂} dt = (A(ω) v)^` (`integral_exp_hat_mul_hat_mul_exp_neg`).
* The Fréchet derivative of `ω ↦ e^{ω̂}` at every `ω`, including `ω = 0`, is
  `v ↦ (A(ω) v)^ e^{ω̂}` (`hasFDerivAt_exp_hat`), entry by entry with no matrix norm in the
  statement (`hasFDerivAt_exp_hat_apply`).
* The spatial velocity of the chart in a direction `v` is `A(ω) v`
  (`vee_expHatDeriv_mul_transpose`), so the spatial Jacobian of exponential coordinates, the
  matrix whose column `j` is `((∂e^{ω̂}/∂ωⱼ) e^{−ω̂})^∨`, is exactly `A(ω)`
  (`expSpatialJacobian_eq`), with determinant `2(1 − cos‖ω‖)/‖ω‖²` (`det_expSpatialJacobian`).
* Equation (A.16) for this chart: the triple product of the spatial velocities of three
  directions is `det A(ω)` times the triple product of the directions
  (`inner_cross_spatial_expHatDeriv`).

Conventions: column vectors, the right-handed hat map of MLS equation (2.4), the Euclidean norm on
`ℝ³`; the matrix-valued statements use the library's `L^∞` operator norm on matrices, whose
topology is the product topology, and the entrywise statement uses no matrix norm. The statements
concern the coordinate map; nothing is claimed about `SO(3)` as a manifold.
-/

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Operator

namespace RoboLean

namespace LieGroup

section Duhamel

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The exponential along a line is continuous (supporting lemma). -/
private theorem continuous_exp_smul (X : Matrix m m ℝ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const X t).continuousAt

/-- The matrix exponential is continuous (supporting lemma). -/
private theorem continuous_matrix_exp : Continuous (NormedSpace.exp : Matrix m m ℝ → Matrix m m ℝ) :=
  continuous_iff_continuousAt.mpr fun X =>
    ((NormedSpace.exp_analytic (𝕂 := ℝ) X).differentiableAt).continuousAt

/-- **Duhamel's formula, integrated form** (the derivative of the exponential used in MLS
Appendix A, §3.3, p. 431, for the exponential chart). For square real matrices `W`, `V` and a real
`s`, `e^{W + sV} e^{−W} = I + s ∫₀¹ e^{t(W + sV)} V e^{−tW} dt`. -/
theorem exp_add_smul_mul_exp_neg (W V : Matrix m m ℝ) (s : ℝ) :
    NormedSpace.exp (W + s • V) * NormedSpace.exp (-W) =
      1 + s • ∫ t in (0 : ℝ)..1,
        NormedSpace.exp (t • (W + s • V)) * V * NormedSpace.exp (t • (-W)) := by
  have hP (t : ℝ) : HasDerivAt
      (fun u : ℝ => NormedSpace.exp (u • (W + s • V)) * NormedSpace.exp (u • (-W)))
      (s • (NormedSpace.exp (t • (W + s • V)) * V * NormedSpace.exp (t • (-W)))) t := by
    have h := (hasDerivAt_exp_smul_const (W + s • V) t).mul (hasDerivAt_exp_smul_const' (-W) t)
    refine h.congr_deriv ?_
    simp only [mul_add, add_mul, mul_neg, neg_mul, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
    abel
  have hcont : Continuous fun t : ℝ =>
      s • (NormedSpace.exp (t • (W + s • V)) * V * NormedSpace.exp (t • (-W))) :=
    ((((continuous_exp_smul (W + s • V)).mul continuous_const).mul
      (continuous_exp_smul (-W)))).const_smul s
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hP t) (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_smul] at hint
  simp only [one_smul, zero_smul, NormedSpace.exp_zero, mul_one] at hint
  rw [hint]
  abel

/-- **Duhamel's formula, derivative form** (MLS Appendix A, §3.3, p. 431, for the exponential
chart). For square real matrices `W`, `V`, the map `s ↦ e^{W + sV}` has at `s = 0` the derivative
`(∫₀¹ e^{tW} V e^{−tW} dt) e^{W}`. -/
theorem hasDerivAt_exp_add_smul (W V : Matrix m m ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (W + s • V))
      ((∫ t in (0 : ℝ)..1, NormedSpace.exp (t • W) * V * NormedSpace.exp (t • (-W))) *
        NormedSpace.exp W) 0 := by
  set g : ℝ → Matrix m m ℝ := fun s => ∫ t in (0 : ℝ)..1,
    NormedSpace.exp (t • (W + s • V)) * V * NormedSpace.exp (t • (-W))
  have hinv : NormedSpace.exp (-W) * NormedSpace.exp W = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl W).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hf (s : ℝ) : NormedSpace.exp (W + s • V) =
      NormedSpace.exp W + s • (g s * NormedSpace.exp W) := by
    have h := congrArg (· * NormedSpace.exp W) (exp_add_smul_mul_exp_neg W V s)
    rw [mul_assoc, hinv, mul_one] at h
    rw [h, add_mul, one_mul, Matrix.smul_mul]
  have hg : Continuous g := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have h1 : Continuous fun p : ℝ × ℝ => NormedSpace.exp (p.2 • (W + p.1 • V)) :=
      continuous_matrix_exp.comp (continuous_snd.smul (continuous_const.add
        (continuous_fst.smul continuous_const)))
    have h2 : Continuous fun p : ℝ × ℝ => NormedSpace.exp (p.2 • (-W)) :=
      (continuous_exp_smul (-W)).comp continuous_snd
    exact (h1.mul continuous_const).mul h2
  have hg0 : g 0 = ∫ t in (0 : ℝ)..1,
      NormedSpace.exp (t • W) * V * NormedSpace.exp (t • (-W)) := by
    simp only [g, zero_smul, add_zero]
  rw [← hg0]
  refine hasDerivAt_iff_tendsto_slope.mpr ?_
  have hk : Continuous fun s : ℝ => g s * NormedSpace.exp W := hg.mul continuous_const
  refine (hk.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_module, hf s, hf 0, zero_smul, add_zero, add_sub_cancel_left, smul_smul,
    sub_zero, inv_mul_cancel₀ hs, one_smul]

end Duhamel

section ExpChart

/-- The hat map as a continuous linear map `ℝ³ →L[ℝ] ℝ^{3×3}` (MLS equation (2.4), p. 26).
Supporting definition. -/
private def hatCLM : Vec3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := Vec3.hat
      map_add' := Vec3.hat_add
      map_smul' := Vec3.hat_smul }

private theorem hat_zero : Vec3.hat 0 = 0 := by
  simpa using Vec3.hat_smul 0 0

/-- `∫₀¹ sin(rt)/r dt = (1 − cos r)/r²` for `r ≠ 0` (supporting lemma). -/
private theorem integral_sin_mul_div (r : ℝ) (hr : r ≠ 0) :
    ∫ t in (0 : ℝ)..1, Real.sin (r * t) / r = (1 - Real.cos r) / r ^ 2 := by
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hr, integral_sin]
  simp only [mul_zero, mul_one, Real.cos_zero, smul_eq_mul]
  field_simp

/-- `∫₀¹ (1 − cos(rt))/r² dt = (r − sin r)/r³` for `r ≠ 0` (supporting lemma). -/
private theorem integral_one_sub_cos_mul_div (r : ℝ) (hr : r ≠ 0) :
    ∫ t in (0 : ℝ)..1, (1 - Real.cos (r * t)) / r ^ 2 = (r - Real.sin r) / r ^ 3 := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun t => Real.cos (r * t)).intervalIntegrable 0 1),
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hr, integral_cos]
  simp only [mul_zero, mul_one, Real.sin_zero, smul_eq_mul, intervalIntegral.integral_const,
    sub_zero]
  field_simp

/-- **The integral of the rotation exponential is the matrix `A(ω)` of MLS Example A.12, printed
p. 413:** `∫₀¹ e^{tω̂} dt = I + ω̂(1 − cos‖ω‖)/‖ω‖² + ω̂²(‖ω‖ − sin‖ω‖)/‖ω‖³` for every `ω ∈ ℝ³`
(at `ω = 0` both sides are the identity, with Lean's convention `x / 0 = 0` in `A(0)`). -/
theorem integral_exp_smul_hat (ω : Vec3) :
    ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • Vec3.hat ω) = Twist.expTranslationMatrix ω := by
  by_cases hω : ω = 0
  · subst hω
    simp [Twist.expTranslationMatrix, hat_zero]
  · have hr : ‖ω‖ ≠ 0 := norm_ne_zero_iff.mpr hω
    simp_rw [Vec3.exp_hat_of_ne_zero ω hω]
    have h1 : Continuous fun t : ℝ => (Real.sin (‖ω‖ * t) / ‖ω‖) • Vec3.hat ω := by fun_prop
    have h2 : Continuous fun t : ℝ =>
        ((1 - Real.cos (‖ω‖ * t)) / ‖ω‖ ^ 2) • Vec3.hat ω ^ 2 := by fun_prop
    rw [intervalIntegral.integral_add (intervalIntegrable_const.add (h1.intervalIntegrable 0 1))
        (h2.intervalIntegrable 0 1),
      intervalIntegral.integral_add intervalIntegrable_const (h1.intervalIntegrable 0 1),
      intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_smul_const, integral_sin_mul_div _ hr,
      integral_one_sub_cos_mul_div _ hr]
    simp [Twist.expTranslationMatrix]

/-- The rotation exponential `e^{−tω̂}` is the transpose of `e^{tω̂}` (MLS p. 28, eq. (2.11), the
exponential series; supporting lemma). -/
private theorem exp_smul_neg_hat (ω : Vec3) (t : ℝ) :
    NormedSpace.exp (t • (-Vec3.hat ω)) = (NormedSpace.exp (t • Vec3.hat ω))ᵀ := by
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, Vec3.hat_transpose]

/-- **Conjugation by the rotation exponential, integrated** (MLS Example A.12, p. 413, and the
adjoint action `R v̂ Rᵀ = (Rv)^` of Lemma 2.1, eq. (2.7), p. 26):
`∫₀¹ e^{tω̂} v̂ e^{−tω̂} dt = (A(ω) v)^`. -/
theorem integral_exp_hat_mul_hat_mul_exp_neg (ω v : Vec3) :
    ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • Vec3.hat ω) * Vec3.hat v *
        NormedSpace.exp (t • (-Vec3.hat ω)) =
      Vec3.hat (WithLp.toLp 2 (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v)) := by
  let L : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => Vec3.hat (WithLp.toLp 2 (M *ᵥ WithLp.ofLp v))
        map_add' := fun M N => by
          rw [Matrix.add_mulVec, WithLp.toLp_add, Vec3.hat_add]
        map_smul' := fun c M => by
          rw [Matrix.smul_mulVec, WithLp.toLp_smul, Vec3.hat_smul]
          rfl }
  have hpt (t : ℝ) : NormedSpace.exp (t • Vec3.hat ω) * Vec3.hat v *
      NormedSpace.exp (t • (-Vec3.hat ω)) = L (NormedSpace.exp (t • Vec3.hat ω)) := by
    rw [exp_smul_neg_hat]
    have h := Vec3.hat_act (Rotation.exp ω t) v
    rw [Rotation.exp_val] at h
    rw [← h]
    rfl
  simp_rw [hpt]
  have h := L.intervalIntegral_comp_comm
    ((continuous_exp_smul (Vec3.hat ω)).intervalIntegrable (μ := volume) 0 1)
  rw [integral_exp_smul_hat] at h
  exact h

/-- **The derivative of the exponential chart of `SO(3)`** (MLS Appendix A, §3.3, pp. 430–431,
with `A(ω)` of Example A.12, p. 413), as a continuous linear map: `v ↦ (A(ω) v)^ e^{ω̂}`. -/
def expHatDeriv (ω : Vec3) : Vec3 →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Vec3.hat (WithLp.toLp 2 (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v)) *
        NormedSpace.exp (Vec3.hat ω)
      map_add' := fun u v => by
        rw [WithLp.ofLp_add, Matrix.mulVec_add, WithLp.toLp_add, Vec3.hat_add, add_mul]
      map_smul' := fun c v => by
        rw [WithLp.ofLp_smul, Matrix.mulVec_smul, WithLp.toLp_smul, Vec3.hat_smul,
          Matrix.smul_mul]
        rfl }

/-- The value of `expHatDeriv` (MLS pp. 430–431 and Example A.12, p. 413). -/
theorem expHatDeriv_apply (ω v : Vec3) :
    expHatDeriv ω v =
      Vec3.hat (WithLp.toLp 2 (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v)) *
        NormedSpace.exp (Vec3.hat ω) := rfl

/-- **The Fréchet derivative of `ω ↦ e^{ω̂}`** (MLS Appendix A, §3.3, pp. 430–431: the Jacobian
of the exponential chart, with `A(ω)` of Example A.12, p. 413). At every `ω ∈ ℝ³`, including
`ω = 0`, the map `ω ↦ e^{ω̂}` into the `3 × 3` matrices has the derivative
`v ↦ (A(ω) v)^ e^{ω̂}`. Matrices carry the library's `L^∞` operator norm. -/
theorem hasFDerivAt_exp_hat (ω : Vec3) :
    HasFDerivAt (fun x : Vec3 => NormedSpace.exp (Vec3.hat x)) (expHatDeriv ω) ω := by
  have hD : DifferentiableAt ℝ (fun x : Vec3 => NormedSpace.exp (Vec3.hat x)) ω :=
    ((NormedSpace.exp_analytic (𝕂 := ℝ) (Vec3.hat ω)).differentiableAt).comp ω
      hatCLM.differentiableAt
  convert hD.hasFDerivAt using 1
  ext1 v
  have hline : HasDerivAt (fun s : ℝ => ω + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ω
  have h1 := hD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := hasDerivAt_exp_add_smul (Vec3.hat ω) (Vec3.hat v)
  have heq : ((fun x : Vec3 => NormedSpace.exp (Vec3.hat x)) ∘ fun s : ℝ => ω + s • v) =
      fun s : ℝ => NormedSpace.exp (Vec3.hat ω + s • Vec3.hat v) := by
    funext s
    simp [Vec3.hat_add, Vec3.hat_smul]
  rw [heq] at h1
  rw [expHatDeriv_apply, ← integral_exp_hat_mul_hat_mul_exp_neg]
  exact h2.unique h1

/-- The derivative of one entry of the exponential chart, as a continuous linear map
`ℝ³ →L[ℝ] ℝ`: `v ↦ ((A(ω) v)^ e^{ω̂})ᵢⱼ` (MLS pp. 430–431 and Example A.12, p. 413). -/
def expHatDerivEntry (ω : Vec3) (i j : Fin 3) : Vec3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => expHatDeriv ω v i j
      map_add' := fun u v => by rw [map_add]; rfl
      map_smul' := fun c v => by rw [map_smul]; rfl }

/-- The value of `expHatDerivEntry` (MLS pp. 430–431 and Example A.12, p. 413). -/
theorem expHatDerivEntry_apply (ω v : Vec3) (i j : Fin 3) :
    expHatDerivEntry ω i j v =
      (Vec3.hat (WithLp.toLp 2 (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v)) *
        NormedSpace.exp (Vec3.hat ω)) i j := rfl

/-- **The Fréchet derivative of the exponential chart, entry by entry** (MLS Appendix A, §3.3,
pp. 430–431, with `A(ω)` of Example A.12, p. 413): each entry of `ω ↦ e^{ω̂}` has at every `ω`
the derivative `v ↦ ((A(ω) v)^ e^{ω̂})ᵢⱼ`. No matrix norm enters the statement. -/
theorem hasFDerivAt_exp_hat_apply (ω : Vec3) (i j : Fin 3) :
    HasFDerivAt (fun x : Vec3 => NormedSpace.exp (Vec3.hat x) i j) (expHatDerivEntry ω i j) ω := by
  have h := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.hasFDerivAt.comp ω
    (hasFDerivAt_exp_hat ω)
  exact h.congr_fderiv (by ext v; rfl)

/-- `e^{ω̂} (e^{ω̂})ᵀ = I` (MLS equation (2.1), p. 23, for the rotation exponential; supporting
lemma). -/
private theorem exp_hat_mul_transpose (ω : Vec3) :
    NormedSpace.exp (Vec3.hat ω) * (NormedSpace.exp (Vec3.hat ω))ᵀ = 1 := by
  have h := Rotation.matrix_exp_transpose_mul (Vec3.hat ω) (Vec3.hat_transpose ω)
  exact mul_eq_one_comm.mp h

/-- **The spatial velocity of the exponential chart** (MLS Appendix A, §3.3, p. 431, with `A(ω)`
of Example A.12, p. 413): `((D e^{ω̂})(ω) v · (e^{ω̂})ᵀ)^∨ = A(ω) v` for every `ω`, `v ∈ ℝ³`;
the right-translated derivative is the spatial angular velocity `Ṙ R⁻¹` of MLS eq. (2.48), p. 52. -/
theorem vee_expHatDeriv_mul_transpose (ω v : Vec3) :
    Vec3.vee (expHatDeriv ω v * (NormedSpace.exp (Vec3.hat ω))ᵀ) =
      WithLp.toLp 2 (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v) := by
  rw [expHatDeriv_apply, mul_assoc, exp_hat_mul_transpose, mul_one, Vec3.vee_hat]

/-- Product of two quadratic polynomials in a matrix `W` with `W³ = -θ² W` (MLS equation (2.13),
printed p. 28, for `W = ω̂`, `θ = ‖ω‖`). Supporting lemma. -/
private theorem quadratic_mul (W : Matrix (Fin 3) (Fin 3) ℝ) (θ a b c d : ℝ)
    (hW : W ^ 3 = -(θ ^ 2) • W) :
    (1 + a • W + b • W ^ 2) * (1 + d • W + c • W ^ 2) =
      1 + (a + d - θ ^ 2 * (a * c + b * d)) • W + (b + c + a * d - θ ^ 2 * (b * c)) • W ^ 2 := by
  have h4 : W ^ 4 = -(θ ^ 2) • W ^ 2 := by
    rw [show W ^ 4 = W * W ^ 3 by rw [pow_succ'], hW, Matrix.mul_smul, ← pow_two]
  have e1 : W * W = W ^ 2 := (pow_two W).symm
  have e2 : W * W ^ 2 = W ^ 3 := (pow_succ' W 2).symm
  have e3 : W ^ 2 * W = W ^ 3 := (pow_succ W 2).symm
  have e4 : W ^ 2 * W ^ 2 = W ^ 4 := by rw [← pow_add]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, e1, e2, e3, e4, hW, h4, smul_smul]
  module

/-- `(e^{ω̂})ᵀ A(ω) = A(ω)ᵀ` (MLS Example A.12, p. 413; supporting lemma for the body velocity). -/
private theorem exp_hat_transpose_mul_expTranslationMatrix (ω : Vec3) :
    (NormedSpace.exp (Vec3.hat ω))ᵀ * Twist.expTranslationMatrix ω =
      (Twist.expTranslationMatrix ω)ᵀ := by
  by_cases hω : ω = 0
  · subst hω
    simp [Twist.expTranslationMatrix, hat_zero]
  have hr : ‖ω‖ ≠ 0 := norm_ne_zero_iff.mpr hω
  have hT : (NormedSpace.exp (Vec3.hat ω))ᵀ = 1 + (-(Real.sin ‖ω‖ / ‖ω‖)) • Vec3.hat ω +
      ((1 - Real.cos ‖ω‖) / ‖ω‖ ^ 2) • Vec3.hat ω ^ 2 := by
    have h1 := exp_smul_neg_hat ω 1
    rw [one_smul, one_smul] at h1
    rw [← h1, ← neg_one_smul ℝ (Vec3.hat ω), Vec3.exp_hat_of_ne_zero ω hω (-1)]
    simp only [mul_neg, mul_one, Real.sin_neg, Real.cos_neg, neg_div]
  have hAT : (Twist.expTranslationMatrix ω)ᵀ = 1 + (-((1 - Real.cos ‖ω‖) / ‖ω‖ ^ 2)) • Vec3.hat ω +
      ((‖ω‖ - Real.sin ‖ω‖) / ‖ω‖ ^ 3) • Vec3.hat ω ^ 2 := by
    rw [Twist.expTranslationMatrix, Matrix.transpose_add, Matrix.transpose_add,
      Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_pow, Vec3.hat_transpose,
      Matrix.transpose_one, neg_smul, smul_neg, neg_sq, ← sub_eq_add_neg]
  rw [hT, hAT, Twist.expTranslationMatrix, quadratic_mul _ ‖ω‖ _ _ _ _ (Vec3.hat_cube ω)]
  congr 3
  · field_simp
    linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq ‖ω‖
  · field_simp
    ring

/-- **The body velocity of the exponential chart** (MLS Appendix A, §3.3, p. 431, with `A(ω)` of
Example A.12, p. 413): `((e^{ω̂})ᵀ (D e^{ω̂})(ω) v)^∨ = A(ω)ᵀ v`, the left-translated derivative
(the body angular velocity `R⁻¹ Ṙ` of MLS eq. (2.49), p. 52); `A(ω)ᵀ = A(−ω)`. -/
theorem vee_transpose_mul_expHatDeriv (ω v : Vec3) :
    Vec3.vee ((NormedSpace.exp (Vec3.hat ω))ᵀ * expHatDeriv ω v) =
      WithLp.toLp 2 ((Twist.expTranslationMatrix ω)ᵀ *ᵥ WithLp.ofLp v) := by
  have hR : NormedSpace.exp (((-1 : ℝ)) • Vec3.hat ω) = (NormedSpace.exp (Vec3.hat ω))ᵀ := by
    rw [neg_smul, ← smul_neg, exp_smul_neg_hat, one_smul]
  have h := Vec3.hat_act (Rotation.exp ω (-1))
    (WithLp.toLp 2 (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v))
  rw [Rotation.exp_val, hR, Matrix.transpose_transpose] at h
  rw [expHatDeriv_apply, ← mul_assoc, ← h, Vec3.vee_hat]
  apply WithLp.ofLp_injective
  change (NormedSpace.exp ((-1 : ℝ) • Vec3.hat ω)) *ᵥ
    (Twist.expTranslationMatrix ω *ᵥ WithLp.ofLp v) = (Twist.expTranslationMatrix ω)ᵀ *ᵥ WithLp.ofLp v
  rw [hR, Matrix.mulVec_mulVec, exp_hat_transpose_mul_expTranslationMatrix]

/-- The spatial Jacobian of exponential coordinates (MLS Appendix A, §3.3, p. 431, and equation
(3.52), p. 116): the `3 × 3` matrix whose column `j` is `((∂e^{ω̂}/∂ωⱼ)(e^{ω̂})ᵀ)^∨`, with the
partial derivative taken as the Fréchet derivative of `ω ↦ e^{ω̂}` in the coordinate direction
`j`. -/
def expSpatialJacobian (ω : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => Vec3.vee (fderiv ℝ (fun x : Vec3 => NormedSpace.exp (Vec3.hat x)) ω
    (EuclideanSpace.single j 1) * (NormedSpace.exp (Vec3.hat ω))ᵀ) i

/-- **The spatial Jacobian of exponential coordinates is `A(ω)`** (MLS Example A.12, p. 413, read
at p. 431): for every `ω ∈ ℝ³`. -/
theorem expSpatialJacobian_eq (ω : Vec3) : expSpatialJacobian ω = Twist.expTranslationMatrix ω := by
  have hf := (hasFDerivAt_exp_hat ω).fderiv
  ext i j
  simp only [expSpatialJacobian, Matrix.of_apply]
  rw [hf, vee_expHatDeriv_mul_transpose]
  simp [EuclideanSpace.single]

/-- **The Jacobian determinant of exponential coordinates** (MLS p. 431, equation (A.16), with
`A(ω)` of Example A.12, p. 413): `det = 2(1 − cos‖ω‖)/‖ω‖²` for `ω ≠ 0`. -/
theorem det_expSpatialJacobian (ω : Vec3) (hω : ω ≠ 0) :
    (expSpatialJacobian ω).det = 2 * (1 - Real.cos ‖ω‖) / ‖ω‖ ^ 2 := by
  rw [expSpatialJacobian_eq, det_expTranslationMatrix ω hω]

/-- MLS p. 431, equation (A.16), at the identity of the chart: the spatial Jacobian at `ω = 0` has
determinant `1`. -/
theorem det_expSpatialJacobian_zero : (expSpatialJacobian 0).det = 1 := by
  rw [expSpatialJacobian_eq, det_expTranslationMatrix_zero]

/-- The determinant of the rows `M a, M b, M c` is `det M` times that of the rows `a, b, c`
(supporting lemma for equation (A.16), MLS p. 431). -/
private theorem det_rows_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (a b c : Fin 3 → ℝ) :
    Matrix.det ![WithLp.ofLp (WithLp.toLp 2 (M *ᵥ a) : Vec3),
        WithLp.ofLp (WithLp.toLp 2 (M *ᵥ b) : Vec3), WithLp.ofLp (WithLp.toLp 2 (M *ᵥ c) : Vec3)] =
      M.det * Matrix.det ![a, b, c] := by
  have h : Matrix.of ![M *ᵥ a, M *ᵥ b, M *ᵥ c] = Matrix.of ![a, b, c] * Mᵀ := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  change Matrix.det (Matrix.of ![M *ᵥ a, M *ᵥ b, M *ᵥ c]) = M.det * Matrix.det (Matrix.of ![a, b, c])
  rw [h, Matrix.det_mul, Matrix.det_transpose, mul_comm]

/-- **Equation (A.16) for the exponential chart of `SO(3)`** (MLS p. 431, with the triple-product
volume form `Ω_SO(3)(ω̂₁, ω̂₂, ω̂₃) = ω₁ · ω₂ × ω₃` right-translated to `e^{ω̂}`): for directions
`u₁, u₂, u₃ ∈ ℝ³` the triple product of the spatial velocities `((D e^{ω̂})(ω) uₖ (e^{ω̂})ᵀ)^∨` is
`det A(ω)` times `u₁ · u₂ × u₃`. -/
theorem inner_cross_spatial_expHatDeriv (ω u₁ u₂ u₃ : Vec3) :
    inner ℝ (Vec3.vee (expHatDeriv ω u₁ * (NormedSpace.exp (Vec3.hat ω))ᵀ))
        (Vec3.cross (Vec3.vee (expHatDeriv ω u₂ * (NormedSpace.exp (Vec3.hat ω))ᵀ))
          (Vec3.vee (expHatDeriv ω u₃ * (NormedSpace.exp (Vec3.hat ω))ᵀ))) =
      (Twist.expTranslationMatrix ω).det * inner ℝ u₁ (Vec3.cross u₂ u₃) := by
  simp only [vee_expHatDeriv_mul_transpose, Twist.inner_cross_eq_det]
  exact det_rows_mulVec _ _ _ _

/-- **Equation (A.16) for the exponential chart, left-translated form** (MLS p. 431, with the
triple-product volume form left-translated to `e^{ω̂}`): the triple product of the body
velocities `((e^{ω̂})ᵀ (D e^{ω̂})(ω) uₖ)^∨` is `det A(ω)` times `u₁ · u₂ × u₃`. -/
theorem inner_cross_body_expHatDeriv (ω u₁ u₂ u₃ : Vec3) :
    inner ℝ (Vec3.vee ((NormedSpace.exp (Vec3.hat ω))ᵀ * expHatDeriv ω u₁))
        (Vec3.cross (Vec3.vee ((NormedSpace.exp (Vec3.hat ω))ᵀ * expHatDeriv ω u₂))
          (Vec3.vee ((NormedSpace.exp (Vec3.hat ω))ᵀ * expHatDeriv ω u₃))) =
      (Twist.expTranslationMatrix ω).det * inner ℝ u₁ (Vec3.cross u₂ u₃) := by
  simp only [vee_transpose_mul_expHatDeriv, Twist.inner_cross_eq_det]
  rw [det_rows_mulVec, Matrix.det_transpose]

end ExpChart

end LieGroup

end RoboLean
