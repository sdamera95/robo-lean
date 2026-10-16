import RoboLean.Grasp.GeometricParameters
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Geometric parameters of a sphere chart and of a plane chart (MLS Examples 5.6 and 5.7)

MLS Chapter 5, Example 5.6, printed pp. 247–248, and Example 5.7, pp. 252–253.

**What MLS states.** Example 5.6: "For the hemisphere centered about the `x`-axis, we have
`c(u, v) = (ρ cos u cos v, ρ cos u sin v, ρ sin u)` with
`U = {(u, v) : −π/2 < u < π/2, −π < v < π}`", `c_u = ρ(−sin u cos v, −sin u sin v, cos u)`,
`c_v = ρ cos u (−sin v, cos v, 0)`, `c_uᵀ c_v = 0`, and "The curvature, torsion, and metric tensors
are: `K = [[1/ρ, 0], [0, 1/ρ]]`, `M = [[ρ, 0], [0, ρ cos u]]`, `T = [0, −1/ρ tan u]`". Example 5.7
uses the plane chart `c_o(u, v) = (u, v, 0)` with `K_o = 0`, `M_o = I`, `T_o = [0 0]`, and the
sphere chart `c_f(u, v) = (ρ cos u cos v, −ρ cos u sin v, ρ sin u)` on the same domain with
`K_f = diag(1/ρ, 1/ρ)`, `M_f = diag(ρ, ρ cos u_f)`, `T_f = [0, −1/ρ tan u_f]`.

**Formalized.** One family covers both sphere charts: `sphereChart ρ σ` with the orientation sign
`σ` in the second component (`σ = 1` is the chart of Example 5.6, `σ = −1` the chart `c_f` of
Example 5.7). For `ρ > 0` and `σ² = 1` it is an orthogonal chart on the printed domain; its metric
tensor is `diag(ρ, ρ cos u)`, its torsion form `[0, −(1/ρ) tan u]`, its Gauss normal
`n = c_u × c_v/‖c_u × c_v‖ = −(σ/ρ) c`, and its curvature tensor `−(σ/ρ) I`. So with the book's
normal (5.19) the chart of Example 5.6 has `K = −(1/ρ) I` and an inward normal, and the chart of
Example 5.7 has `K_f = (1/ρ) I` and an outward normal (`isOutwardNormal_sphereChart_iff`, for the
ball `{x | ‖x‖² − ρ² ≤ 0}`). The plane chart is orthogonal on all of `ℝ²` with `M = I`, `n = e_z`,
`K = 0` and `T = 0`.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Surface

/-- **The sphere charts of MLS Examples 5.6 (p. 247) and 5.7 (p. 253):**
`c(u, v) = (ρ cos u cos v, σ ρ cos u sin v, ρ sin u)`, with the orientation sign `σ = 1` for Example
5.6 and `σ = −1` for the finger chart `c_f` of Example 5.7. -/
def sphereChart (ρ σ : ℝ) (α : Fin 2 → ℝ) : Vec3 :=
  WithLp.toLp 2 ![ρ * cos (α 0) * cos (α 1), σ * (ρ * cos (α 0) * sin (α 1)), ρ * sin (α 0)]

/-- **The domain of the sphere charts (MLS Example 5.6, p. 248, and Example 5.7, p. 253):**
`U = {(u, v) : −π/2 < u < π/2, −π < v < π}`. -/
def sphereDomain : Set (Fin 2 → ℝ) :=
  {α | -(π / 2) < α 0 ∧ α 0 < π / 2 ∧ -π < α 1 ∧ α 1 < π}

/-- Supporting lemma for the charts of MLS Example 5.6, p. 247: a map into `Fin 3 → ℝ` that is twice
continuously differentiable stays so when its values are read as points of `Vec3`. -/
private lemma contDiff_toLp {F : (Fin 2 → ℝ) → Fin 3 → ℝ} (h : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (fun α => (WithLp.toLp 2 (F α) : Vec3)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp h

/-- Supporting lemma for the charts of MLS Example 5.6, p. 247: the derivative of a curve in `Vec3`
given by three coordinate functions. -/
private lemma hasDerivAt_toLp3 {f g k : ℝ → ℝ} {a b d x : ℝ} (hf : HasDerivAt f a x)
    (hg : HasDerivAt g b x) (hk : HasDerivAt k d x) :
    HasDerivAt (fun s => (WithLp.toLp 2 ![f s, g s, k s] : Vec3)) (WithLp.toLp 2 ![a, b, d]) x := by
  have h := (hf.smul_const (WithLp.toLp 2 ![1, 0, 0] : Vec3)).add
    ((hg.smul_const (WithLp.toLp 2 ![0, 1, 0] : Vec3)).add
      (hk.smul_const (WithLp.toLp 2 ![0, 0, 1] : Vec3)))
  convert h using 1
  · funext s
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp
  · apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp

/-- Supporting lemma for MLS Example 5.6, p. 247: the derivative of `s ↦ cos (a + s)` at `0`. -/
private lemma hasDerivAt_cos_add (a : ℝ) : HasDerivAt (fun s => cos (a + s)) (-sin a) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add a).cos

/-- Supporting lemma for MLS Example 5.6, p. 247: the derivative of `s ↦ sin (a + s)` at `0`. -/
private lemma hasDerivAt_sin_add (a : ℝ) : HasDerivAt (fun s => sin (a + s)) (cos a) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add a).sin

/-- Supporting lemma for MLS Example 5.6, p. 247: the Euclidean norm of a point of `Vec3` from its
coordinates. -/
private lemma norm_toLp3 (a b d : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, d] : Vec3)‖ = √(a ^ 2 + b ^ 2 + d ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

/-- Supporting lemma for MLS Example 5.6, p. 247: the sphere chart is twice continuously
differentiable on all of `ℝ²`. -/
private lemma contDiff_sphereChart (ρ σ : ℝ) : ContDiff ℝ 2 (sphereChart ρ σ) := by
  refine contDiff_toLp (contDiff_pi.mpr fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- Supporting lemma for MLS Example 5.6, p. 247: `c_u` of the sphere chart as a function of
`(u, v)` is twice continuously differentiable. -/
private lemma contDiff_sphereChart_partialU (ρ σ : ℝ) :
    ContDiff ℝ 2 (fun α : Fin 2 → ℝ => (WithLp.toLp 2
      ![-(ρ * sin (α 0) * cos (α 1)), σ * -(ρ * sin (α 0) * sin (α 1)), ρ * cos (α 0)] :
        Vec3)) := by
  refine contDiff_toLp (contDiff_pi.mpr fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- **`c_u` of the sphere chart (MLS Example 5.6, p. 248):**
`c_u = ρ(−sin u cos v, −σ sin u sin v, cos u)`, at every point. -/
theorem partialU_sphereChart (ρ σ : ℝ) (α : Fin 2 → ℝ) :
    partialU (sphereChart ρ σ) α = WithLp.toLp 2
      ![-(ρ * sin (α 0) * cos (α 1)), σ * -(ρ * sin (α 0) * sin (α 1)), ρ * cos (α 0)] := by
  refine partialU_eq_of_hasDerivAt ((contDiff_sphereChart ρ σ).differentiable (by simp) α) ?_
  have h := hasDerivAt_toLp3 (((hasDerivAt_cos_add (α 0)).const_mul ρ).mul_const (cos (α 1)))
    ((((hasDerivAt_cos_add (α 0)).const_mul ρ).mul_const (sin (α 1))).const_mul σ)
    ((hasDerivAt_sin_add (α 0)).const_mul ρ)
  convert h using 1
  · funext s
    simp [sphereChart]
  · congr 1
    ext i
    fin_cases i <;> simp

/-- **`c_v` of the sphere chart (MLS Example 5.6, p. 248):** `c_v = ρ cos u (−sin v, σ cos v, 0)`,
at every point. -/
theorem partialV_sphereChart (ρ σ : ℝ) (α : Fin 2 → ℝ) :
    partialV (sphereChart ρ σ) α = WithLp.toLp 2
      ![-(ρ * cos (α 0) * sin (α 1)), σ * (ρ * cos (α 0) * cos (α 1)), 0] := by
  refine partialV_eq_of_hasDerivAt ((contDiff_sphereChart ρ σ).differentiable (by simp) α) ?_
  have h := hasDerivAt_toLp3 ((hasDerivAt_cos_add (α 1)).const_mul (ρ * cos (α 0)))
    (((hasDerivAt_sin_add (α 1)).const_mul (ρ * cos (α 0))).const_mul σ)
    (hasDerivAt_const (0 : ℝ) (ρ * sin (α 0)))
  convert h using 1
  · funext s
    simp [sphereChart]
  · congr 1
    ext i
    fin_cases i <;> simp

/-- Supporting lemma for MLS Example 5.6, p. 248: the domain `U` of the sphere charts is open. -/
private lemma isOpen_sphereDomain : IsOpen sphereDomain :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) continuous_const)))

/-- Supporting lemma for MLS Example 5.6, p. 248: `cos u > 0` on the domain of the sphere charts. -/
private lemma cos_pos_of_mem_sphereDomain {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    0 < cos (α 0) :=
  cos_pos_of_mem_Ioo ⟨hα.1, hα.2.1⟩

/-- Supporting lemma for MLS Example 5.6, p. 248: `‖c_u‖ = ρ` for the sphere chart. -/
private lemma norm_partialU_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1)
    (α : Fin 2 → ℝ) : ‖partialU (sphereChart ρ σ) α‖ = ρ := by
  rw [partialU_sphereChart, norm_toLp3, sqrt_eq_iff_mul_self_eq_of_pos hρ]
  linear_combination (-(ρ ^ 2 * sin (α 0) ^ 2 * sin (α 1) ^ 2)) * hσ -
    ρ ^ 2 * sin (α 0) ^ 2 * cos_sq_add_sin_sq (α 1) - ρ ^ 2 * sin_sq_add_cos_sq (α 0)

/-- Supporting lemma for MLS Example 5.6, p. 248: `‖c_v‖ = ρ cos u` for the sphere chart on its
domain. -/
private lemma norm_partialV_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1)
    {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    ‖partialV (sphereChart ρ σ) α‖ = ρ * cos (α 0) := by
  rw [partialV_sphereChart, norm_toLp3,
    sqrt_eq_iff_mul_self_eq_of_pos (mul_pos hρ (cos_pos_of_mem_sphereDomain hα))]
  linear_combination (-(ρ ^ 2 * cos (α 0) ^ 2 * cos (α 1) ^ 2)) * hσ -
    ρ ^ 2 * cos (α 0) ^ 2 * sin_sq_add_cos_sq (α 1)

/-- Supporting lemma for MLS Example 5.7, p. 252: the sphere chart takes values on the sphere of
radius `ρ`, `‖c(u, v)‖ = ρ`. -/
private lemma norm_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1) (α : Fin 2 → ℝ) :
    ‖sphereChart ρ σ α‖ = ρ := by
  rw [sphereChart, norm_toLp3, sqrt_eq_iff_mul_self_eq_of_pos hρ]
  linear_combination (-(ρ ^ 2 * cos (α 0) ^ 2 * sin (α 1) ^ 2)) * hσ -
    ρ ^ 2 * cos (α 0) ^ 2 * cos_sq_add_sin_sq (α 1) - ρ ^ 2 * cos_sq_add_sin_sq (α 0)

/-- **The sphere chart is an orthogonal chart (MLS Example 5.6, p. 248: "`c_uᵀ c_v = 0` and hence
the chart is orthogonal")** on its domain, for `ρ > 0` and `σ² = 1`. -/
theorem isOrthogonalChartOn_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1) :
    IsOrthogonalChartOn (sphereChart ρ σ) sphereDomain := by
  refine IsOrthogonalChartOn.of_ne_zero isOpen_sphereDomain
    (contDiff_sphereChart ρ σ).contDiffOn (fun α _ => ?_) (fun α _ => ?_) (fun α hα => ?_)
  · rw [IsOrthogonalAt, partialU_sphereChart, partialV_sphereChart,
      EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, Fin.sum_univ_three]
    linear_combination (-(ρ ^ 2 * cos (α 0) * cos (α 1) * sin (α 0) * sin (α 1))) * hσ
  · rw [← norm_ne_zero_iff, norm_partialU_sphereChart hρ hσ]
    exact hρ.ne'
  · rw [← norm_ne_zero_iff, norm_partialV_sphereChart hρ hσ hα]
    exact (mul_pos hρ (cos_pos_of_mem_sphereDomain hα)).ne'

/-- **The metric tensor of the sphere chart (MLS Example 5.6, p. 248, and Example 5.7, p. 253):**
`M = [[ρ, 0], [0, ρ cos u]]`, for `ρ > 0`, `σ² = 1` and `(u, v)` in the domain. -/
theorem metricTensor_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1) {α : Fin 2 → ℝ}
    (hα : α ∈ sphereDomain) :
    metricTensor (sphereChart ρ σ) α = !![ρ, 0; 0, ρ * cos (α 0)] := by
  rw [metricTensor, norm_partialU_sphereChart hρ hσ, norm_partialV_sphereChart hρ hσ hα]

/-- **The Gauss normal of the sphere chart (MLS eq. (5.19), p. 245, for the charts of Examples 5.6
and 5.7):** `n = c_u × c_v/‖c_u × c_v‖ = −(σ/ρ) c(u, v)`, for `ρ > 0`, `σ² = 1` and `(u, v)` in the
domain; it points into the sphere for `σ = 1` and out of it for `σ = −1`. -/
theorem gaussNormal_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1) {α : Fin 2 → ℝ}
    (hα : α ∈ sphereDomain) :
    gaussNormal (sphereChart ρ σ) α = (-σ / ρ) • sphereChart ρ σ α := by
  have horth := (isOrthogonalChartOn_sphereChart hρ hσ).orthogonal α hα
  have hc := cos_pos_of_mem_sphereDomain hα
  rw [gaussNormal, norm_cross_partial horth, norm_partialU_sphereChart hρ hσ,
    norm_partialV_sphereChart hρ hσ hα, partialU_sphereChart, partialV_sphereChart]
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [Vec3.cross, cross_apply, sphereChart]
    field_simp
  · simp [Vec3.cross, cross_apply, sphereChart]
    field_simp
    linear_combination sin (α 1) * hσ
  · simp [Vec3.cross, cross_apply, sphereChart]
    field_simp
    linear_combination (-(sin (α 0) * σ)) * cos_sq_add_sin_sq (α 1)

/-- **The curvature tensor of the sphere chart (MLS eq. (5.21), p. 245, for the charts of Examples
5.6 and 5.7):** `K = −(σ/ρ) I`, for `ρ > 0`, `σ² = 1` and `(u, v)` in the domain. -/
theorem curvatureTensor_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1) {α : Fin 2 → ℝ}
    (hα : α ∈ sphereDomain) :
    curvatureTensor (sphereChart ρ σ) α = !![-σ / ρ, 0; 0, -σ / ρ] := by
  have hd := (contDiff_sphereChart ρ σ).differentiable (by simp) α
  have horth := (isOrthogonalChartOn_sphereChart hρ hσ).orthogonal α hα
  have hev : gaussNormal (sphereChart ρ σ) =ᶠ[𝓝 α] fun β => (-σ / ρ) • sphereChart ρ σ β :=
    Filter.eventually_of_mem (isOpen_sphereDomain.mem_nhds hα) fun β hβ =>
      gaussNormal_sphereChart hρ hσ hβ
  have hnu : partialU (gaussNormal (sphereChart ρ σ)) α =
      (-σ / ρ) • partialU (sphereChart ρ σ) α := by
    rw [partialU_congr hev, partialU, fderiv_fun_const_smul hd]
    rfl
  have hnv : partialV (gaussNormal (sphereChart ρ σ)) α =
      (-σ / ρ) • partialV (sphereChart ρ σ) α := by
    rw [partialV_congr hev, partialV, fderiv_fun_const_smul hd]
    rfl
  have horth' : inner ℝ (partialV (sphereChart ρ σ) α) (partialU (sphereChart ρ σ) α) = 0 := by
    rw [real_inner_comm]
    exact horth
  have hu := norm_partialU_sphereChart hρ hσ α
  have hv := norm_partialV_sphereChart hρ hσ hα
  have hc := cos_pos_of_mem_sphereDomain hα
  rw [curvatureTensor, hnu, hnv]
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, horth', hu, hv]
  rw [show inner ℝ (partialU (sphereChart ρ σ) α) (partialV (sphereChart ρ σ) α) = 0 from horth]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- **The torsion form of the sphere chart (MLS Example 5.6, p. 248, and Example 5.7, p. 253):**
`T = [0, −(1/ρ) tan u]`, for `ρ > 0`, `σ² = 1` and `(u, v)` in the domain. -/
theorem torsionForm_sphereChart {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1) {α : Fin 2 → ℝ}
    (hα : α ∈ sphereDomain) :
    torsionForm (sphereChart ρ σ) α = ![0, -(1 / ρ) * tan (α 0)] := by
  have hcd : ContDiffAt ℝ 2 (sphereChart ρ σ) α := (contDiff_sphereChart ρ σ).contDiffAt
  have horth := (isOrthogonalChartOn_sphereChart hρ hσ).orthogonal α hα
  have hu0 := (isOrthogonalChartOn_sphereChart hρ hσ).partialU_ne_zero hα
  have hv0 := (isOrthogonalChartOn_sphereChart hρ hσ).partialV_ne_zero hα
  have hdu := (contDiff_sphereChart_partialU ρ σ).differentiable (by simp) α
  have hcu : partialU (sphereChart ρ σ) = fun β => (WithLp.toLp 2
      ![-(ρ * sin (β 0) * cos (β 1)), σ * -(ρ * sin (β 0) * sin (β 1)), ρ * cos (β 0)] : Vec3) :=
    funext (partialU_sphereChart ρ σ)
  have huu : partialU (partialU (sphereChart ρ σ)) α = WithLp.toLp 2
      ![-(ρ * cos (α 0) * cos (α 1)), σ * -(ρ * cos (α 0) * sin (α 1)), -(ρ * sin (α 0))] := by
    rw [hcu]
    refine partialU_eq_of_hasDerivAt hdu ?_
    have h := hasDerivAt_toLp3 ((((hasDerivAt_sin_add (α 0)).const_mul ρ).mul_const
        (cos (α 1))).neg) (((((hasDerivAt_sin_add (α 0)).const_mul ρ).mul_const
        (sin (α 1))).neg).const_mul σ) ((hasDerivAt_cos_add (α 0)).const_mul ρ)
    convert h using 1
    · funext s
      simp
    · congr 1
      ext i
      fin_cases i <;> simp
  have huv : partialV (partialU (sphereChart ρ σ)) α = WithLp.toLp 2
      ![ρ * sin (α 0) * sin (α 1), σ * -(ρ * sin (α 0) * cos (α 1)), 0] := by
    rw [hcu]
    refine partialV_eq_of_hasDerivAt hdu ?_
    have h := hasDerivAt_toLp3 (((hasDerivAt_cos_add (α 1)).const_mul (ρ * sin (α 0))).neg)
      ((((hasDerivAt_sin_add (α 1)).const_mul (ρ * sin (α 0))).neg).const_mul σ)
      (hasDerivAt_const (0 : ℝ) (ρ * cos (α 0)))
    convert h using 1
    · funext s
      simp
    · congr 1
      ext i
      fin_cases i <;> simp
  have hc := cos_pos_of_mem_sphereDomain hα
  rw [torsionForm_eq hcd horth hu0 hv0, huu, huv, norm_partialU_sphereChart hρ hσ,
    norm_partialV_sphereChart hρ hσ hα, partialV_sphereChart, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp]
  funext i
  fin_cases i
  · simp [dotProduct, Fin.sum_univ_three]
    field_simp
    left
    linear_combination (-(ρ ^ 2 * cos (α 0) ^ 2 * cos (α 1) * sin (α 1))) * hσ
  · simp [dotProduct, Fin.sum_univ_three, tan_eq_sin_div_cos]
    field_simp
    linear_combination (-(sin (α 0) * cos (α 1) ^ 2)) * hσ - sin (α 0) * sin_sq_add_cos_sq (α 1)

/-- **The ball of radius `ρ` as a body `{x | h x ≤ 0}` (MLS Example 5.7, p. 252, the spherical
finger):** `h(x) = ‖x‖² − ρ²`. -/
def ballFunction (ρ : ℝ) (x : Vec3) : ℝ := ‖x‖ ^ 2 - ρ ^ 2

/-- **Orientation of the sphere charts (MLS p. 244, "outward pointing unit normal"; p. 255):** for
`ρ > 0`, `σ² = 1` and `(u, v)` in the domain, the Gauss normal of `sphereChart ρ σ` points out of
the ball `{x | ‖x‖² − ρ² ≤ 0}` exactly when `σ = −1` (the chart `c_f` of Example 5.7); for the chart
of Example 5.6 (`σ = 1`) it points into the ball. -/
theorem isOutwardNormal_sphereChart_iff {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ ^ 2 = 1)
    {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    IsOutwardNormal (ballFunction ρ) (sphereChart ρ σ) α ↔ σ = -1 := by
  have hfd : fderiv ℝ (ballFunction ρ) (sphereChart ρ σ α) =
      2 • innerSL ℝ (sphereChart ρ σ α) := by
    change fderiv ℝ (fun x : Vec3 => ‖x‖ ^ 2 - ρ ^ 2) _ = _
    rw [fderiv_sub_const, fderiv_norm_sq_apply]
  rw [IsOutwardNormal, hfd, gaussNormal_sphereChart hρ hσ hα]
  simp only [_root_.smul_apply, innerSL_apply_apply, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_sphereChart hρ hσ]
  have e : 2 • (-σ / ρ * ρ ^ 2) = -2 * σ * ρ := by
    rw [nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [e]
  constructor
  · intro h
    have hs : σ < 0 := by nlinarith
    have h2 : (σ + 1) * (σ - 1) = 0 := by linear_combination hσ
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  · rintro rfl
    linarith

/-- **The plane chart of MLS Example 5.7, p. 253:** `c_o(u, v) = (u, v, 0)`. -/
def planeChart (α : Fin 2 → ℝ) : Vec3 := WithLp.toLp 2 ![α 0, α 1, 0]

/-- Supporting lemma for MLS Example 5.7, p. 253: the plane chart is twice continuously
differentiable on all of `ℝ²`. -/
private lemma contDiff_planeChart : ContDiff ℝ 2 planeChart := by
  refine contDiff_toLp (contDiff_pi.mpr fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- Supporting lemma for MLS Example 5.7, p. 253: `c_u = e_x` for the plane chart. -/
private lemma partialU_planeChart (α : Fin 2 → ℝ) :
    partialU planeChart α = WithLp.toLp 2 ![1, 0, 0] := by
  refine partialU_eq_of_hasDerivAt (contDiff_planeChart.differentiable (by simp) α) ?_
  have h := hasDerivAt_toLp3 ((hasDerivAt_id' (0 : ℝ)).const_add (α 0))
    (hasDerivAt_const (0 : ℝ) (α 1)) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  convert h using 1
  funext s
  simp [planeChart]

/-- Supporting lemma for MLS Example 5.7, p. 253: `c_v = e_y` for the plane chart. -/
private lemma partialV_planeChart (α : Fin 2 → ℝ) :
    partialV planeChart α = WithLp.toLp 2 ![0, 1, 0] := by
  refine partialV_eq_of_hasDerivAt (contDiff_planeChart.differentiable (by simp) α) ?_
  have h := hasDerivAt_toLp3 (hasDerivAt_const (0 : ℝ) (α 0))
    ((hasDerivAt_id' (0 : ℝ)).const_add (α 1)) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  convert h using 1
  funext s
  simp [planeChart]

/-- **The plane chart is an orthogonal chart on all of `ℝ²` (MLS Example 5.7, p. 253).** -/
theorem isOrthogonalChartOn_planeChart : IsOrthogonalChartOn planeChart Set.univ := by
  refine IsOrthogonalChartOn.of_ne_zero isOpen_univ contDiff_planeChart.contDiffOn
    (fun α _ => ?_) (fun α _ => ?_) (fun α _ => ?_)
  · rw [IsOrthogonalAt, partialU_planeChart, partialV_planeChart, EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, Fin.sum_univ_three]
  · rw [← norm_ne_zero_iff, partialU_planeChart, norm_toLp3]
    simp
  · rw [← norm_ne_zero_iff, partialV_planeChart, norm_toLp3]
    simp

/-- **The metric tensor of the plane chart (MLS Example 5.7, p. 253):** `M_o = I`. -/
theorem metricTensor_planeChart (α : Fin 2 → ℝ) : metricTensor planeChart α = 1 := by
  rw [metricTensor, partialU_planeChart, partialV_planeChart, norm_toLp3, norm_toLp3,
    Matrix.one_fin_two]
  simp

/-- **The Gauss normal of the plane chart (MLS eq. (5.19), p. 245, for Example 5.7):**
`n = c_u × c_v = e_z`. -/
theorem gaussNormal_planeChart (α : Fin 2 → ℝ) :
    gaussNormal planeChart α = WithLp.toLp 2 ![0, 0, 1] := by
  rw [gaussNormal, partialU_planeChart, partialV_planeChart]
  have h : Vec3.cross (WithLp.toLp 2 ![1, 0, 0]) (WithLp.toLp 2 ![0, 1, 0]) =
      (WithLp.toLp 2 ![0, 0, 1] : Vec3) := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [Vec3.cross, cross_apply]
  rw [h, norm_toLp3]
  simp

/-- **The curvature tensor of the plane chart (MLS Example 5.7, p. 253):** `K_o = 0`. -/
theorem curvatureTensor_planeChart (α : Fin 2 → ℝ) : curvatureTensor planeChart α = 0 := by
  have hn : gaussNormal planeChart = fun _ => (WithLp.toLp 2 ![0, 0, 1] : Vec3) :=
    funext gaussNormal_planeChart
  apply curvatureTensor_eq_zero <;> simp [partialU, partialV, hn]

/-- **The torsion form of the plane chart (MLS Example 5.7, p. 253):** `T_o = [0 0]`. -/
theorem torsionForm_planeChart (α : Fin 2 → ℝ) : torsionForm planeChart α = 0 := by
  have hx : frameX planeChart = fun _ => (WithLp.toLp 2 ![1, 0, 0] : Vec3) := by
    funext β
    rw [frameX, partialU_planeChart, norm_toLp3]
    simp
  funext i
  fin_cases i <;> simp [torsionForm, partialU, partialV, hx]

/-- **Orientation of the plane chart (MLS Example 5.7, p. 252, the plane under the finger):** its
Gauss normal `e_z` points out of the half-space `{x | x_z ≤ 0}`. -/
theorem isOutwardNormal_planeChart (α : Fin 2 → ℝ) :
    IsOutwardNormal (fun x : Vec3 => x 2) planeChart α := by
  have h : fderiv ℝ (fun x : Vec3 => x 2) (planeChart α) =
      EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).fderiv
  rw [IsOutwardNormal, h, gaussNormal_planeChart]
  simp

end Examples
end RoboLean
