import RoboLean.Grasp.RollingContact
import RoboLean.Examples.SphereChart

/-!
# Rolling contact examples: MLS Examples 5.6 and 5.7, Exercises 13 and 16

MLS Chapter 5: Example 5.6, printed pp. 247–248; Example 5.7, pp. 252–253, eq. (5.39); Exercises 13
and 16, p. 262.

**What MLS states.** Example 5.6 prints, for `c(u, v) = (ρ cos u cos v, ρ cos u sin v, ρ sin u)`,
`c_u = ρ(−sin u cos v, −sin u sin v, cos u)`, `c_v = ρ cos u (−sin v, cos v, 0)`, `c_uᵀ c_v = 0`,
and `K = [[1/ρ, 0], [0, 1/ρ]]`, `M = [[ρ, 0], [0, ρ cos u]]`, `T = [0, −1/ρ tan u]`. Example 5.7 (a
spherical finger of radius `ρ` rolling on a plane, "only allowed to roll on the object and not slip
or twist") takes `c_o(u, v) = (u, v, 0)` and `c_f(u, v) = (ρ cos u cos v, −ρ cos u sin v, ρ sin u)`,
prints `K_o = 0`, `K_f = diag(1/ρ, 1/ρ)`, `M_o = I`, `M_f = diag(ρ, ρ cos u_f)`, `T_o = [0 0]`,
`T_f = [0, −1/ρ tan u_f]`, and "The equations governing the evolution of the contact point are"
`(u̇_f, v̇_f, u̇_o, v̇_o, ψ̇) = (0, sec u_f, −ρ sin ψ, −ρ cos ψ, −tan u_f) ω_x`
`+ (−1, 0, −ρ cos ψ, ρ sin ψ, 0) ω_y` (5.39). Exercise 13: "Give an example of two surfaces in
contact which has singular relative curvature form." Exercise 16: "Derive the equations of contact
for a unit sphere in rolling contact with a sphere of radius `ρ`."

**Formalized.** With the book's Gauss normal (5.19):

* Example 5.6: the printed `c_u`, `c_v`, `c_uᵀ c_v = 0`, `M` and `T` hold; the curvature tensor of
  the printed chart is `K = −(1/ρ) I`, the opposite of the printed `(1/ρ) I`, because `c_u × c_v`
  points into the sphere for this chart (`example56_curvatureTensor`,
  `example56_not_isOutwardNormal`).
* Example 5.7: all printed parameters hold, the finger normal is outward and the plane normal is
  `e_z`; (5.39) follows from Corollary 5.11.1 along every rolling motion of the sphere on the plane
  (`example57_contactRates`), the relative curvature form being `(1/ρ) I`.
* Exercise 13: two planes, and a concave spherical finger on a convex sphere of the same radius (the
  case of p. 251), both with outward normals, have relative curvature form `0` for every contact
  angle (`exercise13_planes`, `exercise13_concave_convex`).
* Exercise 16: a unit sphere (finger) rolling on a sphere of radius `ρ` (object), both with the
  outward chart of Example 5.7, has relative curvature form `(1 + 1/ρ) I`, and its equations of
  contact are `exercise16_contactRates`.

Concrete charts and motions are convention checks for the general theorems; they say nothing about a
physical finger or object.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Surface Rolling

/-! ### Algebra for diagonal parameters -/

/-- The inverse of a diagonal `2 × 2` matrix (supporting lemma for the examples of MLS pp. 252–253
and Exercise 16, p. 262). -/
private theorem inv_diag {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![a⁻¹, 0; 0, b⁻¹] := by
  rw [Matrix.inv_eq_left_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

/-- **A scalar curvature tensor is unchanged by `R_ψ` (MLS p. 250, `K̃_o = R_ψ K_o R_ψ`):** for
`K_o = m I`, `K̃_o = m I` (used for the spheres and planes of MLS pp. 252–253 and Exercises 13 and
16, p. 262). -/
theorem rotatedCurvature_scalar (m ψ : ℝ) :
    rotatedCurvature !![m, 0; 0, m] ψ = !![m, 0; 0, m] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotatedCurvature, angleMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | ring1
    | linear_combination m * sin_sq_add_cos_sq ψ

/-- **The relative curvature form of two scalar curvature tensors (MLS p. 250):**
`K_f + K̃_o = (k + m) I` for `K_f = k I` and `K_o = m I`. -/
theorem relativeCurvature_scalar (k m ψ : ℝ) :
    relativeCurvature !![k, 0; 0, k] !![m, 0; 0, m] ψ = !![k + m, 0; 0, k + m] := by
  rw [relativeCurvature, rotatedCurvature_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- (5.38) for diagonal metric tensors and scalar curvature tensors, solved for the rates
(supporting lemma for MLS Example 5.7, p. 253, and Exercise 16, p. 262). -/
private theorem rates_of_rollingEquations {a b c d k m ψ : ℝ} {Tf To : Fin 2 → ℝ}
    {αf' αo' : Fin 2 → ℝ} {ψ' : ℝ} {V : Twist} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hkm : k + m ≠ 0)
    (h : RollingEquations !![a, 0; 0, b] !![k, 0; 0, k] !![c, 0; 0, d] !![m, 0; 0, m] Tf To ψ
      αf' αo' ψ' V) :
    αf' 0 = -V.angular 1 / (a * (k + m)) ∧ αf' 1 = V.angular 0 / (b * (k + m)) ∧
      αo' 0 = (-(cos ψ * V.angular 1) - sin ψ * V.angular 0) / (c * (k + m)) ∧
      αo' 1 = (sin ψ * V.angular 1 - cos ψ * V.angular 0) / (d * (k + m)) ∧
      ψ' = Tf ⬝ᵥ (!![a, 0; 0, b] *ᵥ αf') + To ⬝ᵥ (!![c, 0; 0, d] *ᵥ αo') := by
  obtain ⟨hf, ho, hψ⟩ := h
  rw [relativeCurvature_scalar, inv_diag ha hb, inv_diag hkm hkm] at hf
  rw [relativeCurvature_scalar, inv_diag hc hd, inv_diag hkm hkm] at ho
  refine ⟨?_, ?_, ?_, ?_, hψ⟩
  · rw [hf]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; field_simp
  · rw [hf]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; field_simp
  · rw [ho]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, angleMatrix]; field_simp; ring
  · rw [ho]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, angleMatrix]; field_simp; ring

/-- The sphere chart has `‖c‖² = ρ²` (supporting lemma for MLS Example 5.6, p. 247, and Exercise 13,
p. 262). -/
private theorem inner_sphereChart_self (ρ σ : ℝ) (hσ : σ ^ 2 = 1) (α : Fin 2 → ℝ) :
    inner ℝ (sphereChart ρ σ α) (sphereChart ρ σ α) = ρ ^ 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [sphereChart, dotProduct, Fin.sum_univ_succ]
  linear_combination (ρ ^ 2 * cos (α 0) ^ 2 * sin (α 1) ^ 2) * hσ +
    ρ ^ 2 * cos (α 0) ^ 2 * sin_sq_add_cos_sq (α 1) + ρ ^ 2 * sin_sq_add_cos_sq (α 0)

/-! ### Example 5.6 -/

/-- **MLS Example 5.6, p. 248: `c_u = ρ(−sin u cos v, −sin u sin v, cos u)`** for the printed chart
`c(u, v) = (ρ cos u cos v, ρ cos u sin v, ρ sin u)` (`sphereChart ρ 1`), at every point. -/
theorem example56_partialU (ρ : ℝ) (α : Fin 2 → ℝ) :
    partialU (sphereChart ρ 1) α = WithLp.toLp 2
      ![-(ρ * sin (α 0) * cos (α 1)), -(ρ * sin (α 0) * sin (α 1)), ρ * cos (α 0)] := by
  rw [partialU_sphereChart]
  simp

/-- **MLS Example 5.6, p. 248: `c_v = ρ cos u (−sin v, cos v, 0)`** for the printed chart, at every
point. -/
theorem example56_partialV (ρ : ℝ) (α : Fin 2 → ℝ) :
    partialV (sphereChart ρ 1) α = WithLp.toLp 2
      ![-(ρ * cos (α 0) * sin (α 1)), ρ * cos (α 0) * cos (α 1), 0] := by
  rw [partialV_sphereChart]
  simp

/-- **MLS Example 5.6, p. 248: "`c_uᵀ c_v = 0` and hence the chart is orthogonal"**, at every point
of the printed chart. -/
theorem example56_isOrthogonalAt (ρ : ℝ) (α : Fin 2 → ℝ) : IsOrthogonalAt (sphereChart ρ 1) α := by
  rw [IsOrthogonalAt, example56_partialU, example56_partialV,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_succ]
  ring

/-- **MLS Example 5.6, p. 248: the metric tensor `M = [[ρ, 0], [0, ρ cos u]]`**, as printed, for
`ρ > 0` and `(u, v)` in the chart domain. -/
theorem example56_metricTensor {ρ : ℝ} (hρ : 0 < ρ) {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    metricTensor (sphereChart ρ 1) α = !![ρ, 0; 0, ρ * cos (α 0)] :=
  metricTensor_sphereChart hρ (by norm_num) hα

/-- **MLS Example 5.6, p. 248: the torsion form `T = [0, −1/ρ tan u]`**, as printed, for `ρ > 0` and
`(u, v)` in the chart domain. -/
theorem example56_torsionForm {ρ : ℝ} (hρ : 0 < ρ) {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    torsionForm (sphereChart ρ 1) α = ![0, -(1 / ρ) * tan (α 0)] :=
  torsionForm_sphereChart hρ (by norm_num) hα

/-- **MLS Example 5.6, p. 248, the curvature tensor with the normal of eq. (5.19):** for the printed
chart, `K = −(1/ρ) I`, not the printed `[[1/ρ, 0], [0, 1/ρ]]`; the normal `c_u × c_v/‖c_u × c_v‖` of
this chart points into the sphere. -/
theorem example56_curvatureTensor {ρ : ℝ} (hρ : 0 < ρ) {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    curvatureTensor (sphereChart ρ 1) α = !![-(1 / ρ), 0; 0, -(1 / ρ)] := by
  rw [curvatureTensor_sphereChart hρ (by norm_num) hα]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neg_div]

/-- **The normal of the chart of MLS Example 5.6 (p. 247) is not outward (MLS p. 244, "outward
pointing unit normal"):** it points into the ball `{x | ‖x‖² − ρ² ≤ 0}`. -/
theorem example56_not_isOutwardNormal {ρ : ℝ} (hρ : 0 < ρ) {α : Fin 2 → ℝ}
    (hα : α ∈ sphereDomain) : ¬ IsOutwardNormal (ballFunction ρ) (sphereChart ρ 1) α := by
  rw [isOutwardNormal_sphereChart_iff hρ (by norm_num) hα]
  norm_num

/-! ### Example 5.7 -/

/-- **MLS Example 5.7, p. 253: the finger parameters as printed:** for the chart
`c_f(u, v) = (ρ cos u cos v, −ρ cos u sin v, ρ sin u)` (`sphereChart ρ (−1)`), `ρ > 0` and `(u, v)`
in the domain, `K_f = diag(1/ρ, 1/ρ)`, `M_f = diag(ρ, ρ cos u_f)`, `T_f = [0, −1/ρ tan u_f]`, and
the Gauss normal points out of the ball of radius `ρ`. -/
theorem example57_finger {ρ : ℝ} (hρ : 0 < ρ) {α : Fin 2 → ℝ} (hα : α ∈ sphereDomain) :
    curvatureTensor (sphereChart ρ (-1)) α = !![1 / ρ, 0; 0, 1 / ρ] ∧
      metricTensor (sphereChart ρ (-1)) α = !![ρ, 0; 0, ρ * cos (α 0)] ∧
      torsionForm (sphereChart ρ (-1)) α = ![0, -(1 / ρ) * tan (α 0)] ∧
      IsOutwardNormal (ballFunction ρ) (sphereChart ρ (-1)) α := by
  refine ⟨?_, metricTensor_sphereChart hρ (by norm_num) hα,
    torsionForm_sphereChart hρ (by norm_num) hα,
    (isOutwardNormal_sphereChart_iff hρ (by norm_num) hα).mpr rfl⟩
  rw [curvatureTensor_sphereChart hρ (by norm_num) hα]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **MLS Example 5.7, p. 253: the object parameters as printed:** for the plane chart
`c_o(u, v) = (u, v, 0)`, `K_o = 0`, `M_o = I`, `T_o = [0 0]`, and the normal `e_z` points out of the
half-space below the plane. -/
theorem example57_object (α : Fin 2 → ℝ) :
    curvatureTensor planeChart α = 0 ∧ metricTensor planeChart α = 1 ∧
      torsionForm planeChart α = 0 ∧ IsOutwardNormal (fun x : Vec3 => x 2) planeChart α :=
  ⟨curvatureTensor_planeChart α, metricTensor_planeChart α, torsionForm_planeChart α,
    isOutwardNormal_planeChart α⟩

/-- **MLS Example 5.7, p. 253: the relative curvature form of the sphere on the plane is
`(1/ρ) I`**, invertible for `ρ > 0`. -/
theorem example57_relativeCurvature {ρ : ℝ} (hρ : 0 < ρ) {αf : Fin 2 → ℝ}
    (hαf : αf ∈ sphereDomain) (αo : Fin 2 → ℝ) (ψ : ℝ) :
    relativeCurvature (curvatureTensor (sphereChart ρ (-1)) αf) (curvatureTensor planeChart αo) ψ =
      !![1 / ρ, 0; 0, 1 / ρ] ∧
    IsUnit (relativeCurvature (curvatureTensor (sphereChart ρ (-1)) αf)
      (curvatureTensor planeChart αo) ψ).det := by
  have h : relativeCurvature (curvatureTensor (sphereChart ρ (-1)) αf)
      (curvatureTensor planeChart αo) ψ = !![1 / ρ, 0; 0, 1 / ρ] := by
    rw [(example57_finger hρ hαf).1, curvatureTensor_planeChart,
      show (0 : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 0; 0, 0] from by ext i j; fin_cases i <;>
        fin_cases j <;> rfl, relativeCurvature_scalar]
    simp
  refine ⟨h, ?_⟩
  rw [h, isUnit_iff_ne_zero, Matrix.det_fin_two_of]
  have : (1 / ρ) ≠ 0 := by positivity
  simpa using this

/-- **MLS Example 5.7, p. 253, eq. (5.39): the sphere rolling on the plane.** Let a pose curve `g`
agree near `t` with the relative pose of contact coordinates `η = (α_f, α_o, ψ)` with actual
derivatives at `t`, for the finger chart `c_f` (radius `ρ > 0`, `α_f(t)` in its domain) and the
plane chart `c_o`. For every derivative `D` of `g`, if the relative velocity
`V_{l_o l_f} = Ad⁻¹_{g_{f c_f}} V^b_of` is a pure rolling (p. 249), then
`(u̇_f, v̇_f, u̇_o, v̇_o, ψ̇) = (0, sec u_f, −ρ sin ψ, −ρ cos ψ, −tan u_f) ω_x`
`+ (−1, 0, −ρ cos ψ, ρ sin ψ, 0) ω_y`, with `(ω_x, ω_y)` the rolling velocities. -/
theorem example57_contactRates {ρ : ℝ} (hρ : 0 < ρ) {αf αo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ}
    {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ sphereDomain) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose (sphereChart ρ (-1)) planeChart (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (sphereChart ρ (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) :
    let ω := (Twist.adjoint (contactFrame (sphereChart ρ (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    ![αf' 0, αf' 1, αo' 0, αo' 1, ψ'] =
      ω 0 • ![0, (cos (αf t 0))⁻¹, -ρ * sin (ψ t), -ρ * cos (ψ t), -tan (αf t 0)] +
        ω 1 • ![-1, 0, -ρ * cos (ψ t), ρ * sin (ψ t), 0] := by
  intro ω
  have hR := rollingEquations_of_hasDerivAt (isOrthogonalChartOn_sphereChart hρ (by norm_num))
    isOrthogonalChartOn_planeChart hαf hαo hψ hft (Set.mem_univ _)
    (example57_relativeCurvature hρ hft (αo t) (ψ t)).2 hg hD hr
  obtain ⟨hK, hM, hT, -⟩ := example57_finger hρ hft
  obtain ⟨hKo, hMo, hTo, -⟩ := example57_object (αo t)
  have hcos : 0 < cos (αf t 0) := cos_pos_of_mem_Ioo ⟨hft.1, hft.2.1⟩
  have hKo' : curvatureTensor planeChart (αo t) = !![0, 0; 0, 0] := by
    rw [hKo]; ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hMo' : metricTensor planeChart (αo t) = !![1, 0; 0, 1] := by
    rw [hMo]; ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hK' : curvatureTensor (sphereChart ρ (-1)) (αf t) = !![1 / ρ, 0; 0, 1 / ρ] := hK
  rw [hK', hM, hT, hKo', hMo', hTo] at hR
  obtain ⟨e0, e1, e2, e3, e4⟩ := rates_of_rollingEquations hρ.ne' (by positivity) one_ne_zero
    one_ne_zero (by simp; positivity) hR
  have hω : ω = (Twist.adjoint (contactFrame (sphereChart ρ (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular := rfl
  rw [← hω] at e0 e1 e2 e3
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hc' : cos (αf t 0) ≠ 0 := hcos.ne'
  funext i
  fin_cases i
  · simp [e0]; field_simp
  · simp [e1]; field_simp
  · simp [e2]; field_simp; ring
  · simp [e3]; field_simp; ring
  · simp [e4, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1, tan_eq_sin_div_cos]
    field_simp

/-! ### Exercise 13 -/

/-- **MLS Exercise 13, p. 262, first example: two planes.** For two plane charts (`K_f = K_o = 0`),
the relative curvature form `K_f + K̃_o` is `0`, hence singular, at every contact angle. -/
theorem exercise13_planes (αf αo : Fin 2 → ℝ) (ψ : ℝ) :
    relativeCurvature (curvatureTensor planeChart αf) (curvatureTensor planeChart αo) ψ = 0 ∧
      ¬ IsUnit (relativeCurvature (curvatureTensor planeChart αf)
        (curvatureTensor planeChart αo) ψ).det := by
  have h : relativeCurvature (curvatureTensor planeChart αf)
      (curvatureTensor planeChart αo) ψ = 0 := by
    simp [relativeCurvature, rotatedCurvature, curvatureTensor_planeChart]
  refine ⟨h, ?_⟩
  rw [h]
  simp

/-- **The concave spherical finger of MLS Exercise 13 (p. 262; the case of p. 251, "one object is
concave and the other is convex, and both have the same radius of curvature"):** the body outside
the ball of radius `ρ`, `{x | ρ² − ‖x‖² ≤ 0}`, has outward Gauss normal for the chart of Example 5.6
(`sphereChart ρ 1`), whose curvature tensor is `−(1/ρ) I`. -/
theorem exercise13_concave_isOutwardNormal {ρ : ℝ} (hρ : 0 < ρ) {α : Fin 2 → ℝ}
    (hα : α ∈ sphereDomain) :
    IsOutwardNormal (fun x : Vec3 => -ballFunction ρ x) (sphereChart ρ 1) α := by
  have hfd : fderiv ℝ (fun x : Vec3 => -ballFunction ρ x) (sphereChart ρ 1 α) =
      -(2 • innerSL ℝ (sphereChart ρ 1 α)) := by
    change fderiv ℝ (fun x : Vec3 => -(‖x‖ ^ 2 - ρ ^ 2)) _ = _
    rw [fderiv_fun_neg, fderiv_sub_const, fderiv_norm_sq_apply]
  rw [IsOutwardNormal, hfd, gaussNormal_sphereChart hρ (by norm_num) hα]
  simp only [_root_.neg_apply, _root_.smul_apply, innerSL_apply_apply,
    real_inner_smul_right, inner_sphereChart_self ρ 1 (by norm_num) α]
  have : (0 : ℝ) < 2 * ρ := by positivity
  rw [nsmul_eq_mul]
  field_simp
  positivity

/-- **MLS Exercise 13, p. 262, second example (the case of p. 251): a concave spherical finger on a
convex sphere of the same radius.** For the finger chart `sphereChart ρ 1` (outward for the body
outside the ball, `exercise13_concave_isOutwardNormal`) and the object chart `sphereChart ρ (−1)`
(outward for the ball), `K_f = −(1/ρ) I`, `K_o = (1/ρ) I`, and the relative curvature form is `0`,
hence singular, at every contact angle. -/
theorem exercise13_concave_convex {ρ : ℝ} (hρ : 0 < ρ) {αf αo : Fin 2 → ℝ}
    (hαf : αf ∈ sphereDomain) (hαo : αo ∈ sphereDomain) (ψ : ℝ) :
    relativeCurvature (curvatureTensor (sphereChart ρ 1) αf)
        (curvatureTensor (sphereChart ρ (-1)) αo) ψ = 0 ∧
      ¬ IsUnit (relativeCurvature (curvatureTensor (sphereChart ρ 1) αf)
        (curvatureTensor (sphereChart ρ (-1)) αo) ψ).det := by
  have h : relativeCurvature (curvatureTensor (sphereChart ρ 1) αf)
      (curvatureTensor (sphereChart ρ (-1)) αo) ψ = 0 := by
    rw [example56_curvatureTensor hρ hαf, (example57_finger hρ hαo).1, relativeCurvature_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨h, ?_⟩
  rw [h]
  simp

/-! ### Exercise 16 -/

/-- **MLS Exercise 16, p. 262: the relative curvature form of a unit sphere rolling on a sphere of
radius `ρ`** (both with the outward chart of Example 5.7, `sphereChart 1 (−1)` for the finger and
`sphereChart ρ (−1)` for the object): `K_f + K̃_o = (1 + 1/ρ) I`, invertible for `ρ > 0`. -/
theorem exercise16_relativeCurvature {ρ : ℝ} (hρ : 0 < ρ) {αf αo : Fin 2 → ℝ}
    (hαf : αf ∈ sphereDomain) (hαo : αo ∈ sphereDomain) (ψ : ℝ) :
    relativeCurvature (curvatureTensor (sphereChart 1 (-1)) αf)
        (curvatureTensor (sphereChart ρ (-1)) αo) ψ = !![1 + 1 / ρ, 0; 0, 1 + 1 / ρ] ∧
      IsUnit (relativeCurvature (curvatureTensor (sphereChart 1 (-1)) αf)
        (curvatureTensor (sphereChart ρ (-1)) αo) ψ).det := by
  have h : relativeCurvature (curvatureTensor (sphereChart 1 (-1)) αf)
      (curvatureTensor (sphereChart ρ (-1)) αo) ψ = !![1 + 1 / ρ, 0; 0, 1 + 1 / ρ] := by
    rw [(example57_finger one_pos hαf).1, (example57_finger hρ hαo).1, relativeCurvature_scalar]
    simp
  refine ⟨h, ?_⟩
  rw [h, isUnit_iff_ne_zero, Matrix.det_fin_two_of]
  have : (1 + 1 / ρ) ≠ 0 := by positivity
  simpa using this

/-- **MLS Exercise 16, p. 262: the equations of contact for a unit sphere rolling on a sphere of
radius `ρ`.** For the finger chart `sphereChart 1 (−1)` and the object chart `sphereChart ρ (−1)`
(`ρ > 0`), contact coordinates `η = (α_f, α_o, ψ)` with actual derivatives at `t` inside the chart
domains, a pose curve `g` agreeing near `t` with `g_of(η(s))`, every derivative `D` of `g` and a
pure rolling relative velocity with rolling velocities `(ω_x, ω_y)`: `u̇_f = −ρ/(ρ + 1) ω_y`,
`v̇_f = ρ/(ρ + 1) sec u_f ω_x`, `u̇_o = −(sin ψ ω_x + cos ψ ω_y)/(ρ + 1)`,
`v̇_o = sec u_o (sin ψ ω_y − cos ψ ω_x)/(ρ + 1)` and
`ψ̇ = −ρ/(ρ + 1) tan u_f ω_x − tan u_o (sin ψ ω_y − cos ψ ω_x)/(ρ + 1)`. -/
theorem exercise16_contactRates {ρ : ℝ} (hρ : 0 < ρ) {αf αo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ}
    {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ sphereDomain) (hot : αo t ∈ sphereDomain)
    {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t,
      g s = relativePose (sphereChart 1 (-1)) (sphereChart ρ (-1)) (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (sphereChart 1 (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) :
    let ω := (Twist.adjoint (contactFrame (sphereChart 1 (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    αf' 0 = -(ρ / (ρ + 1)) * ω 1 ∧ αf' 1 = ρ / (ρ + 1) * (cos (αf t 0))⁻¹ * ω 0 ∧
      αo' 0 = -(sin (ψ t) * ω 0 + cos (ψ t) * ω 1) / (ρ + 1) ∧
      αo' 1 = (cos (αo t 0))⁻¹ * (sin (ψ t) * ω 1 - cos (ψ t) * ω 0) / (ρ + 1) ∧
      ψ' = -(ρ / (ρ + 1)) * tan (αf t 0) * ω 0 -
        tan (αo t 0) * (sin (ψ t) * ω 1 - cos (ψ t) * ω 0) / (ρ + 1) := by
  intro ω
  have hR := rollingEquations_of_hasDerivAt (isOrthogonalChartOn_sphereChart one_pos (by norm_num))
    (isOrthogonalChartOn_sphereChart hρ (by norm_num)) hαf hαo hψ hft hot
    (exercise16_relativeCurvature hρ hft hot (ψ t)).2 hg hD hr
  obtain ⟨hK, hM, hT, -⟩ := example57_finger one_pos hft
  obtain ⟨hKo, hMo, hTo, -⟩ := example57_finger hρ hot
  have hcf : 0 < cos (αf t 0) := cos_pos_of_mem_Ioo ⟨hft.1, hft.2.1⟩
  have hco : 0 < cos (αo t 0) := cos_pos_of_mem_Ioo ⟨hot.1, hot.2.1⟩
  rw [hK, hM, hT, hKo, hMo, hTo] at hR
  obtain ⟨e0, e1, e2, e3, e4⟩ := rates_of_rollingEquations one_ne_zero (by positivity)
    hρ.ne' (by positivity) (by positivity) hR
  have hω : ω = (Twist.adjoint (contactFrame (sphereChart 1 (-1)) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular := rfl
  rw [← hω] at e0 e1 e2 e3
  have hρ1 : ρ + 1 ≠ 0 := by positivity
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hcf' : cos (αf t 0) ≠ 0 := hcf.ne'
  have hco' : cos (αo t 0) ≠ 0 := hco.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; field_simp
  · rw [e1]; field_simp
  · rw [e2]; field_simp; ring
  · rw [e3]; field_simp
  · rw [e4]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e1, e3, tan_eq_sin_div_cos]
    field_simp
    ring

end Examples
end RoboLean
