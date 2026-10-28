import RoboLean.Grasp.RollingContact
import RoboLean.Examples.SphereChart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Surfaces of revolution: MLS Exercises 14 and 15

MLS Chapter 5, Exercise 14, printed p. 262: "Calculate the geometric parameters for an ellipsoid, a
parabaloid, and a torus." Exercise 15, p. 262: "The figure below shows an elliptic fingertip in
contact with a flat object. The principal axes of the ellipse have length `a`, `b`, and `c`,
respectively. (a) Give an orthonormal coordinate chart for the fingertip around the point of contact
as shown in the figure. (b) Assume the fingertip is in rolling contact with the object. Derive the
equations of contact. (c) Compute the velocity of the fingertip relative to the object which
satisfies rolling constraint and produces a contact velocity of `α̇_o = (0, v)`, `v ∈ ℝ`." The
geometric parameters are those of MLS §6.1 (pp. 244–246): the metric tensor (5.18), the curvature
tensor (5.21) and the torsion form (5.24) of an orthogonal chart.

**Formalized.** A profile `u ↦ (r(u), z(u))` with `r > 0` turned about the `z`-axis gives the chart
`c(u, v) = (r(u) cos v, r(u) sin v, z(u))`, orthogonal wherever `r > 0` and `(r', z') ≠ 0`. With the
book's normal (5.19) and `s = √(r'² + z'²)`:
`n = (−z' cos v, −z' sin v, r')/s`, `M = diag(s, r)`,
`K = diag((r'' z' − r' z'')/s³, −z'/(r s))` and `T = [0, r'/(r s)]`. The orientation of `n` is
set by the direction in which the profile is traversed; each instance below is traversed so that
`n` points out of the solid (`IsOutwardNormal`), and a convex instance then has positive curvature.

* Exercise 14: the ellipsoid of revolution with equatorial semi-axis `a` and polar semi-axis `c`
  (profile `(a cos u, −c sin u)`), the paraboloid `z = −(x² + y²)/(2a)` (profile `(u, −u²/(2a))`,
  `u > 0`) and the torus with radii `R > a > 0` (profile `(R + a cos u, −a sin u)`).
* Exercise 15 for an ellipsoid with two equal axes, `a = b`: the chart above with the contact point
  `(−a, 0, 0)` at `(u, v) = (0, π)`; the equations of contact against the plane chart of MLS
  Example 5.7 under rolling (Corollary 5.11.1, p. 252); and the rolling velocities that produce
  `α̇_o = (0, v)`.

The exercises give no charts. For an ellipsoid with three different axes the usual chart
`(a cos u cos v, b cos u sin v, c sin u)` has `c_u · c_v = (a² − b²) sin u cos u sin v cos v`, so it
is not orthogonal on any open set unless `a = b`; an orthogonal chart exists near the contact point
(MLS Theorem 5.9, p. 244), but none in elementary closed form is given here, so the three-axis case
is not formalized. "Orthonormal coordinate chart" is read as orthogonal chart: a chart with
`‖c_u‖ = ‖c_v‖ = 1` everywhere would be an isometry from the plane, and no such isometry onto a
curved ellipsoid exists. Concrete charts are convention checks for the general theorems; they say
nothing about a physical fingertip.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Surface Rolling

/-! ### Surfaces of revolution -/

/-- **The chart of a surface of revolution about the `z`-axis (for MLS Exercise 14, p. 262):**
`c(u, v) = (r(u) cos v, r(u) sin v, z(u))` for a profile `u ↦ (r(u), z(u))` in the `xz`-plane. -/
def revolutionChart (r z : ℝ → ℝ) (α : Fin 2 → ℝ) : Vec3 :=
  WithLp.toLp 2 ![r (α 0) * cos (α 1), r (α 0) * sin (α 1), z (α 0)]

/-- **The speed of the profile, `s = √(r'² + z'²)` (for MLS Exercise 14, p. 262):** the length of
`c_u` for the chart of a surface of revolution. -/
def profileSpeed (r z : ℝ → ℝ) (u : ℝ) : ℝ := √(deriv r u ^ 2 + deriv z u ^ 2)

/-- **The domain of the chart of a surface of revolution (MLS pp. 243–244, conditions of a regular
orthogonal chart):** the points with `r(u) > 0` and `(r'(u), z'(u)) ≠ 0`. -/
def revolutionDomain (r z : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {α | 0 < r (α 0) ∧ 0 < deriv r (α 0) ^ 2 + deriv z (α 0) ^ 2}

variable {r z : ℝ → ℝ} {α : Fin 2 → ℝ}

/-- Supporting lemma for the chart of MLS Exercise 14, p. 262: a map into `Fin 3 → ℝ` that is twice
continuously differentiable stays so when its values are read as points of `Vec3`. -/
private lemma contDiff_toLp {F : (Fin 2 → ℝ) → Fin 3 → ℝ} (h : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (fun α => (WithLp.toLp 2 (F α) : Vec3)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp h

/-- Supporting lemma for the chart of MLS Exercise 14, p. 262: a differentiable map into `Fin 3 → ℝ`
stays differentiable when its values are read as points of `Vec3`. -/
private lemma differentiable_toLp {F : (Fin 2 → ℝ) → Fin 3 → ℝ} (h : Differentiable ℝ F) :
    Differentiable ℝ (fun α => (WithLp.toLp 2 (F α) : Vec3)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.differentiable.comp h

/-- Supporting lemma for the chart of MLS Exercise 14, p. 262: the derivative of a curve in `Vec3`
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

/-- Supporting lemma for MLS eq. (5.18), p. 244: the Euclidean norm of a point of `Vec3` from its
coordinates. -/
private lemma norm_toLp3 (a b d : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, d] : Vec3)‖ = √(a ^ 2 + b ^ 2 + d ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

/-- Supporting lemma for MLS p. 243 (`c_u := ∂c/∂u`): the derivative of `s ↦ f(a + s)` at `0` is
`f'(a)` for a differentiable `f`. -/
private lemma hasDerivAt_shift {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a : ℝ) :
    HasDerivAt (fun s => f (a + s)) (deriv f a) 0 :=
  HasDerivAt.comp_const_add a 0 (by simpa using (hf a).hasDerivAt)

/-- Supporting lemma for MLS p. 243: the derivative of `s ↦ cos (a + s)` at `0`. -/
private lemma hasDerivAt_cos_add (a : ℝ) : HasDerivAt (fun s => cos (a + s)) (-sin a) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add a).cos

/-- Supporting lemma for MLS p. 243: the derivative of `s ↦ sin (a + s)` at `0`. -/
private lemma hasDerivAt_sin_add (a : ℝ) : HasDerivAt (fun s => sin (a + s)) (cos a) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add a).sin

/-- Supporting lemma for MLS Exercise 14, p. 262: the chart of a surface of revolution with a twice
continuously differentiable profile is twice continuously differentiable on all of `ℝ²`. -/
private lemma contDiff_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z) :
    ContDiff ℝ 2 (revolutionChart r z) := by
  refine contDiff_toLp (contDiff_pi.mpr fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- Supporting lemma for MLS Exercise 14, p. 262: `c_u = (r' cos v, r' sin v, z')` for the chart of
a surface of revolution, at every point. -/
private lemma partialU_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : partialU (revolutionChart r z) α = WithLp.toLp 2
      ![deriv r (α 0) * cos (α 1), deriv r (α 0) * sin (α 1), deriv z (α 0)] := by
  refine partialU_eq_of_hasDerivAt ((contDiff_revolutionChart hr hz).differentiable
    (by simp) α) ?_
  have h := hasDerivAt_toLp3 ((hasDerivAt_shift (hr.differentiable (by simp)) (α 0)).mul_const
    (cos (α 1))) ((hasDerivAt_shift (hr.differentiable (by simp)) (α 0)).mul_const (sin (α 1)))
    (hasDerivAt_shift (hz.differentiable (by simp)) (α 0))
  convert h using 1
  funext s
  simp [revolutionChart]

/-- Supporting lemma for MLS Exercise 14, p. 262: `c_v = (−r sin v, r cos v, 0)` for the chart of a
surface of revolution, at every point. -/
private lemma partialV_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : partialV (revolutionChart r z) α = WithLp.toLp 2
      ![-(r (α 0) * sin (α 1)), r (α 0) * cos (α 1), 0] := by
  refine partialV_eq_of_hasDerivAt ((contDiff_revolutionChart hr hz).differentiable
    (by simp) α) ?_
  have h := hasDerivAt_toLp3 ((hasDerivAt_cos_add (α 1)).const_mul (r (α 0)))
    ((hasDerivAt_sin_add (α 1)).const_mul (r (α 0))) (hasDerivAt_const (0 : ℝ) (z (α 0)))
  convert h using 1
  · funext s
    simp [revolutionChart]
  · congr 1
    ext i
    fin_cases i <;> simp

/-- Supporting lemma for MLS eqs. (5.21) and (5.24), pp. 245–246:
`c_uu = (r'' cos v, r'' sin v, z'')` for the chart of a surface of revolution. -/
private lemma partialU_partialU_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : partialU (partialU (revolutionChart r z)) α = WithLp.toLp 2
      ![deriv (deriv r) (α 0) * cos (α 1), deriv (deriv r) (α 0) * sin (α 1),
        deriv (deriv z) (α 0)] := by
  have hr2 := hr.differentiable_deriv_two
  have hz2 := hz.differentiable_deriv_two
  rw [funext (partialU_revolutionChart hr hz)]
  refine partialU_eq_of_hasDerivAt (differentiable_toLp ?_ α) ?_
  · refine differentiable_pi.mpr fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have h := hasDerivAt_toLp3 ((hasDerivAt_shift hr2 (α 0)).mul_const (cos (α 1)))
    ((hasDerivAt_shift hr2 (α 0)).mul_const (sin (α 1))) (hasDerivAt_shift hz2 (α 0))
  convert h using 1
  funext s
  simp

/-- Supporting lemma for MLS eqs. (5.21) and (5.24), pp. 245–246: `c_uv = (−r' sin v, r' cos v, 0)`
for the chart of a surface of revolution. -/
private lemma partialV_partialU_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : partialV (partialU (revolutionChart r z)) α = WithLp.toLp 2
      ![-(deriv r (α 0) * sin (α 1)), deriv r (α 0) * cos (α 1), 0] := by
  have hr2 := hr.differentiable_deriv_two
  have hz2 := hz.differentiable_deriv_two
  rw [funext (partialU_revolutionChart hr hz)]
  refine partialV_eq_of_hasDerivAt (differentiable_toLp ?_ α) ?_
  · refine differentiable_pi.mpr fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have h := hasDerivAt_toLp3 ((hasDerivAt_cos_add (α 1)).const_mul (deriv r (α 0)))
    ((hasDerivAt_sin_add (α 1)).const_mul (deriv r (α 0)))
    (hasDerivAt_const (0 : ℝ) (deriv z (α 0)))
  convert h using 1
  · funext s
    simp
  · congr 1
    ext i
    fin_cases i <;> simp

/-- Supporting lemma for MLS eq. (5.21), p. 245: `c_vv = (−r cos v, −r sin v, 0)` for the chart of a
surface of revolution. -/
private lemma partialV_partialV_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : partialV (partialV (revolutionChart r z)) α = WithLp.toLp 2
      ![-(r (α 0) * cos (α 1)), -(r (α 0) * sin (α 1)), 0] := by
  have hr1 : Differentiable ℝ r := hr.differentiable (by simp)
  rw [funext (partialV_revolutionChart hr hz)]
  refine partialV_eq_of_hasDerivAt (differentiable_toLp ?_ α) ?_
  · refine differentiable_pi.mpr fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have h := hasDerivAt_toLp3 (((hasDerivAt_sin_add (α 1)).const_mul (r (α 0))).neg)
    ((hasDerivAt_cos_add (α 1)).const_mul (r (α 0))) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  convert h using 1
  · funext s
    simp
  · congr 1
    ext i
    fin_cases i <;> simp

/-- Supporting lemma for MLS p. 243 (an open chart domain): the domain of the chart of a surface of
revolution is open for a twice continuously differentiable profile. -/
private lemma isOpen_revolutionDomain (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z) :
    IsOpen (revolutionDomain r z) := by
  have hr1 : Continuous (deriv r) := hr.continuous_deriv (by norm_num)
  have hz1 : Continuous (deriv z) := hz.continuous_deriv (by norm_num)
  exact (isOpen_lt continuous_const (hr.continuous.comp (continuous_apply 0))).inter
    (isOpen_lt continuous_const (((hr1.comp (continuous_apply 0)).pow 2).add
      ((hz1.comp (continuous_apply 0)).pow 2)))

/-- Supporting lemma for MLS eq. (5.18), p. 244: the profile speed is positive on the chart
domain. -/
private lemma profileSpeed_pos (hα : α ∈ revolutionDomain r z) : 0 < profileSpeed r z (α 0) :=
  Real.sqrt_pos.mpr hα.2

/-- Supporting lemma for MLS eq. (5.18), p. 244: `‖c_u‖ = s` for the chart of a surface of
revolution. -/
private lemma norm_partialU_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : ‖partialU (revolutionChart r z) α‖ = profileSpeed r z (α 0) := by
  rw [partialU_revolutionChart hr hz, norm_toLp3, profileSpeed]
  congr 1
  linear_combination deriv r (α 0) ^ 2 * cos_sq_add_sin_sq (α 1)

/-- Supporting lemma for MLS eq. (5.18), p. 244: `‖c_v‖ = r` for the chart of a surface of
revolution, where `r > 0`. -/
private lemma norm_partialV_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (hα : α ∈ revolutionDomain r z) : ‖partialV (revolutionChart r z) α‖ = r (α 0) := by
  rw [partialV_revolutionChart hr hz, norm_toLp3, sqrt_eq_iff_mul_self_eq_of_pos hα.1]
  linear_combination -(r (α 0) ^ 2 * sin_sq_add_cos_sq (α 1))

/-- Supporting lemma for MLS p. 244: `c_u · c_v = 0` for the chart of a surface of revolution, at
every point. -/
private lemma isOrthogonalAt_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (α : Fin 2 → ℝ) : IsOrthogonalAt (revolutionChart r z) α := by
  rw [IsOrthogonalAt, partialU_revolutionChart hr hz, partialV_revolutionChart hr hz,
    EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- **The chart of a surface of revolution is an orthogonal chart (MLS p. 244)** on its domain, for
a twice continuously differentiable profile. -/
theorem isOrthogonalChartOn_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z) :
    IsOrthogonalChartOn (revolutionChart r z) (revolutionDomain r z) := by
  refine IsOrthogonalChartOn.of_ne_zero (isOpen_revolutionDomain hr hz)
    (contDiff_revolutionChart hr hz).contDiffOn
    (fun α _ => isOrthogonalAt_revolutionChart hr hz α) (fun α hα => ?_) (fun α hα => ?_)
  · rw [← norm_ne_zero_iff, norm_partialU_revolutionChart hr hz]
    exact (profileSpeed_pos hα).ne'
  · rw [← norm_ne_zero_iff, norm_partialV_revolutionChart hr hz hα]
    exact hα.1.ne'

/-- **The metric tensor of a surface of revolution (MLS eq. (5.18), p. 244):**
`M = diag(s, r)` with `s = √(r'² + z'²)`. -/
theorem metricTensor_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (hα : α ∈ revolutionDomain r z) :
    metricTensor (revolutionChart r z) α = !![profileSpeed r z (α 0), 0; 0, r (α 0)] := by
  rw [metricTensor, norm_partialU_revolutionChart hr hz, norm_partialV_revolutionChart hr hz hα]

/-- **The Gauss normal of a surface of revolution (MLS eq. (5.19), p. 245):**
`n = (−z' cos v, −z' sin v, r')/s`. -/
theorem gaussNormal_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (hα : α ∈ revolutionDomain r z) :
    gaussNormal (revolutionChart r z) α = (profileSpeed r z (α 0))⁻¹ •
      WithLp.toLp 2 ![-(deriv z (α 0) * cos (α 1)), -(deriv z (α 0) * sin (α 1)),
        deriv r (α 0)] := by
  have hs := profileSpeed_pos hα
  have hr0 := hα.1
  rw [gaussNormal, norm_cross_partial (isOrthogonalAt_revolutionChart hr hz α),
    norm_partialU_revolutionChart hr hz, norm_partialV_revolutionChart hr hz hα,
    partialU_revolutionChart hr hz, partialV_revolutionChart hr hz]
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [Vec3.cross, cross_apply]
    field_simp
  · simp [Vec3.cross, cross_apply]
    field_simp
  · simp [Vec3.cross, cross_apply]
    field_simp
    linear_combination deriv r (α 0) * cos_sq_add_sin_sq (α 1)

/-- Supporting lemma for MLS eq. (5.21), p. 245: if `p ⟂ n` at every point, then
`p · n_u = −p_u · n`. -/
private lemma inner_partialU_gaussNormal {c p : (Fin 2 → ℝ) → Vec3} (hp : DifferentiableAt ℝ p α)
    (hn : DifferentiableAt ℝ (gaussNormal c) α)
    (h0 : ∀ β, inner ℝ (p β) (gaussNormal c β) = 0) :
    inner ℝ (p α) (partialU (gaussNormal c) α) = -inner ℝ (partialU p α) (gaussNormal c α) := by
  have d := fderiv_inner_apply ℝ hp hn (Pi.single 0 1)
  rw [show (fun β => inner ℝ (p β) (gaussNormal c β)) = fun _ => (0 : ℝ) from funext h0,
    fderiv_const_apply] at d
  change (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 0 1) =
    inner ℝ (p α) (partialU (gaussNormal c) α) + inner ℝ (partialU p α) (gaussNormal c α) at d
  simp only [_root_.zero_apply] at d
  linarith

/-- Supporting lemma for MLS eq. (5.21), p. 245: if `p ⟂ n` at every point, then
`p · n_v = −p_v · n`. -/
private lemma inner_partialV_gaussNormal {c p : (Fin 2 → ℝ) → Vec3} (hp : DifferentiableAt ℝ p α)
    (hn : DifferentiableAt ℝ (gaussNormal c) α)
    (h0 : ∀ β, inner ℝ (p β) (gaussNormal c β) = 0) :
    inner ℝ (p α) (partialV (gaussNormal c) α) = -inner ℝ (partialV p α) (gaussNormal c α) := by
  have d := fderiv_inner_apply ℝ hp hn (Pi.single 1 1)
  rw [show (fun β => inner ℝ (p β) (gaussNormal c β)) = fun _ => (0 : ℝ) from funext h0,
    fderiv_const_apply] at d
  change (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 1 1) =
    inner ℝ (p α) (partialV (gaussNormal c) α) + inner ℝ (partialV p α) (gaussNormal c α) at d
  simp only [_root_.zero_apply] at d
  linarith

/-- **The curvature tensor of a surface of revolution (MLS eq. (5.21), p. 245):**
`K = diag((r'' z' − r' z'')/s³, −z'/(r s))`, with the normal of `gaussNormal_revolutionChart`. -/
theorem curvatureTensor_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (hα : α ∈ revolutionDomain r z) :
    curvatureTensor (revolutionChart r z) α =
      !![(deriv (deriv r) (α 0) * deriv z (α 0) - deriv r (α 0) * deriv (deriv z) (α 0)) /
          profileSpeed r z (α 0) ^ 3, 0;
        0, -deriv z (α 0) / (r (α 0) * profileSpeed r z (α 0))] := by
  have hc : ContDiffAt ℝ 2 (revolutionChart r z) α := (contDiff_revolutionChart hr hz).contDiffAt
  have hO := isOrthogonalChartOn_revolutionChart hr hz
  have hn := differentiableAt_gaussNormal hc (cross_partial_ne_zero (hO.orthogonal α hα)
    (hO.partialU_ne_zero hα) (hO.partialV_ne_zero hα))
  have zu : ∀ β, inner ℝ (partialU (revolutionChart r z) β)
      (gaussNormal (revolutionChart r z) β) = 0 := fun β => by
    rw [real_inner_comm]; exact inner_gaussNormal_partialU
  have zv : ∀ β, inner ℝ (partialV (revolutionChart r z) β)
      (gaussNormal (revolutionChart r z) β) = 0 := fun β => by
    rw [real_inner_comm]; exact inner_gaussNormal_partialV
  have hs := profileSpeed_pos hα
  have hr0 := hα.1
  rw [curvatureTensor, inner_partialU_gaussNormal (differentiableAt_partialU hc) hn zu,
    inner_partialV_gaussNormal (differentiableAt_partialU hc) hn zu,
    inner_partialU_gaussNormal (differentiableAt_partialV hc) hn zv,
    inner_partialV_gaussNormal (differentiableAt_partialV hc) hn zv, ← partialV_partialU hc,
    partialU_partialU_revolutionChart hr hz, partialV_partialU_revolutionChart hr hz,
    partialV_partialV_revolutionChart hr hz, gaussNormal_revolutionChart hr hz hα,
    norm_partialU_revolutionChart hr hz, norm_partialV_revolutionChart hr hz hα]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inner_smul_right, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three] <;>
    field_simp
  · linear_combination deriv z (α 0) * deriv (deriv r) (α 0) * cos_sq_add_sin_sq (α 1)
  · norm_num
  · norm_num
  · linear_combination -deriv z (α 0) * cos_sq_add_sin_sq (α 1)

/-- **The torsion form of a surface of revolution (MLS eq. (5.24), p. 246):**
`T = [0, r'/(r s)]`. -/
theorem torsionForm_revolutionChart (hr : ContDiff ℝ 2 r) (hz : ContDiff ℝ 2 z)
    (hα : α ∈ revolutionDomain r z) :
    torsionForm (revolutionChart r z) α =
      ![0, deriv r (α 0) / (r (α 0) * profileSpeed r z (α 0))] := by
  have hc : ContDiffAt ℝ 2 (revolutionChart r z) α := (contDiff_revolutionChart hr hz).contDiffAt
  have hO := isOrthogonalChartOn_revolutionChart hr hz
  have hs := profileSpeed_pos hα
  have hr0 := hα.1
  rw [torsionForm_eq hc (hO.orthogonal α hα) (hO.partialU_ne_zero hα) (hO.partialV_ne_zero hα),
    partialU_partialU_revolutionChart hr hz, partialV_partialU_revolutionChart hr hz,
    norm_partialU_revolutionChart hr hz, norm_partialV_revolutionChart hr hz hα,
    partialV_revolutionChart hr hz, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp]
  funext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_three] <;> field_simp
  · norm_num
  · linear_combination deriv r (α 0) * sin_sq_add_cos_sq (α 1)

/-! ### Exercise 14: an ellipsoid of revolution -/

/-- **The ellipsoid of revolution with equatorial semi-axis `a` and polar semi-axis `c` (MLS
Exercise 14, p. 262):** the profile `(a cos u, −c sin u)` turned about the `z`-axis,
`c(u, v) = (a cos u cos v, a cos u sin v, −c sin u)`. -/
def spheroidChart (a c : ℝ) : (Fin 2 → ℝ) → Vec3 :=
  revolutionChart (fun u => a * cos u) (fun u => -(c * sin u))

/-- **The profile speed of the ellipsoid of revolution (MLS Exercise 14, p. 262):**
`s(u) = √(a² sin² u + c² cos² u)`. -/
def spheroidSpeed (a c u : ℝ) : ℝ := √(a ^ 2 * sin u ^ 2 + c ^ 2 * cos u ^ 2)

/-- **The ellipsoid of revolution as a body `{x | h x ≤ 0}` (MLS Exercise 14, p. 262):**
`h(x) = (x₁² + x₂²)/a² + x₃²/c² − 1`. -/
def spheroidFunction (a c : ℝ) (x : Vec3) : ℝ := (x 0 ^ 2 + x 1 ^ 2) / a ^ 2 + x 2 ^ 2 / c ^ 2 - 1

/-- Supporting lemma for MLS pp. 243–244: an orthogonal chart restricts to an orthogonal chart on an
open subset of its domain. -/
private lemma isOrthogonalChartOn_mono {c : (Fin 2 → ℝ) → Vec3} {U V : Set (Fin 2 → ℝ)}
    (hc : IsOrthogonalChartOn c U) (hV : IsOpen V) (hVU : V ⊆ U) : IsOrthogonalChartOn c V :=
  ⟨hV, hc.contDiffOn.mono hVU, fun α hα => hc.injective α (hVU hα),
    fun α hα => hc.orthogonal α (hVU hα)⟩

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ a cos u`. -/
private lemma deriv_mul_cos (a : ℝ) : deriv (fun u => a * cos u) = fun u => -(a * sin u) :=
  funext fun u => by rw [((hasDerivAt_cos u).const_mul a).deriv]; ring

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ −a sin u`. -/
private lemma deriv_neg_mul_sin (a : ℝ) :
    deriv (fun u => -(a * sin u)) = fun u => -(a * cos u) :=
  funext fun u => ((hasDerivAt_sin u).const_mul a).neg.deriv

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ −a cos u`. -/
private lemma deriv_neg_mul_cos (a : ℝ) : deriv (fun u => -(a * cos u)) = fun u => a * sin u :=
  funext fun u => ((hasDerivAt_cos u).const_mul a).neg.deriv.trans (by ring)

/-- Supporting lemma for outward normals (MLS p. 244): the derivative of a body function `h` at `p`
along `w` is the derivative of `t ↦ h(p + t w)` at `0`. -/
private lemma fderiv_apply_of_hasDerivAt {h : Vec3 → ℝ} {p w : Vec3} {d : ℝ}
    (hd : DifferentiableAt ℝ h p) (hl : HasDerivAt (fun t : ℝ => h (p + t • w)) d 0) :
    fderiv ℝ h p w = d := by
  have hline : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
  have h' : HasFDerivAt h (fderiv ℝ h p) (p + (0 : ℝ) • w) := by simpa using hd.hasFDerivAt
  exact (h'.comp_hasDerivAt (0 : ℝ) hline).unique hl

/-- Supporting lemma for outward normals (MLS p. 244): the derivative of a coordinate of
`p + t w`. -/
private lemma hasDerivAt_coord (p w : Vec3) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => p i + t * w i) (w i) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w i)).const_add (p i)

/-- Supporting lemma for MLS Exercise 14, p. 262: the function describing the ellipsoid of
revolution is differentiable. -/
private lemma differentiable_spheroidFunction (a c : ℝ) :
    Differentiable ℝ (spheroidFunction a c) := by
  unfold spheroidFunction
  fun_prop

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of the ellipsoid function along a
line. -/
private lemma hasDerivAt_spheroidFunction (a c : ℝ) (p w : Vec3) :
    HasDerivAt (fun t : ℝ => spheroidFunction a c (p + t • w))
      (2 * (p 0 * w 0 + p 1 * w 1) / a ^ 2 + 2 * (p 2 * w 2) / c ^ 2) 0 := by
  have h := ((((hasDerivAt_coord p w 0).pow 2).add ((hasDerivAt_coord p w 1).pow 2)).div_const
    (a ^ 2)).add (((hasDerivAt_coord p w 2).pow 2).div_const (c ^ 2)) |>.sub_const 1
  convert h using 1
  · funext t
    simp [spheroidFunction]
  · simp
    ring

/-- Supporting lemma for MLS Exercise 14, p. 262: a point with `cos u > 0` lies in the chart domain
of the ellipsoid of revolution. -/
private lemma mem_revolutionDomain_spheroid {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hα : 0 < cos (α 0)) : α ∈ revolutionDomain (fun u => a * cos u) (fun u => -(c * sin u)) := by
  refine ⟨mul_pos ha hα, ?_⟩
  simp only [deriv_mul_cos, deriv_neg_mul_sin]
  nlinarith [sq_nonneg (a * sin (α 0)), pow_pos (mul_pos hc hα) 2]

/-- Supporting lemma for MLS Exercise 14, p. 262: the profile speed of the ellipsoid of
revolution. -/
private lemma profileSpeed_spheroid (a c u : ℝ) :
    profileSpeed (fun u => a * cos u) (fun u => -(c * sin u)) u = spheroidSpeed a c u := by
  simp only [profileSpeed, spheroidSpeed, deriv_mul_cos, deriv_neg_mul_sin]
  congr 1
  ring

/-- Supporting lemma for MLS Exercise 14, p. 262: `s > 0` for the ellipsoid of revolution where
`cos u > 0`. -/
private lemma spheroidSpeed_pos {a c u : ℝ} (hc : 0 < c) (hu : 0 < cos u) :
    0 < spheroidSpeed a c u :=
  sqrt_pos.mpr (by nlinarith [sq_nonneg (a * sin u), pow_pos (mul_pos hc hu) 2])

/-- **The chart of the ellipsoid of revolution is orthogonal (MLS p. 244)** on `{cos u > 0}`, for
`a, c > 0`. -/
theorem isOrthogonalChartOn_spheroidChart {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IsOrthogonalChartOn (spheroidChart a c) {α | 0 < cos (α 0)} :=
  isOrthogonalChartOn_mono (isOrthogonalChartOn_revolutionChart (r := fun u => a * cos u)
    (z := fun u => -(c * sin u)) (by fun_prop) (by fun_prop))
    (isOpen_lt continuous_const (continuous_cos.comp (continuous_apply 0)))
    fun _ hα => mem_revolutionDomain_spheroid ha hc hα

/-- **MLS Exercise 14, p. 262, the ellipsoid of revolution:** for `a, c > 0` and `cos u > 0`, the
chart lies on the ellipsoid, its normal points out of it, and
`M = diag(s, a cos u)`, `K = diag(a c/s³, c/(a s))`, `T = [0, −tan u/s]` with
`s = √(a² sin² u + c² cos² u)`. For `a = c = ρ` these are the printed parameters of the sphere of
MLS Example 5.7, p. 253. -/
theorem exercise14_spheroid {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hα : 0 < cos (α 0)) :
    spheroidFunction a c (spheroidChart a c α) = 0 ∧
      IsOutwardNormal (spheroidFunction a c) (spheroidChart a c) α ∧
      metricTensor (spheroidChart a c) α = !![spheroidSpeed a c (α 0), 0; 0, a * cos (α 0)] ∧
      curvatureTensor (spheroidChart a c) α =
        !![a * c / spheroidSpeed a c (α 0) ^ 3, 0; 0, c / (a * spheroidSpeed a c (α 0))] ∧
      torsionForm (spheroidChart a c) α = ![0, -(tan (α 0) / spheroidSpeed a c (α 0))] := by
  have hr : ContDiff ℝ 2 (fun u => a * cos u) := by fun_prop
  have hz : ContDiff ℝ 2 (fun u => -(c * sin u)) := by fun_prop
  have hd := mem_revolutionDomain_spheroid ha hc hα
  have hs := spheroidSpeed_pos (a := a) hc hα
  rw [spheroidChart]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [spheroidFunction, revolutionChart]
    field_simp
    linear_combination cos (α 0) ^ 2 * cos_sq_add_sin_sq (α 1) + cos_sq_add_sin_sq (α 0)
  · rw [IsOutwardNormal, fderiv_apply_of_hasDerivAt (differentiable_spheroidFunction a c _)
      (hasDerivAt_spheroidFunction a c _ _), gaussNormal_revolutionChart hr hz hd]
    simp [revolutionChart, profileSpeed_spheroid]
    have key : 0 < 2 * (c ^ 2 * cos (α 0) ^ 2 + a ^ 2 * sin (α 0) ^ 2) /
        (a * c * spheroidSpeed a c (α 0)) := by positivity
    convert key using 1
    field_simp
    linear_combination cos (α 0) ^ 2 * c ^ 2 * cos_sq_add_sin_sq (α 1)
  · rw [metricTensor_revolutionChart hr hz hd, profileSpeed_spheroid]
  · rw [curvatureTensor_revolutionChart hr hz hd]
    simp only [deriv_mul_cos, deriv_neg_mul_sin, deriv_neg_mul_cos, profileSpeed_spheroid]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    exact cos_sq_add_sin_sq _
  · rw [torsionForm_revolutionChart hr hz hd]
    simp only [deriv_mul_cos, profileSpeed_spheroid]
    funext i
    fin_cases i <;> simp [tan_eq_sin_div_cos]
    field_simp

/-! ### Exercise 14: a paraboloid -/

/-- **The paraboloid `z = −(x² + y²)/(2a)` (MLS Exercise 14, p. 262):** the profile
`(u, −u²/(2a))` turned about the `z`-axis, `c(u, v) = (u cos v, u sin v, −u²/(2a))`, for `u > 0`
(the vertex `u = 0` is the pole of the chart). -/
def paraboloidChart (a : ℝ) : (Fin 2 → ℝ) → Vec3 :=
  revolutionChart (fun u => u) (fun u => -(u ^ 2 / (2 * a)))

/-- **The profile speed of the paraboloid (MLS Exercise 14, p. 262):** `s(u) = √(1 + u²/a²)`. -/
def paraboloidSpeed (a u : ℝ) : ℝ := √(1 + u ^ 2 / a ^ 2)

/-- **The solid below the paraboloid as a body `{x | h x ≤ 0}` (MLS Exercise 14, p. 262):**
`h(x) = x₃ + (x₁² + x₂²)/(2a)`. -/
def paraboloidFunction (a : ℝ) (x : Vec3) : ℝ := x 2 + (x 0 ^ 2 + x 1 ^ 2) / (2 * a)

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ u`. -/
private lemma deriv_id_fun : deriv (fun u : ℝ => u) = fun _ => 1 :=
  funext fun u => (hasDerivAt_id' u).deriv

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of a constant. -/
private lemma deriv_one_fun : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 :=
  funext fun u => deriv_const u 1

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ −u²/(2a)`. -/
private lemma deriv_neg_sq_div (a : ℝ) :
    deriv (fun u => -(u ^ 2 / (2 * a))) = fun u => -(u / a) :=
  funext fun u => ((hasDerivAt_pow 2 u).div_const (2 * a)).neg.deriv.trans (by simp; ring)

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ −u/a`. -/
private lemma deriv_neg_div (a : ℝ) : deriv (fun u => -(u / a)) = fun _ => -(1 / a) :=
  funext fun u => ((hasDerivAt_id' u).div_const a).neg.deriv

/-- Supporting lemma for MLS Exercise 14, p. 262: a point with `u > 0` lies in the chart domain of
the paraboloid. -/
private lemma mem_revolutionDomain_paraboloid {a : ℝ} (hα : 0 < α 0) :
    α ∈ revolutionDomain (fun u => u) (fun u => -(u ^ 2 / (2 * a))) := by
  refine ⟨hα, ?_⟩
  simp only [deriv_id_fun, deriv_neg_sq_div]
  positivity

/-- Supporting lemma for MLS Exercise 14, p. 262: the profile speed of the paraboloid. -/
private lemma profileSpeed_paraboloid (a u : ℝ) :
    profileSpeed (fun u => u) (fun u => -(u ^ 2 / (2 * a))) u = paraboloidSpeed a u := by
  simp only [profileSpeed, paraboloidSpeed, deriv_id_fun, deriv_neg_sq_div]
  congr 1
  ring

/-- Supporting lemma for MLS Exercise 14, p. 262: the function describing the solid below the
paraboloid is differentiable. -/
private lemma differentiable_paraboloidFunction (a : ℝ) :
    Differentiable ℝ (paraboloidFunction a) := by
  unfold paraboloidFunction
  fun_prop

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of the paraboloid function along a
line. -/
private lemma hasDerivAt_paraboloidFunction (a : ℝ) (p w : Vec3) :
    HasDerivAt (fun t : ℝ => paraboloidFunction a (p + t • w))
      (w 2 + 2 * (p 0 * w 0 + p 1 * w 1) / (2 * a)) 0 := by
  have h := (hasDerivAt_coord p w 2).add ((((hasDerivAt_coord p w 0).pow 2).add
    ((hasDerivAt_coord p w 1).pow 2)).div_const (2 * a))
  convert h using 1
  · funext t
    simp [paraboloidFunction]
  · simp
    ring

/-- **The chart of the paraboloid is orthogonal (MLS p. 244)** on `{u > 0}`, for every `a`. -/
theorem isOrthogonalChartOn_paraboloidChart (a : ℝ) :
    IsOrthogonalChartOn (paraboloidChart a) {α | 0 < α 0} :=
  isOrthogonalChartOn_mono (isOrthogonalChartOn_revolutionChart (r := fun u => u)
    (z := fun u => -(u ^ 2 / (2 * a))) (by fun_prop) (by fun_prop))
    (isOpen_lt continuous_const (continuous_apply 0))
    fun _ hα => mem_revolutionDomain_paraboloid hα

/-- **MLS Exercise 14, p. 262, the paraboloid:** for `a > 0` and `u > 0`, the chart lies on the
paraboloid, its normal points out of the solid below it, and `M = diag(s, u)`,
`K = diag(1/(a s³), 1/(a s))`, `T = [0, 1/(u s)]` with `s = √(1 + u²/a²)`. -/
theorem exercise14_paraboloid {a : ℝ} (ha : 0 < a) (hα : 0 < α 0) :
    paraboloidFunction a (paraboloidChart a α) = 0 ∧
      IsOutwardNormal (paraboloidFunction a) (paraboloidChart a) α ∧
      metricTensor (paraboloidChart a) α = !![paraboloidSpeed a (α 0), 0; 0, α 0] ∧
      curvatureTensor (paraboloidChart a) α =
        !![1 / (a * paraboloidSpeed a (α 0) ^ 3), 0; 0, 1 / (a * paraboloidSpeed a (α 0))] ∧
      torsionForm (paraboloidChart a) α = ![0, 1 / (α 0 * paraboloidSpeed a (α 0))] := by
  have hr : ContDiff ℝ 2 (fun u : ℝ => u) := by fun_prop
  have hz : ContDiff ℝ 2 (fun u => -(u ^ 2 / (2 * a))) := by fun_prop
  have hd := mem_revolutionDomain_paraboloid (a := a) hα
  have hs : 0 < paraboloidSpeed a (α 0) := sqrt_pos.mpr (by positivity)
  rw [paraboloidChart]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [paraboloidFunction, revolutionChart]
    field_simp
    linear_combination α 0 ^ 2 * cos_sq_add_sin_sq (α 1)
  · rw [IsOutwardNormal, fderiv_apply_of_hasDerivAt (differentiable_paraboloidFunction a _)
      (hasDerivAt_paraboloidFunction a _ _), gaussNormal_revolutionChart hr hz hd]
    simp [revolutionChart, profileSpeed_paraboloid]
    have key : 0 < (a ^ 2 + α 0 ^ 2) / (a ^ 2 * paraboloidSpeed a (α 0)) := by positivity
    convert key using 1
    field_simp
    linear_combination α 0 ^ 2 * cos_sq_add_sin_sq (α 1)
  · rw [metricTensor_revolutionChart hr hz hd, profileSpeed_paraboloid]
  · rw [curvatureTensor_revolutionChart hr hz hd]
    simp only [deriv_id_fun, deriv_one_fun, deriv_neg_sq_div, deriv_neg_div,
      profileSpeed_paraboloid]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · rw [torsionForm_revolutionChart hr hz hd]
    simp only [deriv_id_fun, profileSpeed_paraboloid]

/-! ### Exercise 14: a torus -/

/-- **The torus with radii `R > a > 0` (MLS Exercise 14, p. 262):** the circle of radius `a` about
`(R, 0)`, traversed as `(R + a cos u, −a sin u)`, turned about the `z`-axis,
`c(u, v) = ((R + a cos u) cos v, (R + a cos u) sin v, −a sin u)`. -/
def torusChart (R a : ℝ) : (Fin 2 → ℝ) → Vec3 :=
  revolutionChart (fun u => R + a * cos u) (fun u => -(a * sin u))

/-- **The solid torus as a body `{x | h x ≤ 0}` (MLS Exercise 14, p. 262):**
`h(x) = (x₁² + x₂² + x₃² + R² − a²)² − 4R²(x₁² + x₂²)`. -/
def torusFunction (R a : ℝ) (x : Vec3) : ℝ :=
  (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + R ^ 2 - a ^ 2) ^ 2 - 4 * R ^ 2 * (x 0 ^ 2 + x 1 ^ 2)

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of `u ↦ R + a cos u`. -/
private lemma deriv_add_mul_cos (R a : ℝ) :
    deriv (fun u => R + a * cos u) = fun u => -(a * sin u) :=
  funext fun u => (((hasDerivAt_cos u).const_mul a).const_add R).deriv.trans (by ring)

/-- Supporting lemma for MLS Exercise 14, p. 262: every point lies in the chart domain of the torus
for `0 < a < R`. -/
private lemma mem_revolutionDomain_torus {R a : ℝ} (ha : 0 < a) (haR : a < R) (α : Fin 2 → ℝ) :
    α ∈ revolutionDomain (fun u => R + a * cos u) (fun u => -(a * sin u)) := by
  refine ⟨by nlinarith [neg_one_le_cos (α 0)], ?_⟩
  simp only [deriv_add_mul_cos, deriv_neg_mul_sin]
  have e : (-(a * sin (α 0))) ^ 2 + (-(a * cos (α 0))) ^ 2 = a ^ 2 := by
    linear_combination a ^ 2 * sin_sq_add_cos_sq (α 0)
  rw [e]
  positivity

/-- Supporting lemma for MLS Exercise 14, p. 262: the profile speed of the torus is `a`. -/
private lemma profileSpeed_torus {R a : ℝ} (ha : 0 < a) (u : ℝ) :
    profileSpeed (fun u => R + a * cos u) (fun u => -(a * sin u)) u = a := by
  simp only [profileSpeed, deriv_add_mul_cos, deriv_neg_mul_sin]
  rw [sqrt_eq_iff_mul_self_eq_of_pos ha]
  linear_combination -(a ^ 2 * sin_sq_add_cos_sq u)

/-- Supporting lemma for MLS Exercise 14, p. 262: the function describing the solid torus is
differentiable. -/
private lemma differentiable_torusFunction (R a : ℝ) : Differentiable ℝ (torusFunction R a) := by
  unfold torusFunction
  fun_prop

/-- Supporting lemma for MLS Exercise 14, p. 262: the derivative of the torus function along a
line. -/
private lemma hasDerivAt_torusFunction (R a : ℝ) (p w : Vec3) :
    HasDerivAt (fun t : ℝ => torusFunction R a (p + t • w))
      (4 * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + R ^ 2 - a ^ 2) * (p 0 * w 0 + p 1 * w 1 + p 2 * w 2) -
        8 * R ^ 2 * (p 0 * w 0 + p 1 * w 1)) 0 := by
  have hs := (((hasDerivAt_coord p w 0).pow 2).add ((hasDerivAt_coord p w 1).pow 2))
  have h := ((((hs.add ((hasDerivAt_coord p w 2).pow 2)).add_const (R ^ 2)).sub_const
    (a ^ 2)).pow 2).sub (hs.const_mul (4 * R ^ 2))
  convert h using 1
  · funext t
    simp [torusFunction]
  · simp
    ring

/-- **The chart of the torus is orthogonal on all of `ℝ²` (MLS p. 244)**, for `0 < a < R`. -/
theorem isOrthogonalChartOn_torusChart {R a : ℝ} (ha : 0 < a) (haR : a < R) :
    IsOrthogonalChartOn (torusChart R a) Set.univ :=
  isOrthogonalChartOn_mono (isOrthogonalChartOn_revolutionChart (r := fun u => R + a * cos u)
    (z := fun u => -(a * sin u)) (by fun_prop) (by fun_prop)) isOpen_univ
    fun α _ => mem_revolutionDomain_torus ha haR α

/-- **MLS Exercise 14, p. 262, the torus:** for `0 < a < R`, the chart lies on the torus, its normal
points out of the solid torus, and `M = diag(a, R + a cos u)`,
`K = diag(1/a, cos u/(R + a cos u))`, `T = [0, −sin u/(R + a cos u)]`. -/
theorem exercise14_torus {R a : ℝ} (ha : 0 < a) (haR : a < R) (α : Fin 2 → ℝ) :
    torusFunction R a (torusChart R a α) = 0 ∧
      IsOutwardNormal (torusFunction R a) (torusChart R a) α ∧
      metricTensor (torusChart R a) α = !![a, 0; 0, R + a * cos (α 0)] ∧
      curvatureTensor (torusChart R a) α =
        !![1 / a, 0; 0, cos (α 0) / (R + a * cos (α 0))] ∧
      torsionForm (torusChart R a) α = ![0, -(sin (α 0) / (R + a * cos (α 0)))] := by
  have hr : ContDiff ℝ 2 (fun u => R + a * cos u) := by fun_prop
  have hz : ContDiff ℝ 2 (fun u => -(a * sin u)) := by fun_prop
  have hd := mem_revolutionDomain_torus ha haR α
  have hρ : 0 < R + a * cos (α 0) := hd.1
  have hsu : sin (α 0) ^ 2 = 1 - cos (α 0) ^ 2 := by linear_combination sin_sq_add_cos_sq (α 0)
  rw [torusChart]
  set x := revolutionChart (fun u => R + a * cos u) (fun u => -(a * sin u)) α with hx
  have h01 : x 0 ^ 2 + x 1 ^ 2 = (R + a * cos (α 0)) ^ 2 := by
    simp [hx, revolutionChart]
    linear_combination (R + a * cos (α 0)) ^ 2 * cos_sq_add_sin_sq (α 1)
  have h2 : x 2 ^ 2 = a ^ 2 * sin (α 0) ^ 2 := by
    simp [hx, revolutionChart]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [torusFunction, h01, h2, hsu]
    ring
  · have hn : gaussNormal (revolutionChart (fun u => R + a * cos u) (fun u => -(a * sin u))) α =
        WithLp.toLp 2 ![cos (α 0) * cos (α 1), cos (α 0) * sin (α 1), -sin (α 0)] := by
      rw [gaussNormal_revolutionChart hr hz hd, profileSpeed_torus ha]
      apply WithLp.ofLp_injective
      funext i
      fin_cases i <;> simp <;> field_simp
    have hR : 0 < R := ha.trans haR
    rw [IsOutwardNormal, fderiv_apply_of_hasDerivAt (differentiable_torusFunction R a _)
      (hasDerivAt_torusFunction R a _ _), hn, h01, h2]
    have key : 0 < 8 * R * a * (R + a * cos (α 0)) := by positivity
    convert key using 1
    simp [revolutionChart]
    linear_combination (8 * R * (R + a * cos (α 0)) ^ 2 * cos (α 0) -
        8 * R ^ 2 * (R + a * cos (α 0)) * cos (α 0)) * cos_sq_add_sin_sq (α 1) +
      (8 * R * (R + a * cos (α 0)) * a + 4 * a ^ 2 * ((R + a * cos (α 0)) * cos (α 0) *
        (cos (α 1) ^ 2 + sin (α 1) ^ 2) + a * sin (α 0) ^ 2)) * sin_sq_add_cos_sq (α 0)
  · rw [metricTensor_revolutionChart hr hz hd, profileSpeed_torus ha]
  · rw [curvatureTensor_revolutionChart hr hz hd]
    simp only [deriv_add_mul_cos, deriv_neg_mul_sin, deriv_neg_mul_cos, profileSpeed_torus ha]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    exact cos_sq_add_sin_sq _
  · rw [torsionForm_revolutionChart hr hz hd]
    simp only [deriv_add_mul_cos, profileSpeed_torus ha]
    funext i
    fin_cases i <;> simp
    field_simp

/-! ### Exercise 15: an elliptic fingertip rolling on a flat object -/

/-- **MLS Exercise 15(a), p. 262, for an ellipsoid with two equal axes `a = b`:** the chart of the
ellipsoid of revolution is orthogonal near the contact point, which is `c(0, π) = (−a, 0, 0)`, the
end of the `x`-axis facing the object in the figure, with outward normal `(−1, 0, 0)`. -/
theorem exercise15a {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    spheroidChart a c ![0, π] = WithLp.toLp 2 ![-a, 0, 0] ∧
      gaussNormal (spheroidChart a c) ![0, π] = WithLp.toLp 2 ![-1, 0, 0] ∧
      IsOrthogonalChartOn (spheroidChart a c) {α | 0 < cos (α 0)} ∧
      (![0, π] : Fin 2 → ℝ) ∈ {α : Fin 2 → ℝ | 0 < cos (α 0)} := by
  have hr : ContDiff ℝ 2 (fun u => a * cos u) := by fun_prop
  have hz : ContDiff ℝ 2 (fun u => -(c * sin u)) := by fun_prop
  have h0 : (![0, π] : Fin 2 → ℝ) ∈ {α : Fin 2 → ℝ | 0 < cos (α 0)} := by simp
  refine ⟨?_, ?_, isOrthogonalChartOn_spheroidChart ha hc, h0⟩
  · apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [spheroidChart, revolutionChart]
  · rw [spheroidChart, gaussNormal_revolutionChart hr hz (mem_revolutionDomain_spheroid ha hc h0),
      profileSpeed_spheroid]
    have hs : spheroidSpeed a c 0 = c := by simp [spheroidSpeed, sqrt_sq hc.le]
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [hs, hc.ne']

/-- The inverse of a diagonal `2 × 2` matrix (supporting lemma for MLS Exercise 15, p. 262). -/
private theorem inv_diag {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![a⁻¹, 0; 0, b⁻¹] := by
  rw [Matrix.inv_eq_left_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

/-- Supporting lemma for MLS p. 250: against a flat object (`K_o = 0`) the relative curvature form
is `K_f`. -/
private theorem relativeCurvature_zero (K : Matrix (Fin 2) (Fin 2) ℝ) (ψ : ℝ) :
    relativeCurvature K 0 ψ = K := by
  simp [relativeCurvature, rotatedCurvature]

/-- **MLS Exercise 15(b), p. 262, for `a = b`: the equations of contact of the elliptic fingertip
rolling on the flat object.** With the ellipsoid-of-revolution chart for the finger and the plane
chart of MLS Example 5.7 for the object, along every motion to which Corollary 5.11.1 (p. 252)
applies (a pose curve agreeing near `t` with `g_of(η(s))`, `cos u_f > 0`, pure rolling at `t`),
`(u̇_f, v̇_f, u̇_o, v̇_o, ψ̇) =
(0, s/(c cos u_f), −(a s/c) sin ψ, −(a s/c) cos ψ, −(a/c) tan u_f) ω_x +
(−s²/(a c), 0, −(s³/(a c)) cos ψ, (s³/(a c)) sin ψ, 0) ω_y`, with `s = √(a² sin² u_f + c² cos² u_f)`
and `(ω_x, ω_y)` the rolling velocities. For `a = c = ρ` this is MLS eq. (5.39), p. 253. -/
theorem exercise15b {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {αf αo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ}
    {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : 0 < cos (αf t 0)) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose (spheroidChart a c) planeChart (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (spheroidChart a c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) :
    let ω := (Twist.adjoint (contactFrame (spheroidChart a c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    let s := spheroidSpeed a c (αf t 0)
    ![αf' 0, αf' 1, αo' 0, αo' 1, ψ'] =
      ω 0 • ![0, s / (c * cos (αf t 0)), -(a * s / c) * sin (ψ t), -(a * s / c) * cos (ψ t),
          -(a / c) * tan (αf t 0)] +
        ω 1 • ![-(s ^ 2 / (a * c)), 0, -(s ^ 3 / (a * c)) * cos (ψ t),
          (s ^ 3 / (a * c)) * sin (ψ t), 0] := by
  intro ω s
  obtain ⟨-, -, hM, hK, hT⟩ := exercise14_spheroid ha hc hft
  have hsdef : s = spheroidSpeed a c (αf t 0) := rfl
  rw [← hsdef] at hM hK hT
  have hs : 0 < s := spheroidSpeed_pos hc hft
  have hK' : relativeCurvature (curvatureTensor (spheroidChart a c) (αf t))
      (curvatureTensor planeChart (αo t)) (ψ t) = !![a * c / s ^ 3, 0; 0, c / (a * s)] := by
    rw [hK, curvatureTensor_planeChart, relativeCurvature_zero]
  have hX : IsUnit (relativeCurvature (curvatureTensor (spheroidChart a c) (αf t))
      (curvatureTensor planeChart (αo t)) (ψ t)).det := by
    rw [hK', isUnit_iff_ne_zero, Matrix.det_fin_two_of, mul_zero, sub_zero]
    positivity
  obtain ⟨hf, ho, hψ'⟩ := rollingEquations_of_hasDerivAt (isOrthogonalChartOn_spheroidChart ha hc)
    isOrthogonalChartOn_planeChart hαf hαo hψ hft (Set.mem_univ _) hX hg hD hr
  rw [hK', hM] at hf
  rw [hK', metricTensor_planeChart] at ho
  rw [hM, hT, metricTensor_planeChart, torsionForm_planeChart] at hψ'
  have hω : ω = (Twist.adjoint (contactFrame (spheroidChart a c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular := rfl
  rw [← hω] at hf ho
  rw [inv_diag (by positivity) (by positivity), inv_diag (by positivity) (by positivity)] at hf
  rw [inv_diag (by positivity) (by positivity), inv_one, one_mulVec] at ho
  have hcos := hft.ne'
  funext i
  fin_cases i
  · simp [hf, dotProduct, Fin.sum_univ_two]
    field_simp
  · simp [hf, dotProduct, Fin.sum_univ_two]
    field_simp
  · simp [ho, dotProduct, Fin.sum_univ_two, angleMatrix]
    field_simp
    ring
  · simp [ho, dotProduct, Fin.sum_univ_two, angleMatrix]
    field_simp
    ring
  · simp [hψ', hf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, tan_eq_sin_div_cos]
    field_simp

/-- **MLS Exercise 15(c), p. 262, for `a = b`: the rolling velocity that produces `α̇_o = (0, v)`.**
Under the hypotheses of `exercise15b`, the object contact velocity is `α̇_o = (0, v)` exactly when
the rolling velocities are `ω_x = −(c/(a s)) cos ψ v` and `ω_y = (a c/s³) sin ψ v`, with
`s = √(a² sin² u_f + c² cos² u_f)`. The conclusion concerns `ω_x` and `ω_y` only. The other
components of the relative velocity `V^b_{l_o l_f}` are not part of it: `v_x = v_y = ω_z = 0` is
the pure-rolling hypothesis (p. 249), and `v_z = 0` holds along such a motion by Theorem 5.11
(p. 250) without being restated here. -/
theorem exercise15c {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {αf αo : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ}
    {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t) (hαo : HasDerivAt αo αo' t)
    (hψ : HasDerivAt ψ ψ' t) (hft : 0 < cos (αf t 0)) {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose (spheroidChart a c) planeChart (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (spheroidChart a c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) (v : ℝ) :
    let ω := (Twist.adjoint (contactFrame (spheroidChart a c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    let s := spheroidSpeed a c (αf t 0)
    αo' = ![0, v] ↔
      ω 0 = -(c / (a * s)) * cos (ψ t) * v ∧ ω 1 = (a * c / s ^ 3) * sin (ψ t) * v := by
  intro ω s
  have h := exercise15b ha hc hαf hαo hψ hft hg hD hr
  have hω : ω = (Twist.adjoint (contactFrame (spheroidChart a c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular := rfl
  have hsdef : s = spheroidSpeed a c (αf t 0) := rfl
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [← hω, ← hsdef] at h2 h3
  simp at h2 h3
  have hs : 0 < s := spheroidSpeed_pos hc hft
  have ha' := ha.ne'
  have hc' := hc.ne'
  have hs' := hs.ne'
  constructor
  · intro hv
    have e0 : αo' 0 = 0 := by simp [hv]
    have e1 : αo' 1 = v := by simp [hv]
    rw [e0] at h2
    rw [e1] at h3
    have hP : a * s / c * ω 0 = -(cos (ψ t) * v) := by
      linear_combination sin (ψ t) * h2 + cos (ψ t) * h3 -
        (a * s / c * ω 0) * sin_sq_add_cos_sq (ψ t)
    have hQ : s ^ 3 / (a * c) * ω 1 = sin (ψ t) * v := by
      linear_combination cos (ψ t) * h2 - sin (ψ t) * h3 -
        (s ^ 3 / (a * c) * ω 1) * sin_sq_add_cos_sq (ψ t)
    constructor
    · calc ω 0 = c / (a * s) * (a * s / c * ω 0) := by field_simp
        _ = -(c / (a * s)) * cos (ψ t) * v := by rw [hP]; ring
    · calc ω 1 = a * c / s ^ 3 * (s ^ 3 / (a * c) * ω 1) := by field_simp
        _ = a * c / s ^ 3 * sin (ψ t) * v := by rw [hQ]; ring
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [h2, h0, h1]
      field_simp
      ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h3, h0, h1]
      field_simp
      linear_combination v * sin_sq_add_cos_sq (ψ t)

end Examples
end RoboLean
