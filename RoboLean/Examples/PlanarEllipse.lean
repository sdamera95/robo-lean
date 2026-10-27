import RoboLean.Grasp.PlanarRegularContact
import RoboLean.Examples.PlanarContact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# An elliptical finger rolling on a line (MLS Exercise 17(b))

MLS Chapter 5, Exercise 17(b), printed p. 263: "Derive the equations of contact for a planar,
elliptical finger rolling against a flat object", with the kinematics of planar contact of part (a)
(pp. 262–263).

**Conventions** (those of `Grasp.PlanarRegularContact`): points of the plane are `Fin 2 → ℝ`, a
chart has derivative `σ t` with unit tangent `t`, normal `n = J t` (`J` the rotation by `+π/2`) and
curvature `K` with respect to arc length defined by `n' = σ K t`; the curves are in contact when
`c_o(s_o) = p + R c_f(s_f)` with `n_o = −R n_f`.

* The finger is the ellipse with semi-axes `a, b > 0` centred at the origin, traversed clockwise
  from its lowest point, `c_f(φ) = (−a sin φ, −b cos φ)`: speed `σ(φ) = √(a² cos² φ + b² sin² φ)`,
  tangent `(−a cos φ, b sin φ)/σ`, outward normal `(−b sin φ, −a cos φ)/σ` and curvature `a b/σ³`.
  For `a = b = r` and `φ = s/r` it is the disk of `Examples.PlanarContact`. The arc length of an
  ellipse is not an elementary function of `φ`, so the regular-chart form of Exercise 17 is used.
* The object is the line `c_o(s) = (s, 0)` of `Examples.PlanarContact`.
* The finger turns by the angle `θ`, `R(θ) = [[cos θ, −sin θ], [sin θ, cos θ]]`, and rolls when the
  finger's material point at the contact has zero velocity, `Ṙ c_f + ṗ = 0` (no slip).

**Result.** Rolling gives `φ̇ = (σ(φ)²/(a b)) θ̇` and `ṡ_o = −(σ(φ)³/(a b)) θ̇`, so `ṡ_o = −σ φ̇`:
the contact point moves along the line by the arc length it moves along the ellipse. A concrete
rolling motion at `t = 0`, with `tan φ = (a/b) tan θ`, satisfies every hypothesis.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Grasp

/-- **The elliptical finger of MLS Exercise 17(b), p. 263:** the ellipse with semi-axes `a, b`
centred at the origin, traversed clockwise from its lowest point, `c_f(φ) = (−a sin φ, −b cos φ)`.
-/
def ellipseCurve (a b φ : ℝ) : Fin 2 → ℝ := ![-(a * sin φ), -(b * cos φ)]

/-- **The speed of the elliptical chart (MLS Exercise 17(b), p. 263):**
`σ(φ) = ‖c_f'(φ)‖ = √(a² cos² φ + b² sin² φ)`. -/
def ellipseSpeed (a b φ : ℝ) : ℝ := √(a ^ 2 * cos φ ^ 2 + b ^ 2 * sin φ ^ 2)

/-- **The unit tangent of the elliptical chart (MLS Exercise 17(b), p. 263):**
`t(φ) = (−a cos φ, b sin φ)/σ(φ)`. -/
def ellipseTangent (a b φ : ℝ) : Fin 2 → ℝ := (ellipseSpeed a b φ)⁻¹ • ![-(a * cos φ), b * sin φ]

/-- **The curvature of the ellipse with respect to arc length (MLS Exercise 17(b), p. 263, with the
convention `n' = σ K t`):** `K(φ) = a b/σ(φ)³`. -/
def ellipseCurvature (a b φ : ℝ) : ℝ := a * b / ellipseSpeed a b φ ^ 3

/-- A pair of real curves with derivatives `f'` and `g'` gives the plane curve `s ↦ (f s, g s)` with
the derivative `(f', g')` (used for the charts and motions of MLS Exercise 17(b), p. 263). -/
private lemma hasDerivAt_vec2 {f g : ℝ → ℝ} {f' g' s : ℝ} (hf : HasDerivAt f f' s)
    (hg : HasDerivAt g g' s) : HasDerivAt (fun x => ![f x, g x]) ![f', g'] s :=
  hasDerivAt_pi.mpr fun i => by fin_cases i <;> simpa

private lemma ellipseSpeed_sq (a b φ : ℝ) :
    ellipseSpeed a b φ ^ 2 = a ^ 2 * cos φ ^ 2 + b ^ 2 * sin φ ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma ellipseQ_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (φ : ℝ) :
    0 < a ^ 2 * cos φ ^ 2 + b ^ 2 * sin φ ^ 2 := by
  rcases eq_or_ne (cos φ) 0 with h0 | h0
  · have h := sin_sq_add_cos_sq φ
    rw [h0] at h ⊢
    nlinarith [mul_pos hb hb]
  · have : 0 < cos φ ^ 2 := by positivity
    positivity

private lemma ellipseSpeed_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (φ : ℝ) :
    0 < ellipseSpeed a b φ :=
  Real.sqrt_pos.mpr (ellipseQ_pos ha hb φ)

private lemma hasDerivAt_ellipseCurve (a b φ : ℝ) :
    HasDerivAt (ellipseCurve a b) ![-(a * cos φ), b * sin φ] φ := by
  have h := hasDerivAt_vec2 ((hasDerivAt_sin φ).const_mul a).neg
    ((hasDerivAt_cos φ).const_mul b).neg
  convert h using 1
  · funext x
    simp [ellipseCurve]
  · simp

private lemma hasDerivAt_ellipseSpeed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (φ : ℝ) :
    HasDerivAt (ellipseSpeed a b)
      ((b ^ 2 - a ^ 2) * sin φ * cos φ / ellipseSpeed a b φ) φ := by
  have hQ : HasDerivAt (fun x => a ^ 2 * cos x ^ 2 + b ^ 2 * sin x ^ 2)
      (a ^ 2 * (2 * cos φ * -sin φ) + b ^ 2 * (2 * sin φ * cos φ)) φ := by
    have h1 := ((hasDerivAt_cos φ).pow 2).const_mul (a ^ 2)
    have h2 := ((hasDerivAt_sin φ).pow 2).const_mul (b ^ 2)
    convert h1.add h2 using 1
    simp
  have h := HasDerivAt.sqrt hQ (ellipseQ_pos ha hb φ).ne'
  have hs := (ellipseSpeed_pos ha hb φ).ne'
  refine h.congr_deriv ?_
  simp only [ellipseSpeed] at hs ⊢
  field_simp
  ring

private lemma ellipse_normal_aux (a b φ : ℝ) :
    planarNormalRotation *ᵥ ellipseTangent a b φ =
      (ellipseSpeed a b φ)⁻¹ • ![-(b * sin φ), -(a * cos φ)] := by
  ext i
  fin_cases i <;> simp [ellipseTangent, planarNormalRotation, mulVec, dotProduct]

/-- **The elliptical chart is a regular planar chart (MLS Exercise 17(b), p. 263)** with speed `σ`,
unit tangent `t` and curvature `a b/σ³`, for `a, b > 0`. -/
theorem isRegularCurve_ellipse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsRegularCurve (ellipseCurve a b) (ellipseTangent a b) (ellipseSpeed a b)
      (ellipseCurvature a b) where
  hasDerivAt φ := by
    have hs := (ellipseSpeed_pos ha hb φ).ne'
    convert hasDerivAt_ellipseCurve a b φ using 1
    rw [ellipseTangent, smul_smul, mul_inv_cancel₀ hs, one_smul]
  unit φ := by
    have hs := (ellipseSpeed_pos ha hb φ).ne'
    have h2 := ellipseSpeed_sq a b φ
    simp [ellipseTangent, dotProduct]
    field_simp
    linear_combination -h2
  hasDerivAt_normal φ := by
    have hs := (ellipseSpeed_pos ha hb φ).ne'
    have h2 := ellipseSpeed_sq a b φ
    have hv := hasDerivAt_vec2 ((hasDerivAt_sin φ).const_mul b).neg
      ((hasDerivAt_cos φ).const_mul a).neg
    have h := ((hasDerivAt_ellipseSpeed ha hb φ).inv hs).smul hv
    have hf : (fun s => planarNormalRotation *ᵥ ellipseTangent a b s) =
        (ellipseSpeed a b)⁻¹ • fun x => ![-(b * sin x), -(a * cos x)] := by
      funext x
      rw [ellipse_normal_aux]
      rfl
    rw [hf]
    refine h.congr_deriv ?_
    have hsc := sin_sq_add_cos_sq φ
    ext i
    fin_cases i <;> simp [ellipseTangent, ellipseCurvature] <;> field_simp
    · linear_combination (-cos φ) * h2 + (-a ^ 2 * cos φ) * hsc
    · linear_combination sin φ * h2 + b ^ 2 * sin φ * hsc

/-- **The normal of the elliptical chart points out of the ellipse (MLS Exercise 17(b), p. 263):**
`n = J t = (−b sin φ, −a cos φ)/σ(φ)`, a positive multiple of the gradient `(2x/a², 2y/b²)` of
`x²/a² + y²/b²` at `c_f(φ)`. -/
theorem ellipse_normal (a b φ : ℝ) :
    planarNormalRotation *ᵥ ellipseTangent a b φ =
      (ellipseSpeed a b φ)⁻¹ • ![-(b * sin φ), -(a * cos φ)] := by
  exact ellipse_normal_aux a b φ

/-- **The rotation of the plane by `θ` (MLS Exercise 17, p. 262, `g_of = (p, R) ∈ SE(2)`):**
`R(θ) = [[cos θ, −sin θ], [sin θ, cos θ]]`. -/
def planeRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos θ, -sin θ; sin θ, cos θ]

/-- **The derivative of `R(θ)` with respect to `θ` (MLS Exercise 17, p. 262):**
`dR/dθ = [[−sin θ, −cos θ], [cos θ, −sin θ]] = J R(θ)`. -/
def planeRotationDeriv (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-sin θ, -cos θ; cos θ, -sin θ]

/-- **`R(θ)` lies in `SO(2)` (MLS Exercise 17, p. 262).** -/
theorem planeRotation_mem (θ : ℝ) : planeRotation θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [planeRotation, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  exact ⟨rfl, by ring, by rw [neg_sq]; exact cos_sq_add_sin_sq θ⟩

/-- The derivative of the rotation `R(θ)` of the plane (MLS Exercise 17, p. 262). -/
private lemma hasDerivAt_planeRotation (θ : ℝ) :
    HasDerivAt planeRotation (planeRotationDeriv θ) θ := by
  refine Control.hasDerivAt_matrix_iff.mpr fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [planeRotation, planeRotationDeriv, hasDerivAt_sin, hasDerivAt_cos]
  · exact (hasDerivAt_sin θ).neg

/-- **MLS Exercise 17(b), printed p. 263: the equations of contact for an elliptical finger rolling
on a line.** Let the finger, the ellipse `c_f` with semi-axes `a, b > 0`, turn by `θ(s)` and
translate by `p(s)` so that it touches the line `c_o(s) = (s, 0)` with opposed normals near `t`, the
contact coordinates being `φ` on the ellipse and `s_o` on the line, all with derivatives at `t`. If
the finger rolls at `t` (`Ṙ c_f + ṗ = 0`), then `φ̇ = (σ(φ)²/(a b)) θ̇` and
`ṡ_o = −(σ(φ)³/(a b)) θ̇`, with `σ(φ) = √(a² cos² φ + b² sin² φ)`. -/
theorem exercise17b {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {p : ℝ → Fin 2 → ℝ} {θ so φ : ℝ → ℝ}
    {p' : Fin 2 → ℝ} {θ' so' φ' t : ℝ} (hp : HasDerivAt p p' t) (hθ : HasDerivAt θ θ' t)
    (hso : HasDerivAt so so' t) (hφ : HasDerivAt φ φ' t)
    (hc : ∀ᶠ s in 𝓝 t, lineCurve (so s) = p s + planeRotation (θ s) *ᵥ ellipseCurve a b (φ s))
    (hn : ∀ᶠ s in 𝓝 t, planarNormalRotation *ᵥ lineTangent (so s) =
      -(planeRotation (θ s) *ᵥ (planarNormalRotation *ᵥ ellipseTangent a b (φ s))))
    (hroll : (θ' • planeRotationDeriv (θ t)) *ᵥ ellipseCurve a b (φ t) + p' = 0) :
    φ' = ellipseSpeed a b (φ t) ^ 2 / (a * b) * θ' ∧
      so' = -(ellipseSpeed a b (φ t) ^ 3 / (a * b)) * θ' := by
  have hRd : HasDerivAt (fun s => planeRotation (θ s)) (θ' • planeRotationDeriv (θ t)) t := by
    refine Control.hasDerivAt_matrix_iff.mpr fun i j => ?_
    have h := (Control.hasDerivAt_matrix_iff.mp (hasDerivAt_planeRotation (θ t)) i j).comp t hθ
    exact h.congr_deriv (by simp [mul_comm])
  have hs := ellipseSpeed_pos ha hb (φ t)
  have hK : lineCurvature (so t) + ellipseCurvature a b (φ t) ≠ 0 := by
    simp only [lineCurvature, ellipseCurvature, zero_add]
    positivity
  obtain ⟨h1, h2⟩ := planarRegularContact_kinematics (R := fun s => planeRotation (θ s))
    isUnitSpeedCurve_line.isRegularCurve (isRegularCurve_ellipse ha hb)
    (planeRotation_mem (θ t)) hp hRd hso hφ hc hn hK
  rw [hroll] at h1 h2
  have N := congrFun hn.self_of_nhds 1
  rw [ellipse_normal_aux] at h1 h2 N
  simp [lineTangent, lineCurvature, ellipseCurvature, planeRotation, planeRotationDeriv,
    planarNormalRotation, mulVec, dotProduct] at h1 h2 N
  field_simp at h1 h2 N
  refine ⟨?_, ?_⟩ <;> field_simp
  · linear_combination h1 - ellipseSpeed a b (φ t) * θ' * N
  · linear_combination h2 + ellipseSpeed a b (φ t) ^ 2 * θ' * N

/-- **The contact angle of a rolling ellipse (instance of MLS Exercise 17(b), p. 263):**
`φ(θ) = arctan((a/b) tan θ)`, for which the normal of the ellipse at `φ`, turned by `θ`, points
straight down, for `|θ| < π/2`. -/
def ellipseRollAngle (a b θ : ℝ) : ℝ := arctan (a / b * tan θ)

/-- **The translation of the rolling ellipse (instance of MLS Exercise 17(b), p. 263):**
`p(θ) = (−(a²/b) θ, 0) − R(θ) c_f(φ(θ))`, chosen so that the contact point is `s_o(θ) = −(a²/b) θ`
on the line. -/
def ellipseRollPosition (a b θ : ℝ) : Fin 2 → ℝ :=
  lineCurve (-(a ^ 2 / b) * θ) - planeRotation θ *ᵥ ellipseCurve a b (ellipseRollAngle a b θ)

/-- **A concrete motion satisfying every hypothesis of `exercise17b` at `t = 0` (instance of MLS
Exercise 17(b), p. 263):** with `θ(s) = s`, `φ(s) = arctan((a/b) tan s)`, `s_o(s) = −(a²/b) s` and
`p` as in `ellipseRollPosition`, the ellipse touches the line with opposed normals for `|s| < π/2`
and rolls at `s = 0`; the theorem gives `φ̇(0) = a/b` and `ṡ_o(0) = −a²/b`, the derivatives of the
chosen curves. -/
theorem ellipseRolling_instance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ p' : Fin 2 → ℝ, HasDerivAt (ellipseRollPosition a b) p' 0 ∧
      HasDerivAt (ellipseRollAngle a b) (a / b) 0 ∧
      (∀ᶠ s in 𝓝 0, lineCurve (-(a ^ 2 / b) * s) =
        ellipseRollPosition a b s + planeRotation s *ᵥ ellipseCurve a b (ellipseRollAngle a b s)) ∧
      (∀ᶠ s in 𝓝 0, planarNormalRotation *ᵥ lineTangent (-(a ^ 2 / b) * s) =
        -(planeRotation s *ᵥ
          (planarNormalRotation *ᵥ ellipseTangent a b (ellipseRollAngle a b s)))) ∧
      ((1 : ℝ) • planeRotationDeriv 0) *ᵥ ellipseCurve a b (ellipseRollAngle a b 0) + p' = 0 ∧
      a / b = ellipseSpeed a b (ellipseRollAngle a b 0) ^ 2 / (a * b) * 1 ∧
      -(a ^ 2 / b) = -(ellipseSpeed a b (ellipseRollAngle a b 0) ^ 3 / (a * b)) * 1 := by
  have hφ : HasDerivAt (ellipseRollAngle a b) (a / b) 0 := by
    have h := ((Real.hasDerivAt_tan (by simp : cos (0 : ℝ) ≠ 0)).const_mul (a / b)).arctan
    exact h.congr_deriv (by simp)
  have hφ0 : ellipseRollAngle a b 0 = 0 := by simp [ellipseRollAngle]
  have hl : HasDerivAt (fun s => lineCurve (-(a ^ 2 / b) * s)) ![-(a ^ 2 / b), 0] 0 :=
    (hasDerivAt_vec2 ((hasDerivAt_id' (0 : ℝ)).const_mul (-(a ^ 2 / b)))
      (hasDerivAt_const (0 : ℝ) (0 : ℝ))).congr_deriv (by simp)
  have hE := (hasDerivAt_ellipseCurve a b (ellipseRollAngle a b 0)).scomp 0 hφ
  have hM := Control.hasDerivAt_matrix_mulVec
    (Control.hasDerivAt_matrix_iff.mp (hasDerivAt_planeRotation 0)) hE
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < cos s :=
    continuousAt_const.eventually_lt continuous_cos.continuousAt (by simp)
  refine ⟨![-b, 0], ?_, hφ, Filter.Eventually.of_forall fun s => ?_, ?_, ?_, ?_, ?_⟩
  · refine (hl.sub hM).congr_deriv ?_
    ext i
    fin_cases i <;> simp [hφ0, planeRotation, planeRotationDeriv, ellipseCurve]
    field_simp
    ring
  · simp [ellipseRollPosition]
  · filter_upwards [hev] with s hs
    set φ := ellipseRollAngle a b s with hφs
    have hsin : sin φ = a / b * tan s / √(1 + (a / b * tan s) ^ 2) := sin_arctan _
    have hcos : cos φ = 1 / √(1 + (a / b * tan s) ^ 2) := cos_arctan _
    have hcφ : 0 < cos φ := cos_arctan_pos _
    have hr : 0 < √(1 + (a / b * tan s) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hsc := sin_sq_add_cos_sq s
    have hcross : b * cos s * sin φ = a * sin s * cos φ := by
      rw [hsin, hcos, tan_eq_sin_div_cos]
      field_simp
    have hwc : (b * sin s * sin φ + a * cos s * cos φ) * cos s = a * cos φ := by
      linear_combination sin s * hcross + a * cos φ * hsc
    have hw : 0 < b * sin s * sin φ + a * cos s * cos φ := by
      have : b * sin s * sin φ + a * cos s * cos φ = a * cos φ / cos s := by
        field_simp
        linear_combination hwc
      rw [this]
      positivity
    have hQ : a ^ 2 * cos φ ^ 2 + b ^ 2 * sin φ ^ 2 =
        (b * sin s * sin φ + a * cos s * cos φ) ^ 2 := by
      linear_combination (-(a ^ 2 * cos φ ^ 2 + b ^ 2 * sin φ ^ 2)) * hsc +
        (b * cos s * sin φ - a * sin s * cos φ) * hcross
    have hσ : ellipseSpeed a b φ = b * sin s * sin φ + a * cos s * cos φ := by
      rw [ellipseSpeed, hQ, Real.sqrt_sq hw.le]
    rw [ellipse_normal_aux, hσ]
    ext i
    fin_cases i <;>
      simp [lineTangent, planeRotation, planarNormalRotation, mulVec, dotProduct]
    · field_simp
      linear_combination -hcross
    · field_simp
      ring
  · rw [hφ0]
    ext i
    fin_cases i <;> simp [planeRotationDeriv, ellipseCurve]
  · simp [hφ0, ellipseSpeed, Real.sqrt_sq ha.le]
    field_simp
  · simp [hφ0, ellipseSpeed, Real.sqrt_sq ha.le]
    field_simp

end Examples
end RoboLean
