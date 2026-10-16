import RoboLean.Grasp.PlanarContactKinematics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Instances of the kinematics of planar contact (MLS Exercise 17(a))

MLS Chapter 5, Exercise 17(a), printed pp. 262–263, with the conventions of
`RoboLean.Grasp.PlanarContactKinematics`: points of the plane are `Fin 2 → ℝ`, a chart has unit
tangent `t`, normal `n = J t` with `J = [[0, −1], [1, 0]]` and curvature `K` defined by `n' = K t`,
and two curves are in contact when `c_o(s_o) = p + R c_f(s_f)` with opposed normals
`n_o(s_o) = −R n_f(s_f)`.

* The object is the line `c_o(s) = (s, 0)`, with tangent `(1, 0)`, normal `(0, 1)` and curvature
  `0`.
* The finger is the disk of radius `r > 0` centred at the origin, parameterized clockwise by arc
  length from its lowest point, `c_f(s) = (−r sin(s/r), −r cos(s/r))`, with tangent
  `(−cos(s/r), sin(s/r))`, outward normal `(−sin(s/r), −cos(s/r))` and curvature `1/r`.
* The disk rolls on the line: `p(t) = (r t, r)`, `R(t) = [[cos t, sin t], [−sin t, cos t]]`,
  `s_o(t) = r t` and `s_f(t) = −r t`. The contact and opposed-normal conditions hold at every time,
  and the two formulas of the exercise evaluate to `ṡ_f = −r` and `ṡ_o = r`.
* The disk slides on the line without rotating: `p(t) = (t, r)`, `R = 1`, `s_o(t) = t` and
  `s_f(t) = 0`. The two formulas evaluate to `ṡ_f = 0` and `ṡ_o = 1`.

In both motions the values are obtained by applying `Grasp.planarContact_kinematics`; the rolling
values are also recomputed directly from the formulas as a cross-check.
-/

noncomputable section

open Matrix Real

namespace RoboLean
namespace Examples

open Grasp

/-- A pair of real curves with derivatives `f'` and `g'` gives the plane curve `s ↦ (f s, g s)` with
the derivative `(f', g')` (used for the charts and motions of MLS Exercise 17(a), p. 262). -/
private lemma hasDerivAt_vec2 {f g : ℝ → ℝ} {f' g' s : ℝ} (hf : HasDerivAt f f' s)
    (hg : HasDerivAt g g' s) : HasDerivAt (fun x => ![f x, g x]) ![f', g'] s :=
  hasDerivAt_pi.mpr fun i => by fin_cases i <;> simpa

/-- **The line `c(s) = (s, 0)`** as a planar chart parameterized by arc length, the object of the
instances of MLS Exercise 17(a), p. 262 (points of the plane are `Fin 2 → ℝ`). -/
def lineCurve (s : ℝ) : Fin 2 → ℝ := ![s, 0]

/-- **The tangent `(1, 0)` of the line** `lineCurve` (MLS Exercise 17(a), p. 262; the tangent is the
derivative of the chart). -/
def lineTangent (_s : ℝ) : Fin 2 → ℝ := ![1, 0]

/-- **The curvature `0` of the line** `lineCurve` (MLS Exercise 17(a), p. 262; the curvature `K` is
defined by `n' = K t` with `n = J t`). -/
def lineCurvature (_s : ℝ) : ℝ := 0

/-- **The line is a unit-speed planar curve with tangent `(1, 0)` and curvature `0`** (MLS Exercise
17(a), p. 262; normal `n = J t = (0, 1)`, curvature defined by `n' = K t`). -/
theorem isUnitSpeedCurve_line : IsUnitSpeedCurve lineCurve lineTangent lineCurvature where
  hasDerivAt s := hasDerivAt_vec2 (hasDerivAt_id' s) (hasDerivAt_const s 0)
  unit s := by simp [lineTangent, dotProduct]
  hasDerivAt_normal s := by
    simpa [lineCurvature, lineTangent] using
      hasDerivAt_const s (planarNormalRotation *ᵥ ![(1 : ℝ), 0])

/-- **The disk of radius `r` centred at the origin, parameterized clockwise by arc length from its
lowest point**, `c(s) = (−r sin(s/r), −r cos(s/r))`, the finger of the instances of MLS Exercise
17(a), p. 262 (points of the plane are `Fin 2 → ℝ`). -/
def diskCurve (r s : ℝ) : Fin 2 → ℝ := ![-r * sin (s / r), -r * cos (s / r)]

/-- **The tangent `(−cos(s/r), sin(s/r))` of the disk** `diskCurve r` (MLS Exercise 17(a), p. 262;
the tangent is the derivative of the chart). -/
def diskTangent (r s : ℝ) : Fin 2 → ℝ := ![-cos (s / r), sin (s / r)]

/-- **The curvature `1/r` of the disk** `diskCurve r` (MLS Exercise 17(a), p. 262; the curvature `K`
is defined by `n' = K t` with `n = J t`, so the outward normal of a clockwise circle gives
`K = 1/r`). -/
def diskCurvature (r _s : ℝ) : ℝ := 1 / r

/-- **The disk of radius `r ≠ 0` is a unit-speed planar curve with tangent `(−cos(s/r), sin(s/r))`
and curvature `1/r`** (MLS Exercise 17(a), p. 262; normal `n = J t = (−sin(s/r), −cos(s/r))`,
outward for `r > 0`, curvature defined by `n' = K t`). -/
theorem isUnitSpeedCurve_disk {r : ℝ} (hr : r ≠ 0) :
    IsUnitSpeedCurve (diskCurve r) (diskTangent r) (diskCurvature r) where
  hasDerivAt s := by
    have h0 := (((hasDerivAt_id s).div_const r).sin).const_mul (-r)
    have h1 := (((hasDerivAt_id s).div_const r).cos).const_mul (-r)
    refine (hasDerivAt_vec2 h0 h1).congr_deriv ?_
    ext i
    fin_cases i <;> simp [diskTangent] <;> field_simp
  unit s := by simp [diskTangent, dotProduct, ← sq, cos_sq_add_sin_sq]
  hasDerivAt_normal s := by
    have h0 := (((hasDerivAt_id s).div_const r).sin).neg
    have h1 := (((hasDerivAt_id s).div_const r).cos).neg
    convert hasDerivAt_vec2 h0 h1 using 1
    · funext x
      ext i
      fin_cases i <;> simp [diskTangent, planarNormalRotation, mulVec, dotProduct]
    · ext i
      fin_cases i <;> simp [diskTangent, diskCurvature] <;> ring

/-- **The translation `p(t) = (r t, r)` of the disk rolling on the line** (instance of MLS Exercise
17(a), p. 262; `g_of = (p, R)` maps finger coordinates to object coordinates, `x ↦ p + R x`). -/
def rollingPosition (r t : ℝ) : Fin 2 → ℝ := ![r * t, r]

/-- **The rotation `R(t) = [[cos t, sin t], [−sin t, cos t]]` of the disk rolling on the line**
(instance of MLS Exercise 17(a), p. 262; the disk turns clockwise as it rolls in the `+x`
direction). -/
def rollingRotation (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos t, sin t; -sin t, cos t]

/-- **The derivative `Ṙ(t) = [[−sin t, cos t], [−cos t, −sin t]]` of the rolling rotation**
`rollingRotation` (instance of MLS Exercise 17(a), p. 262). -/
def rollingRotationDeriv (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-sin t, cos t; -cos t, -sin t]

/-- **The rolling rotation lies in `SO(2)`** (instance of MLS Exercise 17(a), p. 262, which takes
`g_of = (p, R) ∈ SE(2)`; Mathlib's `specialOrthogonalGroup`). -/
theorem rollingRotation_mem (t : ℝ) :
    rollingRotation t ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [rollingRotation, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  exact ⟨rfl, by ring, cos_sq_add_sin_sq t⟩

/-- **The rolling rotation has the derivative `rollingRotationDeriv`** (instance of MLS Exercise
17(a), p. 262; matrices carry the entrywise product topology). -/
theorem hasDerivAt_rollingRotation (t : ℝ) :
    HasDerivAt rollingRotation (rollingRotationDeriv t) t := by
  refine Control.hasDerivAt_matrix_iff.mpr fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rollingRotation, rollingRotationDeriv, hasDerivAt_sin, hasDerivAt_cos]
  exact (hasDerivAt_sin t).neg

/-- **The disk rolling on the line stays in contact:** `c_o(r s) = p(s) + R(s) c_f(−r s)` for every
`s`, with the line as the object and the disk of radius `r ≠ 0` as the finger (instance of MLS
Exercise 17(a), p. 262; contact convention `c_o(s_o) = p + R c_f(s_f)`). -/
theorem diskRolling_contact {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    lineCurve (r * s) = rollingPosition r s + rollingRotation s *ᵥ diskCurve r (-r * s) := by
  have hs : -(r * s) / r = -s := by field_simp
  ext i
  fin_cases i
  · simp [lineCurve, rollingPosition, rollingRotation, diskCurve, hs]
    ring
  · simp [lineCurve, rollingPosition, rollingRotation, diskCurve, hs]
    linear_combination r * cos_sq_add_sin_sq s

/-- **The disk rolling on the line keeps opposed normals:** `n_o(r s) = −R(s) n_f(−r s)` for every
`s`, with `n = J t` (instance of MLS Exercise 17(a), p. 262; opposed-normal convention
`n_o(s_o) = −R n_f(s_f)`). -/
theorem diskRolling_normal {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    planarNormalRotation *ᵥ lineTangent (r * s) =
      -(rollingRotation s *ᵥ (planarNormalRotation *ᵥ diskTangent r (-r * s))) := by
  have hs : -(r * s) / r = -s := by field_simp
  ext i
  fin_cases i
  · simp [lineTangent, rollingRotation, diskTangent, planarNormalRotation, hs, mulVec,
      dotProduct]
    ring
  · simp [lineTangent, rollingRotation, diskTangent, planarNormalRotation, hs, mulVec,
      dotProduct]
    linear_combination -cos_sq_add_sin_sq s

/-- **MLS Exercise 17(a), p. 262, for the disk of radius `r > 0` rolling on the line:** the two
printed right-hand sides, evaluated at time `t` with `p(t) = (r t, r)`,
`R(t) = [[cos t, sin t], [−sin t, cos t]]`, `s_o(t) = r t`, `s_f(t) = −r t`, `K_o = 0` and
`K_f = 1/r`, equal `ṡ_f = −r` and `ṡ_o = r`. The values come from `Grasp.planarContact_kinematics`,
whose hypotheses this motion satisfies (conventions of `RoboLean.Grasp.PlanarContactKinematics`:
`n_f = J t_f`, contact `c_o(s_o) = p + R c_f(s_f)` with opposed normals). -/
theorem diskRolling_contactRates {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (lineCurvature (r * t) + diskCurvature r (-r * t))⁻¹ *
        (lineTangent (r * t) ⬝ᵥ
            (rollingRotationDeriv t *ᵥ (planarNormalRotation *ᵥ diskTangent r (-r * t))) +
          lineCurvature (r * t) *
            (lineTangent (r * t) ⬝ᵥ
              (rollingRotationDeriv t *ᵥ diskCurve r (-r * t) + ![r, 0]))) = -r ∧
      (lineCurvature (r * t) + diskCurvature r (-r * t))⁻¹ *
        (-(lineTangent (r * t) ⬝ᵥ
            (rollingRotationDeriv t *ᵥ (planarNormalRotation *ᵥ diskTangent r (-r * t)))) +
          diskCurvature r (-r * t) *
            (lineTangent (r * t) ⬝ᵥ
              (rollingRotationDeriv t *ᵥ diskCurve r (-r * t) + ![r, 0]))) = r := by
  have hp : HasDerivAt (rollingPosition r) ![r, 0] t := by
    refine (hasDerivAt_vec2 ((hasDerivAt_id' t).const_mul r) (hasDerivAt_const t r)).congr_deriv ?_
    simp
  have hso : HasDerivAt (fun s => r * s) r t := by
    simpa using (hasDerivAt_id t).const_mul r
  have hsf : HasDerivAt (fun s => -r * s) (-r) t := by
    simpa using (hasDerivAt_id t).const_mul (-r)
  have hK : lineCurvature (r * t) + diskCurvature r (-r * t) ≠ 0 := by
    simp [lineCurvature, diskCurvature, hr.ne']
  obtain ⟨h1, h2⟩ := planarContact_kinematics isUnitSpeedCurve_line
    (isUnitSpeedCurve_disk hr.ne') (rollingRotation_mem t) hp (hasDerivAt_rollingRotation t)
    hso hsf (Filter.Eventually.of_forall (diskRolling_contact hr.ne'))
    (Filter.Eventually.of_forall (diskRolling_normal hr.ne')) hK
  exact ⟨h1.symm, h2.symm⟩

/-- Cross-check of `diskRolling_contactRates` by direct evaluation of the two printed right-hand
sides of MLS Exercise 17(a), p. 262, without the kinematics theorem. -/
example {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (lineCurvature (r * t) + diskCurvature r (-r * t))⁻¹ *
        (lineTangent (r * t) ⬝ᵥ
            (rollingRotationDeriv t *ᵥ (planarNormalRotation *ᵥ diskTangent r (-r * t))) +
          lineCurvature (r * t) *
            (lineTangent (r * t) ⬝ᵥ
              (rollingRotationDeriv t *ᵥ diskCurve r (-r * t) + ![r, 0]))) = -r ∧
      (lineCurvature (r * t) + diskCurvature r (-r * t))⁻¹ *
        (-(lineTangent (r * t) ⬝ᵥ
            (rollingRotationDeriv t *ᵥ (planarNormalRotation *ᵥ diskTangent r (-r * t)))) +
          diskCurvature r (-r * t) *
            (lineTangent (r * t) ⬝ᵥ
              (rollingRotationDeriv t *ᵥ diskCurve r (-r * t) + ![r, 0]))) = r := by
  have hs : -(r * t) / r = -t := by field_simp
  have hc := cos_sq_add_sin_sq t
  simp [lineCurvature, diskCurvature, lineTangent, rollingRotationDeriv, planarNormalRotation,
    diskTangent, diskCurve, hs, mulVec, dotProduct]
  exact ⟨by linear_combination (-r) * hc, by linear_combination (r - r ^ 2 * r⁻¹) * hc⟩

/-- **The translation `p(t) = (t, r)` of the disk sliding on the line without rotating** (instance
of MLS Exercise 17(a), p. 262; `g_of = (p, R)` with `R = 1`, `x ↦ p + x`). -/
def slidingPosition (r t : ℝ) : Fin 2 → ℝ := ![t, r]

/-- **The disk sliding on the line stays in contact:** `c_o(s) = p(s) + c_f(0)` for every `s`
(instance of MLS Exercise 17(a), p. 262, with `R = 1`; contact convention
`c_o(s_o) = p + R c_f(s_f)`). -/
theorem diskSliding_contact (r s : ℝ) :
    lineCurve s = slidingPosition r s + (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ diskCurve r 0 := by
  ext i
  fin_cases i <;> simp [lineCurve, slidingPosition, diskCurve]

/-- **The disk sliding on the line keeps opposed normals:** `n_o(s) = −n_f(0)` for every `s`, with
`n = J t` (instance of MLS Exercise 17(a), p. 262, with `R = 1`; opposed-normal convention
`n_o(s_o) = −R n_f(s_f)`). -/
theorem diskSliding_normal (r s : ℝ) :
    planarNormalRotation *ᵥ lineTangent s =
      -((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (planarNormalRotation *ᵥ diskTangent r 0)) := by
  ext i
  fin_cases i <;> simp [lineTangent, diskTangent, planarNormalRotation, mulVec, dotProduct]

/-- **MLS Exercise 17(a), p. 262, for the disk of radius `r > 0` sliding on the line without
rotating:** the two printed right-hand sides, evaluated at time `t` with `p(t) = (t, r)`, `R = 1`,
`Ṙ = 0`, `s_o(t) = t`, `s_f(t) = 0`, `K_o = 0` and `K_f = 1/r`, equal `ṡ_f = 0` and `ṡ_o = 1`. The
values come from `Grasp.planarContact_kinematics` (conventions of
`RoboLean.Grasp.PlanarContactKinematics`: `n_f = J t_f`, contact `c_o(s_o) = p + R c_f(s_f)` with
opposed normals). -/
theorem diskSliding_contactRates {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (lineCurvature t + diskCurvature r 0)⁻¹ *
        (lineTangent t ⬝ᵥ
            ((0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (planarNormalRotation *ᵥ diskTangent r 0)) +
          lineCurvature t *
            (lineTangent t ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ diskCurve r 0 + ![1, 0]))) =
        0 ∧
      (lineCurvature t + diskCurvature r 0)⁻¹ *
        (-(lineTangent t ⬝ᵥ
            ((0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (planarNormalRotation *ᵥ diskTangent r 0))) +
          diskCurvature r 0 *
            (lineTangent t ⬝ᵥ ((0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ diskCurve r 0 + ![1, 0]))) =
        1 := by
  have hp : HasDerivAt (slidingPosition r) ![1, 0] t := by
    exact hasDerivAt_vec2 (hasDerivAt_id' t) (hasDerivAt_const t r)
  have hK : lineCurvature t + diskCurvature r 0 ≠ 0 := by
    simp [lineCurvature, diskCurvature, hr.ne']
  obtain ⟨h1, h2⟩ := planarContact_kinematics (R := fun _ => 1) (R' := 0) (sf := fun _ => 0)
    isUnitSpeedCurve_line (isUnitSpeedCurve_disk hr.ne')
    (Matrix.specialOrthogonalGroup (Fin 2) ℝ).one_mem hp
    (Control.hasDerivAt_matrix_iff.mpr fun _ _ => hasDerivAt_const t _) (hasDerivAt_id' t)
    (hasDerivAt_const t 0)
    (Filter.Eventually.of_forall (diskSliding_contact r))
    (Filter.Eventually.of_forall (diskSliding_normal r)) hK
  exact ⟨h1.symm, h2.symm⟩

end Examples
end RoboLean
