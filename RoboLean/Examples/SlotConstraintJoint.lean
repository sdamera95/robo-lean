import RoboLean.Examples.SlotConstraint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The slot of §6.3 in joint coordinates: the printed elbow-down parameterization and its Jacobian

MLS Chapter 4, §6.3, printed p. 204: "If the end of the manipulator is at a position `s` along the
slot, then the `xy` coordinates of the end-effector are `x(s) = l + s cos α`, `y(s) = s sin α`.
Solving the inverse kinematics … and assuming the elbow down solution, we have"
`f(s) = (θ₁(s), θ₂(s))` with
`θ₁(s) = tan⁻¹(s sin α / (l + s cos α)) + cos⁻¹((s² + 2ls cos α + l² + l₁² − l₂²) /
(2l₁√(s² + 2ls cos α + l²)))` and `θ₂(s) = π + cos⁻¹((l₁² + l₂² − s² − 2ls cos α − l²)/(2l₁l₂))`,
and "the Jacobian of the mapping is given by" the printed column `J` "(after some simplification)".

Statements, with `R(s) = s² + 2ls cos α + l²` (the squared distance of `(x(s), y(s))` from the base):
* the printed `f(s)` places the end-effector of the planar arm at `(x(s), y(s))`, so `h(f(s)) = 0`,
  whenever `l₁, l₂ > 0`, `l + s cos α > 0` and `(l₁ − l₂)² ≤ R(s) ≤ (l₁ + l₂)²`
  (`planarArmXY_slotElbowDown`, `slotJointConstraint_slotElbowDown`);
* each component of `f` has the printed component of `J` as its derivative at `s` under the strict
  inequalities `(l₁ − l₂)² < R(s) < (l₁ + l₂)²` (`hasDerivAt_slotElbowDown_zero`, `_one`).

Hypotheses the book does not state: `l + s cos α > 0` (the principal `tan⁻¹` gives the polar angle
of `(x, y)` only for `x > 0`) and the reachability bounds (the arguments of `cos⁻¹` in `[−1, 1]`,
strictly inside for the derivative). With `θ₂ ∈ [π, 2π]` the forearm turns clockwise from the first
link; this is the configuration the printed formulas give, called "elbow down" by the book. Angles
from `+x` as in `planarArmXY`; Lean `f s 0`, `f s 1` are the book's `θ₁(s)`, `θ₂(s)`.
-/

noncomputable section

open Real

namespace RoboLean.Examples

/-- The squared distance `R(s) = s² + 2ls cos α + l²` of the slot point `(l + s cos α, s sin α)`
from the base (MLS p. 204, the radicand `s² + 2ls cos α + l²` in `f(s)` and `J`). -/
def slotRadiusSq (l α s : ℝ) : ℝ := s ^ 2 + 2 * l * s * Real.cos α + l ^ 2

/-- **MLS p. 204: the printed elbow-down parameterization `f(s)` of the slot in joint coordinates**,
`θ₁(s) = tan⁻¹(s sin α / (l + s cos α)) + cos⁻¹((R + l₁² − l₂²)/(2l₁√R))`,
`θ₂(s) = π + cos⁻¹((l₁² + l₂² − R)/(2l₁l₂))`, with `R = s² + 2ls cos α + l²`. -/
def slotElbowDown (l α l₁ l₂ s : ℝ) : Fin 2 → ℝ :=
  ![Real.arctan (s * Real.sin α / (l + s * Real.cos α)) +
      Real.arccos ((slotRadiusSq l α s + l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * √(slotRadiusSq l α s))),
    Real.pi + Real.arccos ((l₁ ^ 2 + l₂ ^ 2 - slotRadiusSq l α s) / (2 * l₁ * l₂))]

private theorem slotRadiusSq_eq (l α s : ℝ) :
    slotRadiusSq l α s = (l + s * Real.cos α) ^ 2 + (s * Real.sin α) ^ 2 := by
  rw [slotRadiusSq]
  linear_combination (-(s ^ 2)) * Real.sin_sq_add_cos_sq α

private theorem reach_factor (R l₁ l₂ : ℝ) :
    (R + l₁ ^ 2 - l₂ ^ 2) ^ 2 - 4 * l₁ ^ 2 * R = (R - (l₁ + l₂) ^ 2) * (R - (l₁ - l₂) ^ 2) := by
  ring

private theorem reach_factor' (R l₁ l₂ : ℝ) :
    (l₁ ^ 2 + l₂ ^ 2 - R) ^ 2 - 4 * l₁ ^ 2 * l₂ ^ 2 =
      (R - (l₁ + l₂) ^ 2) * (R - (l₁ - l₂) ^ 2) := by
  ring

/-- Polar form of the slot point through the principal arctangent, for `x > 0`. -/
private theorem cos_sin_arctan_div {x y r : ℝ} (hx : 0 < x) (hr : 0 < r) (hr2 : r ^ 2 = x ^ 2 + y ^ 2) :
    r * Real.cos (Real.arctan (y / x)) = x ∧ r * Real.sin (Real.arctan (y / x)) = y := by
  have hq : √(1 + (y / x) ^ 2) = r / x := by
    rw [show 1 + (y / x) ^ 2 = (r / x) ^ 2 by field_simp; linarith]
    exact Real.sqrt_sq (div_pos hr hx).le
  rw [Real.cos_arctan, Real.sin_arctan, hq]
  constructor <;> field_simp

/-- **MLS p. 204: the printed `f(s)` solves the inverse kinematics of the slot.** For positive link
lengths, `l + s cos α > 0` and `(l₁ − l₂)² ≤ R(s) ≤ (l₁ + l₂)²` (hypotheses not printed), the planar
arm at `f(s)` has its end-effector at `(x(s), y(s)) = (l + s cos α, s sin α)`. -/
theorem planarArmXY_slotElbowDown {l α l₁ l₂ s : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hx : 0 < l + s * Real.cos α) (hlo : (l₁ - l₂) ^ 2 ≤ slotRadiusSq l α s)
    (hhi : slotRadiusSq l α s ≤ (l₁ + l₂) ^ 2) :
    planarArmXY l₁ l₂ (slotElbowDown l α l₁ l₂ s) = slotPath l α ![s] := by
  set R := slotRadiusSq l α s with hR
  set x := l + s * Real.cos α with hxdef
  set y := s * Real.sin α with hydef
  have hRxy : R = x ^ 2 + y ^ 2 := slotRadiusSq_eq l α s
  have hR0 : 0 < R := by rw [hRxy]; positivity
  set r := √R with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hR0
  have hr2 : r ^ 2 = R := Real.sq_sqrt hR0.le
  obtain ⟨hc, hs⟩ := cos_sin_arctan_div (y := y) hx hr0 (by rw [hr2, hRxy])
  set u := (R + l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * r) with hudef
  set v := (l₁ ^ 2 + l₂ ^ 2 - R) / (2 * l₁ * l₂) with hvdef
  have hfac : (R - (l₁ + l₂) ^ 2) * (R - (l₁ - l₂) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hu2 : u ^ 2 ≤ 1 := by
    rw [hudef, div_pow, div_le_one (by positivity), mul_pow, mul_pow, hr2]
    nlinarith [reach_factor R l₁ l₂]
  have hv2 : v ^ 2 ≤ 1 := by
    rw [hvdef, div_pow, div_le_one (by positivity), mul_pow, mul_pow]
    nlinarith [reach_factor' R l₁ l₂]
  have hu1 : -1 ≤ u ∧ u ≤ 1 := abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr (by nlinarith))
  have hv1 : -1 ≤ v ∧ v ≤ 1 := abs_le.mp (abs_le_one_iff_mul_self_le_one.mpr (by nlinarith))
  set Su := √(1 - u ^ 2) with hSu
  set Sv := √(1 - v ^ 2) with hSv
  have hSu2 : Su ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by linarith)
  have hSv2 : Sv ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by linarith)
  have h1 : l₁ - l₂ * v = r * u := by
    rw [hudef, hvdef]
    field_simp
    ring
  have h2 : l₂ * Sv = r * Su := by
    have hsq : (l₂ * Sv) ^ 2 = (r * Su) ^ 2 := by
      rw [mul_pow, mul_pow, hSv2, hSu2, hr2, hudef, hvdef, div_pow, div_pow, mul_pow, mul_pow,
        mul_pow, hr2]
      field_simp
      ring
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  have h3 : u ^ 2 + Su ^ 2 = 1 := by rw [hSu2]; ring
  have cβ : Real.cos (Real.arccos u) = u := Real.cos_arccos hu1.1 hu1.2
  have sβ : Real.sin (Real.arccos u) = Su := Real.sin_arccos u
  have cγ : Real.cos (Real.pi + Real.arccos v) = -v := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_arccos hv1.1 hv1.2]; ring
  have sγ : Real.sin (Real.pi + Real.arccos v) = -Sv := by
    rw [Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_arccos]; ring
  set cφ := Real.cos (Real.arctan (y / x))
  set sφ := Real.sin (Real.arctan (y / x))
  funext i
  fin_cases i
  · simp only [planarArmXY, slotPath, slotElbowDown, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.isValue]
    rw [show s * Real.sin α / (l + s * Real.cos α) = y / x from rfl, ← hR, ← hrdef, ← hudef,
      ← hvdef, Real.cos_add (Real.arctan (y / x) + Real.arccos u) (Real.pi + Real.arccos v),
      Real.cos_add (Real.arctan (y / x)) (Real.arccos u),
      Real.sin_add (Real.arctan (y / x)) (Real.arccos u), cβ, sβ, cγ, sγ]
    linear_combination (cφ * u - sφ * Su) * h1 + (cφ * Su + sφ * u) * h2 + cφ * r * h3 + hc
  · simp only [planarArmXY, slotPath, slotElbowDown, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.mk_one, Fin.isValue]
    rw [show s * Real.sin α / (l + s * Real.cos α) = y / x from rfl, ← hR, ← hrdef, ← hudef,
      ← hvdef, Real.sin_add (Real.arctan (y / x) + Real.arccos u) (Real.pi + Real.arccos v),
      Real.cos_add (Real.arctan (y / x)) (Real.arccos u),
      Real.sin_add (Real.arctan (y / x)) (Real.arccos u), cβ, sβ, cγ, sγ]
    linear_combination (sφ * u + cφ * Su) * h1 + (sφ * Su - cφ * u) * h2 + sφ * r * h3 + hs

/-- **MLS p. 204: `h(f(s)) = 0`**: under the hypotheses of `planarArmXY_slotElbowDown`, the slot
constraint in joint coordinates vanishes at the printed `f(s)`. -/
theorem slotJointConstraint_slotElbowDown {l α l₁ l₂ s : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hx : 0 < l + s * Real.cos α) (hlo : (l₁ - l₂) ^ 2 ≤ slotRadiusSq l α s)
    (hhi : slotRadiusSq l α s ≤ (l₁ + l₂) ^ 2) :
    slotJointConstraint l₁ l₂ l α (slotElbowDown l α l₁ l₂ s) = 0 := by
  rw [slotJointConstraint, planarArmXY_slotElbowDown hl₁ hl₂ hx hlo hhi]
  funext i
  fin_cases i
  simp [slotConstraint, slotPath]
  ring

private theorem hasDerivAt_slotRadiusSq (l α s : ℝ) :
    HasDerivAt (fun s' => slotRadiusSq l α s') (2 * (s + l * Real.cos α)) s := by
  have h := ((hasDerivAt_pow 2 s).add ((hasDerivAt_id s).const_mul (2 * l * Real.cos α))).add_const
    (l ^ 2)
  convert h using 1
  · funext s'
    simp only [slotRadiusSq, id, Pi.add_apply]
    ring
  · norm_num
    ring

/-- **MLS p. 204: the first entry of the printed Jacobian `J`**,
`dθ₁/ds = −(s + l cos α)(R − l₁² + l₂²) / (2l₁ R^{3/2} √(1 − (R + l₁² − l₂²)²/(4l₁²R)))
+ l sin α/(s² + l² + 2ls cos α)`, at every `s` with `l₁ > 0`, `l + s cos α > 0` and
`(l₁ − l₂)² < R(s) < (l₁ + l₂)²`. `R^{3/2}` is written `(√R)³`. -/
theorem hasDerivAt_slotElbowDown_zero {l α l₁ l₂ s : ℝ} (hl₁ : 0 < l₁)
    (hx : 0 < l + s * Real.cos α) (hlo : (l₁ - l₂) ^ 2 < slotRadiusSq l α s)
    (hhi : slotRadiusSq l α s < (l₁ + l₂) ^ 2) :
    HasDerivAt (fun s' => slotElbowDown l α l₁ l₂ s' 0)
      (-(s + l * Real.cos α) * (slotRadiusSq l α s - l₁ ^ 2 + l₂ ^ 2) /
          (2 * l₁ * √(slotRadiusSq l α s) ^ 3 *
            √(1 - (slotRadiusSq l α s + l₁ ^ 2 - l₂ ^ 2) ^ 2 /
              (4 * l₁ ^ 2 * slotRadiusSq l α s))) +
        l * Real.sin α / (s ^ 2 + l ^ 2 + 2 * l * s * Real.cos α)) s := by
  set R := slotRadiusSq l α s with hR
  have hRxy : R = (l + s * Real.cos α) ^ 2 + (s * Real.sin α) ^ 2 := slotRadiusSq_eq l α s
  have hR0 : 0 < R := by rw [hRxy]; positivity
  set r := √R with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hR0
  have hr2 : r ^ 2 = R := Real.sq_sqrt hR0.le
  set u := (R + l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * r) with hudef
  have hfac : (R - (l₁ + l₂) ^ 2) * (R - (l₁ - l₂) ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hu2 : u ^ 2 < 1 := by
    rw [hudef, div_pow, div_lt_one (by positivity), mul_pow, mul_pow, hr2]
    nlinarith [reach_factor R l₁ l₂]
  have hum : u ≠ -1 := by intro h; rw [h] at hu2; norm_num at hu2
  have hup : u ≠ 1 := by intro h; rw [h] at hu2; norm_num at hu2
  -- the arctangent term
  have hwd : HasDerivAt (fun s' => s' * Real.sin α / (l + s' * Real.cos α))
      ((1 * Real.sin α * (l + s * Real.cos α) - s * Real.sin α * (1 * Real.cos α)) /
        (l + s * Real.cos α) ^ 2) s :=
    ((hasDerivAt_id s).mul_const _).div (((hasDerivAt_id s).mul_const _).const_add l) hx.ne'
  -- the arccosine term
  have hsq : HasDerivAt (fun s' => √(slotRadiusSq l α s')) (2 * (s + l * Real.cos α) / (2 * r)) s :=
    (hasDerivAt_slotRadiusSq l α s).sqrt hR0.ne'
  have hud : HasDerivAt (fun s' => (slotRadiusSq l α s' + l₁ ^ 2 - l₂ ^ 2) /
      (2 * l₁ * √(slotRadiusSq l α s')))
      ((2 * (s + l * Real.cos α) * (2 * l₁ * r) -
          (R + l₁ ^ 2 - l₂ ^ 2) * (2 * l₁ * (2 * (s + l * Real.cos α) / (2 * r)))) /
        (2 * l₁ * r) ^ 2) s :=
    (((hasDerivAt_slotRadiusSq l α s).add_const _).sub_const _).div (hsq.const_mul _)
      (by positivity)
  have h := (hwd.arctan).add ((Real.hasDerivAt_arccos hum hup).comp s hud)
  have hX : 1 - u ^ 2 = 1 - (R + l₁ ^ 2 - l₂ ^ 2) ^ 2 / (4 * l₁ ^ 2 * R) := by
    rw [hudef, div_pow, mul_pow, mul_pow, hr2]
    ring
  have hXpos : 0 < 1 - u ^ 2 := by linarith
  have h' : HasDerivAt (fun s' => slotElbowDown l α l₁ l₂ s' 0)
      (1 / (1 + (s * Real.sin α / (l + s * Real.cos α)) ^ 2) *
          ((1 * Real.sin α * (l + s * Real.cos α) - s * Real.sin α * (1 * Real.cos α)) /
            (l + s * Real.cos α) ^ 2) +
        -(1 / √(1 - u ^ 2)) *
          ((2 * (s + l * Real.cos α) * (2 * l₁ * r) -
              (R + l₁ ^ 2 - l₂ ^ 2) * (2 * l₁ * (2 * (s + l * Real.cos α) / (2 * r)))) /
            (2 * l₁ * r) ^ 2)) s := h
  refine h'.congr_deriv ?_
  · rw [← hX]
    have hq : 0 < √(1 - u ^ 2) := Real.sqrt_pos.mpr hXpos
    have hden : s ^ 2 + l ^ 2 + 2 * l * s * Real.cos α = R := by rw [hR, slotRadiusSq]; ring
    rw [hden]
    have hw : 1 + (s * Real.sin α / (l + s * Real.cos α)) ^ 2 = R / (l + s * Real.cos α) ^ 2 := by
      rw [hRxy]
      field_simp
    rw [hw]
    field_simp
    rw [← hr2]
    ring

/-- **MLS p. 204: the second entry of the printed Jacobian `J`**,
`dθ₂/ds = 2(s + l cos α)/√(4l₁²l₂² − (R − l₁² − l₂²)²)`, at every `s` with `l₁, l₂ > 0` and
`(l₁ − l₂)² < R(s) < (l₁ + l₂)²`. -/
theorem hasDerivAt_slotElbowDown_one {l α l₁ l₂ s : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hlo : (l₁ - l₂) ^ 2 < slotRadiusSq l α s) (hhi : slotRadiusSq l α s < (l₁ + l₂) ^ 2) :
    HasDerivAt (fun s' => slotElbowDown l α l₁ l₂ s' 1)
      (2 * (s + l * Real.cos α) /
        √(4 * l₁ ^ 2 * l₂ ^ 2 - (slotRadiusSq l α s - l₁ ^ 2 - l₂ ^ 2) ^ 2)) s := by
  set R := slotRadiusSq l α s with hR
  set v := (l₁ ^ 2 + l₂ ^ 2 - R) / (2 * l₁ * l₂) with hvdef
  have hfac : (R - (l₁ + l₂) ^ 2) * (R - (l₁ - l₂) ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hD : 0 < 4 * l₁ ^ 2 * l₂ ^ 2 - (R - l₁ ^ 2 - l₂ ^ 2) ^ 2 := by
    nlinarith [reach_factor' R l₁ l₂]
  have hv2 : v ^ 2 < 1 := by
    rw [hvdef, div_pow, div_lt_one (by positivity), mul_pow, mul_pow]
    nlinarith [reach_factor' R l₁ l₂]
  have hvm : v ≠ -1 := by intro h; rw [h] at hv2; norm_num at hv2
  have hvp : v ≠ 1 := by intro h; rw [h] at hv2; norm_num at hv2
  have hvd : HasDerivAt (fun s' => (l₁ ^ 2 + l₂ ^ 2 - slotRadiusSq l α s') / (2 * l₁ * l₂))
      (-(2 * (s + l * Real.cos α)) / (2 * l₁ * l₂)) s :=
    ((hasDerivAt_slotRadiusSq l α s).const_sub (l₁ ^ 2 + l₂ ^ 2)).div_const _
  have h := ((Real.hasDerivAt_arccos hvm hvp).comp s hvd).const_add Real.pi
  have hS : √(1 - v ^ 2) = √(4 * l₁ ^ 2 * l₂ ^ 2 - (R - l₁ ^ 2 - l₂ ^ 2) ^ 2) / (2 * l₁ * l₂) := by
    rw [show 1 - v ^ 2 = (4 * l₁ ^ 2 * l₂ ^ 2 - (R - l₁ ^ 2 - l₂ ^ 2) ^ 2) / (2 * l₁ * l₂) ^ 2 by
      rw [hvdef]; field_simp; ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity)]
  have h' : HasDerivAt (fun s' => slotElbowDown l α l₁ l₂ s' 1)
      (-(1 / √(1 - v ^ 2)) * (-(2 * (s + l * Real.cos α)) / (2 * l₁ * l₂))) s := h
  refine h'.congr_deriv ?_
  rw [hS]
  have hq : 0 < √(4 * l₁ ^ 2 * l₂ ^ 2 - (R - l₁ ^ 2 - l₂ ^ 2) ^ 2) := Real.sqrt_pos.mpr hD
  field_simp

end RoboLean.Examples
