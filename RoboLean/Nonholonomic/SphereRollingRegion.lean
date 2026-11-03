import RoboLean.Nonholonomic.SphereRolling
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The geometric phase of a sphere rolling on a plane for regions of the chart: MLS Theorem 8.6

MLS Chapter 8, §4.3, printed pp. 385–386: Theorem 8.6 ("Gauss–Bonnet theorem"): for a closed path
`α_f : [0, 1] → S_f` on the unit sphere enclosing a cap-shaped region `Ω` (Figure 8.4, p. 386),
rolling the sphere on the plane along `α_f` changes the contact angle by `Δψ = −Area of Ω` (8.37);
the proof integrates (8.36) `ψ̇ = −sin u_f v̇_f` and applies Green's theorem,
`∮ −sin u_f dv_f = −∬_Ω cos u_f dv_f du_f`, with the area form `cos u_f du_f dv_f`.

**What is formalized.**

* Regions between two graphs over an interval of `v`:
  `R = {(u, v) : v₀ ≤ v ≤ v₁, φ₁(v) ≤ u ≤ φ₂(v)}` for continuous `φ₁, φ₂` (`chartRegion`). Its
  boundary is traversed counterclockwise in the chart plane (`u` horizontal, `v` vertical) as four
  pieces in unit time each: the bottom segment `(φ₁(v₀), v₀) → (φ₂(v₀), v₀)`, the right graph
  `u = φ₂(v)` with `v` rising from `v₀` to `v₁` (`chartGraphPath`), the top segment
  `(φ₂(v₁), v₁) → (φ₁(v₁), v₁)` and the left graph `u = φ₁(v)` with `v` falling back to `v₀`.
  Rolling once around it changes `ψ` by `−∫_{v₀}^{v₁} ∫_{φ₁(v)}^{φ₂(v)} cos u du dv`
  (`sphere_geometricPhase_region`), which is `−∬_R cos u` as an integral over `R ⊆ ℝ²` for
  `v₀ ≤ v₁` and `φ₁ ≤ φ₂` (`setIntegral_chartRegion`, Fubini), the book's area of `R`. Since
  `ψ̇` involves only `dv_f`, the integral over each graph is a change of variables and the double
  integral is computed slice by slice; Green's theorem is not needed. Disks and convex regions of
  the chart are of this kind; rectangles are the case of constant `φ₁, φ₂`.
* The cap of Figure 8.4 bounded by a latitude circle `u = u₀` contains a pole and lies in no chart
  of this kind. Rolling once along the latitude circle with `v` decreasing changes `ψ` by
  `2π sin u₀ = 2π − ∬_{cap} cos u` (`sphere_geometricPhase_latitude`): the printed (8.37) holds
  for this cap modulo `2π`, not as an equality.

**Hypotheses the book does not state.** The loop is closed in the chart; the orientation is
counterclockwise in the chart plane `(u_f, v_f)`; the boundary pieces are graphs over `v` (or
coordinate segments). The identities hold for every such region of the coordinate plane; they are
the area on the unit sphere where the region lies in the chart domain `|u_f| < π/2` (MLS p. 247),
with the area form taken from the book (p. 386), not derived. No general Jordan curve, no region
with a pole and no finite union of regions is covered.

**Conventions.** As in `SphereRolling`: `α_f = (u_f, v_f)` in `Fin 2 → ℝ` with `u_f` entry `0`;
paths on `[0, 1]`; regions are subsets of `ℝ × ℝ` with `u` the first coordinate.
-/

noncomputable section

open Set Real MeasureTheory intervalIntegral

namespace RoboLean
namespace Nonholonomic

/-- **A boundary piece of a chart region (for MLS Theorem 8.6, p. 385):** the graph `u = φ(v)` with
`v` running linearly from `a` to `b` in unit time, `t ↦ (φ(a + t(b − a)), a + t(b − a))`. -/
def chartGraphPath (φ : ℝ → ℝ) (a b : ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![φ (a + t * (b - a)), a + t * (b - a)]

/-- **MLS proof of Theorem 8.6, p. 386, along a graph: `Δψ = −∫_a^b sin φ(v) dv`** when the sphere
rolls along `u_f = φ(v_f)` from `v_f = a` to `v_f = b` (`ψ̇ = −sin u_f v̇_f`, (8.36)), for `φ`
continuous. -/
theorem IsContactAngleAlong.sub_eq_integral_graph {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ}
    {ψ : ℝ → ℝ} (h : IsContactAngleAlong (chartGraphPath φ a b) ψ 1) :
    ψ 1 - ψ 0 = -∫ v in a..b, sin (φ v) := by
  have hv : ∀ t, deriv (fun s => chartGraphPath φ a b s 1) t = b - a := by
    intro t
    have : HasDerivAt (fun s => chartGraphPath φ a b s 1) (b - a) t := by
      simpa [chartGraphPath] using ((hasDerivAt_id t).mul_const (b - a)).const_add a
    exact this.deriv
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (-(sin (φ (a + t * (b - a))) * (b - a))) t := by
    intro t ht
    simpa [hv, chartGraphPath] using h t ht
  have hc : Continuous fun t => -(sin (φ (a + t * (b - a))) * (b - a)) := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by rwa [uIcc_of_le zero_le_one] at ht)) (hc.intervalIntegrable 0 1)
  have hcv : ∫ t in (0 : ℝ)..1, sin (φ (a + t * (b - a))) * (b - a) = ∫ v in a..b, sin (φ v) := by
    have h1 := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1) (fun v => sin (φ v))
      (b - a) a
    have h2 : a + (b - a) * 1 = b := by ring
    simp only [mul_zero, add_zero, h2, smul_eq_mul] at h1
    rw [← h1, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [mul_comm (b - a) t, mul_comm]
  rw [← hftc, intervalIntegral.integral_neg, hcv]

/-- **MLS Theorem 8.6, p. 385, for regions between two graphs over `v`: `Δψ = −Area`.** Rolling the
sphere on the plane once around the boundary of
`{(u, v) : v₀ ≤ v ≤ v₁, φ₁(v) ≤ u ≤ φ₂(v)}`, counterclockwise in the chart plane as the four pieces
bottom segment, right graph `u = φ₂(v)` upward, top segment, left graph `u = φ₁(v)` downward (each
in unit time, each starting where the previous ended), changes `ψ` by
`−∫_{v₀}^{v₁} ∫_{φ₁(v)}^{φ₂(v)} cos u du dv`, minus the area in the book's area form
`cos u_f du_f dv_f` (p. 386); `φ₁, φ₂` continuous. -/
theorem sphere_geometricPhase_region {φ₁ φ₂ : ℝ → ℝ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (v₀ v₁ : ℝ) {ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ}
    (h₁ : IsContactAngleAlong (chartSegment ![φ₁ v₀, v₀] ![φ₂ v₀, v₀]) ψ₁ 1)
    (h₂ : IsContactAngleAlong (chartGraphPath φ₂ v₀ v₁) ψ₂ 1)
    (h₃ : IsContactAngleAlong (chartSegment ![φ₂ v₁, v₁] ![φ₁ v₁, v₁]) ψ₃ 1)
    (h₄ : IsContactAngleAlong (chartGraphPath φ₁ v₁ v₀) ψ₄ 1)
    (h₁₂ : ψ₂ 0 = ψ₁ 1) (h₂₃ : ψ₃ 0 = ψ₂ 1) (h₃₄ : ψ₄ 0 = ψ₃ 1) :
    ψ₄ 1 - ψ₁ 0 = -∫ v in v₀..v₁, ∫ u in φ₁ v..φ₂ v, cos u := by
  have hseg : ∀ (p q : Fin 2 → ℝ) (t : ℝ), deriv (fun s => chartSegment p q s 1) t = q 1 - p 1 := by
    intro p q t
    have : HasDerivAt (fun s => chartSegment p q s 1) (q 1 - p 1) t := by
      simpa [chartSegment] using ((hasDerivAt_id t).mul_const (q 1 - p 1)).const_add (p 1)
    exact this.deriv
  have hconst : ∀ {φ : ℝ → ℝ} {c : ℝ}, (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ c t) → φ 1 - φ 0 = c := by
    intro φ c hφ
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hφ t (by rwa [uIcc_of_le zero_le_one] at ht))
      (intervalIntegrable_const (c := c))
    simpa using this.symm
  have e₁ : ψ₁ 1 - ψ₁ 0 = 0 := hconst fun t ht => by
    simpa [hseg, chartSegment] using h₁ t ht
  have e₂ := h₂.sub_eq_integral_graph hφ₂
  have e₃ : ψ₃ 1 - ψ₃ 0 = 0 := hconst fun t ht => by
    simpa [hseg, chartSegment] using h₃ t ht
  have e₄ := h₄.sub_eq_integral_graph hφ₁
  rw [intervalIntegral.integral_symm] at e₄
  have harea : ∫ v in v₀..v₁, ∫ u in φ₁ v..φ₂ v, cos u =
      (∫ v in v₀..v₁, sin (φ₂ v)) - ∫ v in v₀..v₁, sin (φ₁ v) := by
    simp only [integral_cos]
    exact intervalIntegral.integral_sub ((continuous_sin.comp hφ₂).intervalIntegrable _ _)
      ((continuous_sin.comp hφ₁).intervalIntegrable _ _)
  rw [harea]
  linarith

/-- **The region of the chart between two graphs over `v`** (for MLS Theorem 8.6, p. 385):
`{(u, v) : v₀ ≤ v ≤ v₁, φ₁(v) ≤ u ≤ φ₂(v)}` as a subset of `ℝ × ℝ`, `u` first. -/
def chartRegion (φ₁ φ₂ : ℝ → ℝ) (v₀ v₁ : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ Icc v₀ v₁ ∧ z.1 ∈ Icc (φ₁ z.2) (φ₂ z.2)}

/-- **MLS p. 386: the area of a chart region in the area form `cos u_f du_f dv_f`, by Fubini:**
`∬_R cos u = ∫_{v₀}^{v₁} ∫_{φ₁(v)}^{φ₂(v)} cos u du dv` for `R = chartRegion φ₁ φ₂ v₀ v₁`,
`φ₁, φ₂` continuous, `v₀ ≤ v₁` and `φ₁ ≤ φ₂` on `[v₀, v₁]` (Lebesgue measure on `ℝ × ℝ`). -/
theorem setIntegral_chartRegion {φ₁ φ₂ : ℝ → ℝ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    {v₀ v₁ : ℝ} (hv : v₀ ≤ v₁) (hle : ∀ v ∈ Icc v₀ v₁, φ₁ v ≤ φ₂ v) :
    ∫ z in chartRegion φ₁ φ₂ v₀ v₁, cos z.1 = ∫ v in v₀..v₁, ∫ u in φ₁ v..φ₂ v, cos u := by
  set R := chartRegion φ₁ φ₂ v₀ v₁ with hR
  have hRc : IsClosed R :=
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const)).inter
      ((isClosed_le (hφ₁.comp continuous_snd) continuous_fst).inter
        (isClosed_le continuous_fst (hφ₂.comp continuous_snd)))
  obtain ⟨c₁, hc₁⟩ := (isCompact_Icc (a := v₀) (b := v₁)).exists_bound_of_continuousOn
    hφ₁.continuousOn
  obtain ⟨c₂, hc₂⟩ := (isCompact_Icc (a := v₀) (b := v₁)).exists_bound_of_continuousOn
    hφ₂.continuousOn
  have hRK : IsCompact R := by
    refine (isCompact_Icc (a := ((-max c₁ c₂, v₀) : ℝ × ℝ))
      (b := (max c₁ c₂, v₁))).of_isClosed_subset hRc fun z hz => ⟨⟨?_, hz.1.1⟩, ⟨?_, hz.1.2⟩⟩
    · have := (abs_le.1 (by simpa using hc₁ z.2 hz.1)).1
      have := hz.2.1
      have := le_max_left c₁ c₂
      change -max c₁ c₂ ≤ z.1
      linarith
    · have := (abs_le.1 (by simpa using hc₂ z.2 hz.1)).2
      have := hz.2.2
      have := le_max_right c₁ c₂
      change z.1 ≤ max c₁ c₂
      linarith
  have hint : Integrable (R.indicator fun z : ℝ × ℝ => cos z.1) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hRc.measurableSet).2
      ((continuous_cos.comp continuous_fst).continuousOn.integrableOn_compact hRK)
  have hpt : ∀ v, ∫ u, R.indicator (fun z : ℝ × ℝ => cos z.1) (u, v) =
      (Icc v₀ v₁).indicator (fun v => ∫ u in φ₁ v..φ₂ v, cos u) v := by
    intro v
    by_cases hv' : v ∈ Icc v₀ v₁
    · rw [Set.indicator_of_mem hv', intervalIntegral.integral_of_le (hle v hv'),
        ← integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator measurableSet_Icc]
      congr 1
      funext u
      simp only [Set.indicator_apply, hR, chartRegion, Set.mem_ofPred_eq, hv', true_and]
    · rw [Set.indicator_of_notMem hv']
      have : ∀ u, R.indicator (fun z : ℝ × ℝ => cos z.1) (u, v) = 0 := fun u =>
        Set.indicator_of_notMem (fun hz => hv' hz.1) _
      simp [this]
  rw [intervalIntegral.integral_of_le hv, ← integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_indicator measurableSet_Icc,
    ← MeasureTheory.integral_indicator hRc.measurableSet,
    Measure.volume_eq_prod, integral_prod_symm _ hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- **MLS Theorem 8.6, p. 385, as an integral over the region:** under the hypotheses of
`sphere_geometricPhase_region`, with `v₀ ≤ v₁` and `φ₁ ≤ φ₂` on `[v₀, v₁]`,
`Δψ = −∬_R cos u_f du_f dv_f`, minus the area of `R` in the book's area form (p. 386). -/
theorem sphere_geometricPhase_chartRegion {φ₁ φ₂ : ℝ → ℝ} (hφ₁ : Continuous φ₁)
    (hφ₂ : Continuous φ₂) {v₀ v₁ : ℝ} (hv : v₀ ≤ v₁) (hle : ∀ v ∈ Icc v₀ v₁, φ₁ v ≤ φ₂ v)
    {ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ}
    (h₁ : IsContactAngleAlong (chartSegment ![φ₁ v₀, v₀] ![φ₂ v₀, v₀]) ψ₁ 1)
    (h₂ : IsContactAngleAlong (chartGraphPath φ₂ v₀ v₁) ψ₂ 1)
    (h₃ : IsContactAngleAlong (chartSegment ![φ₂ v₁, v₁] ![φ₁ v₁, v₁]) ψ₃ 1)
    (h₄ : IsContactAngleAlong (chartGraphPath φ₁ v₁ v₀) ψ₄ 1)
    (h₁₂ : ψ₂ 0 = ψ₁ 1) (h₂₃ : ψ₃ 0 = ψ₂ 1) (h₃₄ : ψ₄ 0 = ψ₃ 1) :
    ψ₄ 1 - ψ₁ 0 = -∫ z in chartRegion φ₁ φ₂ v₀ v₁, cos z.1 := by
  rw [setIntegral_chartRegion hφ₁ hφ₂ hv hle]
  exact sphere_geometricPhase_region hφ₁ hφ₂ v₀ v₁ h₁ h₂ h₃ h₄ h₁₂ h₂₃ h₃₄

/-- **MLS Theorem 8.6, p. 385, for the cap of Figure 8.4 (p. 386), modulo `2π`.** Rolling the sphere
on the plane once along the latitude circle `u_f = u₀`, with `v_f` decreasing from `v₀` to
`v₀ − 2π` in unit time, changes `ψ` by `2π sin u₀`, which is
`2π − ∫_{v₀−2π}^{v₀} ∫_{u₀}^{π/2} cos u`, `2π` minus the area of the polar cap `u_f ≥ u₀` in the
book's area form. So the printed
`Δψ = −Area of Ω` (8.37) holds for this cap only modulo `2π`; the cap contains the pole, where the
chart degenerates. -/
theorem sphere_geometricPhase_latitude (u₀ v₀ : ℝ) {ψ : ℝ → ℝ}
    (h : IsContactAngleAlong (chartSegment ![u₀, v₀] ![u₀, v₀ - 2 * π]) ψ 1) :
    ψ 1 - ψ 0 = 2 * π * sin u₀ ∧
      ψ 1 - ψ 0 = 2 * π - ∫ _v in (v₀ - 2 * π)..v₀, ∫ u in u₀..(π / 2), cos u := by
  have hseg : ∀ (p q : Fin 2 → ℝ) (t : ℝ), deriv (fun s => chartSegment p q s 1) t = q 1 - p 1 := by
    intro p q t
    have : HasDerivAt (fun s => chartSegment p q s 1) (q 1 - p 1) t := by
      simpa [chartSegment] using ((hasDerivAt_id t).mul_const (q 1 - p 1)).const_add (p 1)
    exact this.deriv
  have hconst : ∀ {φ : ℝ → ℝ} {c : ℝ}, (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ c t) → φ 1 - φ 0 = c := by
    intro φ c hφ
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hφ t (by rwa [uIcc_of_le zero_le_one] at ht))
      (intervalIntegrable_const (c := c))
    simpa using this.symm
  have e : ψ 1 - ψ 0 = 2 * π * sin u₀ := hconst fun t ht => by
    have := h t ht
    rw [hseg] at this
    convert this using 1
    simp [chartSegment]
    ring
  refine ⟨e, ?_⟩
  rw [e, integral_cos, sin_pi_div_two, intervalIntegral.integral_const, smul_eq_mul]
  ring

end Nonholonomic
end RoboLean
