import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Segment
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# The move reference: a clamped quintic between two waypoints

A design statement, not from MLS. A move from the joint vector `a` to the joint vector `b`
admitted at time `t₀` with duration `T > 0` follows the reference
`r(t) = a + σ((t − t₀)/T) (b − a)`, where `σ` is the quintic `10τ³ − 15τ⁴ + 6τ⁵` on `[0, 1]`,
`0` before and `1` after (`quinticStep`). Its first and second derivatives vanish at both ends,
so `σ` has a derivative and a second derivative at every point of `ℝ`, with the second
derivative continuous, and the reference is twice differentiable on `ℝ`.

**Formalized.**

* `quinticStep`, `quinticStepDeriv`, `quinticStepDeriv2`, written through the clamp
  `max 0 (min τ 1)`; `hasDerivAt_quinticStep`, `hasDerivAt_quinticStepDeriv` at every point;
  the values `0` and `1` (and vanishing derivatives) outside `(0, 1)`; `0 ≤ σ ≤ 1`;
  `0 ≤ σ' ≤ 15/8`; `|σ''| ≤ 6`.
* `moveRef a b t₀ T` with its velocity `moveRefDeriv` and acceleration `moveRefDeriv2`: the
  derivatives at every time; `r = a`, `ṙ = r̈ = 0` for `t ≤ t₀`; `r = b`, `ṙ = r̈ = 0` for
  `t ≥ t₀ + T`; `r(t)` on the segment from `a` to `b` (each joint between `aᵢ` and `bᵢ`); the
  constant move `moveRef a a`; per-joint bounds `|ṙᵢ| ≤ (15/8) |bᵢ − aᵢ| / T` and
  `|r̈ᵢ| ≤ 6 |bᵢ − aᵢ| / T²`.

Conventions: joint vectors `Fin n → ℝ` (radians for a revolute arm), time in seconds.
-/

noncomputable section

open Set

namespace RoboLean
namespace Cell

/-- **The clamped quintic step (a design statement, not from MLS):**
`σ(τ) = 10c³ − 15c⁴ + 6c⁵` with `c = max 0 (min τ 1)`, so `σ = 0` for `τ ≤ 0`, `σ = 1` for
`τ ≥ 1` and the quintic on `[0, 1]` (dimensionless). -/
def quinticStep (τ : ℝ) : ℝ :=
  10 * max 0 (min τ 1) ^ 3 - 15 * max 0 (min τ 1) ^ 4 + 6 * max 0 (min τ 1) ^ 5

/-- **The derivative of the clamped quintic step (a design statement, not from MLS):**
`σ'(τ) = 30c² − 60c³ + 30c⁴ = 30 c² (1 − c)²` with `c = max 0 (min τ 1)`. -/
def quinticStepDeriv (τ : ℝ) : ℝ :=
  30 * max 0 (min τ 1) ^ 2 - 60 * max 0 (min τ 1) ^ 3 + 30 * max 0 (min τ 1) ^ 4

/-- **The second derivative of the clamped quintic step (a design statement, not from MLS):**
`σ''(τ) = 60c − 180c² + 120c³ = 60 c (1 − c)(1 − 2c)` with `c = max 0 (min τ 1)`. -/
def quinticStepDeriv2 (τ : ℝ) : ℝ :=
  60 * max 0 (min τ 1) - 180 * max 0 (min τ 1) ^ 2 + 120 * max 0 (min τ 1) ^ 3

/-- The clamp is `0` at nonpositive arguments. -/
private lemma clamp_of_nonpos {x : ℝ} (h : x ≤ 0) : max 0 (min x 1) = 0 :=
  max_eq_left ((min_le_left _ _).trans h)

/-- The clamp is `1` at arguments at least `1`. -/
private lemma clamp_of_one_le {x : ℝ} (h : 1 ≤ x) : max 0 (min x 1) = 1 := by
  rw [min_eq_right h, max_eq_right zero_le_one]

/-- The clamp is the identity on `[0, 1]`. -/
private lemma clamp_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : max 0 (min x 1) = x := by
  rw [min_eq_left h1, max_eq_right h0]

/-- The clamp lies in `[0, 1]`. -/
private lemma clamp_mem_Icc (x : ℝ) : max 0 (min x 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

/-- A function whose derivative vanishes at `0` and `1`, composed with the clamp, has the
clamped derivative at every point. -/
private lemma hasDerivAt_comp_clamp {q q' : ℝ → ℝ} (hq : ∀ x, HasDerivAt q (q' x) x)
    (h0 : q' 0 = 0) (h1 : q' 1 = 0) (τ : ℝ) :
    HasDerivAt (fun x => q (max 0 (min x 1))) (q' (max 0 (min τ 1))) τ := by
  set f : ℝ → ℝ := fun x => q (max 0 (min x 1)) with hf
  have hlo : ∀ y, y ≤ 0 → HasDerivWithinAt f 0 (Iic 0) y := fun y hy =>
    (hasDerivWithinAt_const y _ (q 0)).congr (fun x hx => by simp only [hf, clamp_of_nonpos hx])
      (by simp only [hf, clamp_of_nonpos hy])
  have hhi : ∀ y, 1 ≤ y → HasDerivWithinAt f 0 (Ici 1) y := fun y hy =>
    (hasDerivWithinAt_const y _ (q 1)).congr (fun x hx => by simp only [hf, clamp_of_one_le hx])
      (by simp only [hf, clamp_of_one_le hy])
  have hmid : ∀ y, 0 ≤ y → y ≤ 1 → HasDerivWithinAt f (q' y) (Icc 0 1) y := fun y hy0 hy1 =>
    (hq y).hasDerivWithinAt.congr (fun x hx => by simp only [hf, clamp_of_mem hx.1 hx.2])
      (by simp only [hf, clamp_of_mem hy0 hy1])
  rcases lt_or_ge τ 0 with h | h
  · rw [clamp_of_nonpos h.le, h0]
    exact (hlo τ h.le).hasDerivAt (Iic_mem_nhds h)
  rcases eq_or_lt_of_le h with rfl | h
  · rw [clamp_of_nonpos le_rfl, h0]
    have := (hlo 0 le_rfl).union (h0 ▸ hmid 0 le_rfl zero_le_one)
    rw [Iic_union_Icc_eq_Iic zero_le_one] at this
    exact this.hasDerivAt (Iic_mem_nhds zero_lt_one)
  rcases lt_or_ge τ 1 with h' | h'
  · rw [clamp_of_mem h.le h'.le]
    exact (hmid τ h.le h'.le).hasDerivAt (Icc_mem_nhds h h')
  rcases eq_or_lt_of_le h' with rfl | h'
  · rw [clamp_of_one_le le_rfl, h1]
    have := (h1 ▸ hmid 1 zero_le_one le_rfl).union (hhi 1 le_rfl)
    rw [Icc_union_Ici_eq_Ici zero_le_one] at this
    exact this.hasDerivAt (Ici_mem_nhds zero_lt_one)
  · rw [clamp_of_one_le h'.le, h1]
    exact (hhi τ h'.le).hasDerivAt (Ici_mem_nhds h')

/-- **`σ` has the derivative `σ'` at every point (a design statement, not from MLS);** at the
junctions `τ = 0` and `τ = 1` both one-sided derivatives are `0`. -/
theorem hasDerivAt_quinticStep (τ : ℝ) : HasDerivAt quinticStep (quinticStepDeriv τ) τ := by
  refine hasDerivAt_comp_clamp (q := fun x => 10 * x ^ 3 - 15 * x ^ 4 + 6 * x ^ 5)
    (q' := fun x => 30 * x ^ 2 - 60 * x ^ 3 + 30 * x ^ 4) (fun x => ?_) (by norm_num)
    (by norm_num) τ
  refine ((((hasDerivAt_pow 3 x).const_mul 10).sub ((hasDerivAt_pow 4 x).const_mul 15)).add
    ((hasDerivAt_pow 5 x).const_mul 6)).congr_deriv ?_
  push_cast
  ring

/-- **`σ'` has the derivative `σ''` at every point (a design statement, not from MLS);** so `σ`
is twice differentiable on `ℝ`. -/
theorem hasDerivAt_quinticStepDeriv (τ : ℝ) :
    HasDerivAt quinticStepDeriv (quinticStepDeriv2 τ) τ := by
  refine hasDerivAt_comp_clamp (q := fun x => 30 * x ^ 2 - 60 * x ^ 3 + 30 * x ^ 4)
    (q' := fun x => 60 * x - 180 * x ^ 2 + 120 * x ^ 3) (fun x => ?_) (by norm_num)
    (by norm_num) τ
  refine ((((hasDerivAt_pow 2 x).const_mul 30).sub ((hasDerivAt_pow 3 x).const_mul 60)).add
    ((hasDerivAt_pow 4 x).const_mul 30)).congr_deriv ?_
  push_cast
  ring

/-- **The second derivative of `σ` is continuous (a design statement, not from MLS).** -/
theorem continuous_quinticStepDeriv2 : Continuous quinticStepDeriv2 := by
  unfold quinticStepDeriv2
  fun_prop

/-- **`σ = 0` before the move (a design statement, not from MLS).** -/
theorem quinticStep_of_nonpos {τ : ℝ} (h : τ ≤ 0) : quinticStep τ = 0 := by
  simp [quinticStep, clamp_of_nonpos h]

/-- **`σ = 1` after the move (a design statement, not from MLS).** -/
theorem quinticStep_of_one_le {τ : ℝ} (h : 1 ≤ τ) : quinticStep τ = 1 := by
  rw [quinticStep, clamp_of_one_le h]; norm_num

/-- **`σ' = 0` before the move (a design statement, not from MLS).** -/
theorem quinticStepDeriv_of_nonpos {τ : ℝ} (h : τ ≤ 0) : quinticStepDeriv τ = 0 := by
  simp [quinticStepDeriv, clamp_of_nonpos h]

/-- **`σ' = 0` after the move (a design statement, not from MLS).** -/
theorem quinticStepDeriv_of_one_le {τ : ℝ} (h : 1 ≤ τ) : quinticStepDeriv τ = 0 := by
  rw [quinticStepDeriv, clamp_of_one_le h]; norm_num

/-- **`σ'' = 0` before the move (a design statement, not from MLS).** -/
theorem quinticStepDeriv2_of_nonpos {τ : ℝ} (h : τ ≤ 0) : quinticStepDeriv2 τ = 0 := by
  simp [quinticStepDeriv2, clamp_of_nonpos h]

/-- **`σ'' = 0` after the move (a design statement, not from MLS).** -/
theorem quinticStepDeriv2_of_one_le {τ : ℝ} (h : 1 ≤ τ) : quinticStepDeriv2 τ = 0 := by
  rw [quinticStepDeriv2, clamp_of_one_le h]; norm_num

/-- **`0 ≤ σ ≤ 1` everywhere (a design statement, not from MLS).** -/
theorem quinticStep_mem_Icc (τ : ℝ) : quinticStep τ ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := clamp_mem_Icc τ
  set c := max 0 (min τ 1)
  have e1 : quinticStep τ = c ^ 3 * (10 - 15 * c + 6 * c ^ 2) := by
    simp only [quinticStep, c]; ring
  have e2 : 1 - quinticStep τ = (1 - c) ^ 3 * (1 + 3 * c + 6 * c ^ 2) := by
    simp only [quinticStep, c]; ring
  constructor
  · rw [e1]
    exact mul_nonneg (pow_nonneg h0 3) (by nlinarith [sq_nonneg (c - 5 / 4)])
  · have : 0 ≤ 1 - quinticStep τ := by
      rw [e2]
      exact mul_nonneg (pow_nonneg (by linarith) 3) (by positivity)
    linarith

/-- **`0 ≤ σ' ≤ 15/8` everywhere (a design statement, not from MLS);** the maximum `15/8` is
attained at `τ = 1/2`. -/
theorem quinticStepDeriv_mem_Icc (τ : ℝ) : quinticStepDeriv τ ∈ Icc (0 : ℝ) (15 / 8) := by
  obtain ⟨h0, h1⟩ := clamp_mem_Icc τ
  set c := max 0 (min τ 1)
  have e : quinticStepDeriv τ = 30 * (c * (1 - c)) ^ 2 := by
    simp only [quinticStepDeriv, c]; ring
  have hu0 : 0 ≤ c * (1 - c) := mul_nonneg h0 (by linarith)
  have hu1 : c * (1 - c) ≤ 1 / 4 := by nlinarith [sq_nonneg (c - 1 / 2)]
  rw [e]
  constructor
  · positivity
  · nlinarith

/-- **`|σ''| ≤ 6` everywhere (a design statement, not from MLS);** the exact maximum is
`10/√3 ≈ 5.77`. -/
theorem abs_quinticStepDeriv2_le (τ : ℝ) : |quinticStepDeriv2 τ| ≤ 6 := by
  obtain ⟨h0, h1⟩ := clamp_mem_Icc τ
  set c := max 0 (min τ 1)
  set u := c * (1 - c) with hu
  have hu0 : 0 ≤ u := mul_nonneg h0 (by linarith)
  have hu1 : u ≤ 1 / 4 := by nlinarith [sq_nonneg (c - 1 / 2)]
  have e : quinticStepDeriv2 τ ^ 2 = 3600 * u ^ 2 * (1 - 4 * u) := by
    simp only [quinticStepDeriv2, c, hu]; ring
  have : quinticStepDeriv2 τ ^ 2 ≤ 6 ^ 2 := by
    rw [e]; nlinarith [sq_nonneg (u - 1 / 6), mul_nonneg hu0 (sq_nonneg (u - 1 / 6))]
  exact abs_le_of_sq_le_sq this (by norm_num)

variable {n : ℕ}

/-- **The move reference (a design statement, not from MLS):**
`r(t) = a + σ((t − t₀)/T) (b − a)` for a move from the joint vector `a` to `b` admitted at time
`t₀` with duration `T` (seconds; joint vectors in radians for a revolute arm). -/
def moveRef (a b : Fin n → ℝ) (t₀ T t : ℝ) : Fin n → ℝ :=
  a + quinticStep ((t - t₀) / T) • (b - a)

/-- **The velocity of the move reference (a design statement, not from MLS):**
`ṙ(t) = (σ'((t − t₀)/T) / T) (b − a)`. -/
def moveRefDeriv (a b : Fin n → ℝ) (t₀ T t : ℝ) : Fin n → ℝ :=
  (quinticStepDeriv ((t - t₀) / T) / T) • (b - a)

/-- **The acceleration of the move reference (a design statement, not from MLS):**
`r̈(t) = (σ''((t − t₀)/T) / T²) (b − a)`. -/
def moveRefDeriv2 (a b : Fin n → ℝ) (t₀ T t : ℝ) : Fin n → ℝ :=
  (quinticStepDeriv2 ((t - t₀) / T) / T ^ 2) • (b - a)

/-- The normalized time `(t − t₀)/T` has the derivative `1/T` at every time. -/
private lemma hasDerivAt_normTime (t₀ T t : ℝ) : HasDerivAt (fun s => (s - t₀) / T) (1 / T) t :=
  ((hasDerivAt_id t).sub_const t₀).div_const T

/-- Before the move the normalized time is nonpositive. -/
private lemma normTime_nonpos {t₀ T t : ℝ} (hT : 0 < T) (h : t ≤ t₀) : (t - t₀) / T ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le

/-- After the move the normalized time is at least `1`. -/
private lemma one_le_normTime {t₀ T t : ℝ} (hT : 0 < T) (h : t₀ + T ≤ t) : 1 ≤ (t - t₀) / T :=
  (le_div_iff₀ hT).mpr (by linarith)

/-- **The move reference has the velocity `moveRefDeriv` at every time (a design statement, not
from MLS).** -/
theorem hasDerivAt_moveRef (a b : Fin n → ℝ) (t₀ T t : ℝ) :
    HasDerivAt (moveRef a b t₀ T) (moveRefDeriv a b t₀ T t) t := by
  have := (((hasDerivAt_quinticStep ((t - t₀) / T)).comp t
    (hasDerivAt_normTime t₀ T t)).smul_const (b - a)).const_add a
  rw [mul_one_div] at this
  exact this

/-- **The velocity of the move reference has the derivative `moveRefDeriv2` at every time (a
design statement, not from MLS).** -/
theorem hasDerivAt_moveRefDeriv (a b : Fin n → ℝ) (t₀ T t : ℝ) :
    HasDerivAt (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T t) t := by
  have := (((hasDerivAt_quinticStepDeriv ((t - t₀) / T)).comp t
    (hasDerivAt_normTime t₀ T t)).div_const T).smul_const (b - a)
  rw [mul_one_div, div_div, ← sq] at this
  exact this

/-- **Before the move the reference is at the start (a design statement, not from MLS):**
`r(t) = a` for `t ≤ t₀`, `T > 0`. -/
theorem moveRef_of_le {a b : Fin n → ℝ} {t₀ T t : ℝ} (hT : 0 < T) (h : t ≤ t₀) :
    moveRef a b t₀ T t = a := by
  simp [moveRef, quinticStep_of_nonpos (normTime_nonpos hT h)]

/-- **After the move the reference is at the goal (a design statement, not from MLS):**
`r(t) = b` for `t ≥ t₀ + T`, `T > 0`. -/
theorem moveRef_of_ge {a b : Fin n → ℝ} {t₀ T t : ℝ} (hT : 0 < T) (h : t₀ + T ≤ t) :
    moveRef a b t₀ T t = b := by
  simp [moveRef, quinticStep_of_one_le (one_le_normTime hT h)]

/-- **Before the move the reference is at rest (a design statement, not from MLS):** `ṙ(t) = 0`
for `t ≤ t₀`, `T > 0`. -/
theorem moveRefDeriv_of_le {a b : Fin n → ℝ} {t₀ T t : ℝ} (hT : 0 < T) (h : t ≤ t₀) :
    moveRefDeriv a b t₀ T t = 0 := by
  simp [moveRefDeriv, quinticStepDeriv_of_nonpos (normTime_nonpos hT h)]

/-- **After the move the reference is at rest (a design statement, not from MLS):** `ṙ(t) = 0`
for `t ≥ t₀ + T`, `T > 0`. -/
theorem moveRefDeriv_of_ge {a b : Fin n → ℝ} {t₀ T t : ℝ} (hT : 0 < T) (h : t₀ + T ≤ t) :
    moveRefDeriv a b t₀ T t = 0 := by
  simp [moveRefDeriv, quinticStepDeriv_of_one_le (one_le_normTime hT h)]

/-- **Before the move the reference acceleration is zero (a design statement, not from MLS):**
`r̈(t) = 0` for `t ≤ t₀`, `T > 0`. -/
theorem moveRefDeriv2_of_le {a b : Fin n → ℝ} {t₀ T t : ℝ} (hT : 0 < T) (h : t ≤ t₀) :
    moveRefDeriv2 a b t₀ T t = 0 := by
  simp [moveRefDeriv2, quinticStepDeriv2_of_nonpos (normTime_nonpos hT h)]

/-- **After the move the reference acceleration is zero (a design statement, not from MLS):**
`r̈(t) = 0` for `t ≥ t₀ + T`, `T > 0`. -/
theorem moveRefDeriv2_of_ge {a b : Fin n → ℝ} {t₀ T t : ℝ} (hT : 0 < T) (h : t₀ + T ≤ t) :
    moveRefDeriv2 a b t₀ T t = 0 := by
  simp [moveRefDeriv2, quinticStepDeriv2_of_one_le (one_le_normTime hT h)]

/-- **The reference is always a convex combination of the waypoints (a design statement, not
from MLS):** `r(t)` lies on the segment from `a` to `b`, for every `T` and `t`. -/
theorem moveRef_mem_segment (a b : Fin n → ℝ) (t₀ T t : ℝ) :
    moveRef a b t₀ T t ∈ segment ℝ a b := by
  obtain ⟨h0, h1⟩ := quinticStep_mem_Icc ((t - t₀) / T)
  refine ⟨1 - quinticStep ((t - t₀) / T), quinticStep ((t - t₀) / T), by linarith, h0,
    by ring, ?_⟩
  rw [moveRef, sub_smul, one_smul, smul_sub]
  abel

/-- **Each joint of the reference lies between the waypoints' values (a design statement, not
from MLS):** `rᵢ(t) ∈ [min(aᵢ, bᵢ), max(aᵢ, bᵢ)]`. -/
theorem moveRef_apply_mem_uIcc (a b : Fin n → ℝ) (t₀ T t : ℝ) (i : Fin n) :
    moveRef a b t₀ T t i ∈ uIcc (a i) (b i) := by
  obtain ⟨h0, h1⟩ := quinticStep_mem_Icc ((t - t₀) / T)
  rw [← segment_eq_uIcc]
  refine ⟨1 - quinticStep ((t - t₀) / T), quinticStep ((t - t₀) / T), by linarith, h0,
    by ring, ?_⟩
  simp only [moveRef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **The move from a waypoint to itself is the constant reference (a design statement, not from
MLS).** -/
theorem moveRef_self (a : Fin n → ℝ) (t₀ T t : ℝ) : moveRef a a t₀ T t = a := by
  simp [moveRef]

/-- **The move from a waypoint to itself has zero velocity (a design statement, not from
MLS).** -/
theorem moveRefDeriv_self (a : Fin n → ℝ) (t₀ T t : ℝ) : moveRefDeriv a a t₀ T t = 0 := by
  simp [moveRefDeriv]

/-- **The move from a waypoint to itself has zero acceleration (a design statement, not from
MLS).** -/
theorem moveRefDeriv2_self (a : Fin n → ℝ) (t₀ T t : ℝ) : moveRefDeriv2 a a t₀ T t = 0 := by
  simp [moveRefDeriv2]

/-- **Speed bound of the move reference (a design statement, not from MLS):**
`|ṙᵢ(t)| ≤ (15/8) |bᵢ − aᵢ| / T` for `T > 0`. -/
theorem abs_moveRefDeriv_apply_le {a b : Fin n → ℝ} {t₀ T : ℝ} (hT : 0 < T) (t : ℝ)
    (i : Fin n) : |moveRefDeriv a b t₀ T t i| ≤ 15 / 8 * |b i - a i| / T := by
  obtain ⟨h0, h1⟩ := quinticStepDeriv_mem_Icc ((t - t₀) / T)
  simp only [moveRefDeriv, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [abs_mul, abs_div, abs_of_nonneg h0, abs_of_pos hT, div_mul_eq_mul_div]
  gcongr

/-- **Acceleration bound of the move reference (a design statement, not from MLS):**
`|r̈ᵢ(t)| ≤ 6 |bᵢ − aᵢ| / T²` for `T > 0`. -/
theorem abs_moveRefDeriv2_apply_le {a b : Fin n → ℝ} {t₀ T : ℝ} (hT : 0 < T) (t : ℝ)
    (i : Fin n) : |moveRefDeriv2 a b t₀ T t i| ≤ 6 * |b i - a i| / T ^ 2 := by
  have h := abs_quinticStepDeriv2_le ((t - t₀) / T)
  simp only [moveRefDeriv2, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [abs_mul, abs_div, abs_of_pos (pow_pos hT 2), div_mul_eq_mul_div]
  gcongr

end Cell
end RoboLean
