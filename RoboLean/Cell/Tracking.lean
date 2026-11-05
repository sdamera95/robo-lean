import RoboLean.Control.RobotSystem

/-!
# Computed torque under a bounded disturbance torque: an invariant tracking tube

A design statement, not from MLS. It builds on the computed torque law of MLS eq. (4.49)
(printed p. 191) in the form along a motion of MLS p. 301 (`Control.computedTorqueAlong`, the
form of `Control.computedTorque_tracking_along`): the matrices `M(s)`, `C(s)` and the vector
`N(s)` are arbitrary curves, and the plant is driven by the computed torque plus a disturbance
torque `d(s)`,
`M(s) ẍ + C(s) ẋ + N(s) = M(s)(r̈ − K_v (ẋ − ṙ) − K_p (x − r)) + C(s) ẋ + N(s) + d(s)`,
with the critically damped gains `K_p = ω² I`, `K_v = 2ω I`.

**Formalized.**

* `InTube ω δ q q' r r'`: the tracking tube `|eᵢ| ≤ δ` and `|zᵢ| ≤ ω δ` for every joint, with
  `e = q − r` and `z = ė + ω e`; inside it `|ėᵢ| ≤ 2 ω δ` (`InTube.abs_deriv_sub_le`).
* The scalar comparison lemma `abs_le_max_of_hasDerivAt`: `ẏ = −ω y + u` with `|u| ≤ U` gives
  `|y(t)| ≤ max(|y(t₀)|, U/ω)`.
* The disturbance seen through the inertia, `abs_apply_le_of_mulVec_eq`: if
  `m₀ ‖v‖₂² ≤ vᵀ M v` for every `v` and `M w = d` with `‖d‖₂ ≤ d̄`, then `|wᵢ| ≤ d̄ / m₀`.
* Tube invariance with the disturbance bounded at the acceleration level
  (`tube_invariant_on_accel`): if every `w` with `M(s) w = d(s)` has `|wᵢ| ≤ ω² δ`, the tube at
  `t₀` gives the tube at every later time of a finite horizon; no inertia bound is used.
* Tube invariance: with `m₀ ‖v‖₂² ≤ vᵀ M(s) v`, `‖d(s)‖₂ ≤ d̄` and `d̄ ≤ m₀ ω² δ`, the tube at
  `t₀` gives the tube at every later time (`tube_invariant_of_inertia`, on a closed interval).
  The error obeys `ż = −ω z + M⁻¹ d` and `ė = z − ω e`, so the comparison lemma applies twice.
  With the inertia bound required only while every joint is within `η > δ` of the reference, a
  first-exit argument gives the same conclusion on a finite horizon (`tube_invariant_on`) and on
  a ray (`tube_invariant`); this is the form in which a bound valid only on a joint envelope
  around the reference is used without a circular hypothesis.

Conventions: vectors are `Fin n → ℝ`; the Euclidean norm enters only through `v ⬝ᵥ v = ‖v‖₂²`
(the inertia bound `m₀ (v ⬝ᵥ v) ≤ v ⬝ᵥ (M v)` and the disturbance bound `d ⬝ᵥ d ≤ d̄²` with
`0 ≤ d̄`); the tube is a per-joint (sup-norm) condition. Units are those of the robot (for a
revolute arm: radians, seconds, newton metres). Exact model cancellation is assumed; the
disturbance torque carries everything outside the model. Nothing here concerns sampling,
actuator limits or a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

variable {n : ℕ}

/-- **The tracking tube (a design statement, not from MLS).** For a joint vector `q` with
velocity `q'` and a reference value `r` with velocity `r'`, with `e = q − r` and
`z = (q' − r') + ω e`: `|eᵢ| ≤ δ` and `|zᵢ| ≤ ω δ` for every joint `i` (radians and radians per
second for a revolute arm; per-joint bounds). -/
def InTube (ω δ : ℝ) (q q' r r' : Fin n → ℝ) : Prop :=
  ∀ i, |q i - r i| ≤ δ ∧ |q' i - r' i + ω * (q i - r i)| ≤ ω * δ

/-- **Inside the tube every joint is within `δ` of the reference (a design statement, not from
MLS).** -/
theorem InTube.abs_sub_le {ω δ : ℝ} {q q' r r' : Fin n → ℝ} (h : InTube ω δ q q' r r')
    (i : Fin n) : |q i - r i| ≤ δ :=
  (h i).1

/-- **Inside the tube every joint speed is within `2 ω δ` of the reference speed (a design
statement, not from MLS):** `ė = z − ω e`, so `|ėᵢ| ≤ ω δ + ω δ` for `ω ≥ 0`. -/
theorem InTube.abs_deriv_sub_le {ω δ : ℝ} {q q' r r' : Fin n → ℝ} (hω : 0 ≤ ω)
    (h : InTube ω δ q q' r r') (i : Fin n) : |q' i - r' i| ≤ 2 * ω * δ := by
  obtain ⟨h1, h2⟩ := h i
  rw [abs_le] at h1 h2 ⊢
  have k1 := mul_nonneg hω (sub_nonneg.2 h1.1)
  have k2 := mul_nonneg hω (sub_nonneg.2 h1.2)
  constructor <;> nlinarith

/-- One side of the scalar comparison lemma: `ẏ = −ω y + u` with `u ≤ U` gives
`y(t) ≤ max(y(t₀), U/ω)`, from the antitone function `(y − U/ω) e^{ω s}`. -/
private theorem le_max_of_hasDerivAt {ω U t₀ t₁ : ℝ} {y u : ℝ → ℝ} (hω : 0 < ω)
    (hc : ContinuousOn y (Icc t₀ t₁)) (hy : ∀ s ∈ Ioo t₀ t₁, HasDerivAt y (-ω * y s + u s) s)
    (hu : ∀ s ∈ Ioo t₀ t₁, u s ≤ U) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    y t ≤ max (y t₀) (U / ω) := by
  have hderiv : ∀ s ∈ Ioo t₀ t₁, HasDerivAt (fun s => (y s - U / ω) * Real.exp (ω * s))
      ((u s - U) * Real.exp (ω * s)) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (ω * s)) (Real.exp (ω * s) * ω) s := by
      have := ((hasDerivAt_id s).const_mul ω).exp
      simpa only [id, mul_one] using this
    have h1 : HasDerivAt (fun s => (y s - U / ω) * Real.exp (ω * s))
        ((-ω * y s + u s) * Real.exp (ω * s) + (y s - U / ω) * (Real.exp (ω * s) * ω)) s :=
      ((hy s hs).sub_const (U / ω)).mul he
    convert h1 using 1
    field_simp
    ring
  have hanti : AntitoneOn (fun s => (y s - U / ω) * Real.exp (ω * s)) (Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    · exact (hc.sub continuousOn_const).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · rw [interior_Icc]
      exact fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hderiv s hs).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hu s hs)) (Real.exp_pos _).le
  have ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have key : (y t - U / ω) * Real.exp (ω * t) ≤ (y t₀ - U / ω) * Real.exp (ω * t₀) :=
    hanti ht₀ ht ht.1
  have e1 := Real.exp_pos (ω * t)
  have e2 : Real.exp (ω * t₀) ≤ Real.exp (ω * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hω.le)
  rcases le_or_gt (y t₀) (U / ω) with h | h
  · have k : (y t - U / ω) * Real.exp (ω * t) ≤ 0 :=
      key.trans (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) (Real.exp_pos _).le)
    have : y t - U / ω ≤ 0 := by
      by_contra hcon
      linarith [mul_pos (not_le.mp hcon) e1]
    exact le_max_of_le_right (by linarith)
  · have k : (y t - U / ω) * Real.exp (ω * t) ≤ (y t₀ - U / ω) * Real.exp (ω * t) :=
      key.trans (mul_le_mul_of_nonneg_left e2 (by linarith))
    have := le_of_mul_le_mul_right k e1
    exact le_max_of_le_left (by linarith)

/-- **The scalar comparison lemma (a design statement, not from MLS).** For `ω > 0`, a function
`y` continuous on `[t₀, t₁]` with `ẏ(s) = −ω y(s) + u(s)` and `|u(s)| ≤ U` at every
`s ∈ (t₀, t₁)` satisfies `|y(t)| ≤ max(|y(t₀)|, U/ω)` for every `t ∈ [t₀, t₁]`. -/
theorem abs_le_max_of_hasDerivAt {ω U t₀ t₁ : ℝ} {y u : ℝ → ℝ} (hω : 0 < ω)
    (hc : ContinuousOn y (Icc t₀ t₁)) (hy : ∀ s ∈ Ioo t₀ t₁, HasDerivAt y (-ω * y s + u s) s)
    (hu : ∀ s ∈ Ioo t₀ t₁, |u s| ≤ U) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    |y t| ≤ max |y t₀| (U / ω) := by
  have h1 := le_max_of_hasDerivAt hω hc hy (fun s hs => (abs_le.mp (hu s hs)).2) ht
  have h2 := le_max_of_hasDerivAt (U := U) (y := fun s => -y s) (u := fun s => -u s) hω hc.neg
    (fun s hs => by convert (hy s hs).neg using 1; ring)
    (fun s hs => by linarith [(abs_le.mp (hu s hs)).1]) ht
  rw [abs_le']
  exact ⟨h1.trans (max_le_max (le_abs_self _) le_rfl),
    h2.trans (max_le_max (neg_le_abs _) le_rfl)⟩

/-- **A disturbance seen through an inertia matrix (a design statement, not from MLS).** If
`m₀ ‖v‖₂² ≤ vᵀ M v` for every `v` (written `m₀ (v ⬝ᵥ v) ≤ v ⬝ᵥ (M v)`), with `m₀ > 0`, and
`M w = d` with `‖d‖₂ ≤ d̄` (written `d ⬝ᵥ d ≤ d̄²`, `0 ≤ d̄`), then every entry of `w` satisfies
`|wᵢ| ≤ d̄ / m₀`. The matrix need not be symmetric. -/
theorem abs_apply_le_of_mulVec_eq {M : Matrix (Fin n) (Fin n) ℝ} {w d : Fin n → ℝ}
    {m₀ dbar : ℝ} (hm₀ : 0 < m₀) (hdbar : 0 ≤ dbar) (hM : ∀ v, m₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v))
    (hd : d ⬝ᵥ d ≤ dbar ^ 2) (hw : M *ᵥ w = d) (i : Fin n) : |w i| ≤ dbar / m₀ := by
  have hS : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun j _ => mul_self_nonneg (w j)
  have hP : m₀ * (w ⬝ᵥ w) ≤ w ⬝ᵥ d := hw ▸ hM w
  have hCS : (w ⬝ᵥ d) ^ 2 ≤ (w ⬝ᵥ w) * (d ⬝ᵥ d) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w d
    simpa only [dotProduct, sq] using this
  have hwi : w i ^ 2 ≤ w ⬝ᵥ w := by
    rw [sq]
    exact Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => mul_self_nonneg (w j))
      (Finset.mem_univ i)
  have hkey : m₀ ^ 2 * (w ⬝ᵥ w) ≤ dbar ^ 2 := by
    rcases hS.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [mul_zero]
      exact sq_nonneg _
    · have h1 : (m₀ * (w ⬝ᵥ w)) ^ 2 ≤ (w ⬝ᵥ d) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hm₀.le hS) hP 2
      have h2 : (w ⬝ᵥ w) * (m₀ ^ 2 * (w ⬝ᵥ w)) ≤ (w ⬝ᵥ w) * dbar ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hd hS]
      exact le_of_mul_le_mul_left h2 hpos
  have hsq : (m₀ * w i) ^ 2 ≤ dbar ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hwi (sq_nonneg m₀)).trans hkey
  have habs := abs_le_of_sq_le_sq hsq hdbar
  rw [abs_mul, abs_of_pos hm₀] at habs
  rw [le_div_iff₀ hm₀]
  linarith

/-- The core of the tube theorems on an open interval: the hypotheses of
`tube_invariant_on_accel` on `(t₀, t₁)`. -/
private theorem tube_of_accel_Ioo {ω δ t₀ t₁ : ℝ} (hω : 0 < ω) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioo t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioo t₀ t₁, HasDerivAt x' (x'' s) s)
    (hw : ∀ s ∈ Ioo t₀ t₁, ∀ w, Mt s *ᵥ w = d s → ∀ i, |w i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioo t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) := by
  intro t ht i
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hrc' : Continuous r' := continuous_iff_continuousAt.mpr fun t => (hr' t).continuousAt
  have hxc : ContinuousOn x (Icc t₀ t₁) := continuous_fst.comp_continuousOn hc
  have hxc' : ContinuousOn x' (Icc t₀ t₁) := continuous_snd.comp_continuousOn hc
  have hxi : ContinuousOn (fun s => x s i) (Icc t₀ t₁) := continuousOn_pi.1 hxc i
  have hxi' : ContinuousOn (fun s => x' s i) (Icc t₀ t₁) := continuousOn_pi.1 hxc' i
  have hri : ContinuousOn (fun s => r s i) (Icc t₀ t₁) :=
    (continuous_pi_iff.1 hrc i).continuousOn
  have hri' : ContinuousOn (fun s => r' s i) (Icc t₀ t₁) :=
    (continuous_pi_iff.1 hrc' i).continuousOn
  -- the acceleration left over by the disturbance, `w = M⁻¹ d`
  have hwb : ∀ s ∈ Ioo t₀ t₁, |(x'' s - (r'' s - (2 * ω) • (x' s - r' s) -
      ω ^ 2 • (x s - r s))) i| ≤ ω ^ 2 * δ := by
    intro s hs
    have h1 := hE s hs
    simp only [Control.computedTorqueAlong, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    have h2 : Mt s *ᵥ x'' s = Mt s *ᵥ (r'' s - (2 * ω) • (x' s - r' s) - ω ^ 2 • (x s - r s)) +
        d s := by
      rw [← sub_eq_zero] at h1 ⊢
      rw [← h1]
      abel
    have hMw : Mt s *ᵥ (x'' s - (r'' s - (2 * ω) • (x' s - r' s) - ω ^ 2 • (x s - r s))) =
        d s := by
      rw [Matrix.mulVec_sub, h2]
      abel
    exact hw s hs _ hMw i
  -- `z = ė + ω e` obeys `ż = −ω z + w`
  have hzd : ∀ s ∈ Ioo t₀ t₁, HasDerivAt (fun s => x' s i - r' s i + ω * (x s i - r s i))
      (-ω * (x' s i - r' s i + ω * (x s i - r s i)) +
        (x'' s - (r'' s - (2 * ω) • (x' s - r' s) - ω ^ 2 • (x s - r s))) i) s := by
    intro s hs
    have h1 := ((hasDerivAt_pi.mp (hx' s hs) i).sub (hasDerivAt_pi.mp (hr' s) i)).add
      (((hasDerivAt_pi.mp (hx s hs) i).sub (hasDerivAt_pi.mp (hr s) i)).const_mul ω)
    convert h1 using 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzb : ∀ s ∈ Icc t₀ t₁, |x' s i - r' s i + ω * (x s i - r s i)| ≤ ω * δ := by
    intro s hs
    have h := abs_le_max_of_hasDerivAt hω ((hxi'.sub hri').add ((hxi.sub hri).const_smul ω))
      hzd hwb hs
    rw [show ω ^ 2 * δ / ω = ω * δ by field_simp] at h
    exact h.trans (max_le (h₀ i).2 le_rfl)
  -- `e` obeys `ė = −ω e + z`
  have hed : ∀ s ∈ Ioo t₀ t₁, HasDerivAt (fun s => x s i - r s i)
      (-ω * (x s i - r s i) + (x' s i - r' s i + ω * (x s i - r s i))) s := by
    intro s hs
    have h1 := (hasDerivAt_pi.mp (hx s hs) i).sub (hasDerivAt_pi.mp (hr s) i)
    convert h1 using 1
    ring
  have heb := abs_le_max_of_hasDerivAt hω (hxi.sub hri) hed
    (fun s hs => hzb s (Ioo_subset_Icc_self hs)) ht
  rw [show ω * δ / ω = δ by field_simp] at heb
  exact ⟨heb.trans (max_le (h₀ i).1 le_rfl), hzb t ht⟩

/-- **Tube invariance of computed torque under a disturbance bounded at the acceleration level,
on a finite horizon (a design statement, not from MLS; the law is MLS eq. (4.49), p. 191, along a
motion as on p. 301).** Let `ω > 0` and let the reference `r` have velocity `r'` and acceleration
`r''` at every time. Let `(x, x')` be continuous on `[t₀, t₁]` and, at every `s ∈ (t₀, t₁]`: `x`
has velocity `x'` and `x'` has acceleration `x''`; every `w` with `M(s) w = d(s)` satisfies
`|wᵢ| ≤ ω² δ` for every joint (for invertible `M(s)`: `|(M(s)⁻¹ d(s))ᵢ| ≤ ω² δ`, the
acceleration the disturbance torque produces, in rad/s²); and `M ẍ + C ẋ + N = F(s) + d(s)` with
`F` the computed torque with `K_p = ω² I`, `K_v = 2ω I`. No inertia bound and no joint range is
assumed. If the motion is in the tube `InTube ω δ` around the reference at `t₀`, then at every
`t ∈ [t₀, t₁]` it is in the tube and every joint speed is within `2 ω δ` of the reference
speed. -/
theorem tube_invariant_on_accel {ω δ t₀ t₁ : ℝ} (hω : 0 < ω) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hw : ∀ s ∈ Ioc t₀ t₁, ∀ w, Mt s *ᵥ w = d s → ∀ i, |w i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) ∧
      ∀ i, |x' t i - r' t i| ≤ 2 * ω * δ := by
  have h := tube_of_accel_Ioo hω hr hr' hc (fun s hs => hx s (Ioo_subset_Ioc_self hs))
    (fun s hs => hx' s (Ioo_subset_Ioc_self hs)) (fun s hs => hw s (Ioo_subset_Ioc_self hs))
    (fun s hs => hE s (Ioo_subset_Ioc_self hs)) h₀
  exact fun t ht => ⟨h t ht, fun i => (h t ht).abs_deriv_sub_le hω.le i⟩

/-- **Tube invariance of computed torque under a bounded disturbance, with the inertia bound
along the whole interval (a design statement, not from MLS; the law is MLS eq. (4.49), p. 191,
along a motion as on p. 301).** Let `ω > 0`, `m₀ > 0`, `0 ≤ d̄ ≤ m₀ ω² δ`, and let the reference
`r` have velocity `r'` and acceleration `r''` at every time. Let the motion `x` have velocity
`x'` and acceleration `x''` at every `s ∈ (t₀, t₁)`, with `(x, x')` continuous on `[t₀, t₁]`,
and let the matrix and vector curves `M(s)`, `C(s)`, `N(s)` and the disturbance torque `d(s)`
satisfy, at every `s ∈ (t₀, t₁)`, `m₀ ‖v‖₂² ≤ vᵀ M(s) v` for every `v`, `‖d(s)‖₂ ≤ d̄` and
`M ẍ + C ẋ + N = F(s) + d(s)` with `F` the computed torque with `K_p = ω² I`, `K_v = 2ω I`. If
the motion is in the tube `InTube ω δ` around the reference at `t₀`, it is in the tube at every
`t ∈ [t₀, t₁]`. -/
theorem tube_invariant_of_inertia {ω δ m₀ dbar t₀ t₁ : ℝ} (hω : 0 < ω) (hm₀ : 0 < m₀)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ m₀ * ω ^ 2 * δ) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioo t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioo t₀ t₁, HasDerivAt x' (x'' s) s)
    (hM : ∀ s ∈ Ioo t₀ t₁, ∀ v, m₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Mt s *ᵥ v))
    (hd : ∀ s ∈ Ioo t₀ t₁, d s ⬝ᵥ d s ≤ dbar ^ 2)
    (hE : ∀ s ∈ Ioo t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) := by
  exact tube_of_accel_Ioo hω hr hr' hc hx hx'
    (fun s hs w hMw i => (abs_apply_le_of_mulVec_eq hm₀ hdbar₀ (hM s hs) (hd s hs) hMw i).trans
      ((div_le_iff₀ hm₀).2 (by linarith))) hE h₀

/-- **Tube invariance of computed torque under a bounded disturbance on a finite horizon, with
the inertia bound required only near the reference (a design statement, not from MLS; the law
is MLS eq. (4.49), p. 191, along a motion as on p. 301).** Let `ω > 0`, `m₀ > 0`, `δ < η`,
`0 ≤ d̄ ≤ m₀ ω² δ`, and let the reference `r` have velocity `r'` and acceleration `r''` at every
time. Let `(x, x')` be continuous on `[t₀, t₁]` and, at every `s ∈ (t₀, t₁]`: `x` has velocity
`x'` and `x'` has acceleration `x''`; if every joint is within `η` of the reference
(`|xᵢ(s) − rᵢ(s)| ≤ η`) then `m₀ ‖v‖₂² ≤ vᵀ M(s) v` for every `v`; `‖d(s)‖₂ ≤ d̄` (as
`d ⬝ᵥ d ≤ d̄²`); and `M ẍ + C ẋ + N = F(s) + d(s)` with `F` the computed torque with
`K_p = ω² I`, `K_v = 2ω I`. If the motion is in the tube `InTube ω δ` around the reference at
`t₀`, then at every `t ∈ [t₀, t₁]` it is in the tube and every joint speed is within `2 ω δ` of
the reference speed. The proof is a first-exit argument: before the first time some joint
leaves the `η`-band the inertia bound holds, so the tube holds, which keeps every joint within
`δ < η`. -/
theorem tube_invariant_on {ω δ η m₀ dbar t₀ t₁ : ℝ} (hω : 0 < ω) (hm₀ : 0 < m₀) (hδη : δ < η)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ m₀ * ω ^ 2 * δ) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hM : ∀ s ∈ Ioc t₀ t₁, (∀ i, |x s i - r s i| ≤ η) →
      ∀ v, m₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Mt s *ᵥ v))
    (hd : ∀ s ∈ Ioc t₀ t₁, d s ⬝ᵥ d s ≤ dbar ^ 2)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) ∧
      ∀ i, |x' t i - r' t i| ≤ 2 * ω * δ := by
  have hxc : ContinuousOn x (Icc t₀ t₁) := continuous_fst.comp_continuousOn hc
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  -- first exit: every joint stays strictly inside the `η`-band on `[t₀, t₁]`
  have hband : ∀ s ∈ Icc t₀ t₁, ∀ i, |x s i - r s i| < η := by
    by_contra hcon
    simp only [not_forall, not_lt] at hcon
    obtain ⟨s₁, hs₁, i₁, hi₁⟩ := hcon
    set S : Set ℝ := Icc t₀ t₁ ∩ (fun s => x s - r s) ⁻¹' (⋃ i, {v : Fin n → ℝ | η ≤ |v i|})
      with hS
    have hmem : ∀ s, s ∈ S ↔ s ∈ Icc t₀ t₁ ∧ ∃ i, η ≤ |x s i - r s i| := by
      intro s
      simp only [hS, mem_inter_iff, mem_preimage, mem_iUnion, mem_ofPred_eq, Pi.sub_apply]
    have hSc : IsClosed S := (hxc.sub hrc.continuousOn).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_iUnion_of_finite fun i =>
        isClosed_le continuous_const (continuous_apply i).abs)
    have hne : S.Nonempty := ⟨s₁, (hmem s₁).2 ⟨hs₁, i₁, hi₁⟩⟩
    have hbdd : BddBelow S := ⟨t₀, fun s hs => ((hmem s).1 hs).1.1⟩
    obtain ⟨hτI, j, hj⟩ := (hmem _).1 (hSc.csInf_mem hne hbdd)
    have hsub : ∀ s ∈ Ioo t₀ (sInf S), s ∈ Ioc t₀ t₁ := fun s hs => ⟨hs.1, hs.2.le.trans hτI.2⟩
    have hbefore : ∀ s ∈ Ioo t₀ (sInf S), ∀ i, |x s i - r s i| ≤ η := by
      intro s hs i
      by_contra hcon'
      exact notMem_of_lt_csInf hs.2 hbdd
        ((hmem s).2 ⟨⟨hs.1.le, hs.2.le.trans hτI.2⟩, i, (not_le.mp hcon').le⟩)
    have htube := tube_invariant_of_inertia hω hm₀ hdbar₀ hdbar hr hr'
      (hc.mono (Icc_subset_Icc_right hτI.2)) (fun s hs => hx s (hsub s hs))
      (fun s hs => hx' s (hsub s hs)) (fun s hs => hM s (hsub s hs) (hbefore s hs))
      (fun s hs => hd s (hsub s hs)) (fun s hs => hE s (hsub s hs)) h₀ (sInf S)
      ⟨hτI.1, le_rfl⟩
    linarith [(htube j).1]
  have hall := tube_invariant_of_inertia hω hm₀ hdbar₀ hdbar hr hr' hc
    (fun s hs => hx s (Ioo_subset_Ioc_self hs)) (fun s hs => hx' s (Ioo_subset_Ioc_self hs))
    (fun s hs => hM s (Ioo_subset_Ioc_self hs)
      (fun i => (hband s (Ioo_subset_Icc_self hs) i).le))
    (fun s hs => hd s (Ioo_subset_Ioc_self hs)) (fun s hs => hE s (Ioo_subset_Ioc_self hs)) h₀
  intro t ht
  exact ⟨hall t ht, fun i => (hall t ht).abs_deriv_sub_le hω.le i⟩

/-- **Tube invariance of computed torque under a bounded disturbance on an infinite horizon (a
design statement, not from MLS; the law is MLS eq. (4.49), p. 191, along a motion as on p. 301),**
in the form of `Control.computedTorque_tracking_along`: the hypotheses of `tube_invariant_on` at
every `s > t₀`, with `(x, x')` continuous on `[t₀, ∞)`. Conclusion: at every `t ≥ t₀` the motion
is in the tube and every joint speed is within `2 ω δ` of the reference speed. -/
theorem tube_invariant {ω δ η m₀ dbar t₀ : ℝ} (hω : 0 < ω) (hm₀ : 0 < m₀) (hδη : δ < η)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ m₀ * ω ^ 2 * δ) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Ici t₀))
    (hx : ∀ s, t₀ < s → HasDerivAt x (x' s) s) (hx' : ∀ s, t₀ < s → HasDerivAt x' (x'' s) s)
    (hM : ∀ s, t₀ < s → (∀ i, |x s i - r s i| ≤ η) → ∀ v, m₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Mt s *ᵥ v))
    (hd : ∀ s, t₀ < s → d s ⬝ᵥ d s ≤ dbar ^ 2)
    (hE : ∀ s, t₀ < s → Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t, t₀ ≤ t → InTube ω δ (x t) (x' t) (r t) (r' t) ∧
      ∀ i, |x' t i - r' t i| ≤ 2 * ω * δ := fun t ht =>
  tube_invariant_on (t₁ := t) hω hm₀ hδη hdbar₀ hdbar hr hr' (hc.mono Icc_subset_Ici_self)
    (fun s hs => hx s hs.1) (fun s hs => hx' s hs.1) (fun s hs => hM s hs.1)
    (fun s hs => hd s hs.1) (fun s hs => hE s hs.1) h₀ t ⟨ht, le_rfl⟩

end Cell
end RoboLean
