import RoboLean.Cell.Tracking

/-!
# The tracking tube with the acceleration required only from the right

A design statement, not from MLS. The statements of `RoboLean.Cell.Tracking` in the
acceleration-level form, with every derivative of the motion taken from the right
(`HasDerivWithinAt f f' (Ici s) s`) instead of two-sided. The law is computed torque, MLS
eq. (4.49) (printed p. 191), along a motion as on p. 301, with the gains `K_p = ω² I`,
`K_v = 2ω I`, and the plant is driven by the computed torque plus a disturbance torque `d(s)`.

A disturbance that jumps (Coulomb friction when a joint reverses, a torque held between samples)
makes the acceleration jump, so the velocity has no two-sided derivative at the jump; it still
has a right derivative there, the acceleration just after the jump. The statements here ask
for the position and the velocity to have right derivatives at every instant of the horizon, and
for `(x, ẋ)` to be continuous on the closed horizon.

**Formalized.**

* `abs_le_max_of_hasDerivWithinAt_Ici`: the scalar comparison lemma with a right derivative,
  `ẏ = −ω y + u` from the right with `|u| ≤ U` gives `|y(t)| ≤ max(|y(t₀)|, U/ω)`.
* `tube_invariant_on_accel_right`: tube invariance of computed torque under a disturbance
  bounded at the acceleration level, on a finite horizon, for arbitrary matrix and vector curves
  `M(s)`, `C(s)`, `N(s)`, with right derivatives.

Conventions as in `RoboLean.Cell.Tracking`: joint vectors `Fin n → ℝ`, per-joint tube bounds;
for a revolute arm radians, seconds and radians per second squared. The reference keeps its
two-sided derivatives (it is the designer's smooth reference). Exact model cancellation is
assumed; nothing here concerns sampling, actuator limits or a physical arm.
-/

noncomputable section

open Matrix Set Filter Topology

namespace RoboLean
namespace Cell

variable {n : ℕ}

/-- One side of the scalar comparison lemma with a right derivative: `ẏ = −ω y + u` from the
right with `u ≤ U` gives `y(t) ≤ max(y(t₀), U/ω)`. The function `g = (y − U/ω) e^{ω s}` has a
right derivative at most zero on `(t₀, t₁)`, so the one-sided comparison of Mathlib gives
`g(t) ≤ g(a)` for `t₀ < a < t`, and `a → t₀` by continuity gives `g(t) ≤ g(t₀)`. -/
private theorem le_max_of_hasDerivWithinAt_Ici {ω U t₀ t₁ : ℝ} {y u : ℝ → ℝ} (hω : 0 < ω)
    (hc : ContinuousOn y (Icc t₀ t₁))
    (hy : ∀ s ∈ Ioo t₀ t₁, HasDerivWithinAt y (-ω * y s + u s) (Ici s) s)
    (hu : ∀ s ∈ Ioo t₀ t₁, u s ≤ U) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    y t ≤ max (y t₀) (U / ω) := by
  set g : ℝ → ℝ := fun s => (y s - U / ω) * Real.exp (ω * s) with hg
  have hderiv : ∀ s ∈ Ioo t₀ t₁,
      HasDerivWithinAt g ((u s - U) * Real.exp (ω * s)) (Ici s) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (ω * s)) (Real.exp (ω * s) * ω) s := by
      have := ((hasDerivAt_id s).const_mul ω).exp
      simpa only [id, mul_one] using this
    have h1 : HasDerivWithinAt g
        ((-ω * y s + u s) * Real.exp (ω * s) + (y s - U / ω) * (Real.exp (ω * s) * ω))
        (Ici s) s :=
      ((hy s hs).sub_const (U / ω)).mul he.hasDerivWithinAt
    convert h1 using 1
    field_simp
    ring
  have hgc : ContinuousOn g (Icc t₀ t₁) := (hc.sub continuousOn_const).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have key : g t ≤ g t₀ := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [h]
    · have hstep : ∀ a ∈ Ioo t₀ t, g t ≤ g a := by
        intro a ha
        have hsub : ∀ s ∈ Ico a t, s ∈ Ioo t₀ t₁ := fun s hs =>
          ⟨ha.1.trans_le hs.1, hs.2.trans_le ht.2⟩
        exact image_le_of_deriv_right_le_deriv_boundary (hgc.mono (Icc_subset_Icc ha.1.le ht.2))
          (fun s hs => hderiv s (hsub s hs)) (B := fun _ => g a) (B' := fun _ => 0) le_rfl
          continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _)
          (fun s hs => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hu s (hsub s hs)))
            (Real.exp_pos _).le) ⟨ha.2.le, le_rfl⟩
      have hcw : ContinuousWithinAt g (Ioi t₀) t₀ :=
        (hgc t₀ ⟨le_rfl, ht.1.trans ht.2⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT (h.trans_le ht.2))
      exact ge_of_tendsto hcw.tendsto (by
        filter_upwards [Ioo_mem_nhdsGT h] with a ha using hstep a ha)
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

/-- **The scalar comparison lemma with a right derivative (a design statement, not from MLS).**
For `ω > 0`, a function `y` continuous on `[t₀, t₁]` with right derivative
`ẏ(s) = −ω y(s) + u(s)` (taken within `[s, ∞)`) and `|u(s)| ≤ U` at every `s ∈ (t₀, t₁)`
satisfies `|y(t)| ≤ max(|y(t₀)|, U/ω)` for every `t ∈ [t₀, t₁]`. -/
theorem abs_le_max_of_hasDerivWithinAt_Ici {ω U t₀ t₁ : ℝ} {y u : ℝ → ℝ} (hω : 0 < ω)
    (hc : ContinuousOn y (Icc t₀ t₁))
    (hy : ∀ s ∈ Ioo t₀ t₁, HasDerivWithinAt y (-ω * y s + u s) (Ici s) s)
    (hu : ∀ s ∈ Ioo t₀ t₁, |u s| ≤ U) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    |y t| ≤ max |y t₀| (U / ω) := by
  have h1 := le_max_of_hasDerivWithinAt_Ici hω hc hy (fun s hs => (abs_le.mp (hu s hs)).2) ht
  have h2 := le_max_of_hasDerivWithinAt_Ici (U := U) (y := fun s => -y s) (u := fun s => -u s) hω
    hc.neg (fun s hs => by convert (hy s hs).neg using 1; ring)
    (fun s hs => by linarith [(abs_le.mp (hu s hs)).1]) ht
  rw [abs_le']
  exact ⟨h1.trans (max_le_max (le_abs_self _) le_rfl),
    h2.trans (max_le_max (neg_le_abs _) le_rfl)⟩

/-- **Tube invariance of computed torque under a disturbance bounded at the acceleration level,
on a finite horizon, with right derivatives (a design statement, not from MLS; the law is MLS
eq. (4.49), p. 191, along a motion as on p. 301).** Let `ω > 0` and let the reference `r` have
velocity `r'` and acceleration `r''` at every time (two-sided). Let `(x, x')` be continuous on
`[t₀, t₁]` and, at every `s ∈ (t₀, t₁]`: `x` has right derivative `x'(s)` and `x'` has right
derivative `x''(s)` (derivatives within `[s, ∞)`); every `w` with `M(s) w = d(s)` satisfies
`|wᵢ| ≤ ω² δ` for every joint (for invertible `M(s)`: `|(M(s)⁻¹ d(s))ᵢ| ≤ ω² δ`, the
acceleration the disturbance torque produces, in rad/s²); and `M ẍ + C ẋ + N = F(s) + d(s)`
with `ẍ = x''(s)` and `F` the computed torque with `K_p = ω² I`, `K_v = 2ω I`. No inertia bound
and no joint range is assumed. If the motion is in the tube `InTube ω δ` around the reference at
`t₀`, then at every `t ∈ [t₀, t₁]` it is in the tube and every joint speed is within `2 ω δ` of
the reference speed. -/
theorem tube_invariant_on_accel_right {ω δ t₀ t₁ : ℝ} (hω : 0 < ω) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x (x' s) (Ici s) s)
    (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x' (x'' s) (Ici s) s)
    (hw : ∀ s ∈ Ioc t₀ t₁, ∀ w, Mt s *ᵥ w = d s → ∀ i, |w i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) ∧
      ∀ i, |x' t i - r' t i| ≤ 2 * ω * δ := by
  have h : ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) := by
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
      have h1 := hE s (Ioo_subset_Ioc_self hs)
      simp only [Control.computedTorqueAlong, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      have h2 : Mt s *ᵥ x'' s =
          Mt s *ᵥ (r'' s - (2 * ω) • (x' s - r' s) - ω ^ 2 • (x s - r s)) + d s := by
        rw [← sub_eq_zero] at h1 ⊢
        rw [← h1]
        abel
      have hMw : Mt s *ᵥ (x'' s - (r'' s - (2 * ω) • (x' s - r' s) - ω ^ 2 • (x s - r s))) =
          d s := by
        rw [Matrix.mulVec_sub, h2]
        abel
      exact hw s (Ioo_subset_Ioc_self hs) _ hMw i
    -- `z = ė + ω e` obeys `ż = −ω z + w` from the right
    have hzd : ∀ s ∈ Ioo t₀ t₁, HasDerivWithinAt
        (fun s => x' s i - r' s i + ω * (x s i - r s i))
        (-ω * (x' s i - r' s i + ω * (x s i - r s i)) +
          (x'' s - (r'' s - (2 * ω) • (x' s - r' s) - ω ^ 2 • (x s - r s))) i) (Ici s) s := by
      intro s hs
      have h1 := ((hasDerivWithinAt_pi.mp (hx' s (Ioo_subset_Ioc_self hs)) i).sub
        (hasDerivAt_pi.mp (hr' s) i).hasDerivWithinAt).add
        (((hasDerivWithinAt_pi.mp (hx s (Ioo_subset_Ioc_self hs)) i).sub
          (hasDerivAt_pi.mp (hr s) i).hasDerivWithinAt).const_mul ω)
      convert h1 using 1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hzb : ∀ s ∈ Icc t₀ t₁, |x' s i - r' s i + ω * (x s i - r s i)| ≤ ω * δ := by
      intro s hs
      have h := abs_le_max_of_hasDerivWithinAt_Ici hω
        ((hxi'.sub hri').add ((hxi.sub hri).const_smul ω)) hzd hwb hs
      rw [show ω ^ 2 * δ / ω = ω * δ by field_simp] at h
      exact h.trans (max_le (h₀ i).2 le_rfl)
    -- `e` obeys `ė = −ω e + z` from the right
    have hed : ∀ s ∈ Ioo t₀ t₁, HasDerivWithinAt (fun s => x s i - r s i)
        (-ω * (x s i - r s i) + (x' s i - r' s i + ω * (x s i - r s i))) (Ici s) s := by
      intro s hs
      have h1 := (hasDerivWithinAt_pi.mp (hx s (Ioo_subset_Ioc_self hs)) i).sub
        (hasDerivAt_pi.mp (hr s) i).hasDerivWithinAt
      convert h1 using 1
      ring
    have heb := abs_le_max_of_hasDerivWithinAt_Ici hω (hxi.sub hri) hed
      (fun s hs => hzb s (Ioo_subset_Icc_self hs)) ht
    rw [show ω * δ / ω = δ by field_simp] at heb
    exact ⟨heb.trans (max_le (h₀ i).1 le_rfl), hzb t ht⟩
  exact fun t ht => ⟨h t ht, fun i => (h t ht).abs_deriv_sub_le hω.le i⟩

end Cell
end RoboLean
