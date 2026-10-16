import RoboLean.Control.GlobalFlow
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# State-transition matrices of linear time-varying systems (for MLS Theorem 4.6, printed p. 184)

**What MLS prints (pp. 179 and 184).** The linearization of `ẋ = f(x, t)`
(4.37) about the origin is the linear time-varying system `ż = A(t)z` (4.40), with
`A(t) = ∂f(x, t)/∂x |_{x=0}` (4.38); Theorem 4.6 assumes `A(·)` bounded and `0` uniformly
asymptotically stable for (4.40). MLS assumes "the standard conditions for the existence and
uniqueness of solutions", for instance `f(x, t)` Lipschitz in `x` uniformly in `t` and piecewise
continuous in `t` (p. 179). MLS does not define a state-transition matrix.

**Formalized here.**

* Global forward existence for a linear system `u' = B(t)u` in a real Banach space with `B`
  continuous and bounded (`exists_forall_hasDerivAt_linear`), from Mathlib's Picard–Lindelöf
  theorem by gluing, as `exists_isSolution_of_lipschitzWith` (GlobalFlow) does for autonomous
  fields.
* `IsStateTransition A Φ`: `Φ(s, s) = 1`, `Φ(t, s) Φ(s, r) = Φ(t, r)` and
  `∂Φ(t, s)/∂t = A(t) Φ(t, s)` for `t, s, r ≥ 0` (a hypothesis structure, like `HasFlow`).
  Consequences: `Φ(t, s)` is invertible with inverse `Φ(s, t)`; the derivative in the initial
  time is `∂Φ(t, s)/∂s = −Φ(t, s) A(s)` (`hasDerivAt_snd`); `t ↦ Φ(t, t₀) z₀` solves (4.40) from
  `t₀` and every solution is of this form (`isSolution`, `eq_of_isSolution`); Grönwall bounds
  `‖Φ(t, s)‖, ‖Φ(s, t)‖ ≤ e^{M(t − s)}` for `0 ≤ s ≤ t` when `‖A‖ ≤ M`; two state-transition
  matrices of the same `A` agree (`IsStateTransition.unique`).
* Existence (`exists_isStateTransition`): if `A` is continuous and bounded on `[0, ∞)`, a
  state-transition matrix exists. It is `Φ(t, s) = X(t) Y(s)`, where `X' = AX` and `Y' = −YA` start
  from `1` at time `−1` (with `A` extended by `A(0)` to negative times), `YX = 1` because its
  derivative vanishes, and `XY = 1` by uniqueness for `Z' = AZ − ZA`.
* Constant `A(t) ≡ L`: `Φ(t, s) = exp((t − s)L)` (`isStateTransition_exp`).

**Conventions.** Time first, as in `RoboLean.Stability`; the system (4.40) is
`fun t z => A t z` with `A : ℝ → (E →L[ℝ] E)`; "matrix" means a continuous linear map `E →L[ℝ] E`
(for `E = ℝⁿ` it is the map `x ↦ Φ x` of an `n × n` matrix), multiplied by composition; times
`t, s ≥ 0`. Continuity of `A` on `[0, ∞)` is the hypothesis of the existence theorem (MLS's
p. 179 conditions allow piecewise continuity in `t`; with jumps a solution has no derivative at
the jump, and the library's `IsSolution` asks for one at every `t > t₀`).
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Stability

section LinearODE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Uniform local existence for a linear time-varying field (the local step behind
`exists_forall_hasDerivAt_linear`): if `B` is continuous with `‖B t‖ ≤ M'` for all `t` and
`T (2 (M' + 1)) ≤ 1`, then from every initial time `τ` and state `y` a solution of
`u' = B(t) u` with `σ τ = y` exists on `[τ, τ + T]` (one-sided derivatives at the end points).
From Mathlib's Picard–Lindelöf theorem on the closed ball of radius `‖y‖ + 1` about `y`. -/
private theorem exists_local_linear {B : ℝ → F →L[ℝ] F} (hB : Continuous B) {M' : NNReal}
    (hM : ∀ t, ‖B t‖ ≤ M') {T : ℝ} (hT : 0 ≤ T) (hTM : T * (2 * ((M' : ℝ) + 1)) ≤ 1)
    (τ : ℝ) (y : F) :
    ∃ σ : ℝ → F, σ τ = y ∧
      ∀ t ∈ Icc τ (τ + T), HasDerivWithinAt σ (B t (σ t)) (Icc τ (τ + T)) t := by
  set a : NNReal := ‖y‖₊ + 1 with ha
  set L : NNReal := M' * (2 * ‖y‖₊ + 1) with hL
  have hτ : τ ∈ Icc τ (τ + T) := ⟨le_rfl, by linarith⟩
  have hP : IsPicardLindelof (fun t x => B t x) (⟨τ, hτ⟩ : Icc τ (τ + T)) y a 0 L M' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      have hle : ‖B t‖₊ ≤ M' := by
        rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hM t
      exact ((B t).lipschitzWith.weaken hle).lipschitzOnWith
    · intro x _
      exact (hB.clm_apply continuous_const).continuousOn
    · intro t _ x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      have h1 : ‖x‖ ≤ ‖y‖ + (‖y‖ + 1) := by
        have := norm_le_norm_add_norm_sub' x y
        simp only [ha, NNReal.coe_add, coe_nnnorm, NNReal.coe_one] at hx
        linarith
      have h2 := (B t).le_opNorm x
      have h3 : ‖B t‖ * ‖x‖ ≤ (M' : ℝ) * (2 * ‖y‖ + 1) :=
        mul_le_mul (hM t) (by linarith) (norm_nonneg _) M'.2
      simp only [hL, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat,
        coe_nnnorm]
      linarith
    · simp only [hL, ha, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one,
        NNReal.coe_ofNat, NNReal.coe_zero, sub_zero, add_sub_cancel_left, sub_self,
        max_eq_left hT]
      nlinarith [mul_nonneg (sub_nonneg.2 hTM) (norm_nonneg y), M'.2, norm_nonneg y]
  obtain ⟨σ, hσ0, hσ⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨σ, hσ0, hσ⟩

/-- **Global forward existence for a linear time-varying system** (the existence half of MLS's
standing assumption, printed p. 179, for the linearization `ż = A(t) z`, eq. (4.40), p. 184): if
`B : ℝ → (F →L[ℝ] F)` is continuous and `‖B t‖ ≤ M` for all `t`, then from every initial time `s`
and state `u₀` there is a curve `u` with `u s = u₀`, the right derivative `B s u₀` at `s`, and the
derivative `B t (u t)` at every `t > s`. Route: Mathlib's Picard–Lindelöf theorem on intervals of
the uniform length `1 / (2 (max M 0 + 1))`, glued at overlaps by uniqueness, as in
`exists_isSolution_of_lipschitzWith` (GlobalFlow) but with pieces in absolute time. -/
theorem exists_forall_hasDerivAt_linear {B : ℝ → F →L[ℝ] F} (hB : Continuous B) {M : ℝ}
    (hM : ∀ t, ‖B t‖ ≤ M) (s : ℝ) (u₀ : F) :
    ∃ u : ℝ → F, u s = u₀ ∧ HasDerivWithinAt u (B s u₀) (Ici s) s ∧
      ∀ t, s < t → HasDerivAt u (B t (u t)) t := by
  set M' : NNReal := ⟨max M 0, le_max_right _ _⟩ with hM'def
  have hM' : ∀ t, ‖B t‖ ≤ M' := fun t => (hM t).trans (le_max_left _ _)
  have hlip : ∀ t, LipschitzWith M' (fun x => B t x) := fun t =>
    (B t).lipschitzWith.weaken (by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hM' t)
  set h : ℝ := 1 / (4 * ((M' : ℝ) + 1)) with hh
  have hK : (0 : ℝ) < (M' : ℝ) + 1 := by positivity
  have hpos : 0 < h := by positivity
  have hTM : 2 * h * (2 * ((M' : ℝ) + 1)) ≤ 1 := by
    rw [hh]; field_simp; norm_num
  choose σ hσ0 hσ using fun τ y =>
    exists_local_linear hB hM' (by positivity : (0 : ℝ) ≤ 2 * h) hTM τ y
  have hcont : ∀ τ z, ContinuousOn (σ τ z) (Icc τ (τ + 2 * h)) := fun τ z t ht =>
    (hσ τ z t ht).continuousWithinAt
  -- the restart points and the glued curve
  let p : ℕ → F := fun n => Nat.rec u₀ (fun k pk => σ (s + k * h) pk (s + (k + 1) * h)) n
  have hp0 : p 0 = u₀ := rfl
  have hpsucc : ∀ k : ℕ, p (k + 1) = σ (s + k * h) (p k) (s + (k + 1) * h) := fun k => rfl
  -- consecutive pieces agree on their overlap
  have hagree : ∀ k : ℕ, ∀ t ∈ Icc (s + (k + 1) * h) (s + (k + 2) * h),
      σ (s + (k + 1) * h) (p (k + 1)) t = σ (s + k * h) (p k) t := by
    intro k
    refine ODE_solution_unique (v := fun t x => B t x) hlip ?_ ?_ ?_ ?_ ?_
    · exact (hcont _ _).mono (Icc_subset_Icc le_rfl (by linarith))
    · intro t ht
      exact ((hσ _ _ t ⟨ht.1, by linarith [ht.2]⟩).mono
        (Icc_subset_Icc ht.1 le_rfl)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE (by linarith [ht.2]))
    · exact (hcont _ _).mono (Icc_subset_Icc (by nlinarith) (by linarith))
    · intro t ht
      exact ((hσ _ _ t ⟨by nlinarith [ht.1], by linarith [ht.2]⟩).mono
        (Icc_subset_Icc (by nlinarith [ht.1]) le_rfl)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE (by linarith [ht.2]))
    · rw [hσ0, hpsucc]
  set u : ℝ → F := fun t => σ (s + ⌊(t - s) / h⌋₊ * h) (p ⌊(t - s) / h⌋₊) t with hu
  -- on `[s + n h, s + (n + 2) h)` the glued curve is the `n`-th piece
  have hkey : ∀ n : ℕ, ∀ t ∈ Ico (s + n * h) (s + (n + 2) * h),
      u t = σ (s + n * h) (p n) t := by
    intro n t ht
    have ht0 : 0 ≤ t - s := by nlinarith [ht.1, (by positivity : (0 : ℝ) ≤ n * h)]
    set m := ⌊(t - s) / h⌋₊ with hm
    have hm1 : (m : ℝ) * h ≤ t - s :=
      (le_div_iff₀ hpos).1 (Nat.floor_le (div_nonneg ht0 hpos.le))
    have hm2 : t - s < ((m : ℝ) + 1) * h := (div_lt_iff₀ hpos).1 (Nat.lt_floor_add_one _)
    have hnm : (n : ℝ) < m + 1 :=
      lt_of_mul_lt_mul_right (by linarith [ht.1] : (n : ℝ) * h < (m + 1) * h) hpos.le
    have hmn : (m : ℝ) < n + 2 :=
      lt_of_mul_lt_mul_right (by linarith [ht.2] : (m : ℝ) * h < (n + 2) * h) hpos.le
    have hnm' : n < m + 1 := by exact_mod_cast hnm
    have hmn' : m < n + 2 := by exact_mod_cast hmn
    rcases (by omega : m = n ∨ m = n + 1) with h1 | h1
    · simp only [hu, ← hm, h1]
    · simp only [hu, ← hm, h1]
      push_cast
      apply hagree
      rw [h1] at hm1
      push_cast at hm1
      exact ⟨by linarith, by linarith [ht.2]⟩
  have hex : ∀ t, s < t → ∃ n : ℕ, s + n * h < t ∧ t < s + (n + 2) * h := by
    intro t ht
    refine ⟨⌊(t - s) / h - 1 / 2⌋₊, ?_, ?_⟩
    · rcases le_or_gt 0 ((t - s) / h - 1 / 2) with h1 | h1
      · have := Nat.floor_le h1
        have : (⌊(t - s) / h - 1 / 2⌋₊ : ℝ) + 1 / 2 ≤ (t - s) / h := by linarith
        rw [le_div_iff₀ hpos] at this
        nlinarith
      · rw [Nat.floor_of_nonpos h1.le]; simpa using ht
    · have := Nat.lt_floor_add_one ((t - s) / h - 1 / 2)
      have : (t - s) / h < (⌊(t - s) / h - 1 / 2⌋₊ : ℝ) + 2 := by linarith
      have := (div_lt_iff₀ hpos).1 this
      linarith
  have hu0 : ∀ t ∈ Ico s (s + 2 * h), u t = σ s u₀ t := by
    intro t ht
    simpa [hp0] using hkey 0 t ⟨by simpa using ht.1, by simpa using ht.2⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu0 s ⟨le_rfl, by linarith⟩, hσ0]
  · have hd := (hσ s u₀ s ⟨le_rfl, by linarith⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE (by linarith : s < s + 2 * h))
    rw [hσ0] at hd
    refine hd.congr_of_eventuallyEq ?_ (hu0 s ⟨le_rfl, by linarith⟩)
    filter_upwards [Ico_mem_nhdsGE (by linarith : s < s + 2 * h)] with t ht using hu0 t ht
  · intro t ht
    obtain ⟨n, h1, h2⟩ := hex t ht
    have hd := (hσ (s + n * h) (p n) t ⟨h1.le, by linarith⟩).hasDerivAt
      (Icc_mem_nhds h1 (by linarith))
    have heq : u =ᶠ[𝓝 t] σ (s + n * h) (p n) := by
      filter_upwards [Ioo_mem_nhds h1 h2] with r hr using hkey n r ⟨hr.1.le, hr.2⟩
    rw [hkey n t ⟨h1.le, h2⟩]
    exact hd.congr_of_eventuallyEq heq

end LinearODE

/- A curve that is continuous on `[a, ∞)` and has derivative `0` at every `t > a` is constant on
`[a, ∞)` (no derivative at `a` is needed: constancy on `[b, t]` for `a < b` and a limit). -/
private theorem eq_of_hasDerivAt_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : ℝ → F} {a : ℝ} (hc : ContinuousOn w (Ici a)) (hd : ∀ t, a < t → HasDerivAt w 0 t)
    {t : ℝ} (ht : a ≤ t) : w t = w a := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rfl
  have key : ∀ b ∈ Ioo a t, w b = w t := by
    intro b hb
    have := constant_of_has_deriv_right_zero (f := w) (a := b) (b := t)
      (hc.mono fun x hx => mem_Ici.2 (hb.1.le.trans hx.1))
      (fun x hx => (hd x (hb.1.trans_le hx.1)).hasDerivWithinAt) t ⟨hb.2.le, le_rfl⟩
    exact this.symm
  have h1 : Tendsto w (𝓝[>] a) (𝓝 (w a)) :=
    ((hc a self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
  have h2 : Tendsto w (𝓝[>] a) (𝓝 (w t)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with b hb
    exact (key b hb).symm
  exact tendsto_nhds_unique h2 h1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A state-transition matrix of the linear time-varying system `ż = A(t)z`** (MLS eq. (4.40),
p. 184, the linearization in Theorem 4.6) on `[0, ∞)`: `Φ(s, s) = 1`, the composition law
`Φ(t, s) Φ(s, r) = Φ(t, r)`, and `∂Φ(t, s)/∂t = A(t) Φ(t, s)` (a derivative within `[0, ∞)`), for
all `t, s, r ≥ 0`. `Φ(t, s)` maps the state at time `s` to the state at time `t`, forward or
backward. A hypothesis structure, like `HasFlow`; `exists_isStateTransition` constructs one for
`A` continuous and bounded on `[0, ∞)`, and it is unique (`IsStateTransition.unique`). Time first;
matrices are continuous linear maps `E →L[ℝ] E`. MLS does not define `Φ`. -/
structure IsStateTransition (A : ℝ → E →L[ℝ] E) (Φ : ℝ → ℝ → E →L[ℝ] E) : Prop where
  /-- `Φ(s, s) = 1`. -/
  self_eq_one : ∀ s, 0 ≤ s → Φ s s = 1
  /-- The composition law `Φ(t, s) Φ(s, r) = Φ(t, r)`. -/
  mul_eq : ∀ t s r, 0 ≤ t → 0 ≤ s → 0 ≤ r → Φ t s * Φ s r = Φ t r
  /-- `∂Φ(t, s)/∂t = A(t) Φ(t, s)`, as a derivative within `[0, ∞)`. -/
  hasDerivWithinAt : ∀ t s, 0 ≤ t → 0 ≤ s →
    HasDerivWithinAt (fun τ => Φ τ s) (A t * Φ t s) (Ici 0) t

namespace IsStateTransition

variable {A : ℝ → E →L[ℝ] E} {Φ : ℝ → ℝ → E →L[ℝ] E}

/-- **`∂Φ(t, s)/∂t = A(t) Φ(t, s)` at every `t > 0`** (MLS eq. (4.40), p. 184). -/
theorem hasDerivAt (h : IsStateTransition A Φ) {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => Φ τ s) (A t * Φ t s) t :=
  (h.hasDerivWithinAt t s ht.le hs).hasDerivAt (Ici_mem_nhds ht)

/-- `t ↦ Φ(t, s)` is continuous on `[0, ∞)` (state-transition matrix of MLS eq. (4.40), p. 184). -/
theorem continuousOn (h : IsStateTransition A Φ) {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun τ => Φ τ s) (Ici 0) :=
  fun t ht => (h.hasDerivWithinAt t s ht hs).continuousWithinAt

/-- **Invertibility: `Φ(t, s) Φ(s, t) = 1`** (state-transition matrix of MLS eq. (4.40), p. 184). -/
theorem mul_eq_one (h : IsStateTransition A Φ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Φ t s * Φ s t = 1 := by
  rw [h.mul_eq t s t ht hs ht, h.self_eq_one t ht]

/-- **`Φ(t, s)` is invertible** (state-transition matrix of MLS eq. (4.40), p. 184). -/
theorem isUnit (h : IsStateTransition A Φ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    IsUnit (Φ t s) :=
  ⟨⟨Φ t s, Φ s t, h.mul_eq_one ht hs, h.mul_eq_one hs ht⟩, rfl⟩

/-- **The inverse of `Φ(t, s)` is `Φ(s, t)`** (state-transition matrix of MLS eq. (4.40), p. 184),
with Mathlib's `Ring.inverse`. -/
theorem inverse_eq (h : IsStateTransition A Φ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Ring.inverse (Φ t s) = Φ s t :=
  Ring.inverse_unit (⟨Φ t s, Φ s t, h.mul_eq_one ht hs, h.mul_eq_one hs ht⟩ : (E →L[ℝ] E)ˣ)

section Complete

variable [CompleteSpace E]

/-- **The derivative in the initial time: `∂Φ(t, s)/∂s = −Φ(t, s) A(s)`** (state-transition matrix
of MLS eq. (4.40), p. 184), within `[0, ∞)`. From `Φ(t, s) = Φ(t, 0) Φ(s, 0)⁻¹` and the derivative
of the inverse in the Banach algebra `E →L[ℝ] E` (Mathlib's `hasFDerivAt_ringInverse`). -/
theorem hasDerivWithinAt_snd (h : IsStateTransition A Φ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivWithinAt (fun σ => Φ t σ) (-(Φ t s * A s)) (Ici 0) s := by
  set u : (E →L[ℝ] E)ˣ := ⟨Φ s 0, Φ 0 s, h.mul_eq_one hs le_rfl, h.mul_eq_one le_rfl hs⟩
  have h1 := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivWithinAt s
    (h.hasDerivWithinAt s 0 hs le_rfl)
  have h2 := h1.const_mul (Φ t 0)
  have hderiv : Φ t 0 * (-((ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)) ↑u⁻¹ ↑u⁻¹))
      (A s * Φ s 0) = -(Φ t s * A s) := by
    rw [neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    change Φ t 0 * -(Φ 0 s * (A s * Φ s 0) * Φ 0 s) = -(Φ t s * A s)
    rw [mul_neg, ← h.mul_eq t 0 s ht le_rfl hs]
    congr 1
    calc Φ t 0 * (Φ 0 s * (A s * Φ s 0) * Φ 0 s)
        = Φ t 0 * Φ 0 s * A s * (Φ s 0 * Φ 0 s) := by noncomm_ring
      _ = Φ t 0 * Φ 0 s * A s := by rw [h.mul_eq_one hs le_rfl, mul_one]
  rw [← hderiv]
  refine h2.congr (fun σ hσ => ?_) ?_
  · simp only [Function.comp_apply]
    rw [h.inverse_eq hσ le_rfl, h.mul_eq t 0 σ ht le_rfl hσ]
  · simp only [Function.comp_apply]
    rw [h.inverse_eq hs le_rfl, h.mul_eq t 0 s ht le_rfl hs]

/-- **`∂Φ(t, s)/∂s = −Φ(t, s) A(s)` at every `s > 0`** (state-transition matrix of MLS eq. (4.40),
p. 184). -/
theorem hasDerivAt_snd (h : IsStateTransition A Φ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    HasDerivAt (fun σ => Φ t σ) (-(Φ t s * A s)) s :=
  (h.hasDerivWithinAt_snd ht hs.le).hasDerivAt (Ici_mem_nhds hs)

/-- `s ↦ Φ(t, s)` is continuous on `[0, ∞)` (state-transition matrix of MLS eq. (4.40), p. 184). -/
theorem continuousOn_snd (h : IsStateTransition A Φ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun σ => Φ t σ) (Ici 0) :=
  fun _ hs => (h.hasDerivWithinAt_snd ht hs).continuousWithinAt

end Complete

/-- **The state-transition matrix gives the solutions of `ż = A(t)z`** (MLS eq. (4.40), p. 184):
for `t₀ ≥ 0`, `t ↦ Φ(t, t₀) z₀` is a solution from `t₀` (`IsSolution`) with initial state `z₀`. -/
theorem isSolution (h : IsStateTransition A Φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (z₀ : E) :
    IsSolution (fun t z => A t z) t₀ (fun t => Φ t t₀ z₀) := by
  refine ⟨((h.continuousOn ht₀).mono (Ici_subset_Ici.2 ht₀)).clm_apply continuousOn_const,
    fun t ht => ?_⟩
  have := (h.hasDerivAt (ht₀.trans_lt ht) ht₀).clm_apply (hasDerivAt_const t z₀)
  simpa using this

/-- **Uniqueness: every solution of `ż = A(t)z` is `Φ(t, t₀) z(t₀)`** (MLS eq. (4.40), p. 184, and
the uniqueness part of the standing assumption, p. 179): if `x` solves the system from `t₀ ≥ 0`
(`IsSolution`), then `x(t) = Φ(t, t₀) x(t₀)` for `t ≥ t₀`. Proof: `t ↦ Φ(t₀, t) x(t)` has
derivative `0`. No continuity of `A` is used. -/
theorem eq_of_isSolution [CompleteSpace E] (h : IsStateTransition A Φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → E} (hx : IsSolution (fun t z => A t z) t₀ x) {t : ℝ} (ht : t₀ ≤ t) :
    x t = Φ t t₀ (x t₀) := by
  have hw : (fun τ => Φ t₀ τ (x τ)) t = (fun τ => Φ t₀ τ (x τ)) t₀ := by
    refine eq_of_hasDerivAt_eq_zero (w := fun τ => Φ t₀ τ (x τ)) ?_ (fun τ hτ => ?_) ht
    · exact ((h.continuousOn_snd ht₀).mono (Ici_subset_Ici.2 ht₀)).clm_apply hx.1
    · have h1 := (h.hasDerivAt_snd ht₀ (ht₀.trans_lt hτ)).clm_apply (hx.2 τ hτ)
      convert h1 using 1
      simp
  simp only [h.self_eq_one t₀ ht₀, one_apply_eq_self] at hw
  have h2 : Φ t t₀ (Φ t₀ t (x t)) = x t := by
    rw [← mul_apply_eq_comp, h.mul_eq_one (ht₀.trans ht) ht₀, one_apply_eq_self]
  rw [← h2, hw]

/-- **Grönwall's bound forward in time** (for MLS Theorem 4.6, p. 184, with `A(·)` bounded): if
`‖A(t)‖ ≤ M` for `t ≥ 0`, then `‖Φ(t, s)‖ ≤ e^{M(t − s)}` for `0 ≤ s ≤ t`. -/
theorem norm_le_exp (h : IsStateTransition A Φ) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : ‖Φ t s‖ ≤ Real.exp (M * (t - s)) := by
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun τ => Φ τ s)
    (f' := fun τ => A τ * Φ τ s) (δ := 1) (K := M) (ε := 0) (a := s) (b := t)
    ((h.continuousOn hs).mono (Icc_subset_Ici_iff hst |>.2 hs))
    (fun τ hτ => (h.hasDerivWithinAt τ s (hs.trans hτ.1) hs).mono
      (Ici_subset_Ici.2 (hs.trans hτ.1)))
    (by simp only [h.self_eq_one s hs]; exact ContinuousLinearMap.norm_id_le)
    (fun τ hτ => by
      rw [add_zero]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hM τ (hs.trans hτ.1)) (norm_nonneg _)))
    t ⟨hst, le_rfl⟩
  simpa [gronwallBound_ε0] using this

/-- **Grönwall's bound backward in time** (for MLS Theorem 4.6, p. 184, with `A(·)` bounded): if
`‖A(t)‖ ≤ M` for `t ≥ 0`, then `‖Φ(s, t)‖ ≤ e^{M(t − s)}` for `0 ≤ s ≤ t`. -/
theorem norm_le_exp_snd [CompleteSpace E] (h : IsStateTransition A Φ) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖Φ s t‖ ≤ Real.exp (M * (t - s)) := by
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun σ => Φ s σ)
    (f' := fun σ => -(Φ s σ * A σ)) (δ := 1) (K := M) (ε := 0) (a := s) (b := t)
    ((h.continuousOn_snd hs).mono (Icc_subset_Ici_iff hst |>.2 hs))
    (fun σ hσ => (h.hasDerivWithinAt_snd hs (hs.trans hσ.1)).mono
      (Ici_subset_Ici.2 (hs.trans hσ.1)))
    (by simp only [h.self_eq_one s hs]; exact ContinuousLinearMap.norm_id_le)
    (fun σ hσ => by
      rw [add_zero, norm_neg]
      refine (norm_mul_le _ _).trans ?_
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM σ (hs.trans hσ.1)) (norm_nonneg _))
    t ⟨hst, le_rfl⟩
  simpa [gronwallBound_ε0] using this

/-- **The state-transition matrix is unique** (MLS eq. (4.40), p. 184): two state-transition
matrices of the same `A` agree at all `t, s ≥ 0`. Forward in time by uniqueness of solutions
(`eq_of_isSolution`), backward through the inverse. -/
theorem unique [CompleteSpace E] {Φ' : ℝ → ℝ → E →L[ℝ] E} (h : IsStateTransition A Φ)
    (h' : IsStateTransition A Φ') {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) : Φ t s = Φ' t s := by
  have hfwd : ∀ t s, 0 ≤ s → s ≤ t → Φ t s = Φ' t s := by
    intro t s hs hst
    ext1 z
    have := h.eq_of_isSolution hs (h'.isSolution hs z) hst
    simpa [h'.self_eq_one s hs] using this.symm
  rcases le_total s t with hst | hts
  · exact hfwd t s hs hst
  · rw [← h.inverse_eq hs ht, ← h'.inverse_eq hs ht, hfwd s t ht hts]

end IsStateTransition

/-- **Existence of the state-transition matrix** (for MLS Theorem 4.6, p. 184, with the
linearization (4.40)): if `A` is continuous and bounded on `[0, ∞)` (`‖A(t)‖ ≤ M`), then
`ż = A(t)z` has a state-transition matrix. Continuity is a hypothesis MLS does not state for
Theorem 4.6 (its p. 179 conditions allow piecewise continuity in `t`). Construction:
`Φ(t, s) = X(t) Y(s)` with `X' = ÃX`, `Y' = −YÃ`, `X(−1) = Y(−1) = 1`, for the extension
`Ã(t) = A(max t 0)`; `YX = 1` (its derivative vanishes) and `XY = 1` (uniqueness for
`Z' = ÃZ − ZÃ`). -/
theorem exists_isStateTransition [CompleteSpace E] {A : ℝ → E →L[ℝ] E}
    (hA : ContinuousOn A (Ici 0)) {M : ℝ} (hM : ∀ t, 0 ≤ t → ‖A t‖ ≤ M) :
    ∃ Φ : ℝ → ℝ → E →L[ℝ] E, IsStateTransition A Φ := by
  set A' : ℝ → E →L[ℝ] E := fun t => A (max t 0) with hA'
  have hA'c : Continuous A' :=
    hA.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  have hA'M : ∀ t, ‖A' t‖ ≤ M := fun t => hM _ (le_max_right t 0)
  have hA'eq : ∀ t, 0 ≤ t → A' t = A t := fun t ht => by simp [hA', max_eq_left ht]
  -- the fundamental solution `X' = A' X`
  set BX : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (A' t) with hBX
  have hBXc : Continuous BX := (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).continuous.comp hA'c
  have hBXM : ∀ t, ‖BX t‖ ≤ M := fun t =>
    (ContinuousLinearMap.opNorm_mul_apply_le ℝ (E →L[ℝ] E) (A' t)).trans (hA'M t)
  -- the adjoint solution `Y' = −Y A'`
  set BY : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    fun t => -(ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip (A' t) with hBY
  have hBYc : Continuous BY :=
    ((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip.continuous.comp hA'c).neg
  have hBYM : ∀ t, ‖BY t‖ ≤ M := by
    intro t
    change ‖-((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip (A' t))‖ ≤ M
    rw [norm_neg]
    refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun b => ?_).trans (hA'M t)
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_comm ‖A' t‖]
    exact norm_mul_le _ _
  obtain ⟨X, hX0, hXs, hX⟩ := exists_forall_hasDerivAt_linear hBXc hBXM (-1) 1
  obtain ⟨Y, hY0, hYs, hY⟩ := exists_forall_hasDerivAt_linear hBYc hBYM (-1) 1
  simp only [hBX, hBY, ContinuousLinearMap.mul_apply', neg_apply,
    ContinuousLinearMap.flip_apply] at hXs hX hYs hY
  have hXc : ContinuousOn X (Ici (-1)) := by
    intro t ht
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h | h
    · subst h; exact hXs.continuousWithinAt
    · exact (hX t h).continuousAt.continuousWithinAt
  have hYc : ContinuousOn Y (Ici (-1)) := by
    intro t ht
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h | h
    · subst h; exact hYs.continuousWithinAt
    · exact (hY t h).continuousAt.continuousWithinAt
  -- `Y X = 1`
  have hYX : ∀ t, -1 ≤ t → Y t * X t = 1 := by
    intro t ht
    have := eq_of_hasDerivAt_eq_zero (w := fun τ => Y τ * X τ) (hYc.mul hXc)
      (fun τ hτ => by
        have h1 := (hY τ hτ).mul (hX τ hτ)
        convert h1 using 1
        noncomm_ring) ht
    simpa [hX0, hY0] using this
  -- `X Y = 1`, by uniqueness for `Z' = A' Z − Z A'`
  have hXY : ∀ t, -1 ≤ t → X t * Y t = 1 := by
    intro t ht
    set BZ : ℝ → (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := fun τ => BX τ + BY τ with hBZ
    have hBZM : ∀ τ, ‖BZ τ‖₊ ≤ (2 * M).toNNReal := by
      intro τ
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by
        linarith [hBXM τ, norm_nonneg (BX τ)])]
      linarith [norm_add_le (BX τ) (BY τ), hBXM τ, hBYM τ]
    have hlip : ∀ τ, LipschitzWith (2 * M).toNNReal (fun Z => BZ τ Z) := fun τ =>
      (BZ τ).lipschitzWith.weaken (hBZM τ)
    have hBZapp : ∀ τ Z, BZ τ Z = A' τ * Z + -(Z * A' τ) := fun τ Z => by
      simp [hBZ, hBX, hBY]
    have := ODE_solution_unique (v := fun τ Z => BZ τ Z) (f := fun τ => X τ * Y τ)
      (g := fun _ => 1) (a := -1) (b := t) hlip ((hXc.mul hYc).mono Icc_subset_Ici_self)
      (fun τ hτ => by
        rw [hBZapp]
        rcases eq_or_lt_of_le hτ.1 with h | h
        · subst h
          have h1 := hXs.mul hYs
          convert h1 using 1
          simp [hX0, hY0]
        · have h1 := ((hX τ h).mul (hY τ h)).hasDerivWithinAt (s := Ici τ)
          convert h1 using 1
          noncomm_ring)
      continuousOn_const
      (fun τ _ => by
        rw [hBZapp]
        convert hasDerivWithinAt_const τ (Ici τ) (1 : (E →L[ℝ] E)) using 1
        simp)
      (by simp [hX0, hY0]) ⟨ht, le_rfl⟩
    exact this
  refine ⟨fun t s => X t * Y s, ⟨fun s hs => hXY s (by linarith), fun t s r ht hs hr => ?_,
    fun t s ht hs => ?_⟩⟩
  · rw [mul_assoc, ← mul_assoc (Y s), hYX s (by linarith), one_mul]
  · have h1 := ((hX t (by linarith)).mul_const (Y s)).hasDerivWithinAt (s := Ici 0)
    rw [hA'eq t ht, mul_assoc] at h1
    exact h1

/-- **The constant case: `Φ(t, s) = exp((t − s)L)`** (MLS eq. (4.40), p. 184, with
`A(t) ≡ L`; MLS Example 4.5 is such a system): the matrix exponential, Mathlib's
`NormedSpace.exp` in `E →L[ℝ] E`, is the state-transition matrix of `ż = Lz`. -/
theorem isStateTransition_exp [CompleteSpace E] (L : E →L[ℝ] E) :
    IsStateTransition (fun _ => L) (fun t s => NormedSpace.exp ((t - s) • L)) := by
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine ⟨fun s _ => by simp, fun t s r _ _ _ => ?_, fun t s _ _ => ?_⟩
  · have hcomm : Commute ((t - s) • L) ((s - r) • L) :=
      ((Commute.refl L).smul_left _).smul_right _
    rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul]
    congr 2
    ring
  · have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) L (t - s)).comp_sub_const t s
    exact h1.hasDerivWithinAt

end Stability
end RoboLean
