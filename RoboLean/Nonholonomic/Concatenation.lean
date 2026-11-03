import RoboLean.Nonholonomic.Controllability
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Concatenation of trajectories with piecewise constant inputs (MLS pp. 329–331)

**What MLS prints.** The proof of Proposition 7.7 (p. 331) "concatenate[s] the inputs which steer
`q₀` to `q_f ∈ W` with `u′`", and the motion along a bracket (p. 329) runs the input sequence
`u = e₁, e₂, −e₁, −e₂` on four consecutive intervals of length `ε`; both glue piecewise constant
inputs end to end. The proof of Proposition 7.6 (p. 330) builds the manifolds `N_k` from points
`φ^{f_k}_{t_k} ∘ ⋯ ∘ φ^{f₁}_{t₁}(q₀)`, each one segment of an integral curve after the last.

**Proved here.**

* Concatenation: an input on `[0, T₁]` followed by an input on `[0, T₂]` is piecewise constant on
  `[0, T₁ + T₂]` (`IsPiecewiseConstant.concat`), and a trajectory on `[0, T₁]` followed by a
  trajectory on `[0, T₂]` that starts where the first ends is a trajectory on `[0, T₁ + T₂]` for
  the concatenated input (`IsTrajectory.concat`); hence the reachable sets compose,
  `q₁ ∈ R^V(q₀, T₁)`, `q₂ ∈ R^V(q₁, T₂)` give `q₂ ∈ R^V(q₀, T₁ + T₂)` (`mem_reachableSet_trans`).
* One segment of an integral curve: if `γ` is an integral curve of a field `X` that agrees with
  the generator `gⱼ` along `γ` between the times `0` and `σ`, then `γ(σ)` is reachable from `γ(0)`
  in any time `T > 0` with the constant input `(σ / T) eⱼ`, inside any `V` containing that piece of
  `γ` (`mem_reachableSet_of_integralCurve`).

**Conventions.** Those of `Nonholonomic/Controllability`: inputs and trajectories on `[0, T]`,
trajectories continuous on `[0, T]` with the derivative of (7.10) away from finitely many times.
The concatenation at time `T₁` takes the first input and trajectory on `t ≤ T₁` and the second,
shifted by `T₁`, on `t > T₁` (`concatInput`, `concatPath`).
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS p. 331 (Proposition 7.7, "concatenate the inputs"): the input `u` on `[0, T₁]` followed
by `v` shifted to `[T₁, T₁ + T₂]`.** -/
def concatInput (u v : ℝ → Fin m → ℝ) (T₁ : ℝ) : ℝ → Fin m → ℝ :=
  fun t => if t ≤ T₁ then u t else v (t - T₁)

/-- **MLS p. 331 (Proposition 7.7): the curve `x` on `[0, T₁]` followed by `y` shifted to
`[T₁, T₁ + T₂]`.** -/
def concatPath (x y : ℝ → E) (T₁ : ℝ) : ℝ → E :=
  fun t => if t ≤ T₁ then x t else y (t - T₁)

/-- **MLS pp. 329 and 331: concatenated piecewise constant inputs are piecewise constant.** If `u`
is piecewise constant with values in `U` on `[0, T₁]` and `v` on `[0, T₂]`, then
`concatInput u v T₁` is piecewise constant with values in `U` on `[0, T₁ + T₂]`. -/
theorem IsPiecewiseConstant.concat {U : Set (Fin m → ℝ)} {u v : ℝ → Fin m → ℝ} {T₁ T₂ : ℝ}
    (hu : IsPiecewiseConstant U T₁ u) (hv : IsPiecewiseConstant U T₂ v) :
    IsPiecewiseConstant U (T₁ + T₂) (concatInput u v T₁) := by
  obtain ⟨hu1, Su, hSu⟩ := hu
  obtain ⟨hv1, Sv, hSv⟩ := hv
  refine ⟨fun t ht => ?_, Su ∪ Sv.image (fun s => s + T₁) ∪ {T₁}, fun t ht htS => ?_⟩
  · by_cases htT : t ≤ T₁
    · simp only [concatInput, htT, ↓reduceIte]
      exact hu1 t ⟨ht.1, htT⟩
    · simp only [concatInput, htT, ↓reduceIte]
      exact hv1 _ ⟨by linarith [not_le.1 htT], by linarith [ht.2]⟩
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or] at htS
    obtain ⟨⟨htu, htv⟩, htT⟩ := htS
    rcases lt_or_gt_of_ne htT with hlt | hgt
    · filter_upwards [hSu t ⟨ht.1, hlt⟩ htu, Iio_mem_nhds hlt] with s hs hsT
      simp only [concatInput, le_of_lt (mem_Iio.1 hsT), hlt.le, ↓reduceIte, hs]
    · have h1 : t - T₁ ∈ Ioo 0 T₂ := ⟨by linarith, by linarith [ht.2]⟩
      have h2 : t - T₁ ∉ Sv := fun h => htv ⟨t - T₁, h, by ring⟩
      have hlim : Tendsto (fun s => s - T₁) (𝓝 t) (𝓝 (t - T₁)) :=
        (continuous_id.sub continuous_const).tendsto t
      filter_upwards [hlim.eventually (hSv _ h1 h2), Ioi_mem_nhds hgt] with s hs hsT
      simp only [concatInput, not_le.2 (mem_Ioi.1 hsT), not_le.2 hgt, ↓reduceIte, hs]

/-- **MLS p. 331 (Proposition 7.7): concatenated trajectories are a trajectory.** If `x` is a
trajectory of (7.10) on `[0, T₁]` for `u`, `y` one on `[0, T₂]` for `v`, `x(T₁) = y(0)` and
`T₁, T₂ ≥ 0`, then `concatPath x y T₁` is a trajectory on `[0, T₁ + T₂]` for
`concatInput u v T₁`. -/
theorem IsTrajectory.concat {g : Fin m → E → E} {u v : ℝ → Fin m → ℝ} {T₁ T₂ : ℝ} {x y : ℝ → E}
    (hx : IsTrajectory g u T₁ x) (hy : IsTrajectory g v T₂ y) (hxy : x T₁ = y 0) (h₁ : 0 ≤ T₁)
    (h₂ : 0 ≤ T₂) : IsTrajectory g (concatInput u v T₁) (T₁ + T₂) (concatPath x y T₁) := by
  obtain ⟨hxc, Sx, hSx⟩ := hx
  obtain ⟨hyc, Sy, hSy⟩ := hy
  refine ⟨?_, Sx ∪ Sy.image (fun s => s + T₁) ∪ {T₁}, fun t ht htS => ?_⟩
  · rw [← Icc_union_Icc_eq_Icc h₁ (by linarith : T₁ ≤ T₁ + T₂)]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hxc.congr fun t ht => by simp [concatPath, ht.2]
    · have hy' : ContinuousOn (fun t => y (t - T₁)) (Icc T₁ (T₁ + T₂)) :=
        hyc.comp (continuous_id.sub continuous_const).continuousOn fun t ht =>
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine hy'.congr fun t ht => ?_
      by_cases htT : t ≤ T₁
      · rw [le_antisymm htT ht.1]
        simp [concatPath, hxy]
      · simp [concatPath, htT]
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or] at htS
    obtain ⟨⟨htx, hty⟩, htT⟩ := htS
    rcases lt_or_gt_of_ne htT with hlt | hgt
    · have hev : concatPath x y T₁ =ᶠ[𝓝 t] x := by
        filter_upwards [Iio_mem_nhds hlt] with s hs
        simp [concatPath, le_of_lt (mem_Iio.1 hs)]
      have hval : concatPath x y T₁ t = x t := by simp [concatPath, hlt.le]
      have hin : concatInput u v T₁ t = u t := by simp [concatInput, hlt.le]
      rw [hval, hin]
      exact (hSx t ⟨ht.1, hlt⟩ htx).congr_of_eventuallyEq hev
    · have h1 : t - T₁ ∈ Ioo 0 T₂ := ⟨by linarith, by linarith [ht.2]⟩
      have h2 : t - T₁ ∉ Sy := fun h => hty ⟨t - T₁, h, by ring⟩
      have hd := HasDerivAt.comp_sub_const t T₁ (hSy _ h1 h2)
      have hev : concatPath x y T₁ =ᶠ[𝓝 t] fun s => y (s - T₁) := by
        filter_upwards [Ioi_mem_nhds hgt] with s hs
        simp [concatPath, not_le.2 (mem_Ioi.1 hs)]
      have hval : concatPath x y T₁ t = y (t - T₁) := by simp [concatPath, not_le.2 hgt]
      have hin : concatInput u v T₁ t = v (t - T₁) := by simp [concatInput, not_le.2 hgt]
      rw [hval, hin]
      exact hd.congr_of_eventuallyEq hev

/-- **MLS p. 331 (Proposition 7.7): reachable sets compose under concatenation.** If
`q₁ ∈ R^V(q₀, T₁)` and `q₂ ∈ R^V(q₁, T₂)` with `T₁, T₂ ≥ 0`, then `q₂ ∈ R^V(q₀, T₁ + T₂)`. -/
theorem mem_reachableSet_trans {g : Fin m → E → E} {U : Set (Fin m → ℝ)} {V : Set E}
    {q₀ q₁ q₂ : E} {T₁ T₂ : ℝ} (h₁ : q₁ ∈ reachableSet g U V q₀ T₁)
    (h₂ : q₂ ∈ reachableSet g U V q₁ T₂) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) :
    q₂ ∈ reachableSet g U V q₀ (T₁ + T₂) := by
  obtain ⟨u, x, hu, hx, hx0, hxT, hxV⟩ := h₁
  obtain ⟨v, y, hv, hy, hy0, hyT, hyV⟩ := h₂
  refine ⟨concatInput u v T₁, concatPath x y T₁, hu.concat hv,
    hx.concat hy (hxT.trans hy0.symm) hT₁ hT₂, by simp [concatPath, hT₁, hx0], ?_, fun t ht => ?_⟩
  · rcases eq_or_lt_of_le hT₂ with h0 | hpos
    · subst h0
      simp only [concatPath, add_zero, le_refl, ↓reduceIte]
      rw [hxT, ← hy0, hyT]
    · simp [concatPath, not_le.2 (by linarith : T₁ < T₁ + T₂), hyT]
  · by_cases htT : t ≤ T₁
    · simp only [concatPath, htT, ↓reduceIte]
      exact hxV t ⟨ht.1, htT⟩
    · simp only [concatPath, htT, ↓reduceIte]
      exact hyV _ ⟨by linarith [not_le.1 htT], by linarith [ht.2]⟩

/-- **MLS p. 330 (Proposition 7.6, one factor `φ^{f}_{t}` of `N_k`) with p. 329 (a constant
input): one segment of an integral curve is reachable.** Let `γ` be an integral curve of a field
`X` (`γ′(s) = X(γ(s))` for all `s`), with `X(γ(s)) = gⱼ(γ(s))` and `γ(s) ∈ V` for every `s`
between `0` and `σ`. Then for every `T > 0` with `(σ / T) eⱼ ∈ U`, `γ(σ) ∈ R^V(γ(0), T)`, by the
constant input `(σ / T) eⱼ` and the trajectory `t ↦ γ(σ t / T)`. -/
theorem mem_reachableSet_of_integralCurve {g : Fin m → E → E} {U : Set (Fin m → ℝ)} {V : Set E}
    {X : E → E} {γ : ℝ → E} (j : Fin m) {σ T : ℝ} (hT : 0 < T)
    (hU : (Pi.single j (σ / T) : Fin m → ℝ) ∈ U) (hγ : ∀ s, HasDerivAt γ (X (γ s)) s)
    (hXg : ∀ s ∈ uIcc 0 σ, X (γ s) = g j (γ s)) (hV : ∀ s ∈ uIcc 0 σ, γ s ∈ V) :
    γ σ ∈ reachableSet g U V (γ 0) T := by
  set c := σ / T with hc
  have hmem : ∀ t ∈ Icc 0 T, c * t ∈ uIcc 0 σ := by
    intro t ht
    have hθ0 : 0 ≤ t / T := div_nonneg ht.1 hT.le
    have hθ1 : t / T ≤ 1 := (div_le_one hT).2 ht.2
    have key : c * t = σ * (t / T) := by rw [hc]; ring
    rw [key, mem_uIcc]
    rcases le_total 0 σ with hσ | hσ
    · exact Or.inl ⟨mul_nonneg hσ hθ0, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith⟩
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun s => (hγ s).continuousAt
  refine ⟨fun _ => Pi.single j c, fun t => γ (c * t),
    ⟨fun _ _ => hU, ∅, fun _ _ _ => Eventually.of_forall fun _ => rfl⟩,
    ⟨(hγc.comp (continuous_const.mul continuous_id)).continuousOn, ∅, fun t ht _ => ?_⟩,
    by simp, ?_, fun t ht => hV _ (hmem t ht)⟩
  · have hd := (hγ (c * t)).scomp t ((hasDerivAt_id t).const_mul c)
    have hX := hXg (c * t) (hmem t (Ioo_subset_Icc_self ht))
    have hdf : driftFree g (γ (c * t)) (Pi.single j c) = c • g j (γ (c * t)) := by
      simp [driftFree, Pi.single_apply, ite_smul]
    rw [hdf, ← hX]
    simpa [Function.comp_def] using hd
  · show γ (c * T) = γ σ
    rw [hc, div_mul_cancel₀ σ hT.ne']

end Nonholonomic
end RoboLean
