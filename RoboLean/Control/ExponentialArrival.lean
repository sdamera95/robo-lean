import RoboLean.Control.AugmentedPD

/-!
# Exponential bounds with explicit constants, arrival times, and PD set-point regulation

MLS Chapter 4, Definition 4.3 (printed pp. 180–181, eq. (4.34)) and Propositions 4.9–4.10
(pp. 193–195).

**Arrival times.** Definition 4.3 bounds a solution by
`‖x(t) − x*‖ ≤ m e^{−α(t − t₀)} ‖x(t₀) − x*‖`.
When the constants are known, the bound gives an explicit time after which the solution stays
within a tolerance `ε`: for initial errors at most `ρ`, every elapsed time
`τ ≥ T*(C, α, ρ, ε) = max(0, log(Cρ/ε)/α)` gives `C e^{−ατ} ‖x(t₀) − x*‖ ≤ ε`
(`Stability.arrivalTime`, `Stability.mul_exp_mul_le_of_arrivalTime_le`). The library's notions
`ExponentiallyStable` and `GloballyExponentiallyStable` assert that constants exist; the structure
`Stability.ExponentialBoundOn f x* C α ρ` names them, with the radius `ρ` of the initial errors it
covers, and is related to both notions.

**PD set-point regulation is exponential on bounded sets.** For a constant set point `θ_d`
(`θ̇_d ≡ 0`, `θ̈_d ≡ 0`) the augmented PD law (4.53) of p. 194 is
`τ = N(θ, θ̇) − K_v θ̇ − K_p (θ − θ_d)`, the PD law (4.51) of p. 193 with compensation of `N`, the
library's `ManipulatorModel.pdCompensatedTorque`
(`ManipulatorModel.augmentedPDTorque_const_eq_pdCompensatedTorque`); MLS p. 195 remarks that for
`θ̇_d ≡ 0` the law (4.53) "simplifies to the original PD control law (4.51)", the `N` term of
(4.53) aside. Proposition 4.10 as formalized in the library (semiglobal exponential tracking,
`ManipulatorModel.augmentedPD_tracking`) therefore gives exponential convergence to the set point
under the hypotheses of that theorem, with one overshoot constant `C` and, for every radius `ρ` of
initial errors, a rate `α`; the constants do not depend on the set point
(`ManipulatorModel.exponentialBoundOn_pdCompensatedTorque`). For this law Proposition 4.9 (p. 193)
states global asymptotic stability; the exponential bound here holds on bounded sets of initial
errors. The constants come from the Lyapunov function of the proof of Proposition 4.10 and are not
computed numerically here.

Conventions: the state is `(θ, θ̇)` with Mathlib's sup norms on `Fin n → ℝ` and on products, as in
`Control/Stability`; times are `t ≥ t₀ ≥ 0`; `Real.log` is the natural logarithm. Nothing here
concerns sampling, numerical integration, model error or a physical manipulator.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean

namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The arrival time of an exponential bound (MLS eq. (4.34), Definition 4.3, pp. 180–181).**
For constants `C, α` of the bound `‖x(t) − x*‖ ≤ C e^{−α(t − t₀)} ‖x(t₀) − x*‖`, an initial-error
bound `ρ` and a tolerance `ε`, the elapsed time `T* = max(0, log(Cρ/ε)/α)` after which the bound
is at most `ε` (`mul_exp_mul_le_of_arrivalTime_le`). A design quantity, not printed in MLS. -/
def arrivalTime (C α ρ ε : ℝ) : ℝ :=
  max 0 (Real.log (C * ρ / ε) / α)

/-- **The exponential bound is within the tolerance after the arrival time (MLS eq. (4.34),
p. 180).** For `C, α, ε > 0`, an initial error `0 ≤ e₀ ≤ ρ` and an elapsed time
`τ ≥ arrivalTime C α ρ ε`, the bound of Definition 4.3 satisfies `C e^{−ατ} e₀ ≤ ε`. -/
theorem mul_exp_mul_le_of_arrivalTime_le {C α ρ ε e₀ τ : ℝ} (hC : 0 < C) (hα : 0 < α)
    (hε : 0 < ε) (he₀ : 0 ≤ e₀) (hρ : e₀ ≤ ρ) (hτ : arrivalTime C α ρ ε ≤ τ) :
    C * Real.exp (-α * τ) * e₀ ≤ ε := by
  have hτ0 : 0 ≤ τ := (le_max_left _ _).trans hτ
  have hlog : Real.log (C * ρ / ε) / α ≤ τ := (le_max_right _ _).trans hτ
  have hρ0 : 0 ≤ ρ := he₀.trans hρ
  by_cases hcase : C * ρ ≤ ε
  · have he : Real.exp (-α * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc C * Real.exp (-α * τ) * e₀ ≤ C * 1 * e₀ := by gcongr
      _ ≤ C * ρ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hρ hC.le
      _ ≤ ε := hcase
  · have hCρ : 0 < C * ρ := hε.trans (not_le.mp hcase)
    have h1 : Real.log (C * ρ / ε) ≤ α * τ := by
      rw [div_le_iff₀ hα] at hlog
      linarith
    have h2 : Real.exp (-α * τ) ≤ ε / (C * ρ) := by
      have h3 : C * ρ / ε ≤ Real.exp (α * τ) := by
        calc C * ρ / ε = Real.exp (Real.log (C * ρ / ε)) :=
              (Real.exp_log (div_pos hCρ hε)).symm
          _ ≤ Real.exp (α * τ) := Real.exp_le_exp.mpr h1
      rw [show -α * τ = -(α * τ) by ring, Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) (div_pos hε hCρ), inv_div]
      exact h3
    have hρpos : 0 < ρ := pos_of_mul_pos_right hCρ hC.le
    calc C * Real.exp (-α * τ) * e₀ ≤ C * (ε / (C * ρ)) * ρ := by gcongr
      _ = ε := by field_simp

/-- **An exponential bound with named constants on a ball of initial errors (MLS Definition 4.3,
eq. (4.34), pp. 180–181).** `C > 0`, `α > 0`, and every solution from a time `t₀ ≥ 0` whose initial
error `‖x(t₀) − x*‖` is smaller than `ρ` satisfies
`‖x(t) − x*‖ ≤ C e^{−α(t − t₀)} ‖x(t₀) − x*‖` for all `t ≥ t₀`. With `ρ` fixed this is the bound
of Definition 4.3 with explicit constants; for every `ρ` it is the global bound of p. 181. -/
structure ExponentialBoundOn (f : ℝ → E → E) (xe : E) (C α ρ : ℝ) : Prop where
  /-- The overshoot constant is positive. -/
  pos_C : 0 < C
  /-- The rate is positive. -/
  pos_α : 0 < α
  /-- The bound (4.34) for initial errors smaller than `ρ`. -/
  bound : ∀ t₀, 0 ≤ t₀ → ∀ x, IsSolution f t₀ x → ‖x t₀ - xe‖ < ρ → ∀ t, t₀ ≤ t →
    ‖x t - xe‖ ≤ C * Real.exp (-α * (t - t₀)) * ‖x t₀ - xe‖

/-- **Arrival within a tolerance (MLS eq. (4.34), p. 180).** Under an exponential bound with
constants `(C, α)` on the initial errors smaller than `ρ`, every solution from `t₀ ≥ 0` that starts
within `ρ` is within `ε > 0` of `x*` at every time `t` with `t − t₀ ≥ arrivalTime C α ρ ε`. -/
theorem ExponentialBoundOn.norm_sub_le_of_arrivalTime_le {f : ℝ → E → E} {xe : E} {C α ρ ε : ℝ}
    (h : ExponentialBoundOn f xe C α ρ) (hε : 0 < ε) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E}
    (hx : IsSolution f t₀ x) (hx₀ : ‖x t₀ - xe‖ < ρ) {t : ℝ}
    (ht : arrivalTime C α ρ ε ≤ t - t₀) : ‖x t - xe‖ ≤ ε := by
  have h0 : (0 : ℝ) ≤ arrivalTime C α ρ ε := le_max_left _ _
  have hb := h.bound t₀ ht₀ x hx hx₀ t (by linarith)
  exact hb.trans (mul_exp_mul_le_of_arrivalTime_le h.pos_C h.pos_α hε (norm_nonneg _) hx₀.le ht)

/-- **Named constants give exponential stability (MLS Definition 4.3, p. 180).** An exponential
bound on a ball of positive radius is exponential stability in the library's sense
(`ExponentiallyStable`, constants independent of `t₀ ≥ 0`). -/
theorem ExponentialBoundOn.exponentiallyStable {f : ℝ → E → E} {xe : E} {C α ρ : ℝ}
    (h : ExponentialBoundOn f xe C α ρ) (hρ : 0 < ρ) : ExponentiallyStable f xe :=
  ⟨C, h.pos_C, α, h.pos_α, ρ / 2, half_pos hρ, fun t₀ ht₀ x hx hx₀ t ht =>
    h.bound t₀ ht₀ x hx (by linarith) t ht⟩

/-- **Exponential stability names its constants (MLS Definition 4.3, p. 180).** Exponential
stability gives constants `C, α` and a positive radius `ρ` with an exponential bound on the
initial errors smaller than `ρ`. -/
theorem ExponentiallyStable.exists_exponentialBoundOn {f : ℝ → E → E} {xe : E}
    (h : ExponentiallyStable f xe) : ∃ C α ρ, 0 < ρ ∧ ExponentialBoundOn f xe C α ρ := by
  obtain ⟨m, hm, α, hα, ε, hε, h⟩ := h
  exact ⟨m, α, ε, hε, hm, hα, fun t₀ ht₀ x hx hx₀ t ht => h t₀ ht₀ x hx hx₀.le t ht⟩

/-- **Global exponential stability names its constants for every radius (MLS p. 181).** Global
exponential stability gives constants `C, α` with an exponential bound on every ball of initial
errors. -/
theorem GloballyExponentiallyStable.exists_exponentialBoundOn {f : ℝ → E → E} {xe : E}
    (h : GloballyExponentiallyStable f xe) : ∃ C α, ∀ ρ, ExponentialBoundOn f xe C α ρ := by
  obtain ⟨m, hm, α, hα, h⟩ := h
  exact ⟨m, α, fun _ => ⟨hm, hα, fun t₀ ht₀ x hx _ t ht => h t₀ ht₀ x hx t ht⟩⟩

end Stability

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **The augmented PD law at a constant set point is PD with compensation of `N` (MLS eqs.
(4.51) and (4.53), pp. 193–194, and the remark of p. 195).** With `θ_d(t) ≡ θ_d`, `θ̇_d ≡ 0` and
`θ̈_d ≡ 0`, the law `M(θ) θ̈_d + C(θ, θ̇) θ̇_d + N(θ, θ̇) − K_v ė − K_p e` is
`N(θ, θ̇) − K_v θ̇ − K_p (θ − θ_d)`, the library's `pdCompensatedTorque`, at every time and state.
MLS p. 195 says the law "simplifies to the original PD control law (4.51)"; the `N` term remains.
No hypothesis is needed. -/
theorem augmentedPDTorque_const_eq_pdCompensatedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ)
    (θd : Fin n → ℝ) :
    P.augmentedPDTorque Kp Kv (fun _ => θd) (fun _ => 0) (fun _ => 0) =
      P.pdCompensatedTorque Kp Kv θd := by
  funext t q v
  simp [augmentedPDTorque, pdCompensatedTorque]

/-- **PD set-point regulation is exponential on every bounded set of initial errors (MLS
Proposition 4.10, p. 194, specialized to a constant set point as on p. 195; compare Proposition
4.9, p. 193).**
Under the hypotheses of `augmentedPD_tracking` without the trajectory (symmetric link inertias,
`M(q)` positive definite for every `q`, `M` uniformly positive definite and bounded, `C` bounded by
the joint rate, `K_p, K_v` positive definite), there is `C > 0` and, for every `ρ > 0`, a rate
`α > 0` such that for **every** set point `θ_d` the PD law with compensation of `N` has the
exponential bound with constants `(C, α)` at `(θ_d, 0)` on the initial errors smaller than `ρ`
(state `(θ, θ̇)`, sup norm). The constants do not depend on the set point. -/
theorem exponentialBoundOn_pdCompensatedTorque (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMl : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin n → ℝ, |v ⬝ᵥ (P.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ q u v w : Fin n → ℝ, |v ⬝ᵥ (P.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ C > 0, ∀ ρ > 0, ∃ α > 0, ∀ θd : Fin n → ℝ,
      Stability.ExponentialBoundOn (P.field (P.pdCompensatedTorque Kp Kv θd)) (θd, 0) C α ρ := by
  obtain ⟨lam, hlam, hMl⟩ := hMl
  obtain ⟨μ₀, hMb⟩ := hMb
  obtain ⟨δ₀, hCb⟩ := hCb
  set μ := max μ₀ 0 with hμdef
  set δ := max δ₀ 0 with hδdef
  have hμ : 0 ≤ μ := le_max_right _ _
  have hδ : 0 ≤ δ := le_max_right _ _
  have hMb' : ∀ q v w : Fin n → ℝ, |v ⬝ᵥ (P.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := fun q v w =>
    (hMb q v w).trans (by gcongr; exact le_max_left _ _)
  have hCb' : ∀ q u v w : Fin n → ℝ, |v ⬝ᵥ (P.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖ :=
    fun q u v w => (hCb q u v w).trans (by gcongr; exact le_max_left _ _)
  obtain ⟨kp, hkp0, hkp⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKp
  obtain ⟨κp, hκp0, hκpb⟩ := QuadraticBounds.exists_dotProduct_mulVec_le_mul_sq_norm Kp
  obtain ⟨kv, hkv0, hkv⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKv
  obtain ⟨κv, hκv0, hκv⟩ := Control.exists_abs_dotProduct_mulVec_le Kv
  have hmm : 0 < min lam kp := lt_min hlam hkp0
  set ε₀ := min lam kp / (2 * (μ + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀μ : 2 * ε₀ * μ ≤ min lam kp := by
    have e : 2 * ε₀ * μ = min lam kp * (μ / (μ + 1)) := by
      rw [hε₀def]
      field_simp
    have : μ / (μ + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    rw [e]
    nlinarith
  set A := μ + κp + ε₀ * μ + 1 with hAdef
  have hA : 0 < A := by positivity
  set s₁ := Real.sqrt (min lam kp / 4 / A) with hs₁def
  have hs₁ : 0 < s₁ := Real.sqrt_pos.mpr (by positivity)
  have hCpos : 0 < Real.sqrt (A / (min lam kp / 4)) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt (A / (min lam kp / 4)), hCpos, fun ρ hρ => ?_⟩
  set R := ρ / s₁ + ρ with hRdef
  have hR : 0 < R := by positivity
  set c := δ * R with hcdef
  have hc : 0 ≤ c := by positivity
  set D := 2 * kp * μ + (κv + c) ^ 2 with hDdef
  have hD : 0 ≤ D := by positivity
  set ε := min ε₀ (kp * kv / (D + 1)) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεμ : 2 * ε * μ ≤ min lam kp := le_trans (by gcongr) hε₀μ
  have hεc : ε * D ≤ kp * kv := by
    have h1 : ε ≤ kp * kv / (D + 1) := min_le_right _ _
    have h2 : ε * (D + 1) ≤ kp * kv := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  set a₂ := μ + κp + ε * μ + 1 with ha₂def
  have ha₂ : 0 < a₂ := by positivity
  have ha₂A : a₂ ≤ A := by
    have := mul_le_mul_of_nonneg_right hεε₀ hμ
    linarith
  have hαpos : 0 < min (kv / 2) (ε * kp / 2) / (2 * a₂) :=
    div_pos (lt_min (by positivity) (by positivity)) (by positivity)
  refine ⟨min (kv / 2) (ε * kp / 2) / (2 * a₂), hαpos, fun θd => ⟨hCpos, hαpos,
    fun t₀ ht₀ x hx hx₀ t ht => ?_⟩⟩
  have hCu : ∀ t : ℝ, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (P.C (θd + z.1) (0 + z.2) *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖ := by
    intro t _ z hz v₁ v₂
    have h2 : ‖(0 : Fin n → ℝ) + z.2‖ ≤ R := by
      simpa using (norm_snd_le z).trans hz
    calc |v₁ ⬝ᵥ (P.C (θd + z.1) (0 + z.2) *ᵥ v₂)|
        ≤ δ * ‖(0 : Fin n → ℝ) + z.2‖ * ‖v₁‖ * ‖v₂‖ := hCb' _ _ _ _
      _ ≤ δ * R * ‖v₁‖ * ‖v₂‖ := by gcongr
  have hx₀' : ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin n → ℝ)) t₀)‖ <
      min R (R * Real.sqrt (min lam kp / 4 / (μ + κp + ε * μ + 1))) := by
    have hs : s₁ ≤ Real.sqrt (min lam kp / 4 / a₂) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) ha₂ ha₂A)
    have hRs : R * s₁ = ρ + ρ * s₁ := by
      rw [hRdef]
      field_simp
    refine lt_min (by
      have : 0 < ρ / s₁ := by positivity
      linarith) ?_
    calc ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin n → ℝ)) t₀)‖ < ρ := hx₀
      _ < ρ + ρ * s₁ := lt_add_of_pos_right ρ (by positivity)
      _ = R * s₁ := hRs.symm
      _ ≤ R * Real.sqrt (min lam kp / 4 / a₂) := by gcongr
  have hx' : Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv (fun _ => θd)
      (fun _ => 0) (fun _ => 0))) t₀ x := by
    rw [augmentedPDTorque_const_eq_pdCompensatedTorque]
    exact hx
  have key := P.norm_le_augmentedPD_of_bounds h hM hKp.isHermitian.isSymm
    (fun t => hasDerivAt_const t θd) (fun t => hasDerivAt_const t (0 : Fin n → ℝ)) hR hε hlam
    hμ hkp0 hκp0.le hkv0 (fun t _ z _ v => hMl _ v) (fun t _ z _ => hMb' _) hCu hkp
    (fun v => hκpb v) hkv hκv hεμ hεc ht₀ hx' hx₀' ht
  refine key.trans ?_
  gcongr

end ManipulatorModel

end RoboLean
