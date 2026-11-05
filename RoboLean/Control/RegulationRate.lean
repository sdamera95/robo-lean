import RoboLean.Control.ExponentialArrival

/-!
# Exponential regulation from a decay rate of the Lyapunov function on an energy sublevel set

MLS Chapter 4: Theorem 4.5 (printed pp. 183–184), Proposition 4.9 (p. 193) and Proposition 4.10
(p. 194) at a constant set point (p. 195).

**The rate lemma.** MLS Theorem 4.5 bounds `V̇ ≤ −α₃‖x‖²` and obtains the rate `α₃/(2α₂)` of
p. 184. When the derivative is bounded by the function itself, `V̇ ≤ −kV`, on a region that the
solution does not leave, the same argument gives the rate `k/2` and the overshoot `√(a₂/a₁)`
directly (`Stability.norm_le_of_lyapunov_rate_of_mem`); the rate does not lose the factor
`a₁/a₂` that passing through `‖x‖²` costs.

**The invariant region.** Under PD control with compensation of `N` at a constant set point
(the law (4.51) of p. 193 with the `N` term; `ManipulatorModel.pdCompensatedTorque`), the energy
`½ θ̇ᵀ M(θ) θ̇ + ½ eᵀ K_p e` of the proof of Proposition 4.9 does not increase along solutions
when `K_v` is positive semidefinite (`ManipulatorModel.augmentedEnergy_zero_le_of_isSolution`;
the library writes it as the skewed energy `augmentedEnergy` with `ε = 0`). Its sublevel sets are
therefore invariant, and on such a set the cross terms of the skewed energy of Proposition 4.10,
which grow with the state, are bounded.

**The regulation theorem.** If the skewed energy `V = ½ ėᵀMė + ½ eᵀK_pe + ε eᵀMė` satisfies
`a₁‖(e, ė)‖² ≤ V ≤ a₂‖(e, ė)‖²` and `V̇ ≤ −kV` on the energy sublevel set `{energy ≤ E₀}`, and every
initial state error smaller than `ρ` has energy at most `E₀`, then the closed loop has the
exponential bound with constants `C ≥ √(a₂/a₁)` and `α = k/2` on the initial errors smaller than
`ρ` (`ManipulatorModel.exponentialBoundOn_pdCompensatedTorque_of_sublevel`). The hypotheses are
inequalities at single states and carry no statement about solutions.

Conventions: the state is `(θ, θ̇)`, the error `(e, ė) = (θ − θ_d, θ̇)`; norms are Mathlib's sup
norms on `Fin n → ℝ` and on products, as in `Control/Stability`; times are `t ≥ t₀ ≥ 0`. The
ideal continuous model with exact cancellation of `N`; nothing here concerns sampling, numerical
integration, model error or a physical manipulator.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean

namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The rate of MLS Theorem 4.5 (pp. 183–184) from `V̇ ≤ −kV` on a region the solution stays
in.** If on `U` the bounds `a₁‖y‖² ≤ V(t, y) ≤ a₂‖y‖²` and `V̇(t, y) ≤ −k V(t, y)` hold for `t ≥ 0`,
`V̇` is the derivative along the solutions in `U`, and the solution from `t₀ ≥ 0` stays in `U`, then
`‖x(t)‖ ≤ √(a₂/a₁) e^{−(k/2)(t − t₀)} ‖x(t₀)‖` for `t ≥ t₀`. MLS states the decay as
`V̇ ≤ −α₃‖x‖²` with the rate `α₃/(2α₂)` of p. 184; the bound by `V` itself gives the rate `k/2`.
No sign condition on `k` is needed. -/
theorem norm_le_of_lyapunov_rate_of_mem {f : ℝ → E → E} {V Vdot : ℝ → E → ℝ}
    {a₁ a₂ k : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) {U : Set E}
    (hcont : ContinuousOn (fun p : ℝ × E => V p.1 p.2) (Ici 0 ×ˢ univ))
    (hlow : ∀ t, 0 ≤ t → ∀ y ∈ U, a₁ * ‖y‖ ^ 2 ≤ V t y)
    (hup : ∀ t, 0 ≤ t → ∀ y ∈ U, V t y ≤ a₂ * ‖y‖ ^ 2)
    (hVdot : HasDerivAlongSolutions f V Vdot U)
    (hdec : ∀ t, 0 ≤ t → ∀ y ∈ U, Vdot t y ≤ -(k * V t y))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : IsSolution f t₀ x) (hin : ∀ s, t₀ ≤ s → x s ∈ U)
    {t : ℝ} (ht : t₀ ≤ t) :
    ‖x t‖ ≤ Real.sqrt (a₂ / a₁) * Real.exp (-(k / 2) * (t - t₀)) * ‖x t₀‖ := by
  set g : ℝ → ℝ := fun s => Real.exp (k * (s - t₀)) * V s (x s) with hg
  have hgc : ContinuousOn g (Ici t₀) := by
    have h1 : ContinuousOn (fun s => (s, x s)) (Ici t₀) := continuousOn_id.prodMk hx.1
    have h2 : ContinuousOn (fun s => V s (x s)) (Ici t₀) :=
      hcont.comp h1 fun s hs => ⟨ht₀.trans hs, mem_univ _⟩
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const))).continuousOn.mul h2
  have hanti : AntitoneOn g (Ici t₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀) hgc
      (f' := fun s => k * Real.exp (k * (s - t₀)) * V s (x s) +
        Real.exp (k * (s - t₀)) * Vdot s (x s)) ?_ ?_
    · intro s hs
      rw [interior_Ici] at hs
      have he : HasDerivAt (fun s => Real.exp (k * (s - t₀))) (Real.exp (k * (s - t₀)) * k) s := by
        have := ((hasDerivAt_id s).sub_const t₀).const_mul k
        simpa using this.exp
      have hv := hVdot t₀ ht₀ x hx s hs (hin s (le_of_lt hs))
      refine HasDerivAt.hasDerivWithinAt ?_
      convert he.mul hv using 1
      ring_nf
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : 0 ≤ s := ht₀.trans (le_of_lt hs)
      have h2 := hdec s hs0 (x s) (hin s (le_of_lt hs))
      have hepos := Real.exp_pos (k * (s - t₀))
      have e : k * Real.exp (k * (s - t₀)) * V s (x s) + Real.exp (k * (s - t₀)) * Vdot s (x s) =
          Real.exp (k * (s - t₀)) * (k * V s (x s) + Vdot s (x s)) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos hepos.le (by linarith)
  have hgt : g t ≤ g t₀ := hanti self_mem_Ici ht ht
  have hg0 : g t₀ = V t₀ (x t₀) := by simp [hg]
  have hVt : V t (x t) ≤ Real.exp (-(k * (t - t₀))) * (a₂ * ‖x t₀‖ ^ 2) := by
    have h1 : Real.exp (k * (t - t₀)) * V t (x t) ≤ a₂ * ‖x t₀‖ ^ 2 := by
      have := hup t₀ ht₀ (x t₀) (hin t₀ le_rfl)
      rw [hg0] at hgt
      exact hgt.trans this
    have h2 : V t (x t) = Real.exp (-(k * (t - t₀))) * (Real.exp (k * (t - t₀)) * V t (x t)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hsq : ‖x t‖ ^ 2 ≤
      (Real.sqrt (a₂ / a₁) * Real.exp (-(k / 2) * (t - t₀)) * ‖x t₀‖) ^ 2 := by
    have h1 : a₁ * ‖x t‖ ^ 2 ≤ Real.exp (-(k * (t - t₀))) * (a₂ * ‖x t₀‖ ^ 2) :=
      (hlow t (ht₀.trans ht) (x t) (hin t ht)).trans hVt
    have h2 : (Real.sqrt (a₂ / a₁) * Real.exp (-(k / 2) * (t - t₀)) * ‖x t₀‖) ^ 2 =
        a₂ / a₁ * Real.exp (-(k * (t - t₀))) * ‖x t₀‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos ha₂ ha₁).le, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring_nf
    rw [h2]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha₁]
    nlinarith
  have hnn : 0 ≤ Real.sqrt (a₂ / a₁) * Real.exp (-(k / 2) * (t - t₀)) * ‖x t₀‖ := by
    positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp hsq

/-- **An exponential bound on a ball holds on every smaller ball (MLS Definition 4.3, p. 180).**
The constants `(C, α)` of an exponential bound on the initial errors smaller than `ρ` serve for
the initial errors smaller than any `ρ' ≤ ρ`. -/
theorem ExponentialBoundOn.mono_radius {f : ℝ → E → E} {xe : E} {C α ρ ρ' : ℝ}
    (h : ExponentialBoundOn f xe C α ρ) (hρ : ρ' ≤ ρ) : ExponentialBoundOn f xe C α ρ' :=
  ⟨h.pos_C, h.pos_α, fun t₀ ht₀ x hx hx₀ t ht => h.bound t₀ ht₀ x hx (hx₀.trans_le hρ) t ht⟩

end Stability

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **The energy of the proof of MLS Proposition 4.9 (p. 193) does not increase.** With symmetric
link inertias, `M(q)` positive definite for every `q`, `K_p` symmetric and `ėᵀK_vė ≥ 0` for every
`ė`, along every solution of the closed loop under PD control with compensation of `N` at the
constant set point `θ_d` from `t₀ ≥ 0`, the energy `½ θ̇ᵀ M(θ) θ̇ + ½ eᵀ K_p e`, `e = θ − θ_d`
(`augmentedEnergy` with `ε = 0`), at a time `t ≥ t₀` is at most its value at `t₀`. -/
theorem augmentedEnergy_zero_le_of_isSolution (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm)
    (hKv : ∀ w, 0 ≤ w ⬝ᵥ (Kv *ᵥ w)) (θd : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : Stability.IsSolution (P.field (P.pdCompensatedTorque Kp Kv θd)) t₀ x) {t : ℝ}
    (ht : t₀ ≤ t) :
    P.augmentedEnergy Kp 0 (x t).1 ((x t).1 - θd) (x t).2 ≤
      P.augmentedEnergy Kp 0 (x t₀).1 ((x t₀).1 - θd) (x t₀).2 := by
  have hx' : Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv (fun _ => θd)
      (fun _ => 0) (fun _ => 0))) t₀ x := by
    rw [augmentedPDTorque_const_eq_pdCompensatedTorque]
    exact hx
  have hd : ∀ s, HasDerivAt (fun _ : ℝ => θd) ((fun _ : ℝ => (0 : Fin n → ℝ)) s) s :=
    fun s => hasDerivAt_const s θd
  have hd' : ∀ s, HasDerivAt (fun _ : ℝ => (0 : Fin n → ℝ)) ((fun _ : ℝ => (0 : Fin n → ℝ)) s) s :=
    fun s => hasDerivAt_const s 0
  have hxd : ∀ s, HasDerivAt (fun s => ((fun _ : ℝ => θd) s, (fun _ : ℝ => (0 : Fin n → ℝ)) s))
      ((fun _ : ℝ => (0 : Fin n → ℝ)) s, (fun _ : ℝ => (0 : Fin n → ℝ)) s) s :=
    fun s => (hd s).prodMk (hd' s)
  have hz := (Stability.isSolution_errorSystem_iff hxd (f := P.field
    (P.augmentedPDTorque Kp Kv (fun _ => θd) (fun _ => 0) (fun _ => 0)))).mpr hx'
  have hVd := P.hasDerivAlongSolutions_augmentedEnergy h hM (Kv := Kv) hKp 0 hd hd'
  have hneg : ∀ s, 0 ≤ s → ∀ y ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))),
      P.augmentedEnergyRate Kp Kv 0 ((fun _ : ℝ => θd) s + y.1)
        ((fun _ : ℝ => (0 : Fin n → ℝ)) s + y.2) y.1 y.2 ≤ 0 := by
    intro s _ y _
    have := hKv y.2
    simp only [augmentedEnergyRate, zero_mul, add_zero, sub_zero]
    linarith
  have hanti := Stability.antitoneOn_of_isSolution
    (P.continuous_augmentedEnergy_comp Kp 0 (θd := fun _ => θd) continuous_const).continuousOn
    hVd hneg ht₀ hz (convex_Ici t₀) subset_rfl (fun s hs => by
      rw [interior_Ici] at hs
      exact ⟨hs, mem_univ _⟩)
  have key := hanti self_mem_Ici ht ht
  simpa using key

/-- **Exponential set-point regulation with constants from a decay rate on an energy sublevel set
(MLS Proposition 4.10, p. 194, at a constant set point as on p. 195; Theorem 4.5, pp. 183–184;
Definition 4.3, p. 180).** Hypotheses: symmetric link inertias; `M(q)` positive definite for every
`q`; `K_p` symmetric; `ėᵀK_vė ≥ 0`; constants `a₁, a₂, k, C > 0` with `a₂ ≤ C² a₁`; a level `E₀`
such that every error `(e, ė)` with `‖(e, ė)‖ < ρ` has energy `½ ėᵀM(θ_d + e)ė + ½ eᵀK_pe ≤ E₀`;
and on the sublevel set `{energy ≤ E₀}` the skewed energy
`V = ½ ėᵀMė + ½ eᵀK_pe + ε eᵀMė` (`augmentedEnergy`) satisfies `a₁‖(e, ė)‖² ≤ V ≤ a₂‖(e, ė)‖²` and
its derivative along the closed loop (`augmentedEnergyRate` at the joint rate `θ̇ = ė`) satisfies
`V̇ ≤ −kV`. Then the closed loop under PD control with compensation of `N` at `θ_d` has the
exponential bound with constants `C` and `α = k/2` at `(θ_d, 0)` on the initial errors smaller than
`ρ` (sup norm on the state `(θ, θ̇)`). The sublevel set is invariant by
`augmentedEnergy_zero_le_of_isSolution`; MLS argues with `ε` small and states no constants. -/
theorem exponentialBoundOn_pdCompensatedTorque_of_sublevel
    (h : ∀ k, (P.chain.linkInertia k).IsSymm) (hM : ∀ q, (P.M q).PosDef)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm) (hKv : ∀ w, 0 ≤ w ⬝ᵥ (Kv *ᵥ w))
    (θd : Fin n → ℝ) {ε k a₁ a₂ E₀ ρ C : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hk : 0 < k)
    (hC : 0 < C) (hCa : a₂ ≤ C ^ 2 * a₁)
    (hE₀ : ∀ e w : Fin n → ℝ, ‖(e, w)‖ < ρ → P.augmentedEnergy Kp 0 (θd + e) e w ≤ E₀)
    (hlow : ∀ e w : Fin n → ℝ, P.augmentedEnergy Kp 0 (θd + e) e w ≤ E₀ →
      a₁ * ‖(e, w)‖ ^ 2 ≤ P.augmentedEnergy Kp ε (θd + e) e w)
    (hup : ∀ e w : Fin n → ℝ, P.augmentedEnergy Kp 0 (θd + e) e w ≤ E₀ →
      P.augmentedEnergy Kp ε (θd + e) e w ≤ a₂ * ‖(e, w)‖ ^ 2)
    (hdec : ∀ e w : Fin n → ℝ, P.augmentedEnergy Kp 0 (θd + e) e w ≤ E₀ →
      P.augmentedEnergyRate Kp Kv ε (θd + e) w e w ≤
        -(k * P.augmentedEnergy Kp ε (θd + e) e w)) :
    Stability.ExponentialBoundOn (P.field (P.pdCompensatedTorque Kp Kv θd)) (θd, 0) C (k / 2)
      ρ := by
  have hα : 0 < k / 2 := by positivity
  refine ⟨hC, hα, fun t₀ ht₀ x hx hx₀ t ht => ?_⟩
  have hx' : Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv (fun _ => θd)
      (fun _ => 0) (fun _ => 0))) t₀ x := by
    rw [augmentedPDTorque_const_eq_pdCompensatedTorque]
    exact hx
  have hd : ∀ s, HasDerivAt (fun _ : ℝ => θd) ((fun _ : ℝ => (0 : Fin n → ℝ)) s) s :=
    fun s => hasDerivAt_const s θd
  have hd' : ∀ s, HasDerivAt (fun _ : ℝ => (0 : Fin n → ℝ)) ((fun _ : ℝ => (0 : Fin n → ℝ)) s) s :=
    fun s => hasDerivAt_const s 0
  have hxd : ∀ s, HasDerivAt (fun s => ((fun _ : ℝ => θd) s, (fun _ : ℝ => (0 : Fin n → ℝ)) s))
      ((fun _ : ℝ => (0 : Fin n → ℝ)) s, (fun _ : ℝ => (0 : Fin n → ℝ)) s) s :=
    fun s => (hd s).prodMk (hd' s)
  have hz := (Stability.isSolution_errorSystem_iff hxd (f := P.field
    (P.augmentedPDTorque Kp Kv (fun _ => θd) (fun _ => 0) (fun _ => 0)))).mpr hx'
  have hin : ∀ s, t₀ ≤ s → x s - ((fun _ : ℝ => θd) s, (fun _ : ℝ => (0 : Fin n → ℝ)) s) ∈
      {y : (Fin n → ℝ) × (Fin n → ℝ) | P.augmentedEnergy Kp 0 (θd + y.1) y.1 y.2 ≤ E₀} := by
    intro s hs
    have h1 := P.augmentedEnergy_zero_le_of_isSolution h hM hKp hKv θd ht₀ hx hs
    have h2 := hE₀ ((x t₀).1 - θd) (x t₀).2 (by
      have e : (((x t₀).1 - θd, (x t₀).2) : (Fin n → ℝ) × (Fin n → ℝ)) = x t₀ - (θd, 0) := by
        ext <;> simp
      rw [e]
      exact hx₀)
    rw [add_sub_cancel] at h2
    show P.augmentedEnergy Kp 0 (θd + ((x s).1 - θd)) ((x s).1 - θd) ((x s).2 - 0) ≤ E₀
    rw [add_sub_cancel, sub_zero]
    exact h1.trans h2
  have key := Stability.norm_le_of_lyapunov_rate_of_mem
    (E := (Fin n → ℝ) × (Fin n → ℝ))
    (V := fun (t : ℝ) (y : (Fin n → ℝ) × (Fin n → ℝ)) =>
      P.augmentedEnergy Kp ε ((fun _ : ℝ => θd) t + y.1) y.1 y.2)
    (Vdot := fun (t : ℝ) (y : (Fin n → ℝ) × (Fin n → ℝ)) =>
      P.augmentedEnergyRate Kp Kv ε ((fun _ : ℝ => θd) t + y.1)
      ((fun _ : ℝ => (0 : Fin n → ℝ)) t + y.2) y.1 y.2)
    ha₁ ha₂
    (U := {y : (Fin n → ℝ) × (Fin n → ℝ) | P.augmentedEnergy Kp 0 (θd + y.1) y.1 y.2 ≤ E₀})
    (P.continuous_augmentedEnergy_comp Kp ε (θd := fun _ => θd) continuous_const).continuousOn
    (fun t _ y hy => by
      have := hlow y.1 y.2 hy
      rwa [Prod.mk.eta] at this)
    (fun t _ y hy => by
      have := hup y.1 y.2 hy
      rwa [Prod.mk.eta] at this)
    ((P.hasDerivAlongSolutions_augmentedEnergy h hM (Kv := Kv) hKp ε hd hd').mono (subset_univ _))
    (fun t _ y hy => by
      have := hdec y.1 y.2 hy
      show P.augmentedEnergyRate Kp Kv ε (θd + y.1) (0 + y.2) y.1 y.2 ≤
        -(k * P.augmentedEnergy Kp ε (θd + y.1) y.1 y.2)
      rw [zero_add]
      exact this) ht₀ hz hin ht
  have hCs : Real.sqrt (a₂ / a₁) ≤ C := by
    rw [Real.sqrt_le_iff]
    refine ⟨hC.le, ?_⟩
    rw [div_le_iff₀ ha₁]
    linarith
  refine key.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCs (Real.exp_pos _).le)
    (norm_nonneg _)

end ManipulatorModel

end RoboLean
