import RoboLean.Control.ErrorDynamics

/-!
# Computed torque control (MLS §5.2, eqs. (4.48)–(4.50), Proposition 4.8, pp. 190–192)

**What MLS prints.** For (4.47) and a desired trajectory `θ_d` that is "at
least twice differentiable" (p. 190), the computed torque law is (4.49), p. 191,
`τ = M(θ)(θ̈_d − K_v ė − K_p e) + C(θ, θ̇) θ̇ + N(θ, θ̇)` with `e = θ − θ_d` and constant gain
matrices. Substituting gives `M(θ)(ë + K_v ė + K_p e) = 0`, and "since `M(θ)` is always positive
definite" the error equation (4.50) `ë + K_v ė + K_p e = 0`. Proposition 4.8, p. 192: "If
`K_p, K_v ∈ ℝⁿˣⁿ` are positive definite, symmetric matrices, then the control law (4.49) applied to
the system (4.47) results in exponential trajectory tracking." The printed proof shows that the
eigenvalues of `A = [[0, I], [−K_p, −K_v]]` have negative real part.

**Formalized.**

* the algebraic closed loop at one time (`equationsOfMotionAt_computedTorque_iff`): with
  symmetric link inertias and `M(θ(t))` positive definite, the equations of motion hold under
  (4.49) at `t` exactly when (4.50) holds at `t`;
* the state-space form (`isSolution_errorField`): every solution of the closed-loop first-order
  system gives an error `(e, ė)` that solves the linear system `d/dt (e, ė) = A (e, ė)` of p. 192;
* **exponential trajectory tracking** (`computedTorque_tracking`): there are `m, α > 0`,
  depending only on `K_p` and `K_v`, such that every closed-loop solution from `t₀ ≥ 0` has
  `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀`; the same for motions satisfying
  Lagrange's equations (`computedTorque_tracking_of_equationsOfMotionAt`).

The route differs from the printed proof: global exponential stability of the error system is
proved with the skewed energy of Example 4.5 (p. 186) and Theorem 4.5 (`ErrorDynamics`), not from
the eigenvalues. `M(q)` positive definite for every `q` is a hypothesis (MLS asserts it, Lemma
4.2(1)). The tracking bound uses the sup norm on `ℝⁿ × ℝⁿ`. Exact cancellation of the model is
assumed, as in MLS; nothing here concerns model error, actuator limits or sampling.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **MLS eq. (4.49), p. 191: the computed torque control law**
`τ = M(θ)(θ̈_d − K_v ė − K_p e) + C(θ, θ̇) θ̇ + N(θ, θ̇)`, `e = θ − θ_d`, for a desired trajectory
`θ_d` with velocity `θ_d'` and acceleration `θ_d''`, as a feedback law `u(t, θ, θ̇)`. -/
def computedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd θd' θd'' : ℝ → Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun t q v => P.M q *ᵥ (θd'' t - Kv *ᵥ (v - θd' t) - Kp *ᵥ (q - θd t)) + P.C q v *ᵥ v + P.N q v

/-- **MLS eqs. (4.49)–(4.50), p. 191: the computed-torque error equation.** With symmetric link
inertias and `M(θ(t))` positive definite, along a motion whose velocity `θ'` near `t` and
acceleration `θ''` at `t` are actual derivatives, the equations of motion (4.47) hold at `t` under
the computed torque law (4.49) exactly when `ë + K_v ė + K_p e = 0` at `t`, with
`e = θ − θ_d`, `ė = θ' − θ_d'`, `ë = θ'' − θ_d''`. No hypothesis on the gains is needed here. -/
theorem equationsOfMotionAt_computedTorque_iff (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd θd' θd'' : ℝ → Fin n → ℝ)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hM : (P.M (θ t)).PosDef)
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) :
    P.EquationsOfMotionAt θ (P.computedTorque Kp Kv θd θd' θd'' t (θ t) (θ' t)) t ↔
      (θ'' - θd'' t) + Kv *ᵥ (θ' t - θd' t) + Kp *ᵥ (θ t - θd t) = 0 := by
  rw [P.equationsOfMotionAt_iff h hθ hθ', computedTorque, add_left_inj, add_left_inj]
  set w := θd'' t - Kv *ᵥ (θ' t - θd' t) - Kp *ᵥ (θ t - θd t)
  have herr : (θ'' - θd'' t) + Kv *ᵥ (θ' t - θd' t) + Kp *ᵥ (θ t - θd t) = θ'' - w := by
    simp only [w]
    abel
  rw [herr, sub_eq_zero]
  constructor
  · intro hMw
    rw [← Control.PosDef.inv_mulVec_mulVec hM θ'', hMw, Control.PosDef.inv_mulVec_mulVec hM]
  · intro hw
    rw [hw]

/-- **MLS p. 192 (proof of Proposition 4.8): the closed-loop error solves the linear error
system.** With `M(q)` positive definite for every `q`, and a desired trajectory with actual
derivatives `θ_d' = θ̇_d`, `θ_d'' = θ̈_d` at every time, every solution `x = (θ, θ̇)` from `t₀` of
the system (4.47) under the computed torque law (4.49) gives an error
`(e, ė) = (θ − θ_d, θ̇ − θ̇_d)` that solves `d/dt (e, ė) = (ė, −K_v ė − K_p e)` from `t₀`. -/
theorem isSolution_errorField (hM : ∀ q, (P.M q).PosDef) (Kp Kv : Matrix (Fin n) (Fin n) ℝ)
    {θd θd' θd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt θd (θd' t) t)
    (hd' : ∀ t, HasDerivAt θd' (θd'' t) t) {t₀ : ℝ} {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : Stability.IsSolution (P.field (P.computedTorque Kp Kv θd θd' θd'')) t₀ x) :
    Stability.IsSolution (Control.errorField Kp Kv) t₀
      (fun t => ((x t).1 - θd t, (x t).2 - θd' t)) := by
  have hdc : Continuous θd := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hdc' : Continuous θd' := continuous_iff_continuousAt.mpr fun t => (hd' t).continuousAt
  refine ⟨((continuous_fst.comp_continuousOn hx.1).sub hdc.continuousOn).prodMk
    ((continuous_snd.comp_continuousOn hx.1).sub hdc'.continuousOn), fun t ht => ?_⟩
  have hf : HasDerivAt (fun s => (x s).1)
      (P.field (P.computedTorque Kp Kv θd θd' θd'') t (x t)).1 t := (hx.2 t ht).fst
  have hs : HasDerivAt (fun s => (x s).2)
      (P.field (P.computedTorque Kp Kv θd θd' θd'') t (x t)).2 t := (hx.2 t ht).snd
  have h1 := hf.sub (hd t)
  have h2 := hs.sub (hd' t)
  have hacc : (P.field (P.computedTorque Kp Kv θd θd' θd'') t (x t)).2 =
      θd'' t - Kv *ᵥ ((x t).2 - θd' t) - Kp *ᵥ ((x t).1 - θd t) := by
    simp only [field, computedTorque]
    rw [show P.M (x t).1 *ᵥ (θd'' t - Kv *ᵥ ((x t).2 - θd' t) - Kp *ᵥ ((x t).1 - θd t)) +
        P.C (x t).1 (x t).2 *ᵥ (x t).2 + P.N (x t).1 (x t).2 - P.C (x t).1 (x t).2 *ᵥ (x t).2 -
          P.N (x t).1 (x t).2 =
        P.M (x t).1 *ᵥ (θd'' t - Kv *ᵥ ((x t).2 - θd' t) - Kp *ᵥ ((x t).1 - θd t)) by abel,
      Control.PosDef.inv_mulVec_mulVec (hM _)]
  rw [hacc] at h2
  convert h1.prodMk h2 using 1
  simp only [Control.errorField, field, Prod.mk.injEq, true_and]
  abel

/-- **MLS Proposition 4.8, p. 192: computed torque gives exponential trajectory tracking.** With
`M(q)` positive definite for every `q`, `K_p` and `K_v` symmetric positive definite, and a desired
trajectory with actual derivatives `θ_d' = θ̇_d`, `θ_d'' = θ̈_d` at every time, there are constants
`m, α > 0`, depending only on `K_p` and `K_v`, such that every solution `x = (θ, θ̇)` from `t₀ ≥ 0`
of (4.47) under (4.49) satisfies, for `t ≥ t₀`,
`‖(θ(t) − θ_d(t), θ̇(t) − θ̇_d(t))‖ ≤ m e^{−α(t − t₀)} ‖(θ(t₀) − θ_d(t₀), θ̇(t₀) − θ̇_d(t₀))‖`. -/
theorem computedTorque_tracking (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ}
    (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {θd θd' θd'' : ℝ → Fin n → ℝ}, (∀ t, HasDerivAt θd (θd' t) t) →
      (∀ t, HasDerivAt θd' (θd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.computedTorque Kp Kv θd θd' θd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, hexp⟩ := Control.globallyExponentiallyStable_errorField hKp hKv
  refine ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x hx t ht => ?_⟩
  simpa using hexp t₀ ht₀ _ (P.isSolution_errorField hM Kp Kv hd hd' hx) t ht

/-- **MLS Proposition 4.8, p. 192, for motions satisfying Lagrange's equations.** With symmetric
link inertias, `M(q)` positive definite for every `q` and `K_p`, `K_v` symmetric positive
definite, there are `m, α > 0` such that for every desired trajectory as in
`computedTorque_tracking` and every motion `θ` with velocity `θ'` and acceleration `θ''` at every
`t > t₀ ≥ 0`, `(θ, θ')` continuous on `[t₀, ∞)`, satisfying (4.47) under the computed torque law
(4.49) at every `t > t₀`, the tracking error obeys the exponential bound for `t ≥ t₀`. -/
theorem computedTorque_tracking_of_equationsOfMotionAt (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef)
    (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {θd θd' θd'' : ℝ → Fin n → ℝ}, (∀ t, HasDerivAt θd (θd' t) t) →
      (∀ t, HasDerivAt θd' (θd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ θ θ' θ'' : ℝ → Fin n → ℝ,
      ContinuousOn (fun s => (θ s, θ' s)) (Ici t₀) → (∀ s, t₀ < s → HasDerivAt θ (θ' s) s) →
      (∀ s, t₀ < s → HasDerivAt θ' (θ'' s) s) →
      (∀ s, t₀ < s →
        P.EquationsOfMotionAt θ (P.computedTorque Kp Kv θd θd' θd'' s (θ s) (θ' s)) s) →
      ∀ t, t₀ ≤ t → ‖(θ t - θd t, θ' t - θd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(θ t₀ - θd t₀, θ' t₀ - θd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := P.computedTorque_tracking hM hKp hKv
  refine ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ θ θ' θ'' hc hθ hθ' hE t ht => ?_⟩
  exact htrack hd hd' t₀ ht₀ _ (P.isSolution_of_equationsOfMotionAt h hM hc hθ hθ' hE) t ht

end ManipulatorModel
end RoboLean
