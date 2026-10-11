import RoboLean.Control.PDAsymptotic
import RoboLean.Control.LyapunovFlow

/-!
# The solution flow of the PD closed loop (MLS (4.52), p. 193; standing assumption, p. 179)

E019 proved asymptotic stability of PD set-point control with compensation of `N`
(`ManipulatorModel.globallyAsymptoticallyStableAt_pdCompensatedTorque`, MLS Proposition 4.9 as
formalized) under a solution-flow hypothesis `Stability.HasFlow` for the closed loop (4.52), and
constructed the flow only for constant inertia. This module supplies the a-priori bound that the
flow construction for a nonlinear closed loop needs: the energy
`V = ½ θ̇ᵀ M(θ) θ̇ + ½ eᵀ K_p e` of the proof of Proposition 4.9 (p. 193) does not increase along
any solution of (4.52) on any interval `[0, T]`, in the `HasDerivWithinAt … (Icc 0 T)` form that
Mathlib's Picard–Lindelöf theorem produces (`pdEnergy_le_of_hasDerivWithinAt`). With
`Stability.exists_hasFlow_of_lyapunov` (`LyapunovFlow`) this gives the flow of (4.52) whenever the
closed loop is locally Lipschitz and `M` is uniformly positive definite
(`exists_hasFlow_pdClosedLoop`), and hence Proposition 4.9 as formalized with the flow hypothesis
replaced by local Lipschitz continuity of the closed loop
(`globallyAsymptoticallyStableAt_pdCompensatedTorque_of_locallyLipschitz`). Local Lipschitz
continuity needs second-order regularity of `M` (the closed loop contains `C`, built from the
first derivatives of `M`), which the library does not prove for a general chain; it is discharged
for the planar two-link arm in `RoboLean.Examples.PlanarTwoLinkControl`.

Conventions: the state is `(θ, θ̇) ∈ ℝⁿ × ℝⁿ` with the sup norm; gains are Mathlib's `PosDef`
(symmetric) or `PosSemidef`; symmetric link inertias and `M(q)` positive definite for every `q`
are hypotheses, as in `PDControl`.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **The equations of motion along a solution of the closed loop on an open time interval (MLS
(4.31), (4.47)).** With symmetric link inertias and `M(q)` positive definite for every `q`, if the
curve `γ` has the actual derivative `f(γ(s))` at every `s` of a neighbourhood of `t`, where `f` is
the closed loop of a time-invariant feedback law `u`, then `θ = γ.1` satisfies (4.47) at `t` with
`τ = u(θ(t), θ̇(t))`. -/
theorem equationsOfMotionAt_of_eventually_hasDerivAt (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ} {t : ℝ}
    {γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hγ : ∀ᶠ s in 𝓝 t, HasDerivAt γ (P.field u t (γ s)) s) :
    P.EquationsOfMotionAt (fun s => (γ s).1) (u t (γ t).1 (γ t).2) t := by
  have hθ : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => (γ s).1) (γ s).2 s := by
    filter_upwards [hγ] with s hs
    exact hs.fst
  rw [P.equationsOfMotionAt_iff h hθ hγ.self_of_nhds.snd]
  simp only [field]
  rw [Control.PosDef.mulVec_inv_mulVec (hM _)]
  abel

/-- **The energy does not increase along the closed loop (4.52) on an interval (MLS p. 193:
`V̇ = −θ̇ᵀ K_v θ̇ ≤ 0`).** With symmetric link inertias, `M(q)` positive definite for every `q`,
`K_p` symmetric and `K_v` positive semidefinite, every solution `γ` of `pdClosedLoop` on
`[0, T]` (in the form `HasDerivWithinAt γ (f (γ s)) (Icc 0 T) s` for `s ∈ [0, T]`) satisfies
`V(γ(s)) ≤ V(γ(0))` for `s ∈ [0, T]`, with `V = ½ θ̇ᵀ M(θ) θ̇ + ½ eᵀ K_p e`. -/
theorem pdEnergy_le_of_hasDerivWithinAt (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm)
    (hKv : Kv.PosSemidef) (θd : Fin n → ℝ) {T : ℝ} {γ : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hγ : ∀ s ∈ Icc 0 T, HasDerivWithinAt γ (P.pdClosedLoop Kp Kv θd (γ s)) (Icc 0 T) s) :
    ∀ s ∈ Icc 0 T, P.pdEnergy Kp θd (γ s).1 (γ s).2 ≤ P.pdEnergy Kp θd (γ 0).1 (γ 0).2 := by
  intro s hs
  have hcont : ContinuousOn γ (Icc 0 T) := fun r hr => (hγ r hr).continuousWithinAt
  have hint : ∀ r ∈ Ioo 0 T, HasDerivAt γ (P.pdClosedLoop Kp Kv θd (γ r)) r := fun r hr =>
    (hγ r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hanti : AntitoneOn (fun r => P.pdEnergy Kp θd (γ r).1 (γ r).2) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      ((P.continuous_pdEnergy Kp θd).comp_continuousOn hcont)
      (f' := fun r => -((γ r).2 ⬝ᵥ (Kv *ᵥ (γ r).2))) (fun r hr => ?_) (fun r _ => ?_)
    · rw [interior_Icc] at hr
      have hev : ∀ᶠ r' in 𝓝 r, HasDerivAt γ
          (P.field (P.pdCompensatedTorque Kp Kv θd) r (γ r')) r' := by
        filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
        exact hint r' hr'
      have hE := P.equationsOfMotionAt_of_eventually_hasDerivAt h hM hev
      have hθ : ∀ᶠ r' in 𝓝 r, HasDerivAt (fun s => (γ s).1) (γ r').2 r' := by
        filter_upwards [hev] with r' hr'
        exact hr'.fst
      exact (P.hasDerivAt_pdEnergy h hKp θd hθ hev.self_of_nhds.snd hE).hasDerivWithinAt
    · have := hKv.dotProduct_mulVec_nonneg (γ r).2
      simp only [star_trivial] at this
      linarith
  exact hanti ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1

/-- **The closed loop (4.52) has a solution flow (MLS p. 179's standing assumption, discharged
here for the PD closed loop of p. 193)** when it is locally Lipschitz: with symmetric link
inertias, `M(q)` positive definite for every `q` and uniformly positive definite
(`λ‖v‖² ≤ vᵀ M(q) v`), `K_p` positive definite and `K_v` positive semidefinite, a locally
Lipschitz closed loop `pdClosedLoop` has a flow `φ` (`Stability.HasFlow`), constructed from
Mathlib's local Picard–Lindelöf solutions with the energy `V = ½ θ̇ᵀMθ̇ + ½ eᵀK_pe` as a trapping
Lyapunov function (`Stability.exists_hasFlow_of_lyapunov`). -/
theorem exists_hasFlow_pdClosedLoop (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosSemidef) (θd : Fin n → ℝ)
    (hF : LocallyLipschitz (P.pdClosedLoop Kp Kv θd)) :
    ∃ φ, Stability.HasFlow (P.pdClosedLoop Kp Kv θd) φ :=
  Stability.exists_hasFlow_of_lyapunov hF (P.continuous_pdEnergy Kp θd)
    (fun c => P.isCompact_pdEnergy_sublevel hMu hKp θd c)
    (fun _ _ _ hγ => P.pdEnergy_le_of_hasDerivWithinAt h hM hKp.isHermitian.isSymm hKv θd hγ)

/-- **MLS Proposition 4.9 (p. 193) as formalized, with the flow hypothesis replaced by local
Lipschitz continuity of the closed loop.** With symmetric link inertias, `M(q)` positive definite
for every `q` and uniformly positive definite, `K_p`, `K_v` positive definite and the closed loop
(4.52) locally Lipschitz, PD control with compensation of `N` makes `(θ_d, 0)` globally
asymptotically stable at every `t₀ ≥ 0` (state `(θ, θ̇)`, sup norm). -/
theorem globallyAsymptoticallyStableAt_pdCompensatedTorque_of_locallyLipschitz
    (h : ∀ k, (P.chain.linkInertia k).IsSymm) (hM : ∀ q, (P.M q).PosDef)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {θd : Fin n → ℝ}
    (hF : LocallyLipschitz (P.pdClosedLoop Kp Kv θd)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt (P.field (P.pdCompensatedTorque Kp Kv θd))
      (θd, 0) t₀ := by
  obtain ⟨φ, hφ⟩ := P.exists_hasFlow_pdClosedLoop h hM hMu hKp hKv.posSemidef θd hF
  exact P.globallyAsymptoticallyStableAt_pdCompensatedTorque h hM hMu hKp hKv hφ ht₀

end ManipulatorModel
end RoboLean
