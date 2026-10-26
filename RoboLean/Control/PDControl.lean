import RoboLean.Control.ManipulatorSystem
import RoboLean.Control.QuadraticBounds
import RoboLean.Control.RobotPDControl

/-!
# PD set-point control of a manipulator (MLS §5.3, Proposition 4.9, pp. 193–195)

**What MLS prints (pp. 193–195).** The PD law (4.51) is `τ = −K_v ė − K_p e`
with `e = θ − θ_d`. Proposition 4.9 (p. 193): "If `θ̇_d ≡ 0` and `K_v, K_p > 0`, the control law
(4.51) applied to the system (4.47) renders the equilibrium point `θ = θ_d` globally
asymptotically stable." The proof writes the closed loop as (4.52),
`M(θ) θ̈ + C(θ, θ̇) θ̇ + K_v θ̇ + K_p (θ − θ_d) = 0`, which has no `N` term although (4.47) has
`N(θ, θ̇)`; it takes `V = ½ θ̇ᵀ M θ̇ + ½ θᵀ K_p θ` (with `θ_d = 0`), gets `V̇ = −θ̇ᵀ K_v θ̇` from
the skew symmetry of `Ṁ − 2C`, and concludes asymptotic stability by Lasalle's principle (p. 194).
On p. 195, after the augmented law (4.53) `τ = M θ̈_d + C θ̇_d + N − K_v ė − K_p e`, MLS says that
for `θ̇_d ≡ 0` "the control law (4.53) simplifies to the original PD control law (4.51)"; with
`θ̇_d ≡ 0` it is `τ = N(θ, θ̇) − K_v θ̇ − K_p e`, which is (4.51) only when `N = 0`.

**Resolution (proved here).** For the system (4.47) with a nonzero `N`:

* under the bare law (4.51), `(θ_d, 0)` is an equilibrium of the closed loop exactly when
  `N(θ_d, 0) = 0` (`isEquilibrium_pdTorque_iff`), and the constant motion `θ ≡ θ_d` satisfies the
  equations of motion exactly then (`equationsOfMotionAt_const_pdTorque_iff`). An instance with
  `N(θ_d, 0) ≠ 0` is the gravity term of MLS Example 4.3 at `θ = 0`
  (`RoboLean.Examples.threeLinkArm_not_equilibrium_pd`). So the printed statement holds as written
  only for `N(θ_d, 0) = 0`, in particular in a gravity-free and friction-free setting, where
  (4.52) is the closed loop;
* the version formalized is the law with compensation of `N`, `τ = N(θ, θ̇) − K_v θ̇ − K_p e`
  (`pdCompensatedTorque`, the case `θ̇_d ≡ 0`, `θ̈_d ≡ 0` of (4.53)), whose closed loop is (4.52).
  With symmetric link inertias, `V = T(θ, θ̇) + ½ eᵀ K_p e` has `V̇ = −θ̇ᵀ K_v θ̇` along every
  motion (`hasDerivAt_pdEnergy`), `(θ_d, 0)` is an equilibrium
  (`isEquilibrium_pdCompensatedTorque`), and it is stable in the sense of Lyapunov
  (`stableAt_pdCompensatedTorque`, Theorem 4.4(1)). The energy identity and the stability
  theorem are those for every robot of `Control/RobotPDControl` applied to the manipulator as a
  robot (`toRobotSystem`, with `toRobotSystem_hasSkewProperty` and
  `toRobotSystem_differentiableAlongMotions`).

**Asymptotic stability** (the printed conclusion) is proved in `PDAsymptotic` by Lasalle's
principle (Theorem 4.7, p. 188), under a solution-flow hypothesis and a uniform bound on `M`.
Gain hypotheses: `K_p` symmetric positive definite
(Mathlib's `PosDef` includes symmetry; MLS writes `K_p > 0`); for stability `K_v` positive
semidefinite suffices (MLS: `K_v > 0`). `M(q)` positive definite for every `q` is a hypothesis
(MLS Lemma 4.2(1); `InertialChain.massMatrix_posDef_of_joints` discharges it for revolute and
prismatic chains with positive definite link inertias).
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-! ### The control laws -/

/-- **MLS eq. (4.51), p. 193: the PD control law** `τ = −K_v ė − K_p e`, `e = θ − θ_d`, for a
constant set point `θ_d` (`θ̇_d ≡ 0`, so `ė = θ̇`), as a feedback law `u(t, θ, θ̇)`. -/
def pdTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun _ q v => -(Kv *ᵥ v) - Kp *ᵥ (q - θd)

/-- **PD set-point control with compensation of `N` (MLS eq. (4.53), p. 194, with `θ̇_d ≡ 0`):**
`τ = N(θ, θ̇) − K_v θ̇ − K_p (θ − θ_d)`. Under it the closed loop is MLS's (4.52). -/
def pdCompensatedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun _ q v => P.N q v - Kv *ᵥ v - Kp *ᵥ (q - θd)

/-- **The Lyapunov function of the proof of MLS Proposition 4.9 (p. 193):**
`V(θ, θ̇) = ½ θ̇ᵀ M(θ) θ̇ + ½ (θ − θ_d)ᵀ K_p (θ − θ_d)` (MLS shifts to `θ_d = 0`). -/
def pdEnergy (Kp : Matrix (Fin n) (Fin n) ℝ) (θd q v : Fin n → ℝ) : ℝ :=
  P.chain.kineticEnergy q v + (1 / 2 : ℝ) * ((q - θd) ⬝ᵥ (Kp *ᵥ (q - θd)))

/-! ### The bare PD law (4.51): `θ_d` is a rest point only where `N(θ_d, 0) = 0` -/

/-- **Rest motions of (4.47) (MLS p. 190).** With symmetric link inertias, the constant motion
`θ ≡ q` satisfies the equations of motion at `t` under the torque `τ` exactly when
`τ = N(q, 0)`. -/
theorem equationsOfMotionAt_const_iff (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (q τ : Fin n → ℝ) (t : ℝ) : P.EquationsOfMotionAt (fun _ => q) τ t ↔ P.N q 0 = τ := by
  rw [P.equationsOfMotionAt_iff h (θ' := fun _ => 0) (θ'' := 0)
    (Eventually.of_forall fun s => hasDerivAt_const s q) (hasDerivAt_const t 0)]
  simp

/-- **The caution on MLS Proposition 4.9 (p. 193), at the level of motions.** With symmetric
link inertias, the constant motion `θ ≡ θ_d` satisfies the equations of motion (4.47) under the
bare PD law (4.51) exactly when `N(θ_d, 0) = 0`. -/
theorem equationsOfMotionAt_const_pdTorque_iff (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) (t : ℝ) :
    P.EquationsOfMotionAt (fun _ => θd) (pdTorque Kp Kv θd t θd 0) t ↔ P.N θd 0 = 0 := by
  rw [P.equationsOfMotionAt_const_iff h]
  simp [pdTorque]

/-- **The caution on MLS Proposition 4.9 (p. 193), in state space.** With `M(θ_d)` positive
definite, `(θ_d, 0)` is an equilibrium of (4.47) under the bare PD law (4.51) exactly when
`N(θ_d, 0) = 0`. -/
theorem isEquilibrium_pdTorque_iff (Kp Kv : Matrix (Fin n) (Fin n) ℝ) {θd : Fin n → ℝ}
    (hM : (P.M θd).PosDef) :
    Stability.IsEquilibrium (P.field (pdTorque Kp Kv θd)) (θd, 0) ↔ P.N θd 0 = 0 := by
  rw [P.isEquilibrium_field_iff _ hM]
  simp [pdTorque, eq_comm]

/-! ### PD with compensation of `N` -/

/-- With `M(θ_d)` positive definite, `(θ_d, 0)` is an equilibrium of (4.47) under PD control with
compensation of `N` (MLS (4.53) with `θ̇_d ≡ 0`). -/
theorem isEquilibrium_pdCompensatedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) {θd : Fin n → ℝ}
    (hM : (P.M θd).PosDef) :
    Stability.IsEquilibrium (P.field (P.pdCompensatedTorque Kp Kv θd)) (θd, 0) := by
  rw [P.isEquilibrium_field_iff _ hM]
  simp [pdCompensatedTorque]

/-- **MLS proof of Proposition 4.9, p. 193, for the law with compensation of `N`:
`V̇ = −θ̇ᵀ K_v θ̇`.** With symmetric link inertias and `K_p` symmetric, along a motion whose
velocity `θ'` near `t` and acceleration `θ''` at `t` are actual derivatives and which satisfies
the equations of motion (4.47) at `t` under `τ = N(θ, θ̇) − K_v θ̇ − K_p (θ − θ_d)`, the function
`V = ½ θ̇ᵀ M(θ) θ̇ + ½ (θ − θ_d)ᵀ K_p (θ − θ_d)` has derivative `−θ̇ᵀ K_v θ̇` at `t`. The proof is
the energy identity for matrix curves (`Control.hasDerivAt_pdEnergy_along`) with the skew symmetry
of `Ṁ − 2C` (MLS Lemma 4.2(2), `toRobotSystem_hasSkewProperty`). -/
theorem hasDerivAt_pdEnergy (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm) (θd : Fin n → ℝ)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hE : P.EquationsOfMotionAt θ (P.pdCompensatedTorque Kp Kv θd t (θ t) (θ' t)) t) :
    HasDerivAt (fun s => P.pdEnergy Kp θd (θ s) (θ' s)) (-(θ' t ⬝ᵥ (Kv *ᵥ θ' t))) t := by
  have hx := hθ.self_of_nhds
  have heq := (P.equationsOfMotionAt_iff h hθ hθ' _).mp hE
  have hMd := Christoffel.hasDerivAt_comp (P.chain.hasFDerivAt_massMatrix (θ t))
    (fun k => hasDerivAt_pi.mp hx k)
  refine Control.hasDerivAt_pdEnergy_along (Mt := fun s => P.M (θ s))
    (Ct := P.C (θ t) (θ' t)) hKp θd hx hθ' hMd
    (P.chain.massMatrix_isSymm h (θ t)) (P.toRobotSystem_hasSkewProperty h hx hMd) ?_
  calc _ = (P.M (θ t) *ᵥ θ'' + P.C (θ t) (θ' t) *ᵥ θ' t + P.N (θ t) (θ' t)) -
        P.pdCompensatedTorque Kp Kv θd t (θ t) (θ' t) := by
        simp only [pdCompensatedTorque]
        abel
    _ = 0 := by rw [heq, sub_self]

/-- **MLS Proposition 4.9 (p. 193), stability part, for PD control with compensation of `N`.**
With symmetric link inertias, `M(q)` positive definite for every `q`, `K_p` symmetric positive
definite and `K_v` positive semidefinite, the set point `(θ_d, 0)` of the closed loop (4.52)
(the system (4.47) under `τ = N(θ, θ̇) − K_v θ̇ − K_p (θ − θ_d)`) is stable in the sense of
Lyapunov (Definition 4.1) at every initial time `t₀ ≥ 0`. Proof: Theorem 4.4(1) with
`V = ½ θ̇ᵀ M(θ) θ̇ + ½ eᵀ K_p e`, which is locally positive definite by compactness, and
`V̇ = −θ̇ᵀ K_v θ̇ ≤ 0` (`Control.RobotSystem.stableAt_pdCompensatedTorque` for `toRobotSystem`).
Asymptotic stability (the printed conclusion) is `asymptoticallyStableAt_pdCompensatedTorque` in
`PDAsymptotic`. -/
theorem stableAt_pdCompensatedTorque (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef)
    (hKv : Kv.PosSemidef) (θd : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.StableAt (P.field (P.pdCompensatedTorque Kp Kv θd)) (θd, 0) t₀ :=
  P.toRobotSystem.stableAt_pdCompensatedTorque hM P.continuous_M
    P.toRobotSystem_differentiableAlongMotions (P.toRobotSystem_hasSkewProperty h) hKp hKv θd ht₀

end ManipulatorModel
end RoboLean
