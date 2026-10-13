import RoboLean.Control.PDAsymptotic
import RoboLean.Control.StabilityTheorems

/-!
# Augmented PD control and exponential trajectory tracking (MLS Proposition 4.10, pp. 194–195)

**What MLS prints (read this session, pp. 194–195, rendered).** The augmented PD control law is
(4.53), `τ = M(θ) θ̈_d + C(θ, θ̇) θ̇_d + N(θ, θ̇) − K_v ė − K_p e` with `e = θ − θ_d`, and
Proposition 4.10 states: "The control law (4.53) applied to the system (4.47) results in
exponential trajectory tracking if `K_v, K_p > 0`." The proof writes the closed loop as (4.54),
`M(θ) ë + C(θ, θ̇) ė + K_v ė + K_p e = 0`, takes the skewed energy
`V(e, ė, t) = ½ ėᵀ M(θ) ė + ½ eᵀ K_p e + ε eᵀ M(θ) ė`, "positive definite for `ε` sufficiently
small since `M(θ) > 0` and `K_p > 0`", and computes along (4.54)

`V̇ = −ėᵀ(K_v − εM)ė + ½ ėᵀ(Ṁ − 2C)ė + ε eᵀ(−K_p e − K_v ė − C ė + Ṁ ė)`
`  = −ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε eᵀ(−K_v + ½ Ṁ)ė`,

then: "Choosing `ε > 0` sufficiently small insures that `V̇` is negative definite (see Exercise 11)
and hence the system is exponentially stable using Theorem 4.5."

**Formalized.**

* the law (4.53) (`augmentedPDTorque`) and the closed loop (4.54) at each time
  (`equationsOfMotionAt_augmentedPDTorque_iff`, no gain hypothesis);
* the skewed energy (`augmentedEnergy`) and the derivative identity along every motion of the
  closed loop (`hasDerivAt_augmentedEnergy`), with the `Ṁ`- and `C`-terms explicit:
  `V̇ = −ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε eᵀ(−K_v + Ṁ − C)ė` (`augmentedEnergyRate`).
  The first line of MLS's display agrees with it after (4.54) and the skew symmetry are used; the
  last line differs: MLS's `½ Ṁ` is `Ṁ − C` here. Since `Ṁ = C + Cᵀ` (`Mdot_sub_C`, from the skew
  symmetry of `Ṁ − 2C`, Lemma 4.2), the difference is `ε eᵀ(½ Ṁ − C)ė`, the bilinear form of a
  skew-symmetric matrix at `(e, ė)`, which vanishes for `e = ė` but not in general (on the planar
  two-link arm it is nonzero at one evaluated point, E023 gate `Observation.lean`); it does not
  change the order of the terms, and the argument below bounds the corrected term;
* the bounds that make the argument work, with an explicit smallness condition on `ε`, on the
  tube `‖(e, ė)‖ ≤ R` around the desired trajectory (`augmentedEnergy_bounds`,
  `augmentedEnergyRate_le`): `M` bounded below by `λ` and above by `μ`, and `C` bounded by `c` on
  the tube; `2εμ ≤ min(λ, k_p)` and `ε(2 k_p μ + (κ_v + c)²) ≤ k_p k_v`, where
  `k_p, k_v` bound the gain forms below and `κ_v` bounds `|eᵀ K_v ė|` by `κ_v ‖e‖‖ė‖`;
* exponential decay of the tracking error on the tube by Theorem 4.5, local form
  (`norm_le_augmentedPD_of_bounds`), and from global bounds (`M` uniformly positive definite and
  bounded, `|vᵀ C(q, u) w| ≤ δ ‖u‖‖v‖‖w‖`, `θ̇_d` bounded) **semiglobal** exponential tracking:
  one overshoot constant `m`, and for every radius `ρ` of initial errors a rate `α`
  (`augmentedPD_tracking`), hence exponential stability (Definition 4.3) of the tracking-error
  system (`exponentiallyStable_augmentedPD`);
* for constant inertia (`C = 0`), **global** exponential tracking with no bound on `θ̇_d`
  (`augmentedPD_tracking_of_const`).

**What MLS states and what is proved.** MLS claims exponential tracking for `K_v, K_p > 0` with no
further condition. The terms `ε eᵀ(−K_v + Ṁ − C)ė` are bounded by `ε(κ_v + c)‖e‖‖ė‖`, and `c`
grows with the joint velocity `θ̇ = θ̇_d + ė` (`C` is linear in `θ̇`), so "negative definite for
`ε` small" holds on bounded tubes, with `ε` and the rate depending on the tube: the result proved
is semiglobal (every bounded set of initial errors, with a rate depending on it), and global when
`C = 0`. Whether a single `ε` works for all initial errors when `C ≠ 0` is not settled here
(hypothesis, not checked). Hypotheses MLS does not state: the bounds on `M` and `C` (MLS's
"`M(θ) > 0`" read as uniform, as on p. 191), a bound on `θ̇_d` (MLS: `θ_d` "at least twice
differentiable", p. 190), symmetric link inertias (for the skew symmetry), and `M(q)` positive
definite for every `q` (Lemma 4.2(1)). No bound on `θ̈_d` is needed: it cancels in (4.54).

Conventions: the state is `(θ, θ̇)`; the tracking error is `(e, ė) = (θ − θ_d, θ̇ − θ̇_d)`, the
state of the error system `Stability.errorSystem` relative to `(θ_d, θ̇_d)`; norms are Mathlib's
sup norms on `Fin n → ℝ` and on products; gains are `Matrix.PosDef` (symmetric). Exact model
cancellation is assumed, as in MLS (p. 195: "asymptotic tracking requires exact cancellation");
nothing here concerns model error, sampling or actuator limits.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean

/-! ### Tracking errors as solutions -/

namespace Stability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The error system relative to a reference curve** (MLS p. 179 shifts a constant equilibrium
to the origin; for trajectory tracking, §5, p. 190, the reference moves): with `x_d` and its
derivative `x_d'`, `ż = f(t, z + x_d(t)) − x_d'(t)`. Its solutions are the errors `x − x_d` of the
solutions `x` of `f` (`isSolution_errorSystem_iff`). Time is the first argument. -/
def errorSystem (f : ℝ → E → E) (xd xd' : ℝ → E) : ℝ → E → E :=
  fun t z => f t (z + xd t) - xd' t

/-- **Tracking errors solve the error system** (MLS pp. 179, 190): if `x_d` has derivative
`x_d'(t)` at every `t`, then `t ↦ x(t) − x_d(t)` solves `errorSystem f x_d x_d'` from `t₀`
exactly when `x` solves `f` from `t₀`. -/
theorem isSolution_errorSystem_iff {f : ℝ → E → E} {xd xd' : ℝ → E}
    (hxd : ∀ t, HasDerivAt xd (xd' t) t) {t₀ : ℝ} {x : ℝ → E} :
    IsSolution (errorSystem f xd xd') t₀ (fun t => x t - xd t) ↔ IsSolution f t₀ x := by
  have hc : Continuous xd := continuous_iff_continuousAt.mpr fun t => (hxd t).continuousAt
  simp only [IsSolution, errorSystem, sub_add_cancel]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(h1.add hc.continuousOn).congr fun t _ => by simp, fun t ht => ?_⟩
    have h3 := (h2 t ht).add (hxd t)
    rw [sub_add_cancel] at h3
    convert h3 using 1
    funext s
    simp
  · rintro ⟨h1, h2⟩
    exact ⟨h1.sub hc.continuousOn, fun t ht => (h2 t ht).sub (hxd t)⟩

end Stability

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-! ### The rate `Ṁ` of the inertia matrix and the identity `Ṁ = C + Cᵀ` -/

/-- **The rate `Ṁ` of the manipulator inertia matrix along a motion** (MLS pp. 169–171):
`Ṁ(θ, θ̇) = ∑ₖ θ̇ₖ ∂M/∂θₖ`, from the actual partial derivatives of `M` at `θ` (E013's
`InertialChain.massMatrixDeriv`). -/
def Mdot (q v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Christoffel.rate (Christoffel.partials (P.chain.massMatrixDeriv q)) v

/-- **The chain rule for `M(θ(t))` (MLS pp. 169–171):** along a motion `θ` with velocity `θ'` at
`t`, every entry of `s ↦ M(θ(s))` has the derivative `Ṁ(θ(t), θ')ᵢⱼ` at `t`. -/
theorem hasDerivAt_M_comp {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t)
    (i j : Fin n) : HasDerivAt (fun s => P.M (θ s) i j) (P.Mdot (θ t) θ' i j) t :=
  Christoffel.hasDerivAt_comp (P.chain.hasFDerivAt_massMatrix (θ t))
    (fun k => hasDerivAt_pi.mp hθ k) i j

/-- **`Ṁ − C = Cᵀ`, i.e. `Ṁ = C + Cᵀ` (MLS Lemma 4.2(2), p. 171, with the symmetry of `Ṁ`).**
With symmetric link inertias, `Ṁ − 2C` is skew-symmetric and `Ṁ` is symmetric, so
`Ṁ(θ, θ̇) − C(θ, θ̇) = C(θ, θ̇)ᵀ` at every configuration and joint rate. -/
theorem Mdot_sub_C (h : ∀ k, (P.chain.linkInertia k).IsSymm) (q v : Fin n → ℝ) :
    P.Mdot q v - P.C q v = (P.C q v)ᵀ := by
  have hdM := Christoffel.partials_isSymm (P.chain.massMatrix_isSymm h)
    (P.chain.hasFDerivAt_massMatrix q)
  have hskew := Christoffel.skew_rate_sub_two_coriolisMatrix hdM v
  have hR : ∀ i j, P.Mdot q v i j = P.Mdot q v j i := by
    intro i j
    simp only [Mdot, Christoffel.rate_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [(hdM k).apply j i]
  ext i j
  have h1 := congrFun (congrFun hskew i) j
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul] at h1
  simp only [Matrix.sub_apply, Matrix.transpose_apply]
  have h2 := hR i j
  simp only [Mdot, C] at h1 h2 ⊢
  linarith

/-- **The corrected cross term of MLS p. 195:** with symmetric link inertias,
`eᵀ (Ṁ − C) ė = ėᵀ C e` (from `Ṁ − C = Cᵀ`). -/
theorem dotProduct_Mdot_sub_C_mulVec (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (q v e w : Fin n → ℝ) :
    e ⬝ᵥ ((P.Mdot q v - P.C q v) *ᵥ w) = w ⬝ᵥ (P.C q v *ᵥ e) := by
  rw [P.Mdot_sub_C h, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

/-- **The passivity identity `ėᵀ(Ṁ − 2C)ė = 0` (MLS Lemma 4.2(2), p. 171)** at every
configuration, joint rate and vector, for symmetric link inertias. -/
theorem dotProduct_Mdot_sub_two_C_mulVec (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (q v w : Fin n → ℝ) : w ⬝ᵥ ((P.Mdot q v - (2 : ℝ) • P.C q v) *ᵥ w) = 0 :=
  Christoffel.dotProduct_mulVec_eq_zero_of_transpose_eq_neg
    (Christoffel.skew_rate_sub_two_coriolisMatrix (Christoffel.partials_isSymm
      (P.chain.massMatrix_isSymm h) (P.chain.hasFDerivAt_massMatrix q)) v) w

/-! ### The augmented PD law (4.53) and the closed loop (4.54) -/

/-- **MLS eq. (4.53), p. 194: the augmented PD control law**
`τ = M(θ) θ̈_d + C(θ, θ̇) θ̇_d + N(θ, θ̇) − K_v ė − K_p e`, `e = θ − θ_d`, `ė = θ̇ − θ̇_d`, for a
desired trajectory `θ_d` with velocity `θ_d'` and acceleration `θ_d''`, as a feedback law
`u(t, θ, θ̇)`. -/
def augmentedPDTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd θd' θd'' : ℝ → Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun t q v => P.M q *ᵥ θd'' t + P.C q v *ᵥ θd' t + P.N q v - Kv *ᵥ (v - θd' t) -
    Kp *ᵥ (q - θd t)

/-- **MLS eq. (4.54), p. 194: the closed loop of the augmented PD law.** With symmetric link
inertias, along a motion whose velocity `θ'` near `t` and acceleration `θ''` at `t` are actual
derivatives, the equations of motion (4.47) hold at `t` under (4.53) exactly when
`M(θ) ë + C(θ, θ̇) ė + K_v ė + K_p e = 0` at `t`, with `e = θ − θ_d`, `ė = θ' − θ_d'`,
`ë = θ'' − θ_d''`. No hypothesis on the gains is needed. -/
theorem equationsOfMotionAt_augmentedPDTorque_iff (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd θd' θd'' : ℝ → Fin n → ℝ)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) :
    P.EquationsOfMotionAt θ (P.augmentedPDTorque Kp Kv θd θd' θd'' t (θ t) (θ' t)) t ↔
      P.M (θ t) *ᵥ (θ'' - θd'' t) + P.C (θ t) (θ' t) *ᵥ (θ' t - θd' t) +
        Kv *ᵥ (θ' t - θd' t) + Kp *ᵥ (θ t - θd t) = 0 := by
  rw [P.equationsOfMotionAt_iff h hθ hθ', ← sub_eq_zero]
  have e : P.M (θ t) *ᵥ θ'' + P.C (θ t) (θ' t) *ᵥ θ' t + P.N (θ t) (θ' t) -
      P.augmentedPDTorque Kp Kv θd θd' θd'' t (θ t) (θ' t) =
      P.M (θ t) *ᵥ (θ'' - θd'' t) + P.C (θ t) (θ' t) *ᵥ (θ' t - θd' t) +
        Kv *ᵥ (θ' t - θd' t) + Kp *ᵥ (θ t - θd t) := by
    simp only [augmentedPDTorque, Matrix.mulVec_sub]
    abel
  rw [e]

/-! ### The skewed energy and its derivative along the closed loop -/

/-- **The Lyapunov function of the proof of MLS Proposition 4.10, p. 194:**
`V = ½ ėᵀ M(θ) ė + ½ eᵀ K_p e + ε eᵀ M(θ) ė`, at the configuration `q = θ`, with position error
`e` and velocity error `w = ė`. MLS writes `V(e, ė, t)`; the time enters through
`θ = θ_d(t) + e`. -/
def augmentedEnergy (Kp : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (q e w : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (w ⬝ᵥ (P.M q *ᵥ w)) + (1 / 2 : ℝ) * (e ⬝ᵥ (Kp *ᵥ e)) + ε * (e ⬝ᵥ (P.M q *ᵥ w))

/-- **The derivative of the skewed energy along the closed loop (4.54), MLS p. 195, corrected:**
`V̇ = −ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε eᵀ(−K_v + Ṁ − C)ė`, at the configuration `q = θ` and joint
rate `v = θ̇`, with `e`, `w = ė`. MLS's last line has `½ Ṁ` in place of `Ṁ − C` (see the module
docstring). -/
def augmentedEnergyRate (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (q v e w : Fin n → ℝ) : ℝ :=
  -(w ⬝ᵥ (Kv *ᵥ w)) + ε * (w ⬝ᵥ (P.M q *ᵥ w)) - ε * (e ⬝ᵥ (Kp *ᵥ e)) +
    ε * (e ⬝ᵥ ((-Kv + P.Mdot q v - P.C q v) *ᵥ w))

/-- **MLS proof of Proposition 4.10, p. 195: the derivative of `V` along the closed loop.** With
symmetric link inertias and `K_p` symmetric, along a motion `θ` whose velocity `θ'` near `t` and
acceleration `θ''` at `t` are actual derivatives, for a desired trajectory with
`θ̇_d(t) = θ_d'(t)` and `θ̈_d(t) = θ_d''(t)` at `t`, if the equations of motion (4.47) hold at `t`
under the augmented PD law (4.53), then
`s ↦ ½ ėᵀ M(θ) ė + ½ eᵀ K_p e + ε eᵀ M(θ) ė` has the derivative
`−ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε eᵀ(−K_v + Ṁ − C)ė` at `t` (`augmentedEnergyRate`). The proof
uses (4.54), the symmetry of `M` and `K_p`, and the skew symmetry of `Ṁ − 2C`; `θ̈_d` cancels. -/
theorem hasDerivAt_augmentedEnergy (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm) (ε : ℝ)
    {θd θd' θd'' : ℝ → Fin n → ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hd : HasDerivAt θd (θd' t) t) (hd' : HasDerivAt θd' (θd'' t) t)
    (hE : P.EquationsOfMotionAt θ (P.augmentedPDTorque Kp Kv θd θd' θd'' t (θ t) (θ' t)) t) :
    HasDerivAt (fun s => P.augmentedEnergy Kp ε (θ s) (θ s - θd s) (θ' s - θd' s))
      (P.augmentedEnergyRate Kp Kv ε (θ t) (θ' t) (θ t - θd t) (θ' t - θd' t)) t := by
  have hcl := (P.equationsOfMotionAt_augmentedPDTorque_iff h Kp Kv θd θd' θd'' hθ hθ').mp hE
  set e := θ t - θd t with he_def
  set w := θ' t - θd' t with hw_def
  set a := θ'' - θd'' t with ha_def
  have he : HasDerivAt (fun s => θ s - θd s) w t := hθ.self_of_nhds.sub hd
  have hw : HasDerivAt (fun s => θ' s - θd' s) a t := hθ'.sub hd'
  have hM := P.hasDerivAt_M_comp hθ.self_of_nhds
  have hMw := Control.hasDerivAt_matrix_mulVec hM hw
  have h1 := Control.hasDerivAt_dotProduct hw hMw
  have h2 := Control.hasDerivAt_dotProduct he (Control.hasDerivAt_mulVec_const Kp he)
  have h3 := Control.hasDerivAt_dotProduct he hMw
  have key := ((h1.const_mul (1 / 2 : ℝ)).add (h2.const_mul (1 / 2 : ℝ))).add (h3.const_mul ε)
  rw [← he_def, ← hw_def] at key
  convert key using 1
  · funext s
    simp only [augmentedEnergy, Pi.add_apply]
  -- the algebra of p. 195
  have hMsymm : (P.M (θ t)).IsSymm := P.chain.massMatrix_isSymm h (θ t)
  have hMa : P.M (θ t) *ᵥ a = -(P.C (θ t) (θ' t) *ᵥ w) - Kv *ᵥ w - Kp *ᵥ e := by
    rw [← sub_eq_zero, ← hcl]
    abel
  have hs1 : a ⬝ᵥ (P.M (θ t) *ᵥ w) = w ⬝ᵥ (P.M (θ t) *ᵥ a) :=
    Control.dotProduct_mulVec_comm hMsymm a w
  have hs2 : w ⬝ᵥ (Kp *ᵥ e) = e ⬝ᵥ (Kp *ᵥ w) := Control.dotProduct_mulVec_comm hKp w e
  have hskew := P.dotProduct_Mdot_sub_two_C_mulVec h (θ t) (θ' t) w
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul] at hskew
  rw [hs1, hMa]
  simp only [augmentedEnergyRate, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.neg_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_neg]
  rw [hs2]
  linear_combination (-1 / 2 : ℝ) * hskew

/-! ### Bounds on the tube around the desired trajectory -/

/-- The scalar core of `augmentedEnergy_bounds`: `Y = ėᵀMė`, `Z = eᵀK_pe`, `Q = eᵀMė`,
`a = ‖e‖`, `b = ‖ė‖`. -/
private lemma energy_bounds_scalar {lam kp μ κp ε a b Y Z Q : ℝ}
    (hμ : 0 ≤ μ) (hκp : 0 ≤ κp) (hε : 0 ≤ ε) (hεμ : 2 * ε * μ ≤ min lam kp)
    (hY : lam * b ^ 2 ≤ Y) (hY' : Y ≤ μ * b ^ 2) (hZ : kp * a ^ 2 ≤ Z) (hZ' : Z ≤ κp * a ^ 2)
    (hQ : |Q| ≤ μ * a * b) :
    min lam kp / 4 * (a ^ 2 + b ^ 2) ≤ 1 / 2 * Y + 1 / 2 * Z + ε * Q ∧
      1 / 2 * Y + 1 / 2 * Z + ε * Q ≤ (μ + κp + ε * μ) / 2 * (a ^ 2 + b ^ 2) := by
  have hab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hQ1 : -(μ * a * b) ≤ Q := (abs_le.mp hQ).1
  have hQ2 : Q ≤ μ * a * b := (abs_le.mp hQ).2
  have hεQ1 : ε * (-(μ * a * b)) ≤ ε * Q := mul_le_mul_of_nonneg_left hQ1 hε
  have hεQ2 : ε * Q ≤ ε * (μ * a * b) := mul_le_mul_of_nonneg_left hQ2 hε
  have hεμ0 : 0 ≤ ε * μ := mul_nonneg hε hμ
  have hcross : ε * μ * (2 * (a * b)) ≤ ε * μ * (a ^ 2 + b ^ 2) :=
    mul_le_mul_of_nonneg_left hab hεμ0
  have hm1 := min_le_left lam kp
  have hm2 := min_le_right lam kp
  have ha2 := sq_nonneg a
  have hb2 := sq_nonneg b
  constructor
  · have h1 : min lam kp * b ^ 2 ≤ lam * b ^ 2 := mul_le_mul_of_nonneg_right hm1 hb2
    have h2 : min lam kp * a ^ 2 ≤ kp * a ^ 2 := mul_le_mul_of_nonneg_right hm2 ha2
    have h3 : 2 * ε * μ * (a ^ 2 + b ^ 2) ≤ min lam kp * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_right hεμ (by positivity)
    nlinarith
  · have h1 : 0 ≤ μ * a ^ 2 := mul_nonneg hμ ha2
    have h2 : 0 ≤ κp * b ^ 2 := mul_nonneg hκp hb2
    nlinarith

/-- The scalar core of `augmentedEnergyRate_le`: `X = ėᵀK_vė`, `Y = ėᵀMė`, `Z = eᵀK_pe`, `W` the
cross terms, `a = ‖e‖`, `b = ‖ė‖`, with the smallness condition `ε(2k_pμ + K²) ≤ k_p k_v`. -/
private lemma rate_bound_scalar {kv kp ε μ K a b X Y Z W : ℝ} (hkp : 0 < kp) (hε : 0 < ε)
    (hX : kv * b ^ 2 ≤ X) (hY : Y ≤ μ * b ^ 2) (hZ : kp * a ^ 2 ≤ Z) (hW : W ≤ K * a * b)
    (hc : ε * (2 * kp * μ + K ^ 2) ≤ kp * kv) :
    -X + ε * Y - ε * Z + ε * W ≤ -(min (kv / 2) (ε * kp / 2) * (a ^ 2 + b ^ 2)) := by
  have h1 : 2 * kp * (K * a * b) ≤ kp ^ 2 * a ^ 2 + K ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (kp * a - K * b)]
  have e1 : ε * W ≤ ε * (K * a * b) := mul_le_mul_of_nonneg_left hW hε.le
  have e2 : ε * Y ≤ ε * (μ * b ^ 2) := mul_le_mul_of_nonneg_left hY hε.le
  have e3 : ε * (kp * a ^ 2) ≤ ε * Z := mul_le_mul_of_nonneg_left hZ hε.le
  have e4 : ε * (2 * kp * (K * a * b)) ≤ ε * (kp ^ 2 * a ^ 2 + K ^ 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hε.le
  have e5 : ε * (2 * kp * μ + K ^ 2) * b ^ 2 ≤ kp * kv * b ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg b)
  have hB : -X + ε * Y - ε * Z + ε * W ≤
      -(kv * b ^ 2) + ε * (μ * b ^ 2) - ε * (kp * a ^ 2) + ε * (K * a * b) := by linarith
  have hL : -X + ε * Y - ε * Z + ε * W ≤ -(ε * kp / 2 * a ^ 2 + kv / 2 * b ^ 2) := by
    have h2 : 2 * kp * (-X + ε * Y - ε * Z + ε * W) ≤
        2 * kp * (-(ε * kp / 2 * a ^ 2 + kv / 2 * b ^ 2)) := by
      have h3 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 * kp)
      nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hm1 : min (kv / 2) (ε * kp / 2) * b ^ 2 ≤ kv / 2 * b ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg b)
  have hm2 : min (kv / 2) (ε * kp / 2) * a ^ 2 ≤ ε * kp / 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg a)
  nlinarith

/-- **The skewed energy is positive definite for `ε` small (MLS p. 195, "positive definite for
`ε` sufficiently small since `M(θ) > 0` and `K_p > 0`"), with explicit constants.** At a
configuration `q` where `λ‖v‖² ≤ vᵀM(q)v` and `|vᵀM(q)v'| ≤ μ‖v‖‖v'‖`, with
`k_p‖v‖² ≤ vᵀK_pv ≤ κ_p‖v‖²`, `μ, κ_p, ε ≥ 0` and `2εμ ≤ min(λ, k_p)`:
`¼ min(λ, k_p)(‖e‖² + ‖ė‖²) ≤ V ≤ ½(μ + κ_p + εμ)(‖e‖² + ‖ė‖²)` (sup norms on `ℝⁿ`). -/
theorem augmentedEnergy_bounds {Kp : Matrix (Fin n) (Fin n) ℝ} {ε lam μ kp κp : ℝ}
    {q e w : Fin n → ℝ} (hμ : 0 ≤ μ) (hκp : 0 ≤ κp) (hε : 0 ≤ ε)
    (hεμ : 2 * ε * μ ≤ min lam kp) (hMl : ∀ v, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    (hMu : ∀ v v', |v ⬝ᵥ (P.M q *ᵥ v')| ≤ μ * ‖v‖ * ‖v'‖)
    (hkp : ∀ v, kp * ‖v‖ ^ 2 ≤ v ⬝ᵥ (Kp *ᵥ v)) (hκpb : ∀ v, v ⬝ᵥ (Kp *ᵥ v) ≤ κp * ‖v‖ ^ 2) :
    min lam kp / 4 * (‖e‖ ^ 2 + ‖w‖ ^ 2) ≤ P.augmentedEnergy Kp ε q e w ∧
      P.augmentedEnergy Kp ε q e w ≤ (μ + κp + ε * μ) / 2 * (‖e‖ ^ 2 + ‖w‖ ^ 2) := by
  have hY' : w ⬝ᵥ (P.M q *ᵥ w) ≤ μ * ‖w‖ ^ 2 := by
    have := (le_abs_self _).trans (hMu w w)
    nlinarith
  exact energy_bounds_scalar hμ hκp hε hεμ (hMl w) hY' (hkp e)
    (hκpb e) (hMu e w)

/-- **`V̇` is negative definite for `ε` small (MLS p. 195, "Choosing `ε > 0` sufficiently small
insures that `V̇` is negative definite"), with an explicit condition.** With symmetric link
inertias, at a configuration `q` and joint rate `v` where `|v₁ᵀM(q)v₂| ≤ μ‖v₁‖‖v₂‖` and
`|v₁ᵀC(q, v)v₂| ≤ c‖v₁‖‖v₂‖`, with `k_p‖v‖² ≤ vᵀK_pv`, `k_v‖v‖² ≤ vᵀK_vv`,
`|v₁ᵀK_vv₂| ≤ κ_v‖v₁‖‖v₂‖`, `k_p, ε > 0` and `ε(2k_pμ + (κ_v + c)²) ≤ k_p k_v`:
`V̇ ≤ −min(k_v/2, εk_p/2)(‖e‖² + ‖ė‖²)`. Since `C(q, v)` is linear in `v`, `c` grows with the joint
rate; the bound is used on a tube where `‖v‖` is bounded. -/
theorem augmentedEnergyRate_le (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} {ε μ c kp kv κv : ℝ} {q v e w : Fin n → ℝ}
    (hkp0 : 0 < kp) (hε : 0 < ε) (hMu : ∀ v₁ v₂, |v₁ ⬝ᵥ (P.M q *ᵥ v₂)| ≤ μ * ‖v₁‖ * ‖v₂‖)
    (hCu : ∀ v₁ v₂, |v₁ ⬝ᵥ (P.C q v *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖)
    (hkp : ∀ v₁, kp * ‖v₁‖ ^ 2 ≤ v₁ ⬝ᵥ (Kp *ᵥ v₁)) (hkv : ∀ v₁, kv * ‖v₁‖ ^ 2 ≤ v₁ ⬝ᵥ (Kv *ᵥ v₁))
    (hκv : ∀ v₁ v₂, |v₁ ⬝ᵥ (Kv *ᵥ v₂)| ≤ κv * ‖v₁‖ * ‖v₂‖)
    (hεc : ε * (2 * kp * μ + (κv + c) ^ 2) ≤ kp * kv) :
    P.augmentedEnergyRate Kp Kv ε q v e w ≤ -(min (kv / 2) (ε * kp / 2) * (‖e‖ ^ 2 + ‖w‖ ^ 2)) := by
  have hW : e ⬝ᵥ ((-Kv + P.Mdot q v - P.C q v) *ᵥ w) = -(e ⬝ᵥ (Kv *ᵥ w)) + w ⬝ᵥ (P.C q v *ᵥ e) := by
    rw [show -Kv + P.Mdot q v - P.C q v = -Kv + (P.Mdot q v - P.C q v) by abel,
      Matrix.add_mulVec, dotProduct_add, Matrix.neg_mulVec, dotProduct_neg,
      P.dotProduct_Mdot_sub_C_mulVec h]
  have hWb : -(e ⬝ᵥ (Kv *ᵥ w)) + w ⬝ᵥ (P.C q v *ᵥ e) ≤ (κv + c) * ‖e‖ * ‖w‖ := by
    have h1 := (neg_le_abs _).trans (hκv e w)
    have h2 := (le_abs_self _).trans (hCu w e)
    nlinarith
  have hY : w ⬝ᵥ (P.M q *ᵥ w) ≤ μ * ‖w‖ ^ 2 := by
    have := (le_abs_self _).trans (hMu w w)
    nlinarith
  unfold augmentedEnergyRate
  rw [hW]
  exact rate_bound_scalar hkp0 hε (hkv w) hY (hkp e) hWb hεc

/-! ### Exponential tracking -/

/-- **The derivative of the skewed energy along the tracking-error system (MLS p. 195).** With
symmetric link inertias, `M(q)` positive definite for every `q` and `K_p` symmetric, for a desired
trajectory with `θ̇_d = θ_d'` and `θ̈_d = θ_d''` at every time, along every solution `(e, ė)` of
the error system of the closed loop under (4.53) relative to `(θ_d, θ̇_d)`, the function
`V(t, (e, ė)) = augmentedEnergy (θ_d(t) + e) e ė` has the derivative
`augmentedEnergyRate (θ_d(t) + e) (θ̇_d(t) + ė) e ė`, on the whole error space. -/
theorem hasDerivAlongSolutions_augmentedEnergy (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm) (ε : ℝ)
    {θd θd' θd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt θd (θd' t) t)
    (hd' : ∀ t, HasDerivAt θd' (θd'' t) t) :
    Stability.HasDerivAlongSolutions
      (Stability.errorSystem (P.field (P.augmentedPDTorque Kp Kv θd θd' θd''))
        (fun t => (θd t, θd' t)) (fun t => (θd' t, θd'' t)))
      (fun t z => P.augmentedEnergy Kp ε (θd t + z.1) z.1 z.2)
      (fun t z => P.augmentedEnergyRate Kp Kv ε (θd t + z.1) (θd' t + z.2) z.1 z.2) univ := by
  intro t₀ _ z hz t ht _
  have hxd : ∀ s, HasDerivAt (fun s => (θd s, θd' s)) (θd' s, θd'' s) s :=
    fun s => (hd s).prodMk (hd' s)
  set x : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun s => z s + (θd s, θd' s) with hxdef
  have hx : Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv θd θd' θd'')) t₀ x := by
    refine (Stability.isSolution_errorSystem_iff hxd).mp ?_
    simpa [hxdef] using hz
  have hE := P.equationsOfMotionAt_of_isSolution h hM hx ht
  have key := P.hasDerivAt_augmentedEnergy h hKp ε (P.eventually_hasDerivAt_fst hx ht)
    (hx.2 t ht).snd (hd t) (hd' t) hE
  convert key using 1
  · funext s
    simp [hxdef, add_comm]
  · simp [hxdef, add_comm]

/-- The skewed energy along the desired trajectory is jointly continuous in `(t, (e, ė))`. -/
theorem continuous_augmentedEnergy_comp (Kp : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    {θd : ℝ → Fin n → ℝ} (hθd : Continuous θd) :
    Continuous fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      P.augmentedEnergy Kp ε (θd p.1 + p.2.1) p.2.1 p.2.2 := by
  have he : Continuous fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1 :=
    continuous_fst.comp continuous_snd
  have hw : Continuous fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2 :=
    continuous_snd.comp continuous_snd
  have hq : Continuous fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => θd p.1 + p.2.1 :=
    (hθd.comp continuous_fst).add he
  have hMq := P.continuous_M.comp hq
  unfold augmentedEnergy
  exact ((continuous_const.mul (hw.dotProduct (hMq.matrix_mulVec hw))).add
    (continuous_const.mul (he.dotProduct (continuous_const.matrix_mulVec he)))).add
    (continuous_const.mul (he.dotProduct (hMq.matrix_mulVec hw)))

/-- **MLS Proposition 4.10 (p. 194) on a tube, with explicit constants: exponential decay of the
tracking error by Theorem 4.5 (local form).** Hypotheses: symmetric link inertias; `M(q)`
positive definite for every `q`; `K_p` symmetric; a desired trajectory with `θ̇_d = θ_d'`,
`θ̈_d = θ_d''`; on the tube `‖(e, ė)‖ ≤ R` around it, for `t ≥ 0`, with `θ = θ_d(t) + e`,
`θ̇ = θ̇_d(t) + ė`: `λ‖v‖² ≤ vᵀM(θ)v`, `|v₁ᵀM(θ)v₂| ≤ μ‖v₁‖‖v₂‖`,
`|v₁ᵀC(θ, θ̇)v₂| ≤ c‖v₁‖‖v₂‖`; gain bounds `k_p‖v‖² ≤ vᵀK_pv ≤ κ_p‖v‖²`, `k_v‖v‖² ≤ vᵀK_vv`,
`|v₁ᵀK_vv₂| ≤ κ_v‖v₁‖‖v₂‖`; and `ε > 0` with `2εμ ≤ min(λ, k_p)` and
`ε(2k_pμ + (κ_v + c)²) ≤ k_p k_v`. Then, with `a₁ = min(λ, k_p)/4`, `a₂ = μ + κ_p + εμ + 1`,
`a₃ = min(k_v/2, εk_p/2)`, every closed-loop solution from `t₀ ≥ 0` whose initial tracking error
satisfies `‖(e, ė)(t₀)‖ < min(R, R√(a₁/a₂))` obeys
`‖(e, ė)(t)‖ ≤ √(a₂/a₁) e^{−(a₃/(2a₂))(t − t₀)} ‖(e, ė)(t₀)‖` for `t ≥ t₀` (sup norm on
`ℝⁿ × ℝⁿ`). -/
theorem norm_le_augmentedPD_of_bounds (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm)
    {θd θd' θd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt θd (θd' t) t)
    (hd' : ∀ t, HasDerivAt θd' (θd'' t) t) {R ε lam μ c kp κp kv κv : ℝ} (hR : 0 < R)
    (hε : 0 < ε) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hkp0 : 0 < kp) (hκp : 0 ≤ κp) (hkv0 : 0 < kv)
    (hMl : ∀ t, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      ∀ v, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M (θd t + z.1) *ᵥ v))
    (hMu : ∀ t, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (P.M (θd t + z.1) *ᵥ v₂)| ≤ μ * ‖v₁‖ * ‖v₂‖)
    (hCu : ∀ t, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (P.C (θd t + z.1) (θd' t + z.2) *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖)
    (hkp : ∀ v, kp * ‖v‖ ^ 2 ≤ v ⬝ᵥ (Kp *ᵥ v)) (hκpb : ∀ v, v ⬝ᵥ (Kp *ᵥ v) ≤ κp * ‖v‖ ^ 2)
    (hkv : ∀ v, kv * ‖v‖ ^ 2 ≤ v ⬝ᵥ (Kv *ᵥ v))
    (hκv : ∀ v₁ v₂, |v₁ ⬝ᵥ (Kv *ᵥ v₂)| ≤ κv * ‖v₁‖ * ‖v₂‖)
    (hεμ : 2 * ε * μ ≤ min lam kp) (hεc : ε * (2 * kp * μ + (κv + c) ^ 2) ≤ kp * kv)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv θd θd' θd'')) t₀ x)
    (hx₀ : ‖x t₀ - (θd t₀, θd' t₀)‖ <
      min R (R * Real.sqrt (min lam kp / 4 / (μ + κp + ε * μ + 1))))
    {t : ℝ} (ht : t₀ ≤ t) :
    ‖x t - (θd t, θd' t)‖ ≤ Real.sqrt ((μ + κp + ε * μ + 1) / (min lam kp / 4)) *
      Real.exp (-(min (kv / 2) (ε * kp / 2) / (2 * (μ + κp + ε * μ + 1))) * (t - t₀)) *
        ‖x t₀ - (θd t₀, θd' t₀)‖ := by
  have hxd : ∀ s, HasDerivAt (fun s => (θd s, θd' s)) (θd' s, θd'' s) s :=
    fun s => (hd s).prodMk (hd' s)
  have hθd : Continuous θd := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hz := (Stability.isSolution_errorSystem_iff hxd (f := P.field
    (P.augmentedPDTorque Kp Kv θd θd' θd''))).mpr hx
  have ha₁ : 0 < min lam kp / 4 := by have := lt_min hlam hkp0; positivity
  have ha₂ : 0 < μ + κp + ε * μ + 1 := by positivity
  have ha₃ : 0 < min (kv / 2) (ε * kp / 2) := lt_min (by positivity) (by positivity)
  have hsq : ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 :=
    Control.sq_norm_prod_le
  have hsq' : ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    intro z
    have h1 := norm_fst_le z
    have h2 := norm_snd_le z
    have := norm_nonneg z.1
    have := norm_nonneg z.2
    nlinarith
  have hbounds : ∀ t, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      min lam kp / 4 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ P.augmentedEnergy Kp ε (θd t + z.1) z.1 z.2 ∧
        P.augmentedEnergy Kp ε (θd t + z.1) z.1 z.2 ≤
          (μ + κp + ε * μ) / 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) :=
    fun t ht z hz => P.augmentedEnergy_bounds hμ hκp hε.le hεμ (hMl t ht z hz) (hMu t ht z hz)
      hkp hκpb
  have key := Stability.norm_le_of_quadratic_lyapunov_local
    (f := Stability.errorSystem (P.field (P.augmentedPDTorque Kp Kv θd θd' θd''))
      (fun t => (θd t, θd' t)) (fun t => (θd' t, θd'' t)))
    (V := fun t z => P.augmentedEnergy Kp ε (θd t + z.1) z.1 z.2)
    (Vdot := fun t z => P.augmentedEnergyRate Kp Kv ε (θd t + z.1) (θd' t + z.2) z.1 z.2)
    ha₁ ha₂ ha₃ hR (P.continuous_augmentedEnergy_comp Kp ε hθd).continuousOn
    (fun t ht z hz => by
      have h1 := (hbounds t ht z hz).1
      have h2 := mul_le_mul_of_nonneg_left (hsq z) ha₁.le
      exact h2.trans h1)
    (fun t ht z hz => by
      have h1 := (hbounds t ht z hz).2
      have h2 := hsq' z
      have hc0 : 0 ≤ (μ + κp + ε * μ) / 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2 hc0
      have h4 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
      nlinarith)
    ((P.hasDerivAlongSolutions_augmentedEnergy h hM hKp ε hd hd').mono (subset_univ _))
    (fun t ht z hz => by
      have h1 := P.augmentedEnergyRate_le h (q := θd t + z.1) (v := θd' t + z.2) (e := z.1)
        (w := z.2) hkp0 hε (hMu t ht z hz) (hCu t ht z hz) hkp hkv hκv hεc
      have h2 := mul_le_mul_of_nonneg_left (hsq z) ha₃.le
      linarith)
    ht₀ hz hx₀ ht
  simpa using key

/-- The tracking error of a closed-loop state, written as a pair (sup norm on the product). -/
private lemma sub_pair (x : (Fin n → ℝ) × (Fin n → ℝ)) (a b : Fin n → ℝ) :
    x - (a, b) = (x.1 - a, x.2 - b) := rfl

/-- **MLS Proposition 4.10 (p. 194) as formalized: semiglobal exponential trajectory tracking
under the augmented PD law (4.53).** Hypotheses: symmetric link inertias; `M(q)` positive
definite for every `q` (Lemma 4.2(1)); `M` uniformly positive definite and bounded
(`λ‖v‖² ≤ vᵀM(q)v`, `|vᵀM(q)w| ≤ μ‖v‖‖w‖` for all `q`; MLS's "`M(θ) > 0`", uniform as on p. 191);
the Coriolis matrix bounded by the joint rate, `|vᵀC(q, u)w| ≤ δ‖u‖‖v‖‖w‖` (a bound on the
first derivatives of `M`); `K_p, K_v` positive definite (Mathlib's `PosDef`, symmetric); a desired
trajectory with `θ̇_d = θ_d'`, `θ̈_d = θ_d''` at every time and `‖θ̇_d(t)‖ ≤ v_d` for `t ≥ 0`. Then
there is `m > 0` and, for every `ρ > 0`, a rate `α > 0` such that every closed-loop solution from
`t₀ ≥ 0` whose initial tracking error is smaller than `ρ` satisfies
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀` (sup norm on `ℝⁿ × ℝⁿ`). MLS
claims this with no bounds and no dependence of the rate on the initial error; the rate here
shrinks as `ρ` grows when `δ > 0` (the `C`-terms of `V̇` grow with the joint rate). -/
theorem augmentedPD_tracking (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMl : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin n → ℝ, |v ⬝ᵥ (P.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ q u v w : Fin n → ℝ, |v ⬝ᵥ (P.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef)
    {θd θd' θd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt θd (θd' t) t)
    (hd' : ∀ t, HasDerivAt θd' (θd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖θd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv θd θd' θd'')) t₀ x →
      ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ < ρ → ∀ t, t₀ ≤ t →
        ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  obtain ⟨lam, hlam, hMl⟩ := hMl
  obtain ⟨μ₀, hMb⟩ := hMb
  obtain ⟨δ₀, hCb⟩ := hCb
  obtain ⟨vd₀, hvd⟩ := hvd
  set μ := max μ₀ 0 with hμdef
  set δ := max δ₀ 0 with hδdef
  set vd := max vd₀ 0 with hvddef
  have hμ : 0 ≤ μ := le_max_right _ _
  have hδ : 0 ≤ δ := le_max_right _ _
  have hvd0 : 0 ≤ vd := le_max_right _ _
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
  refine ⟨Real.sqrt (A / (min lam kp / 4)), Real.sqrt_pos.mpr (by positivity), fun ρ hρ => ?_⟩
  set R := ρ / s₁ + ρ with hRdef
  have hR : 0 < R := by positivity
  set c := δ * (vd + R) with hcdef
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
  refine ⟨min (kv / 2) (ε * kp / 2) / (2 * a₂),
    div_pos (lt_min (by positivity) (by positivity)) (by positivity),
    fun t₀ ht₀ x hx hx₀ t ht => ?_⟩
  have hCu : ∀ t, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (P.C (θd t + z.1) (θd' t + z.2) *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖ := by
    intro t ht z hz v₁ v₂
    have h2 : ‖θd' t + z.2‖ ≤ vd + R :=
      (norm_add_le _ _).trans (add_le_add ((hvd t ht).trans (le_max_left _ _))
        ((norm_snd_le z).trans hz))
    calc |v₁ ⬝ᵥ (P.C (θd t + z.1) (θd' t + z.2) *ᵥ v₂)|
        ≤ δ * ‖θd' t + z.2‖ * ‖v₁‖ * ‖v₂‖ := hCb' _ _ _ _
      _ ≤ δ * (vd + R) * ‖v₁‖ * ‖v₂‖ := by gcongr
  have hx₀' : ‖x t₀ - (θd t₀, θd' t₀)‖ <
      min R (R * Real.sqrt (min lam kp / 4 / (μ + κp + ε * μ + 1))) := by
    rw [sub_pair]
    have hs : s₁ ≤ Real.sqrt (min lam kp / 4 / a₂) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) ha₂ ha₂A)
    have hRs : R * s₁ = ρ + ρ * s₁ := by
      rw [hRdef]
      field_simp
    refine lt_min (by
      have : 0 < ρ / s₁ := by positivity
      linarith) ?_
    calc ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ < ρ := hx₀
      _ < ρ + ρ * s₁ := lt_add_of_pos_right ρ (by positivity)
      _ = R * s₁ := hRs.symm
      _ ≤ R * Real.sqrt (min lam kp / 4 / a₂) := by gcongr
  have key := P.norm_le_augmentedPD_of_bounds h hM hKp.isHermitian.isSymm hd hd' hR hε hlam hμ
    hkp0 hκp0.le hkv0 (fun t _ z _ v => hMl _ v) (fun t _ z _ => hMb' _) hCu hkp
    (fun v => hκpb v) hkv hκv hεμ hεc ht₀ hx hx₀' ht
  rw [sub_pair, sub_pair] at key
  refine key.trans ?_
  gcongr

/-- **MLS Proposition 4.10 (p. 194), in the form of Definition 4.3: the tracking error is
exponentially stable.** Under the hypotheses of `augmentedPD_tracking`, the origin of the
tracking-error system (the closed loop under (4.53) seen relative to `(θ_d, θ̇_d)`,
`Stability.errorSystem`) is exponentially stable (Definition 4.3, p. 180, constants independent
of `t₀ ≥ 0`). -/
theorem exponentiallyStable_augmentedPD (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMl : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin n → ℝ, |v ⬝ᵥ (P.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ q u v w : Fin n → ℝ, |v ⬝ᵥ (P.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef)
    {θd θd' θd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt θd (θd' t) t)
    (hd' : ∀ t, HasDerivAt θd' (θd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖θd' t‖ ≤ vd) :
    Stability.ExponentiallyStable
      (Stability.errorSystem (P.field (P.augmentedPDTorque Kp Kv θd θd' θd''))
        (fun t => (θd t, θd' t)) (fun t => (θd' t, θd'' t))) 0 := by
  obtain ⟨m, hm, H⟩ := P.augmentedPD_tracking h hM hMl hMb hCb hKp hKv hd hd' hvd
  obtain ⟨α, hα, H⟩ := H 1 one_pos
  refine ⟨m, hm, α, hα, 1 / 2, by norm_num, fun t₀ ht₀ z hz hz₀ t ht => ?_⟩
  have hxd : ∀ s, HasDerivAt (fun s => (θd s, θd' s)) (θd' s, θd'' s) s :=
    fun s => (hd s).prodMk (hd' s)
  have hx : Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv θd θd' θd'')) t₀
      (fun s => z s + (θd s, θd' s)) :=
    (Stability.isSolution_errorSystem_iff hxd).mp (by simpa using hz)
  have hz₀' : ‖z t₀‖ < 1 := by
    rw [sub_zero] at hz₀
    linarith
  have := H t₀ ht₀ _ hx (by simpa using hz₀') t ht
  simpa using this

/-- **MLS Proposition 4.10 (p. 194) for constant inertia: global exponential tracking.** With
symmetric link inertias, `M(q) = M₀` positive definite for every `q` (so `C = 0`), and `K_p, K_v`
positive definite, there are `m, α > 0`, depending only on `M₀`, `K_p`, `K_v`, such that for every
desired trajectory with `θ̇_d = θ_d'`, `θ̈_d = θ_d''` (no bound on them) every closed-loop solution
under (4.53) from `t₀ ≥ 0` satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for
`t ≥ t₀`. Here the `C`-terms of `V̇` vanish, so one `ε` serves every initial error. -/
theorem augmentedPD_tracking_of_const (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {M₀ : Matrix (Fin n) (Fin n) ℝ} (hM0 : ∀ q, P.M q = M₀) (hM₀ : M₀.PosDef)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {θd θd' θd'' : ℝ → Fin n → ℝ}, (∀ t, HasDerivAt θd (θd' t) t) →
      (∀ t, HasDerivAt θd' (θd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv θd θd' θd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  have hM : ∀ q, (P.M q).PosDef := fun q => hM0 q ▸ hM₀
  obtain ⟨lam, hlam, hMl⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hM₀
  obtain ⟨μ, hμ, hMb⟩ := Control.exists_abs_dotProduct_mulVec_le M₀
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
  set D := 2 * kp * μ + (κv + 0) ^ 2 with hDdef
  have hD : 0 ≤ D := by positivity
  set ε := min ε₀ (kp * kv / (D + 1)) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεμ : 2 * ε * μ ≤ min lam kp := le_trans (by gcongr; exact min_le_left _ _) hε₀μ
  have hεc : ε * D ≤ kp * kv := by
    have h1 : ε ≤ kp * kv / (D + 1) := min_le_right _ _
    have h2 : ε * (D + 1) ≤ kp * kv := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  set a₂ := μ + κp + ε * μ + 1 with ha₂def
  have ha₂ : 0 < a₂ := by positivity
  set s₁ := Real.sqrt (min lam kp / 4 / a₂) with hs₁def
  have hs₁ : 0 < s₁ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt (a₂ / (min lam kp / 4)), Real.sqrt_pos.mpr (by positivity),
    min (kv / 2) (ε * kp / 2) / (2 * a₂),
    div_pos (lt_min (by positivity) (by positivity)) (by positivity),
    fun {θd θd' θd''} hd hd' t₀ ht₀ x hx t ht => ?_⟩
  set e₀ := ‖x t₀ - (θd t₀, θd' t₀)‖ with he₀def
  set R := (e₀ + 1) / s₁ + (e₀ + 1) with hRdef
  have he₀ : 0 ≤ e₀ := norm_nonneg _
  have hR : 0 < R := by positivity
  have hx₀' : ‖x t₀ - (θd t₀, θd' t₀)‖ < min R (R * s₁) := by
    have hRs : R * s₁ = (e₀ + 1) + (e₀ + 1) * s₁ := by
      rw [hRdef]
      field_simp
    refine lt_min ?_ ?_
    · have : 0 < (e₀ + 1) / s₁ := by positivity
      linarith
    · rw [hRs]
      have : 0 < (e₀ + 1) * s₁ := by positivity
      linarith
  have hCu : ∀ t, 0 ≤ t → ∀ z : (Fin n → ℝ) × (Fin n → ℝ), ‖z‖ ≤ R →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (P.C (θd t + z.1) (θd' t + z.2) *ᵥ v₂)| ≤ 0 * ‖v₁‖ * ‖v₂‖ := by
    intro t _ z _ v₁ v₂
    rw [P.C_eq_zero_of_const hM0]
    simp
  have key := P.norm_le_augmentedPD_of_bounds h hM hKp.isHermitian.isSymm hd hd' hR hε hlam hμ
    hkp0 hκp0.le hkv0 (fun t _ z _ v => hM0 (θd t + z.1) ▸ hMl v)
    (fun t _ z _ v₁ v₂ => hM0 (θd t + z.1) ▸ hMb v₁ v₂) hCu hkp (fun v => hκpb v) hkv hκv hεμ
    hεc ht₀ hx hx₀' ht
  rw [sub_pair, sub_pair] at key
  exact key

/-- **For constant inertia the tracking-error system of (4.53) is linear (MLS (4.54) with
`C = 0`, p. 194):** if `M(q) = M₀` is positive definite for every `q`, the error system of the
closed loop relative to `(θ_d, θ̇_d)` is `(e, ė) ↦ (ė, M₀⁻¹(−K_v ė − K_p e))` at every time, the
linear field `pdLinearPart M₀ K_p K_v`; `θ̈_d` and `N` cancel. -/
theorem errorSystem_augmentedPD_of_const {M₀ : Matrix (Fin n) (Fin n) ℝ} (hM0 : ∀ q, P.M q = M₀)
    (hM₀ : M₀.PosDef) (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd θd' θd'' : ℝ → Fin n → ℝ) :
    Stability.errorSystem (P.field (P.augmentedPDTorque Kp Kv θd θd' θd''))
        (fun t => (θd t, θd' t)) (fun t => (θd' t, θd'' t)) =
      fun _ z => pdLinearPart M₀ Kp Kv z := by
  funext t z
  rw [pdLinearPart_apply]
  simp only [Stability.errorSystem, field, augmentedPDTorque, hM0, P.C_eq_zero_of_const hM0,
    Prod.fst_add, Prod.snd_add, add_sub_cancel_right, Matrix.zero_mulVec, add_zero, sub_zero,
    Prod.mk_sub_mk, Prod.mk.injEq, true_and]
  have e : M₀ *ᵥ θd'' t + P.N (z.1 + θd t) (z.2 + θd' t) - Kv *ᵥ z.2 - Kp *ᵥ z.1 -
      P.N (z.1 + θd t) (z.2 + θd' t) = M₀ *ᵥ θd'' t + (-(Kv *ᵥ z.2) - Kp *ᵥ z.1) := by abel
  rw [e, Matrix.mulVec_add, Control.PosDef.inv_mulVec_mulVec hM₀, add_sub_cancel_left]

end ManipulatorModel
end RoboLean
