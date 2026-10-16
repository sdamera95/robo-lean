import RoboLean.Control.ComputedTorque
import RoboLean.Control.AugmentedPD

/-!
# The book's "robot" `(M, C, N)` and computed torque for it (MLS §6.5, Proposition 4.8)

MLS Chapter 6, §5, printed pp. 300–303, with Proposition 4.8
(p. 192).

**What MLS states.** For a constrained robot system `M(q) ẍ + C(q, q̇) ẋ + N(q, q̇) = F` (p. 300),
"we also assume that `M(q) > 0` for all `q` and that `Ṁ − 2C` is a skew-symmetric matrix. These
properties hold for all of the systems given in this chapter"; "since the only essential properties
required by the proofs of convergence are that `M(q)` be positive definite and `Ṁ − 2C`
skew-symmetric, all of the previous proofs apply directly" (p. 301), and the computed torque
controller "becomes `F = M(q)(ẍ_d − K_v ė − K_p e) + C(q, q̇) ẋ + N(q, q̇)`". On p. 303 a *robot* is
"a dynamical system whose equations of motion have the form `M(q) q̈ + C(q, q̇) q̇ + N(q, q̇) = F`.
The quantities `M`, `C`, and `N` completely parameterize the dynamics of the mechanism."

**Formalized.**

* `Control.RobotSystem p`: the triple `(M, C, N)` on `x ∈ ℝᵖ` (`Fin p → ℝ`), with no structural
  hypothesis in the structure; the two properties are separate statements: `M(x)` positive definite
  (a hypothesis where used) and `HasSkewProperty` (`Ṁ − 2C` skew along every motion).
* The first-order system `field u` of a feedback law (MLS eq. (4.31)) and the computed torque law
  `computedTorque` (MLS eq. (4.49) with the book's `C ẋ + N`).
* **Proposition 4.8 for every robot** (`computedTorque_tracking`, and for motions satisfying the
  equations, `computedTorque_tracking_of_equations`), proved from one time-varying core
  (`Control.computedTorque_tracking_along`): along any motion whose equations of motion
  `M(s) ẍ + C(s) ẋ + N(s) = F` hold with the computed-torque input and `M(s)` positive definite, the
  tracking error decays exponentially. Only positive definiteness is used; the skew property is not
  needed by computed torque (it is needed by the PD-type laws, not formalized here).
* `ManipulatorModel.toRobotSystem`: the open-chain manipulator model (4.47) is a robot; its field
  and computed torque law are those of `ManipulatorModel` by definition (`toRobotSystem_field`,
  `toRobotSystem_computedTorque`) and it has the skew property for symmetric link inertias
  (`toRobotSystem_hasSkewProperty`, Lemma 4.2(2)).

The time-varying core covers the case MLS notes on p. 301, "in this controller `M(q)` depends on
both `θ` and `x`": the matrices may depend on time through coordinates that are not part of the
robot's state. The robot's inputs and outputs (`x_d`, `F_d`; `x`, `F`, p. 303) and the `attach` and
`control` operations (pp. 304–306) are not formalized here. Exact model cancellation is assumed, as
in MLS; nothing here concerns model error, sampling or actuator limits. Norms are the sup norms of
`Fin p → ℝ` and of products.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace Control

/-- **The book's robot `(M, C, N)` (MLS printed p. 303):** "a dynamical system whose equations of
motion have the form `M(q) q̈ + C(q, q̇) q̇ + N(q, q̇) = F`", on the configuration `x ∈ ℝᵖ` (MLS's
`x` of p. 300). No structural property is part of the structure: positive definiteness of `M` is a
hypothesis where used and the skew property is `HasSkewProperty`. -/
structure RobotSystem (p : ℕ) where
  /-- The inertia matrix `M(x)` (MLS p. 303). -/
  M : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ
  /-- The Coriolis matrix `C(x, ẋ)` (MLS p. 303). -/
  C : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ
  /-- The gravitational and nonconservative forces `N(x, ẋ)` (MLS p. 303). -/
  N : (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ

/-- **The computed torque law of MLS eq. (4.49), p. 191, as a function of time,** for matrix curves:
`F(s) = M(s)(ẍ_d − K_v (ẋ − ẋ_d) − K_p (x − x_d)) + C(s) ẋ + N(s)` (MLS p. 301 for constrained
systems). -/
def computedTorqueAlong (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (Mt Ct : Matrix (Fin p) (Fin p) ℝ)
    (Nt : Fin p → ℝ) (xd xd' xd'' x x' : Fin p → ℝ) : Fin p → ℝ :=
  Mt *ᵥ (xd'' - Kv *ᵥ (x' - xd') - Kp *ᵥ (x - xd)) + Ct *ᵥ x' + Nt

/-- **MLS Proposition 4.8, p. 192, the time-varying core of the proof (MLS p. 301, "all of the
previous proofs apply directly").** For `K_p`, `K_v` symmetric positive definite there are
`m, α > 0`, depending only on the gains, such that: for every desired trajectory with actual
derivatives `ẋ_d`, `ẍ_d`, every `t₀ ≥ 0`, every motion `x` with velocity `x'` and acceleration `x''`
at every `t > t₀` and `(x, x')` continuous on `[t₀, ∞)`, and all matrix and vector curves `M(s)`,
`C(s)`, `N(s)` with `M(s)` positive definite for `s > t₀`: if `M(s) ẍ + C(s) ẋ + N(s) = F(s)` with
the computed torque `F(s)` of (4.49) for every `s > t₀`, then
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀`, `e = x − x_d`. -/
theorem computedTorque_tracking_along {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef)
    (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ (x x' x'' : ℝ → Fin p → ℝ)
      (Mt Ct : ℝ → Matrix (Fin p) (Fin p) ℝ) (Nt : ℝ → Fin p → ℝ),
      ContinuousOn (fun s => (x s, x' s)) (Ici t₀) → (∀ s, t₀ < s → HasDerivAt x (x' s) s) →
      (∀ s, t₀ < s → HasDerivAt x' (x'' s) s) → (∀ s, t₀ < s → (Mt s).PosDef) →
      (∀ s, t₀ < s → Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
        computedTorqueAlong Kp Kv (Mt s) (Ct s) (Nt s) (xd s) (xd' s) (xd'' s) (x s) (x' s)) →
      ∀ t, t₀ ≤ t → ‖(x t - xd t, x' t - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(x t₀ - xd t₀, x' t₀ - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, hexp⟩ := globallyExponentiallyStable_errorField hKp hKv
  refine ⟨m, hm, α, hα, fun {xd xd' xd''} hd hd' t₀ ht₀ x x' x'' Mt Ct Nt hc hx hx' hM hE t ht =>
    ?_⟩
  have hdc : Continuous xd := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hdc' : Continuous xd' := continuous_iff_continuousAt.mpr fun t => (hd' t).continuousAt
  have hsol : Stability.IsSolution (errorField Kp Kv) t₀
      (fun s => (x s - xd s, x' s - xd' s)) := by
    refine ⟨((continuous_fst.comp_continuousOn hc).sub hdc.continuousOn).prodMk
      ((continuous_snd.comp_continuousOn hc).sub hdc'.continuousOn), fun s hs => ?_⟩
    have hacc : x'' s = xd'' s - Kv *ᵥ (x' s - xd' s) - Kp *ᵥ (x s - xd s) := by
      have h1 := hE s hs
      rw [computedTorqueAlong, add_left_inj, add_left_inj] at h1
      rw [← PosDef.inv_mulVec_mulVec (hM s hs) (x'' s), h1, PosDef.inv_mulVec_mulVec (hM s hs)]
    have h1 := (hx s hs).sub (hd s)
    have h2 := (hx' s hs).sub (hd' s)
    rw [hacc] at h2
    convert h1.prodMk h2 using 1
    simp only [errorField, Prod.mk.injEq, true_and]
    abel
  simpa using hexp t₀ ht₀ _ hsol t ht

/-- **`Ṁ − 2C` is skew-symmetric along every motion (MLS printed p. 300; Lemma 4.2(2), p. 171; Lemma
6.1(2), p. 279),** for an inertia field `M(x)` and a Coriolis field `C(x, ẋ)` of `k × k` matrices on
configurations `x ∈ ℝᵖ`: for every motion `x` with velocity `x'` at `t` and every actual entrywise
derivative `Ṁ` of `s ↦ M(x(s))` at `t`, `Ṁ − 2C(x(t), x')` is skew-symmetric. For a robot `k = p`
(`RobotSystem.HasSkewProperty`); `k ≠ p` covers finger fields written in object coordinates. -/
def SkewAlongMotions {p k : ℕ} (M : (Fin p → ℝ) → Matrix (Fin k) (Fin k) ℝ)
    (C : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ} {Md : Matrix (Fin k) (Fin k) ℝ},
    HasDerivAt x x' t → (∀ i j, HasDerivAt (fun s => M (x s) i j) (Md i j) t) →
      (Md - (2 : ℝ) • C (x t) x')ᵀ = -(Md - (2 : ℝ) • C (x t) x')

namespace RobotSystem

variable {p : ℕ} (R : RobotSystem p)

/-- **The closed-loop first-order system of a robot under a feedback law `F = u(t, x, ẋ)`** (MLS eq.
(4.31) for the robot of p. 303): `f(t, (x, v)) = (v, M(x)⁻¹ (u(t, x, v) − C(x, v) v − N(x, v)))` on
the state `(x, ẋ)`, with Mathlib's `Matrix.inv`; every theorem using it assumes `M(x)` positive
definite. -/
def field (u : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ) :
    ℝ → (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ) :=
  fun t z => (z.2, (R.M z.1)⁻¹ *ᵥ (u t z.1 z.2 - R.C z.1 z.2 *ᵥ z.2 - R.N z.1 z.2))

/-- **The computed torque law for a robot (MLS printed p. 301, eq. (4.49)):**
`F = M(x)(ẍ_d − K_v ė − K_p e) + C(x, ẋ) ẋ + N(x, ẋ)`, `e = x − x_d`, as a feedback law `u(t, x, ẋ)`
for a desired trajectory `x_d` with velocity `x_d'` and acceleration `x_d''`. -/
def computedTorque (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd xd' xd'' : ℝ → Fin p → ℝ) :
    ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ :=
  fun t q v => computedTorqueAlong Kp Kv (R.M q) (R.C q v) (R.N q v) (xd t) (xd' t) (xd'' t) q v

/-- **Solutions of the robot's first-order system satisfy its equations of motion (MLS (4.31) for
the robot of p. 303).** With `M(x)` positive definite for every `x`, along a solution `z` of
`field u` from `t₀`, at every `t > t₀` the position `z.1` has velocity `z.2` and
`M ẍ + C ẋ + N = u(t, x, ẋ)` holds with `ẍ` the derivative of `z.2`. -/
theorem equations_of_isSolution (hM : ∀ q, (R.M q).PosDef)
    {u : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ} {t₀ : ℝ}
    {z : ℝ → (Fin p → ℝ) × (Fin p → ℝ)} (hz : Stability.IsSolution (R.field u) t₀ z) {t : ℝ}
    (ht : t₀ < t) :
    HasDerivAt (fun s => (z s).1) (z t).2 t ∧
      R.M (z t).1 *ᵥ (R.field u t (z t)).2 + R.C (z t).1 (z t).2 *ᵥ (z t).2 +
        R.N (z t).1 (z t).2 = u t (z t).1 (z t).2 := by
  refine ⟨(hz.2 t ht).fst, ?_⟩
  simp only [field]
  rw [PosDef.mulVec_inv_mulVec (hM _)]
  abel

/-- **The robot's equations of motion give solutions of its first-order system (MLS eq. (4.31), p.
179, for the robot of p. 303).** With `M(x)` positive definite for every `x`: if `x` has velocity
`x'` and `x'` has acceleration `x''` at every `t > t₀`, `(x, x')` is continuous on `[t₀, ∞)` and
`M ẍ + C ẋ + N = u(t, x, ẋ)` at every `t > t₀`, then `(x, x')` solves `field u` from `t₀`. -/
theorem isSolution_of_equations (hM : ∀ q, (R.M q).PosDef)
    {u : ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ} {t₀ : ℝ} {x x' x'' : ℝ → Fin p → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Ici t₀))
    (hx : ∀ s, t₀ < s → HasDerivAt x (x' s) s) (hx' : ∀ s, t₀ < s → HasDerivAt x' (x'' s) s)
    (hE : ∀ s, t₀ < s →
      R.M (x s) *ᵥ x'' s + R.C (x s) (x' s) *ᵥ x' s + R.N (x s) (x' s) = u s (x s) (x' s)) :
    Stability.IsSolution (R.field u) t₀ (fun s => (x s, x' s)) := by
  refine ⟨hc, fun t ht => ?_⟩
  have hacc : x'' t = (R.M (x t))⁻¹ *ᵥ
      (u t (x t) (x' t) - R.C (x t) (x' t) *ᵥ x' t - R.N (x t) (x' t)) := by
    have e : u t (x t) (x' t) - R.C (x t) (x' t) *ᵥ x' t - R.N (x t) (x' t) =
        R.M (x t) *ᵥ x'' t := by
      rw [← hE t ht]
      abel
    rw [e, PosDef.inv_mulVec_mulVec (hM _)]
  simp only [field]
  rw [← hacc]
  exact (hx t ht).prodMk (hx' t ht)

/-- **MLS Proposition 4.8, p. 192, for a robot (MLS printed p. 301: "we can use any of the
controllers derived for open-chain manipulators to asymptotically track a trajectory `x_d(t)`").**
With `M(x)` positive definite for every `x` and `K_p`, `K_v` symmetric positive definite, there are
`m, α > 0`, depending only on the gains, such that for every desired trajectory with actual
derivatives `ẋ_d`, `ẍ_d` every solution `z = (x, ẋ)` from `t₀ ≥ 0` of the robot under the computed
torque law satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀`. -/
theorem computedTorque_tracking (hM : ∀ q, (R.M q).PosDef) {Kp Kv : Matrix (Fin p) (Fin p) ℝ}
    (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ z : ℝ → (Fin p → ℝ) × (Fin p → ℝ),
      Stability.IsSolution (R.field (R.computedTorque Kp Kv xd xd' xd'')) t₀ z →
      ∀ t, t₀ ≤ t → ‖((z t).1 - xd t, (z t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((z t₀).1 - xd t₀, (z t₀).2 - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := computedTorque_tracking_along hKp hKv
  refine ⟨m, hm, α, hα, fun {xd xd' xd''} hd hd' t₀ ht₀ z hz t ht => ?_⟩
  have hc : ContinuousOn (fun s => ((z s).1, (z s).2)) (Ici t₀) := hz.1
  exact htrack hd hd' t₀ ht₀ (fun s => (z s).1) (fun s => (z s).2)
    (fun s => (R.field (R.computedTorque Kp Kv xd xd' xd'') s (z s)).2) (fun s => R.M (z s).1)
    (fun s => R.C (z s).1 (z s).2) (fun s => R.N (z s).1 (z s).2) hc
    (fun s hs => (R.equations_of_isSolution hM hz hs).1) (fun s hs => (hz.2 s hs).snd)
    (fun s _ => hM _) (fun s hs => (R.equations_of_isSolution hM hz hs).2) t ht

/-- **MLS Proposition 4.8, p. 192, for a robot, along motions satisfying its equations of motion.**
With `M(x)` positive definite for every `x` and `K_p`, `K_v` symmetric positive definite, there are
`m, α > 0` such that for every desired trajectory as in `computedTorque_tracking` and every motion
`x` with velocity `x'` and acceleration `x''` at every `t > t₀ ≥ 0`, `(x, x')` continuous on
`[t₀, ∞)`, satisfying `M ẍ + C ẋ + N = F` under the computed torque law at every `t > t₀`, the
tracking error obeys the exponential bound for `t ≥ t₀`. -/
theorem computedTorque_tracking_of_equations (hM : ∀ q, (R.M q).PosDef)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x x' x'' : ℝ → Fin p → ℝ,
      ContinuousOn (fun s => (x s, x' s)) (Ici t₀) → (∀ s, t₀ < s → HasDerivAt x (x' s) s) →
      (∀ s, t₀ < s → HasDerivAt x' (x'' s) s) →
      (∀ s, t₀ < s → R.M (x s) *ᵥ x'' s + R.C (x s) (x' s) *ᵥ x' s + R.N (x s) (x' s) =
        R.computedTorque Kp Kv xd xd' xd'' s (x s) (x' s)) →
      ∀ t, t₀ ≤ t → ‖(x t - xd t, x' t - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(x t₀ - xd t₀, x' t₀ - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := computedTorque_tracking_along hKp hKv
  exact ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x x' x'' hc hx hx' hE t ht =>
    htrack hd hd' t₀ ht₀ x x' x'' (fun s => R.M (x s)) (fun s => R.C (x s) (x' s))
      (fun s => R.N (x s) (x' s)) hc hx hx' (fun s _ => hM _) hE t ht⟩

/-- **The skew property of a robot (MLS printed p. 300, "`Ṁ − 2C` is a skew-symmetric matrix"; Lemma
4.2(2), p. 171; Lemma 6.1(2), p. 279), along motions** (`Control.SkewAlongMotions` for `M`, `C`). -/
def HasSkewProperty : Prop :=
  SkewAlongMotions R.M R.C

end RobotSystem
end Control

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **The open-chain manipulator (4.47) as a robot (MLS printed p. 303: "we model an actuated,
open-chain manipulator" as a robot):** `M`, `C`, `N` of `ManipulatorModel` (MLS eqs. (4.19),
(4.23), p. 170). -/
def toRobotSystem : Control.RobotSystem n :=
  ⟨P.M, P.C, P.N⟩

/-- **The robot's first-order system is the closed loop of MLS eq. (4.47) of `ManipulatorModel`**
(eq. (4.31)), by definition. -/
theorem toRobotSystem_field (u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ) :
    P.toRobotSystem.field u = P.field u :=
  rfl

/-- **The robot's computed torque law is the law of `ManipulatorModel`, MLS eq. (4.49), p. 191**, by
definition. -/
theorem toRobotSystem_computedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ)
    (θd θd' θd'' : ℝ → Fin n → ℝ) :
    P.toRobotSystem.computedTorque Kp Kv θd θd' θd'' = P.computedTorque Kp Kv θd θd' θd'' :=
  rfl

/-- **The open-chain manipulator has the skew property (MLS Lemma 4.2(2), p. 171)** for symmetric
link inertias: along every motion, every actual derivative of `s ↦ M(θ(s))` minus `2C` is
skew-symmetric (`Ṁ = C + Cᵀ`, `Mdot_sub_C`). -/
theorem toRobotSystem_hasSkewProperty (h : ∀ k, (P.chain.linkInertia k).IsSymm) :
    P.toRobotSystem.HasSkewProperty := by
  intro x x' t Md hx hMd
  have hMd' : Md = P.Mdot (x t) x' := by
    ext i j
    exact (hMd i j).unique (P.hasDerivAt_M_comp hx i j)
  have hs := P.Mdot_sub_C h (x t) x'
  change (Md - (2 : ℝ) • P.C (x t) x')ᵀ = -(Md - (2 : ℝ) • P.C (x t) x')
  have hMeq : Md = P.C (x t) x' + (P.C (x t) x')ᵀ := by
    rw [hMd', ← hs]
    abel
  rw [hMeq, two_smul, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_add,
    Matrix.transpose_transpose]
  abel

end ManipulatorModel
end RoboLean
