import RoboLean.Dynamics.MassMatrixDerivative
import RoboLean.Control.Stability
import RoboLean.Control.MatrixAnalysis
import Mathlib.Topology.Instances.Matrix

/-!
# The manipulator as a first-order system (MLS §5.1, eq. (4.47), p. 190)

MLS states the control problem for `M(θ) θ̈ + C(θ, θ̇) θ̇ + N(θ, θ̇) = τ` (eq. (4.47), p. 190).
Here:

* a `ManipulatorModel n` is an `InertialChain n` with link masses, a gravitational constant, an
  upward vector and a field `Nₑ(θ, θ̇)` of further joint forces (for example friction, MLS p. 170);
* `M` is the manipulator inertia matrix (4.19), `C` the Christoffel Coriolis matrix (4.23) built
  from the actual partial derivatives of `M` (E013), and `N(θ, θ̇) = ∂V/∂θ + Nₑ(θ, θ̇)` with `V` the
  gravitational potential energy (p. 169);
* `EquationsOfMotionAt θ τ t` is Lagrange's equations (Theorem 4.1, E013's predicate) for
  `L = T − V` with generalized force `τ − Nₑ`, and it is equivalent to (4.47) at `t`
  (`equationsOfMotionAt_iff`; only symmetric link inertias are assumed);
* `field u` is the first-order system `ẋ = f(t, x)` of MLS eq. (4.31) on the state
  `x = (θ, θ̇) ∈ ℝⁿ × ℝⁿ` under a feedback law `τ = u(t, θ, θ̇)`:
  `f(t, (q, v)) = (v, M(q)⁻¹ (u(t, q, v) − C(q, v) v − N(q, v)))`. With `M(q)` positive definite,
  its solutions (`Stability.IsSolution`) are exactly the motions satisfying (4.47) with
  `τ = u(t, θ, θ̇)` at every `t > t₀` (`equationsOfMotionAt_of_isSolution`,
  `isSolution_of_equationsOfMotionAt`).

MLS assumes that arbitrary joint torques can be commanded (p. 189); nothing here models actuator
limits, sampling or model error. The state norm is the sup norm of `(Fin n → ℝ) × (Fin n → ℝ)`.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean

/-! ### The model (MLS eq. (4.47), p. 190) -/

/-- **The manipulator model of MLS eq. (4.47), p. 190:** an open chain with link inertias
(`InertialChain`, p. 168), the link masses `m_k`, the gravitational constant `g`, the upward
vector `up` (gravity is `−g • up`, E013) and a field `Nₑ(θ, θ̇)` of further joint forces, such as
friction, collected with gravity in `N` (p. 170). The masses are not tied by type to the
generalized inertias. -/
structure ManipulatorModel (n : ℕ) where
  /-- The open chain with its link frames and generalized inertias (MLS p. 168). -/
  chain : InertialChain n
  /-- The link masses `m_k` (MLS p. 169). -/
  mass : Fin n → ℝ
  /-- The gravitational constant `g` (MLS p. 169). -/
  gravity : ℝ
  /-- The upward vector, opposite to gravity, in base coordinates (E013 convention). -/
  up : Vec3
  /-- Further joint forces `Nₑ(θ, θ̇)`, for example viscous friction (MLS p. 170). -/
  jointForce : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- The manipulator inertia matrix `M(θ)` of MLS eq. (4.19), p. 168. -/
def M (q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P.chain.massMatrix q

/-- **The manipulator inertia matrix depends continuously on the configuration** (its entries are
differentiable, MLS Proposition 4.3, p. 176, E013). -/
theorem continuous_M : Continuous P.M :=
  continuous_matrix fun i j => (P.chain.differentiable_massMatrix i j).continuous

/-- The Coriolis matrix `C(θ, θ̇)` of MLS eq. (4.23), p. 170, from the actual partial derivatives
of `M` (E013 `InertialChain.massMatrixDeriv`). -/
def C (q v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Christoffel.coriolisMatrix (Christoffel.partials (P.chain.massMatrixDeriv q)) v

/-- The term `N(θ, θ̇)` of MLS eq. (4.47), p. 190: the gravity term `∂V/∂θ` (p. 174) plus the
further joint forces `Nₑ(θ, θ̇)` (p. 170). -/
def N (q v : Fin n → ℝ) : Fin n → ℝ :=
  P.chain.gravityTerm P.mass P.gravity P.up q + P.jointForce q v

/-- The Lagrangian `L = T − V` of the manipulator in uniform gravity (MLS p. 169). -/
def lagrangian : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  P.chain.lagrangian (P.chain.potentialEnergy P.mass P.gravity P.up)

/-- **MLS eq. (4.47), p. 190, at time `t`, as Lagrange's equations (Theorem 4.1, p. 158).** The
motion `θ` under the actuator torque `τ` satisfies Lagrange's equations for `L = T − V` with
generalized force `τ − Nₑ(θ, θ̇)` (the split of p. 170), with velocity `deriv θ`. -/
def EquationsOfMotionAt (θ : ℝ → Fin n → ℝ) (τ : Fin n → ℝ) (t : ℝ) : Prop :=
  Lagrangian.LagrangeEquationsAt P.lagrangian θ (τ - P.jointForce (θ t) (deriv θ t)) t

/-- **MLS eq. (4.47), p. 190:** with symmetric link inertias, along a motion whose velocity `θ'`
near `t` and acceleration `θ''` at `t` are actual derivatives, the equations of motion hold at `t`
exactly when `M(θ) θ̈ + C(θ, θ̇) θ̇ + N(θ, θ̇) = τ`. -/
theorem equationsOfMotionAt_iff (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (τ : Fin n → ℝ) :
    P.EquationsOfMotionAt θ τ t ↔
      P.M (θ t) *ᵥ θ'' + P.C (θ t) (θ' t) *ᵥ θ' t + P.N (θ t) (θ' t) = τ := by
  have hdt : deriv θ t = θ' t := hθ.self_of_nhds.deriv
  rw [EquationsOfMotionAt, hdt, lagrangian,
    P.chain.lagrangeEquationsAt_potentialEnergy_iff h _ _ _ hθ hθ', M, C, N, ← add_assoc,
    eq_sub_iff_add_eq]

/-- **The power balance of the kinetic energy (MLS p. 172 with eq. (4.47)).** With symmetric link
inertias, along a motion satisfying the equations of motion at `t` under the torque `τ`, the
kinetic energy `T = ½ θ̇ᵀ M(θ) θ̇` has derivative `θ̇ ⬝ (τ − N(θ, θ̇))` at `t`. -/
theorem hasDerivAt_kineticEnergy (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) {τ : Fin n → ℝ}
    (hE : P.EquationsOfMotionAt θ τ t) :
    HasDerivAt (fun s => P.chain.kineticEnergy (θ s) (θ' s))
      (θ' t ⬝ᵥ (τ - P.N (θ t) (θ' t))) t := by
  have hdt : deriv θ t = θ' t := hθ.self_of_nhds.deriv
  rw [EquationsOfMotionAt, hdt] at hE
  have hH := P.chain.hasDerivAt_energy_gravity h P.mass P.gravity P.up hθ hθ' hE
  have hV := P.chain.hasDerivAt_potentialEnergy P.mass P.gravity P.up
    (hasDerivAt_pi.mp hθ.self_of_nhds)
  rw [← P.chain.gravityTerm_eq_gravityJacobian_everywhere] at hV
  have := hH.sub hV
  convert this using 1
  · funext s
    simp only [Pi.sub_apply]
    ring
  · rw [N, dotProduct_sub, dotProduct_sub, dotProduct_add]
    ring

/-! ### The state-space form `ẋ = f(t, x)` (MLS eq. (4.31) for eq. (4.47)) -/

/-- **The closed-loop first-order system of MLS eq. (4.47) under a feedback law
`τ = u(t, θ, θ̇)`,** in the form `ẋ = f(t, x)` of eq. (4.31) with state `x = (θ, θ̇)`:
`f(t, (q, v)) = (v, M(q)⁻¹ (u(t, q, v) − C(q, v) v − N(q, v)))`. The matrix inverse is Mathlib's
`Matrix.inv`; every theorem using it assumes `M(q)` positive definite. -/
def field (u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ) :
    ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun t x => (x.2, (P.M x.1)⁻¹ *ᵥ (u t x.1 x.2 - P.C x.1 x.2 *ᵥ x.2 - P.N x.1 x.2))

/-- Along a solution of the closed-loop system from `t₀`, the position has velocity `θ̇` near
every `t > t₀`. -/
theorem eventually_hasDerivAt_fst {u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ} {t₀ : ℝ}
    {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hx : Stability.IsSolution (P.field u) t₀ x) {t : ℝ}
    (ht : t₀ < t) : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => (x s).1) (x s).2 s := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact (hx.2 s hs).fst

/-- **Solutions of the first-order system satisfy the equations of motion (MLS (4.31), (4.47)).**
With symmetric link inertias and `M(q)` positive definite for every `q`, every solution `x` of
`field u` from `t₀` gives a motion `θ = x.1` with velocity `x.2` satisfying (4.47) with
`τ = u(t, θ, θ̇)` at every `t > t₀`. -/
theorem equationsOfMotionAt_of_isSolution (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ} {t₀ : ℝ}
    {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hx : Stability.IsSolution (P.field u) t₀ x) {t : ℝ}
    (ht : t₀ < t) : P.EquationsOfMotionAt (fun s => (x s).1) (u t (x t).1 (x t).2) t := by
  rw [P.equationsOfMotionAt_iff h (P.eventually_hasDerivAt_fst hx ht) (hx.2 t ht).snd]
  simp only [field]
  rw [Control.PosDef.mulVec_inv_mulVec (hM _)]
  abel

/-- **The equations of motion give solutions of the first-order system (MLS (4.31), (4.47)).**
With symmetric link inertias and `M(q)` positive definite for every `q`: if `θ` has velocity `θ'`
and `θ'` has acceleration `θ''` at every `t > t₀`, `(θ, θ')` is continuous on `[t₀, ∞)`, and (4.47)
holds with `τ = u(t, θ, θ̇)` at every `t > t₀`, then `(θ, θ')` solves `field u` from `t₀`. -/
theorem isSolution_of_equationsOfMotionAt (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ} {t₀ : ℝ}
    {θ θ' θ'' : ℝ → Fin n → ℝ} (hc : ContinuousOn (fun s => (θ s, θ' s)) (Ici t₀))
    (hθ : ∀ s, t₀ < s → HasDerivAt θ (θ' s) s) (hθ' : ∀ s, t₀ < s → HasDerivAt θ' (θ'' s) s)
    (hE : ∀ s, t₀ < s → P.EquationsOfMotionAt θ (u s (θ s) (θ' s)) s) :
    Stability.IsSolution (P.field u) t₀ (fun s => (θ s, θ' s)) := by
  refine ⟨hc, fun t ht => ?_⟩
  have hev : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hθ s hs
  have heq := (P.equationsOfMotionAt_iff h hev (hθ' t ht) _).mp (hE t ht)
  have hacc : θ'' t = (P.M (θ t))⁻¹ *ᵥ
      (u t (θ t) (θ' t) - P.C (θ t) (θ' t) *ᵥ θ' t - P.N (θ t) (θ' t)) := by
    have e : u t (θ t) (θ' t) - P.C (θ t) (θ' t) *ᵥ θ' t - P.N (θ t) (θ' t) =
        P.M (θ t) *ᵥ θ'' t := by
      rw [← heq]
      abel
    rw [e, Control.PosDef.inv_mulVec_mulVec (hM _)]
  simp only [field]
  rw [← hacc]
  exact (hθ t ht).prodMk (hθ' t ht)

/-- **Rest points of the closed loop (MLS p. 179 for eq. (4.47)).** With `M(q)` positive
definite, the state `(q, 0)` is an equilibrium of `field u` exactly when the feedback law
balances the static joint forces there: `u(t, q, 0) = N(q, 0)` for every `t`. -/
theorem isEquilibrium_field_iff (u : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ)
    {q : Fin n → ℝ} (hM : (P.M q).PosDef) :
    Stability.IsEquilibrium (P.field u) (q, 0) ↔ ∀ t, u t q 0 = P.N q 0 := by
  simp only [Stability.IsEquilibrium, field, Matrix.mulVec_zero, sub_zero, Prod.mk_eq_zero,
    true_and]
  refine forall_congr' fun t => ⟨fun h0 => ?_, fun h0 => by rw [h0, sub_self, Matrix.mulVec_zero]⟩
  have := Control.PosDef.mulVec_inv_mulVec hM (u t q 0 - P.N q 0)
  rw [h0, Matrix.mulVec_zero] at this
  exact sub_eq_zero.mp this.symm

end ManipulatorModel
end RoboLean
