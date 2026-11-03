import RoboLean.Dynamics.ConstrainedLagrangian
import RoboLean.Control.RobotSystem
import RoboLean.Kinematics.MapJacobian

/-!
# Control of constrained manipulators (MLS Chapter 4, §6, eqs. (4.56)–(4.63), pp. 200–202)

**What MLS prints.** A robot `M(θ) θ̈ + C(θ, θ̇) θ̇ + N(θ, θ̇) = τ` moves on a surface given by
independent smooth constraints `h_j(θ) = 0`, `j = 1, …, k` (4.56), with a smooth injective map
`f : ℝ^{n−k} → ℝⁿ` such that `h(f(φ)) = 0` (4.57). Torques `τ_N = Σ λ_j ∇h_j` (4.58) do no work
along the surface. Along `θ = f(φ)`, (4.59) `θ̇ = J φ̇`, `θ̈ = J φ̈ + J̇ φ̇` with `J = ∂f/∂φ`, and
premultiplying the substituted equations (4.60) by `Jᵀ` gives (4.62)
`M̃ φ̈ + C̃ φ̇ + Ñ = F` with `M̃ = Jᵀ M J`, `C̃ = Jᵀ (C J + M J̇)`, `Ñ = Jᵀ N`, `F = Jᵀ τ` (4.61);
"we shall show in Chapter 6 that equation (4.62) also satisfies the properties in Lemma 4.2"
(p. 201). The hybrid position/force law (4.63), p. 202, is
`τ = M J (φ̈_d − K_v ė − K_p e) + (C J + M J̇) φ̇ + N + Σ λ_i(t) ∇h_i`, `e = φ − φ_d`; "we defer the
analysis and proof of convergence for this control law until Chapter 6".

**Formalized.** Configurations `θ ∈ ℝⁿ`, surface coordinates `φ ∈ ℝᵐ` and constraint values in
`ℝᵏ` are `Fin n → ℝ`, `Fin m → ℝ`, `Fin k → ℝ`; `∂f/∂φ` and `∂h/∂θ` are `MapJacobian.jac` (rows of
`∂h/∂θ` are the gradients `∇h_j`) and `J̇ = MapJacobian.jacDot f φ φ̇`. The robot is any
`Control.RobotSystem n`.

* `IsSurfaceParametrization h f`: the hypotheses of (4.56)–(4.57) as a structure: `h` and `f` of
  class `C²`, `f` injective, `h ∘ f = 0`, the gradients `∇h_j` independent on the surface,
  `m + k = n`, and `∂f/∂φ` onto the tangent space `ker ∂h/∂θ` of the level set. Consequences:
  `∂h/∂θ · ∂f/∂φ = 0`, `Jᵀ ∇h_j = 0`, and `J` injective.
* (4.58): normal torques do no work along any motion that stays on the surface.
* (4.61)–(4.62): `projectedM`, `projectedC`, `projectedN`; the constrained equations of motion
  `M θ̈ + C θ̇ + N + (∂h/∂θ)ᵀ μ = τ` (the library's multiplier sign of (6.4)) along `θ = f(φ)` imply
  (4.62), and conversely (4.62) gives a multiplier `μ`.
* The properties of Lemma 4.2 for (4.62), deferred by the book to Chapter 6: `M̃` symmetric and
  positive definite, and `J̇ᵀ M J + Jᵀ Ṁ J + Jᵀ M J̇ − 2 C̃` skew-symmetric when `Ṁ − 2C` is.
* (4.63): `hybridTorque`; the closed-loop identity: under the constrained equations the error obeys
  `ë + K_v ė + K_p e = 0` and the constraint multiplier equals the commanded `λ`; and exponential
  tracking of `(e, ė)` with `μ = λ` along every closed-loop motion (Proposition 4.8's route,
  `Control.computedTorque_tracking_along`).

**Differences from the page.** Smoothness is `C²`, which is what the statements use. The
hypotheses "independent" and `m = n − k` are explicit; the tangent-space condition (the derivative
of `f` onto `ker ∂h/∂θ`) is the formal content of "`φ` parameterizes the allowable motion on the
surface". `M(θ)` positive definite is a hypothesis where used. Motions on the surface are taken in
the form `θ = f ∘ φ`; that every motion on the surface has this form is not claimed. Exact model
cancellation is assumed, as in MLS; nothing here concerns friction, unilateral contact, model
error or sampling.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace Control

open MapJacobian

variable {n m k : ℕ}

/-- **The constraint surface and its parameterization (MLS eqs. (4.56)–(4.57), p. 200):**
independent smooth constraints `h_j(θ) = 0`, `j = 1, …, k`, and a smooth injective map
`f : ℝ^{n−k} → ℝⁿ` with `h(f(φ)) = 0` whose derivative is onto the tangent space of the level set.
Smoothness is taken as `C²`. -/
structure IsSurfaceParametrization (h : (Fin n → ℝ) → Fin k → ℝ)
    (f : (Fin m → ℝ) → Fin n → ℝ) : Prop where
  /-- The constraints are smooth, taken as `C²` (MLS (4.56), p. 200). -/
  contDiff_h : ContDiff ℝ 2 h
  /-- The parameterization is smooth, taken as `C²` (MLS (4.57), p. 200). -/
  contDiff_f : ContDiff ℝ 2 f
  /-- The parameterization is injective (MLS p. 200). -/
  injective : Function.Injective f
  /-- `h_j(f(φ)) = 0`, MLS eq. (4.57), p. 200. -/
  comp_eq_zero : ∀ φ, h (f φ) = 0
  /-- The constraints are independent on the surface: the gradients `∇h_j(f(φ))` are linearly
  independent (MLS p. 200). -/
  independent : ∀ φ, LinearIndependent ℝ (jac h (f φ)).row
  /-- The parameter space has dimension `n − k` (MLS p. 200, `f : ℝ^{n−k} → ℝⁿ`). -/
  dim_eq : m + k = n
  /-- `φ` parameterizes the allowable motion (MLS p. 200): the derivative of `f` is onto the
  tangent space `{v : ∂h/∂θ v = 0}` of the level set. -/
  tangent_mem_range : ∀ φ v, jac h (f φ) *ᵥ v = 0 → ∃ w, jac f φ *ᵥ w = v

namespace IsSurfaceParametrization

variable {h : (Fin n → ℝ) → Fin k → ℝ} {f : (Fin m → ℝ) → Fin n → ℝ}

/-- Differentiating `h(f(φ)) = 0` (MLS eq. (4.57), p. 200): `∂h/∂θ (f(φ)) · ∂f/∂φ (φ) = 0`, so the
columns of `J` are tangent to the surface. -/
theorem jac_mul_jac_eq_zero (hp : IsSurfaceParametrization h f) (φ : Fin m → ℝ) :
    jac h (f φ) * jac f φ = 0 := by
  have hfd : DifferentiableAt ℝ f φ := (hp.contDiff_f.differentiable (by norm_num)) φ
  have hhd : DifferentiableAt ℝ h (f φ) := (hp.contDiff_h.differentiable (by norm_num)) (f φ)
  have h0 : fderiv ℝ (h ∘ f) φ = 0 := by
    rw [show h ∘ f = fun _ => 0 from funext hp.comp_eq_zero]
    exact fderiv_const_apply _
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← Matrix.mulVec_mulVec, jac_mulVec,
    jac_mulVec, ← ContinuousLinearMap.comp_apply, ← fderiv_comp φ hhd hfd, h0]
  rfl

/-- The normal torques `τ_N = Σ λ_j ∇h_j` of MLS eq. (4.58), p. 200, are annihilated by `Jᵀ`:
`Jᵀ (∂h/∂θ)ᵀ λ = 0`, "by pre-multiplying by `Jᵀ`, we have eliminated the information about the
forces of constraint" (p. 201). -/
theorem transpose_mulVec_normal (hp : IsSurfaceParametrization h f) (φ : Fin m → ℝ)
    (lam : Fin k → ℝ) : (jac f φ)ᵀ *ᵥ ((jac h (f φ))ᵀ *ᵥ lam) = 0 := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hp.jac_mul_jac_eq_zero, Matrix.transpose_zero,
    Matrix.zero_mulVec]

/-- The Jacobian `J = ∂f/∂φ` of the parameterization of MLS (4.57), p. 200, is injective: `φ` are
generalized coordinates of the motion on the surface (p. 201). -/
theorem injective_jac (hp : IsSurfaceParametrization h f) (φ : Fin m → ℝ) :
    Function.Injective (jac f φ).mulVec := by
  set A := (jac f φ).mulVecLin
  set B := (jac h (f φ)).mulVecLin
  have hrange : LinearMap.range A = LinearMap.ker B := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      change jac h (f φ) *ᵥ (jac f φ *ᵥ w) = 0
      rw [Matrix.mulVec_mulVec, hp.jac_mul_jac_eq_zero, Matrix.zero_mulVec]
    · intro v hv
      obtain ⟨w, hw⟩ := hp.tangent_mem_range φ v hv
      exact ⟨w, hw⟩
  have hBt : Function.Injective ((jac h (f φ))ᵀ *ᵥ ·) :=
    (Constrained.transpose_mulVec_injective_iff _).mpr (hp.independent φ)
  have hrkB : Module.finrank ℝ (LinearMap.range B) = k := by
    have h1 : (jac h (f φ))ᵀ.rank = k := by
      unfold Matrix.rank
      rw [LinearMap.finrank_range_of_inj (f := (jac h (f φ))ᵀ.mulVecLin) hBt, Module.finrank_fin_fun]
    rw [Matrix.rank_transpose] at h1
    exact h1
  have hkerB : Module.finrank ℝ (LinearMap.ker B) = m := by
    have := LinearMap.finrank_range_add_finrank_ker B
    rw [hrkB, Module.finrank_fin_fun] at this
    have hd := hp.dim_eq
    omega
  have hkerA : Module.finrank ℝ (LinearMap.ker A) = 0 := by
    have := LinearMap.finrank_range_add_finrank_ker A
    rw [hrange, hkerB, Module.finrank_fin_fun] at this
    omega
  have hbot : LinearMap.ker A = ⊥ := Submodule.finrank_eq_zero.mp hkerA
  exact LinearMap.ker_eq_bot.mp hbot

end IsSurfaceParametrization

/-- **MLS eq. (4.58), p. 200: normal torques do no work.** For every motion `θ` that stays on the
level set `h = 0` and has velocity `θ'` at `t`, with `h` differentiable at `θ(t)`,
`τ_N · θ̇ = Σ λ_i ∇h_i · θ̇ = Σ λ_i (d/dt) h_i(θ) = 0`. -/
theorem normalTorque_dotProduct_eq_zero {h : (Fin n → ℝ) → Fin k → ℝ} {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hh : DifferentiableAt ℝ h (θ t)) (hθ : HasDerivAt θ θ' t)
    (hon : ∀ s, h (θ s) = 0) (lam : Fin k → ℝ) :
    ((jac h (θ t))ᵀ *ᵥ lam) ⬝ᵥ θ' = 0 := by
  have h1 := hasDerivAt_comp hh hθ
  have h2 : HasDerivAt (fun s => h (θ s)) 0 t := by
    rw [show (fun s => h (θ s)) = fun _ => 0 from funext hon]
    exact hasDerivAt_const t 0
  have hz : jac h (θ t) *ᵥ θ' = 0 := h1.unique h2
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hz, dotProduct_zero]

namespace RobotSystem

variable (R : RobotSystem n)

/-- **The projected inertia matrix `M̃(φ) = Jᵀ M(f(φ)) J`, MLS eq. (4.61), p. 201.** -/
def projectedM (f : (Fin m → ℝ) → Fin n → ℝ) (φ : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (jac f φ)ᵀ * R.M (f φ) * jac f φ

/-- **The projected Coriolis matrix `C̃(φ, φ̇) = Jᵀ (C(f(φ), J φ̇) J + M(f(φ)) J̇)`, MLS eq. (4.61),
p. 201,** with `J̇ = MapJacobian.jacDot f φ φ̇`. -/
def projectedC (f : (Fin m → ℝ) → Fin n → ℝ) (φ φ' : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (jac f φ)ᵀ * (R.C (f φ) (jac f φ *ᵥ φ') * jac f φ + R.M (f φ) * jacDot f φ φ')

/-- **The projected force `Ñ(φ, φ̇) = Jᵀ N(f(φ), J φ̇)`, MLS eq. (4.61), p. 201.** -/
def projectedN (f : (Fin m → ℝ) → Fin n → ℝ) (φ φ' : Fin m → ℝ) : Fin m → ℝ :=
  (jac f φ)ᵀ *ᵥ R.N (f φ) (jac f φ *ᵥ φ')

/-- **The equations of motion of the robot on the constraint surface at one time (MLS p. 200 with
(6.4), p. 269):** `M(θ) θ̈ + C(θ, θ̇) θ̇ + N(θ, θ̇) + (∂h/∂θ)ᵀ μ = τ`, with the frictionless
constraint force `−(∂h/∂θ)ᵀ μ` normal to the surface (library sign of (6.4)). -/
def ConstrainedEquationsAt (h : (Fin n → ℝ) → Fin k → ℝ) (θ θ' θ'' τ : Fin n → ℝ)
    (μ : Fin k → ℝ) : Prop :=
  R.M θ *ᵥ θ'' + R.C θ θ' *ᵥ θ' + R.N θ θ' + (jac h θ)ᵀ *ᵥ μ = τ

/-- **MLS eq. (4.59), p. 201:** along `θ = f(φ)` with `f` of class `C²`, `θ̇ = J φ̇` and
`θ̈ = J φ̈ + J̇ φ̇`, as actual derivatives. -/
theorem hasDerivAt_comp_surface {f : (Fin m → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    {φ φ' : ℝ → Fin m → ℝ} {φ'' : Fin m → ℝ} {t : ℝ} (hφ : ∀ s, HasDerivAt φ (φ' s) s)
    (hφ' : HasDerivAt φ' φ'' t) :
    HasDerivAt (fun s => f (φ s)) (jac f (φ t) *ᵥ φ' t) t ∧
      HasDerivAt (fun s => jac f (φ s) *ᵥ φ' s)
        (jac f (φ t) *ᵥ φ'' + jacDot f (φ t) (φ' t) *ᵥ φ' t) t := by
  refine ⟨hasDerivAt_comp ((hf.differentiable (by norm_num)) (φ t)) (hφ t), ?_⟩
  have := hasDerivAt_jac_mulVec_comp hf (hφ t) hφ'
  rwa [add_comm] at this

/-- **MLS eqs. (4.60)–(4.62), pp. 201: the projected equations of motion.** If the robot satisfies
its constrained equations of motion at `θ = f(φ)`, `θ̇ = J φ̇`, `θ̈ = J φ̈ + J̇ φ̇` with some
multiplier `μ`, then `M̃ φ̈ + C̃ φ̇ + Ñ = Jᵀ τ`: premultiplying by `Jᵀ` removes the constraint force. -/
theorem projected_eq_of_constrainedEquationsAt {h : (Fin n → ℝ) → Fin k → ℝ}
    {f : (Fin m → ℝ) → Fin n → ℝ} (hp : IsSurfaceParametrization h f) {φ φ' φ'' : Fin m → ℝ}
    {τ : Fin n → ℝ} {μ : Fin k → ℝ}
    (hE : R.ConstrainedEquationsAt h (f φ) (jac f φ *ᵥ φ')
      (jac f φ *ᵥ φ'' + jacDot f φ φ' *ᵥ φ') τ μ) :
    R.projectedM f φ *ᵥ φ'' + R.projectedC f φ φ' *ᵥ φ' + R.projectedN f φ φ' =
      (jac f φ)ᵀ *ᵥ τ := by
  rw [← hE]
  simp only [projectedM, projectedC, projectedN, Matrix.mulVec_add, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hp.transpose_mulVec_normal, add_zero]
  abel

/-- **The converse of (4.62) (MLS p. 201):** if the projected equations hold, there is a multiplier
`μ` with which the robot satisfies its constrained equations of motion at `θ = f(φ)`: the
component of the equations of motion normal to the surface is a constraint force. -/
theorem exists_constrainedEquationsAt_of_projected {h : (Fin n → ℝ) → Fin k → ℝ}
    {f : (Fin m → ℝ) → Fin n → ℝ} (hp : IsSurfaceParametrization h f) {φ φ' φ'' : Fin m → ℝ}
    {τ : Fin n → ℝ}
    (hE : R.projectedM f φ *ᵥ φ'' + R.projectedC f φ φ' *ᵥ φ' + R.projectedN f φ φ' =
      (jac f φ)ᵀ *ᵥ τ) :
    ∃ μ : Fin k → ℝ, R.ConstrainedEquationsAt h (f φ) (jac f φ *ᵥ φ')
      (jac f φ *ᵥ φ'' + jacDot f φ φ' *ᵥ φ') τ μ := by
  set θ'' := jac f φ *ᵥ φ'' + jacDot f φ φ' *ᵥ φ'
  set r := τ - (R.M (f φ) *ᵥ θ'' + R.C (f φ) (jac f φ *ᵥ φ') *ᵥ (jac f φ *ᵥ φ') +
    R.N (f φ) (jac f φ *ᵥ φ'))
  have hJr : (jac f φ)ᵀ *ᵥ r = 0 := by
    simp only [r, θ'', Matrix.mulVec_sub, ← hE]
    simp only [projectedM, projectedC, projectedN, Matrix.mulVec_add, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec]
    abel
  have hw : Constrained.DoesNoVirtualWork (jac h (f φ)) r := by
    intro δq hδ
    obtain ⟨w, rfl⟩ := hp.tangent_mem_range φ δq hδ
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hJr, zero_dotProduct]
  obtain ⟨μ, hμ⟩ := (Constrained.doesNoVirtualWork_iff_exists _ _).mp hw
  refine ⟨μ, ?_⟩
  rw [ConstrainedEquationsAt, hμ]
  simp only [r]
  abel

/-- **Lemma 4.2(1) for (4.62) (MLS p. 201, proved by the book in Chapter 6):** `M̃ = Jᵀ M J` is
symmetric where `M` is. -/
theorem projectedM_isSymm (f : (Fin m → ℝ) → Fin n → ℝ) {φ : Fin m → ℝ}
    (hM : (R.M (f φ)).IsSymm) : (R.projectedM f φ).IsSymm := by
  change ((jac f φ)ᵀ * R.M (f φ) * jac f φ)ᵀ = (jac f φ)ᵀ * R.M (f φ) * jac f φ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM.eq,
    Matrix.mul_assoc]

/-- **Lemma 4.2(1) for (4.62) (MLS p. 201, proved by the book in Chapter 6):** `M̃ = Jᵀ M J` is
positive definite where `M` is, because `J` is injective. -/
theorem projectedM_posDef {h : (Fin n → ℝ) → Fin k → ℝ} {f : (Fin m → ℝ) → Fin n → ℝ}
    (hp : IsSurfaceParametrization h f) {φ : Fin m → ℝ} (hM : (R.M (f φ)).PosDef) :
    (R.projectedM f φ).PosDef := by
  have := Matrix.PosDef.conjTranspose_mul_mul_same hM (hp.injective_jac φ)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Lemma 4.2(2) for (4.62) (MLS p. 201, proved by the book in Chapter 6),** in the congruence
form of Lemma 6.1: with `J̇ = jacDot f φ φ̇`, a symmetric `M(f(φ))` and an `Ṁ` with `Ṁ − 2C`
skew-symmetric at `(f(φ), J φ̇)`, the matrix `J̇ᵀ M J + Jᵀ Ṁ J + Jᵀ M J̇ − 2 C̃` is skew-symmetric;
`J̇ᵀ M J + Jᵀ Ṁ J + Jᵀ M J̇` is the derivative of `M̃` along a motion with `Ṁ` that of `M`. -/
theorem skew_projectedMdot_sub_two_projectedC (f : (Fin m → ℝ) → Fin n → ℝ) {φ φ' : Fin m → ℝ}
    {Md : Matrix (Fin n) (Fin n) ℝ} (hM : (R.M (f φ))ᵀ = R.M (f φ))
    (hs : (Md - (2 : ℝ) • R.C (f φ) (jac f φ *ᵥ φ'))ᵀ =
      -(Md - (2 : ℝ) • R.C (f φ) (jac f φ *ᵥ φ'))) :
    ((jacDot f φ φ')ᵀ * R.M (f φ) * jac f φ + (jac f φ)ᵀ * Md * jac f φ +
        (jac f φ)ᵀ * R.M (f φ) * jacDot f φ φ' - (2 : ℝ) • R.projectedC f φ φ')ᵀ =
      -((jacDot f φ φ')ᵀ * R.M (f φ) * jac f φ + (jac f φ)ᵀ * Md * jac f φ +
        (jac f φ)ᵀ * R.M (f φ) * jacDot f φ φ' - (2 : ℝ) • R.projectedC f φ φ') := by
  exact Control.skew_reduced hM hs

/-- **The derivative of `M̃(φ(t))` along a motion (MLS eq. (4.61), p. 201):** for `f` of class
`C²`, a motion `φ` with velocity `φ'` at `t` and an entrywise derivative `Ṁ` of `s ↦ M(f(φ(s)))` at
`t`, every entry of `s ↦ M̃(φ(s))` has the derivative `J̇ᵀ M J + Jᵀ Ṁ J + Jᵀ M J̇` at `t`, with
`J̇ = jacDot f φ φ'`. -/
theorem hasDerivAt_projectedM_comp {f : (Fin m → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    {φ : ℝ → Fin m → ℝ} {φ' : Fin m → ℝ} {t : ℝ} (hφ : HasDerivAt φ φ' t)
    {Md : Matrix (Fin n) (Fin n) ℝ} (hMd : ∀ i j, HasDerivAt (fun s => R.M (f (φ s)) i j) (Md i j) t)
    (i j : Fin m) :
    HasDerivAt (fun s => R.projectedM f (φ s) i j)
      (((jacDot f (φ t) φ')ᵀ * R.M (f (φ t)) * jac f (φ t) + (jac f (φ t))ᵀ * Md * jac f (φ t) +
        (jac f (φ t))ᵀ * R.M (f (φ t)) * jacDot f (φ t) φ') i j) t := by
  have hJ := hasDerivAt_jac_comp hf hφ
  have hJt := hasDerivAt_matrix_transpose hJ
  have h1 := hasDerivAt_matrix_mul hJt hMd
  have h2 := hasDerivAt_matrix_mul h1 hJ i j
  rw [Matrix.add_mul] at h2
  exact h2

/-- **Lemma 4.2(2) for (4.62) along motions (MLS p. 201, proved by the book in Chapter 6):** if `M`
is symmetric and `Ṁ − 2C` is skew-symmetric along every motion of the robot, then along every motion
`φ` on the surface, with `f` of class `C²`, an entrywise derivative `Ṁ` of `s ↦ M(f(φ(s)))` and any
entrywise derivative `M̃˙` of `s ↦ M̃(φ(s))` at `t`, the matrix `M̃˙ − 2 C̃` is skew-symmetric. -/
theorem skew_deriv_projectedM_sub_two_projectedC {f : (Fin m → ℝ) → Fin n → ℝ}
    (hf : ContDiff ℝ 2 f) (hsym : ∀ q, (R.M q)ᵀ = R.M q) (hskew : SkewAlongMotions R.M R.C)
    {φ : ℝ → Fin m → ℝ} {φ' : Fin m → ℝ} {t : ℝ} (hφ : HasDerivAt φ φ' t)
    {Md : Matrix (Fin n) (Fin n) ℝ} (hMd : ∀ i j, HasDerivAt (fun s => R.M (f (φ s)) i j) (Md i j) t)
    {Mtd : Matrix (Fin m) (Fin m) ℝ}
    (hMtd : ∀ i j, HasDerivAt (fun s => R.projectedM f (φ s) i j) (Mtd i j) t) :
    (Mtd - (2 : ℝ) • R.projectedC f (φ t) φ')ᵀ = -(Mtd - (2 : ℝ) • R.projectedC f (φ t) φ') := by
  have e : Mtd = (jacDot f (φ t) φ')ᵀ * R.M (f (φ t)) * jac f (φ t) +
      (jac f (φ t))ᵀ * Md * jac f (φ t) + (jac f (φ t))ᵀ * R.M (f (φ t)) * jacDot f (φ t) φ' := by
    ext i j
    exact (hMtd i j).unique (R.hasDerivAt_projectedM_comp hf hφ hMd i j)
  have hs := hskew (hasDerivAt_comp ((hf.differentiable (by norm_num)) (φ t)) hφ) hMd
  rw [e]
  exact R.skew_projectedMdot_sub_two_projectedC f (hsym _) hs

/-- **The hybrid position/force control law of MLS eq. (4.63), p. 202:**
`τ = M(θ) J (φ̈_d − K_v ė − K_p e) + (C(θ, θ̇) J + M(θ) J̇) φ̇ + N(θ, θ̇) + Σ λ_i ∇h_i(θ)` with
`θ = f(φ)`, `θ̇ = J φ̇`, `e = φ − φ_d`, `J̇ = jacDot f φ φ̇`, and the commanded normal force `λ`. -/
def hybridTorque (h : (Fin n → ℝ) → Fin k → ℝ) (f : (Fin m → ℝ) → Fin n → ℝ)
    (Kp Kv : Matrix (Fin m) (Fin m) ℝ) (φd φd' φd'' φ φ' : Fin m → ℝ) (lam : Fin k → ℝ) :
    Fin n → ℝ :=
  R.M (f φ) *ᵥ (jac f φ *ᵥ (φd'' - Kv *ᵥ (φ' - φd') - Kp *ᵥ (φ - φd))) +
    (R.C (f φ) (jac f φ *ᵥ φ') * jac f φ + R.M (f φ) * jacDot f φ φ') *ᵥ φ' +
    R.N (f φ) (jac f φ *ᵥ φ') + (jac h (f φ))ᵀ *ᵥ lam

/-- **The hybrid law (4.63) projects to computed torque for (4.62) (MLS pp. 201–202):**
`Jᵀ τ = M̃ (φ̈_d − K_v ė − K_p e) + C̃ φ̇ + Ñ`, the computed torque law (4.49) of the projected
robot; the normal term `Σ λ_i ∇h_i` drops out. -/
theorem transpose_mulVec_hybridTorque {h : (Fin n → ℝ) → Fin k → ℝ}
    {f : (Fin m → ℝ) → Fin n → ℝ} (hp : IsSurfaceParametrization h f)
    (Kp Kv : Matrix (Fin m) (Fin m) ℝ) (φd φd' φd'' φ φ' : Fin m → ℝ) (lam : Fin k → ℝ) :
    (jac f φ)ᵀ *ᵥ R.hybridTorque h f Kp Kv φd φd' φd'' φ φ' lam =
      computedTorqueAlong Kp Kv (R.projectedM f φ) (R.projectedC f φ φ') (R.projectedN f φ φ')
        φd φd' φd'' φ φ' := by
  simp only [hybridTorque, computedTorqueAlong, projectedM, projectedC, projectedN,
    Matrix.mulVec_add, ← Matrix.mulVec_mulVec, hp.transpose_mulVec_normal, add_zero]

/-- **The closed loop of the hybrid law (4.63) at one time (MLS p. 202, analysis deferred by the
book to Chapter 6):** if the robot satisfies its constrained equations of motion at `θ = f(φ)`,
`θ̇ = J φ̇`, `θ̈ = J φ̈ + J̇ φ̇` with the input (4.63) and a multiplier `μ`, and `M(f(φ))` is positive
definite, then the error obeys `ë + K_v ė + K_p e = 0` and the constraint multiplier is the
commanded normal force, `μ = λ`. -/
theorem hybridTorque_closedLoop {h : (Fin n → ℝ) → Fin k → ℝ} {f : (Fin m → ℝ) → Fin n → ℝ}
    (hp : IsSurfaceParametrization h f) {Kp Kv : Matrix (Fin m) (Fin m) ℝ}
    {φd φd' φd'' φ φ' φ'' : Fin m → ℝ} {lam μ : Fin k → ℝ} (hM : (R.M (f φ)).PosDef)
    (hE : R.ConstrainedEquationsAt h (f φ) (jac f φ *ᵥ φ')
      (jac f φ *ᵥ φ'' + jacDot f φ φ' *ᵥ φ') (R.hybridTorque h f Kp Kv φd φd' φd'' φ φ' lam) μ) :
    (φ'' - φd'') + Kv *ᵥ (φ' - φd') + Kp *ᵥ (φ - φd) = 0 ∧ μ = lam := by
  have key : R.M (f φ) *ᵥ (jac f φ *ᵥ (φ'' - (φd'' - Kv *ᵥ (φ' - φd') - Kp *ᵥ (φ - φd)))) =
      (jac h (f φ))ᵀ *ᵥ (lam - μ) := by
    have e := hE
    simp only [ConstrainedEquationsAt, hybridTorque, Matrix.mulVec_add, Matrix.add_mulVec,
      Matrix.mulVec_sub, ← Matrix.mulVec_mulVec] at e ⊢
    linear_combination e
  have herr : φ'' - (φd'' - Kv *ᵥ (φ' - φd') - Kp *ᵥ (φ - φd)) = 0 := by
    have h1 := congrArg ((jac f φ)ᵀ *ᵥ ·) key
    simp only [hp.transpose_mulVec_normal] at h1
    have h1' : R.projectedM f φ *ᵥ (φ'' - (φd'' - Kv *ᵥ (φ' - φd') - Kp *ᵥ (φ - φd))) = 0 := by
      simp only [projectedM, ← Matrix.mulVec_mulVec]
      exact h1
    rw [← PosDef.inv_mulVec_mulVec (R.projectedM_posDef hp hM) (φ'' - _), h1',
      Matrix.mulVec_zero]
  refine ⟨?_, ?_⟩
  · rw [← herr]
    abel
  · have h2 : (jac h (f φ))ᵀ *ᵥ (lam - μ) = (jac h (f φ))ᵀ *ᵥ 0 := by
      rw [← key, herr, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
    have := (Constrained.transpose_mulVec_injective_iff _).mpr (hp.independent φ) h2
    exact (sub_eq_zero.mp this).symm

/-- **Exponential tracking under the hybrid position/force law (4.63) (MLS p. 202; convergence
deferred by the book to Chapter 6, proved here along Proposition 4.8, p. 192).** For `K_p`, `K_v`
symmetric positive definite there are `m₀, α > 0`, depending only on the gains, such that: for
every desired path `φ_d` with actual derivatives, every `t₀ ≥ 0`, every motion `φ` with velocity
`φ'` and acceleration `φ''` for `t > t₀` and `(φ, φ')` continuous on `[t₀, ∞)`, every commanded
normal force `λ(t)` and multiplier `μ(t)`: if `M` is positive definite and the robot satisfies its
constrained equations of motion along `θ = f(φ)` with the input (4.63) for `t > t₀`, then
`‖(e(t), ė(t))‖ ≤ m₀ e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀` and `μ(t) = λ(t)` for `t > t₀`.
Sup norm on `ℝᵐ × ℝᵐ`. -/
theorem hybridTorque_tracking {h : (Fin n → ℝ) → Fin k → ℝ} {f : (Fin m → ℝ) → Fin n → ℝ}
    (hp : IsSurfaceParametrization h f) (hM : ∀ q, (R.M q).PosDef)
    {Kp Kv : Matrix (Fin m) (Fin m) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m₀ > 0, ∃ α > 0, ∀ {φd φd' φd'' : ℝ → Fin m → ℝ}, (∀ t, HasDerivAt φd (φd' t) t) →
      (∀ t, HasDerivAt φd' (φd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ (φ φ' φ'' : ℝ → Fin m → ℝ)
      (lam μ : ℝ → Fin k → ℝ),
      ContinuousOn (fun s => (φ s, φ' s)) (Ici t₀) → (∀ s, t₀ < s → HasDerivAt φ (φ' s) s) →
      (∀ s, t₀ < s → HasDerivAt φ' (φ'' s) s) →
      (∀ s, t₀ < s → R.ConstrainedEquationsAt h (f (φ s)) (jac f (φ s) *ᵥ φ' s)
        (jac f (φ s) *ᵥ φ'' s + jacDot f (φ s) (φ' s) *ᵥ φ' s)
        (R.hybridTorque h f Kp Kv (φd s) (φd' s) (φd'' s) (φ s) (φ' s) (lam s)) (μ s)) →
      (∀ t, t₀ ≤ t → ‖(φ t - φd t, φ' t - φd' t)‖ ≤
        m₀ * Real.exp (-α * (t - t₀)) * ‖(φ t₀ - φd t₀, φ' t₀ - φd' t₀)‖) ∧
      ∀ s, t₀ < s → μ s = lam s := by
  obtain ⟨m₀, hm, α, hα, hT⟩ := computedTorque_tracking_along hKp hKv
  refine ⟨m₀, hm, α, hα, fun {φd φd' φd''} hd hd' t₀ ht₀ φ φ' φ'' lam μ hc hφ hφ' hE => ⟨?_, ?_⟩⟩
  · exact hT hd hd' t₀ ht₀ φ φ' φ'' (fun s => R.projectedM f (φ s))
      (fun s => R.projectedC f (φ s) (φ' s)) (fun s => R.projectedN f (φ s) (φ' s)) hc hφ hφ'
      (fun s _ => R.projectedM_posDef hp (hM _))
      (fun s hs => by
        rw [R.projected_eq_of_constrainedEquationsAt hp (hE s hs),
          R.transpose_mulVec_hybridTorque hp])
  · exact fun s hs => (R.hybridTorque_closedLoop hp (hM _) (hE s hs)).2

end RobotSystem

end Control
end RoboLean
