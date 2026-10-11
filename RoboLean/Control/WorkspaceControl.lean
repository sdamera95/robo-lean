import RoboLean.Kinematics.MapJacobian
import RoboLean.Control.ComputedTorque
import RoboLean.Control.AugmentedPD

/-!
# Workspace dynamics and workspace computed torque (MLS §5.4, eq. (4.55), Lemma 4.11, pp. 195–198)

**What MLS prints (read this session, printed pp. 196–198).** Let `f : Q → ℝᵖ` be "a smooth and
invertible mapping" from joint variables `θ` to workspace variables `x`, with `n = p` (p. 196);
`ẋ = J(θ) θ̇` with `J = ∂f/∂θ`, and "under the assumption that `f` is smooth and invertible"
`θ̇ = J⁻¹ ẋ`, `θ̈ = J⁻¹ ẍ + (d/dt)(J⁻¹) ẋ`. Substituting into `M θ̈ + C θ̇ + N = τ` and
premultiplying by `J⁻ᵀ := (J⁻¹)ᵀ` gives (4.55), p. 197, `M̃(θ) ẍ + C̃(θ, θ̇) ẋ + Ñ(θ, θ̇) = F` with
`M̃ = J⁻ᵀ M J⁻¹`, `C̃ = J⁻ᵀ (C J⁻¹ + M (d/dt)(J⁻¹))`, `Ñ = J⁻ᵀ N`, `F = J⁻ᵀ τ`. Lemma 4.11, p. 197:
"1. `M̃(θ)` is symmetric and positive definite. 2. `M̃˙ − 2C̃ ∈ ℝⁿˣⁿ` is a skew-symmetric matrix."
The workspace computed torque law, p. 198, is printed as
`F = M̃(θ)(ẍ_d − K_v ė − K_p e) + C(θ, θ̇) ẋ + N(θ, θ̇)`, `τ = Jᵀ F`, `e = x − x_d`, with the error
dynamics `ë + K_v ė + K_p e = 0`; "The PD control law can be similarly extended to workspace
coordinates" (no formula).

**Formalized.** For a `ManipulatorModel n` and a map `f : ℝⁿ → ℝⁿ`:

* the effective parameters `workspaceM`, `workspaceC`, `workspaceN`, with
  `C̃ = J⁻ᵀ (C − M J⁻¹ J̇) J⁻¹` and `J̇ = MapJacobian.jacDot f θ θ̇`; along every motion with
  `J(θ(t))` invertible and `f` of class `C²` this is the printed `J⁻ᵀ (C J⁻¹ + M (d/dt)(J⁻¹))`
  (`workspaceC_eq_printed`);
* (4.55): the workspace left-hand side is `J⁻ᵀ` times the joint-space one
  (`workspaceDynamics_eq`), and (4.55) is equivalent to the equations of motion at `t`, under
  `J(θ(t))` invertible: with the explicit `ẋ = J θ̇`, `ẍ = J̇ θ̇ + J θ̈`
  (`equationsOfMotionAt_iff_workspace`) and with the actual derivatives of `x = f ∘ θ`
  (`equationsOfMotionAt_iff_workspace_of_hasDerivAt`);
* Lemma 4.11(1): `M̃` symmetric for symmetric link inertias (`workspaceM_isSymm`), and positive
  definite where `M` is and `J` is invertible (`workspaceM_posDef`);
* Lemma 4.11(2): the actual derivative of `M̃(θ(t))` is `workspaceMdot`
  (`hasDerivAt_workspaceM_comp`), `workspaceMdot − 2 C̃` is skew-symmetric at every `(θ, θ̇)`
  (`skew_workspaceMdot_sub_two_workspaceC`), and so is `M̃˙ − 2 C̃` for every actual derivative
  `M̃˙` along a motion with `J(θ(t))` invertible (`skew_deriv_workspaceM_sub_two_workspaceC`); the
  proof is by congruence from Lemma 4.2(2) (E013), through the identity
  `M̃˙ − 2C̃ = Xᵀ(Ṁ − 2C)X + X'ᵀMX − XᵀMX'`, `X = J⁻¹`, `X' = (d/dt) J⁻¹`
  (`workspaceMdot_sub_two_workspaceC_eq`);
* the workspace computed torque law with the effective `C̃` and `Ñ` (`workspaceComputedTorque`),
  its error equation `ë + K_v ė + K_p e = 0` at each time
  (`equationsOfMotionAt_workspaceComputedTorque_iff`), the error
  `(e, ė) = (f(θ) − x_d, J θ̇ − ẋ_d)` as a solution of the linear error system
  (`isSolution_errorField_workspace`) and exponential tracking in workspace coordinates
  (`workspaceComputedTorque_tracking`), for every closed-loop solution on which `J` stays
  invertible.

**Differences from the page, recorded in E029.** (1) The hypothesis is `f` of class `C²` with
`J(θ)` invertible where it is used (along the motion), not "smooth and invertible": a smooth
bijection can have a singular Jacobian (`θ ↦ θ³` at `0`), and MLS's proofs use only that `J` is
invertible (p. 197); a global hypothesis `∀ θ, J(θ)` invertible would exclude the planar arm,
singular at `sin θ₂ = 0`. (2) The computed torque law uses `C̃ ẋ + Ñ`; the printed law has
`C(θ, θ̇) ẋ + N(θ, θ̇)`, for which the error equation does not follow from (4.55). (3) The printed
proof of Lemma 4.11(2) writes tildes on the right-hand side of its identity; the identity used is
the one with `Ṁ − 2C` and `M` (`workspaceMdot_sub_two_workspaceC_eq`). (4) The workspace PD law is
not formalized: the page gives no formula. Symmetric link inertias and `M(q)` positive definite
are hypotheses where they are used (as in `ManipulatorSystem` and `ComputedTorque`); the norm is
the sup norm of `(Fin n → ℝ) × (Fin n → ℝ)`. Exact cancellation of the model is assumed, as in MLS;
nothing here concerns model error, sampling, actuator limits or a physical arm.
-/

noncomputable section

open Matrix Filter Topology Set
open RoboLean.MapJacobian

namespace RoboLean
namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n) (f : (Fin n → ℝ) → Fin n → ℝ)

/-! ### The effective parameters (MLS p. 197) -/

/-- **The effective inertia `M̃(θ) = J⁻ᵀ M(θ) J⁻¹` of MLS p. 197**, with `J = jac f θ` the
Jacobian matrix of the workspace map `f` and `J⁻ᵀ = (J⁻¹)ᵀ` (`Matrix.inv`; meaningful where `J` is
invertible). -/
def workspaceM (q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((jac f q)⁻¹)ᵀ * P.M q * (jac f q)⁻¹

/-- **The effective Coriolis matrix `C̃(θ, θ̇)` of MLS p. 197**, in the closed form
`C̃ = J⁻ᵀ (C − M J⁻¹ J̇) J⁻¹` with `J̇ = jacDot f θ θ̇`; along a motion it equals the printed
`J⁻ᵀ (C J⁻¹ + M (d/dt)(J⁻¹))` (`workspaceC_eq_printed`). -/
def workspaceC (q v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((jac f q)⁻¹)ᵀ * (P.C q v - P.M q * (jac f q)⁻¹ * jacDot f q v) * (jac f q)⁻¹

/-- **The effective gravity and friction term `Ñ(θ, θ̇) = J⁻ᵀ N(θ, θ̇)` of MLS p. 197.** -/
def workspaceN (q v : Fin n → ℝ) : Fin n → ℝ :=
  ((jac f q)⁻¹)ᵀ *ᵥ P.N q v

/-- **The printed form of `C̃` (MLS p. 197).** For a `C²` map `f`, a motion `θ` with velocity `θ'`
at `t` and `J(θ(t))` invertible, every actual derivative `X'` of `s ↦ J(θ(s))⁻¹` at `t` (entry by
entry) gives `C̃(θ(t), θ') = J⁻ᵀ (C J⁻¹ + M X')`. -/
theorem workspaceC_eq_printed (hf : ContDiff ℝ 2 f) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : HasDerivAt θ θ' t) (hJ : IsUnit (jac f (θ t)).det)
    {X' : Matrix (Fin n) (Fin n) ℝ}
    (hX' : ∀ i j, HasDerivAt (fun s => (jac f (θ s))⁻¹ i j) (X' i j) t) :
    P.workspaceC f (θ t) θ' =
      ((jac f (θ t))⁻¹)ᵀ * (P.C (θ t) θ' * (jac f (θ t))⁻¹ + P.M (θ t) * X') := by
  have hX : X' = -((jac f (θ t))⁻¹ * jacDot f (θ t) θ' * (jac f (θ t))⁻¹) := by
    ext i j
    exact (hX' i j).unique (hasDerivAt_jac_inv_comp hf hθ hJ i j)
  rw [hX]
  unfold workspaceC
  noncomm_ring

/-! ### Eq. (4.55) -/

/-- **The algebra of MLS eq. (4.55), p. 197:** where `J(θ)` is invertible, the workspace form
`M̃ ẍ + C̃ ẋ + Ñ` with `ẋ = J v`, `ẍ = J̇ v + J a` is `J⁻ᵀ (M a + C v + N)`, the joint-space
left-hand side of (4.47) premultiplied by `J⁻ᵀ`. -/
theorem workspaceDynamics_eq {q : Fin n → ℝ} (hJ : IsUnit (jac f q).det) (v a : Fin n → ℝ) :
    P.workspaceM f q *ᵥ (jacDot f q v *ᵥ v + jac f q *ᵥ a) +
        P.workspaceC f q v *ᵥ (jac f q *ᵥ v) + P.workspaceN f q v =
      ((jac f q)⁻¹)ᵀ *ᵥ (P.M q *ᵥ a + P.C q v *ᵥ v + P.N q v) := by
  have hXJ : (jac f q)⁻¹ * jac f q = 1 := Matrix.nonsing_inv_mul _ hJ
  simp only [workspaceM, workspaceC, workspaceN, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, hXJ, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec]
  abel

/-- The transpose of the inverse cancels the transpose: `J⁻ᵀ (Jᵀ w) = w` where `J` is
invertible. -/
private theorem inv_transpose_mulVec_transpose_mulVec {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : IsUnit J.det) (w : Fin n → ℝ) : (J⁻¹)ᵀ *ᵥ (Jᵀ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ,
    Matrix.transpose_one, Matrix.one_mulVec]

/-- `J⁻ᵀ` is injective on vectors where `J` is invertible. -/
private theorem inv_transpose_mulVec_injective {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : IsUnit J.det) : Function.Injective ((J⁻¹)ᵀ *ᵥ ·) := by
  intro a b hab
  have h := congrArg (Jᵀ *ᵥ ·) hab
  simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hJ,
    Matrix.transpose_one, Matrix.one_mulVec] at h
  exact h

/-- **MLS eq. (4.55), p. 197: the workspace form of the equations of motion.** With symmetric link
inertias, along a motion whose velocity `θ'` near `t` and acceleration `θ''` at `t` are actual
derivatives, and with `J(θ(t))` invertible, the equations of motion (4.47) hold at `t` under the
torque `τ` exactly when `M̃ ẍ + C̃ ẋ + Ñ = J⁻ᵀ τ`, with `ẋ = J θ'(t)` and `ẍ = J̇ θ'(t) + J θ''`
(the actual workspace velocity and acceleration for `C²` maps `f`, `MapJacobian.hasDerivAt_comp`,
`MapJacobian.hasDerivAt_jac_mulVec_comp`). -/
theorem equationsOfMotionAt_iff_workspace (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hJ : IsUnit (jac f (θ t)).det) (τ : Fin n → ℝ) :
    P.EquationsOfMotionAt θ τ t ↔
      P.workspaceM f (θ t) *ᵥ (jacDot f (θ t) (θ' t) *ᵥ θ' t + jac f (θ t) *ᵥ θ'') +
          P.workspaceC f (θ t) (θ' t) *ᵥ (jac f (θ t) *ᵥ θ' t) + P.workspaceN f (θ t) (θ' t) =
        ((jac f (θ t))⁻¹)ᵀ *ᵥ τ := by
  rw [P.equationsOfMotionAt_iff h hθ hθ', P.workspaceDynamics_eq f hJ]
  exact (inv_transpose_mulVec_injective hJ).eq_iff.symm

/-- **MLS eq. (4.55), p. 197, with the actual workspace derivatives.** With symmetric link
inertias, a `C²` map `f`, a motion `θ` with velocity `θ'` near `t` and acceleration `θ''` at `t`,
and `J(θ(t))` invertible: if `x'` is the velocity of `x = f ∘ θ` near `t` and `x''` the derivative
of `x'` at `t`, the equations of motion hold at `t` under `τ` exactly when
`M̃(θ) x'' + C̃(θ, θ̇) x' + Ñ(θ, θ̇) = J⁻ᵀ τ` at `t`. -/
theorem equationsOfMotionAt_iff_workspace_of_hasDerivAt (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hf : ContDiff ℝ 2 f) {θ θ' x' : ℝ → Fin n → ℝ} {θ'' x'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => f (θ s)) (x' s) s) (hx' : HasDerivAt x' x'' t)
    (hJ : IsUnit (jac f (θ t)).det) (τ : Fin n → ℝ) :
    P.EquationsOfMotionAt θ τ t ↔
      P.workspaceM f (θ t) *ᵥ x'' + P.workspaceC f (θ t) (θ' t) *ᵥ x' t +
          P.workspaceN f (θ t) (θ' t) = ((jac f (θ t))⁻¹)ᵀ *ᵥ τ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hev : x' =ᶠ[𝓝 t] fun s => jac f (θ s) *ᵥ θ' s := by
    filter_upwards [hθ, hx] with s h1 h2
    exact h2.unique (hasDerivAt_comp (hd _) h1)
  have hv : x' t = jac f (θ t) *ᵥ θ' t := hev.self_of_nhds
  have ha : x'' = jacDot f (θ t) (θ' t) *ᵥ θ' t + jac f (θ t) *ᵥ θ'' :=
    hx'.unique ((hasDerivAt_jac_mulVec_comp hf hθ.self_of_nhds hθ').congr_of_eventuallyEq hev)
  rw [hv, ha]
  exact P.equationsOfMotionAt_iff_workspace f h hθ hθ' hJ τ

/-! ### Lemma 4.11(1): `M̃` symmetric and positive definite -/

/-- **MLS Lemma 4.11(1), p. 197, symmetry:** with symmetric link inertias, `M̃(θ) = J⁻ᵀ M J⁻¹` is
symmetric at every configuration (no invertibility is needed for symmetry). -/
theorem workspaceM_isSymm (h : ∀ k, (P.chain.linkInertia k).IsSymm) (q : Fin n → ℝ) :
    (P.workspaceM f q).IsSymm := by
  have hM : (P.M q)ᵀ = P.M q := (P.chain.massMatrix_isSymm h q).eq
  unfold Matrix.IsSymm workspaceM
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM,
    Matrix.mul_assoc]

/-- **MLS Lemma 4.11(1), p. 197, positive definiteness:** where `M(θ)` is positive definite and
`J(θ)` is invertible, `M̃(θ) = J⁻ᵀ M J⁻¹` is positive definite (Mathlib's `Matrix.PosDef`, which
includes symmetry). -/
theorem workspaceM_posDef {q : Fin n → ℝ} (hM : (P.M q).PosDef) (hJ : IsUnit (jac f q).det) :
    (P.workspaceM f q).PosDef := by
  have hinj : Function.Injective ((jac f q)⁻¹).mulVec := by
    intro a b hab
    have := congrArg ((jac f q).mulVec) hab
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ] using this
  simpa [workspaceM] using hM.conjTranspose_mul_mul_same hinj

/-! ### Lemma 4.11(2): `M̃˙ − 2C̃` skew-symmetric -/

/-- **The rate `M̃˙` of the effective inertia along a motion (MLS p. 197):** with `X = J⁻¹`,
`X' = −X J̇ X` (the derivative of `J⁻¹`, `MapJacobian.hasDerivAt_jac_inv_comp`) and `Ṁ = Mdot`,
`M̃˙ = X'ᵀ M X + Xᵀ Ṁ X + Xᵀ M X'`. -/
def workspaceMdot (q v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (-((jac f q)⁻¹ * jacDot f q v * (jac f q)⁻¹))ᵀ * P.M q * (jac f q)⁻¹ +
    ((jac f q)⁻¹)ᵀ * P.Mdot q v * (jac f q)⁻¹ +
    ((jac f q)⁻¹)ᵀ * P.M q * (-((jac f q)⁻¹ * jacDot f q v * (jac f q)⁻¹))

/-- **`M̃˙` is the actual derivative of `M̃(θ(t))` (MLS p. 197).** For a `C²` map `f`, a motion
`θ` with velocity `θ'` at `t` and `J(θ(t))` invertible, every entry of `s ↦ M̃(θ(s))` has the
derivative `workspaceMdot f (θ t) θ'` (same entry) at `t`. -/
theorem hasDerivAt_workspaceM_comp (hf : ContDiff ℝ 2 f) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : HasDerivAt θ θ' t) (hJ : IsUnit (jac f (θ t)).det) (i j : Fin n) :
    HasDerivAt (fun s => P.workspaceM f (θ s) i j) (P.workspaceMdot f (θ t) θ' i j) t := by
  have hX := hasDerivAt_jac_inv_comp hf hθ hJ
  have hXT := hasDerivAt_matrix_transpose hX
  have hM := P.hasDerivAt_M_comp hθ
  have h := hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hXT hM) hX i j
  convert h using 1
  · rfl
  · rw [workspaceMdot, Matrix.add_mul]

/-- **The identity in the proof of MLS Lemma 4.11(2), p. 197, in the form that holds:** with
`X = J⁻¹` and `X' = −X J̇ X` (the derivative of `J⁻¹` along a motion,
`MapJacobian.hasDerivAt_jac_inv_comp`),
`M̃˙ − 2C̃ = Xᵀ (Ṁ − 2C) X + X'ᵀ M X − Xᵀ M X'`, at every configuration and rate. MLS prints the
right-hand side with `M̃˙ − 2C̃` and `M̃` in place of `Ṁ − 2C` and `M`, so the printed right-hand
side contains its own left-hand side (E029 source observation). -/
theorem workspaceMdot_sub_two_workspaceC_eq (q v : Fin n → ℝ) :
    P.workspaceMdot f q v - (2 : ℝ) • P.workspaceC f q v =
      ((jac f q)⁻¹)ᵀ * (P.Mdot q v - (2 : ℝ) • P.C q v) * (jac f q)⁻¹ +
        (-((jac f q)⁻¹ * jacDot f q v * (jac f q)⁻¹))ᵀ * P.M q * (jac f q)⁻¹ -
        ((jac f q)⁻¹)ᵀ * P.M q * (-((jac f q)⁻¹ * jacDot f q v * (jac f q)⁻¹)) := by
  simp only [workspaceMdot, workspaceC, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  module

/-- The congruence step of the proof of MLS Lemma 4.11(2), p. 197: if `M` is symmetric and
`Ṁ − 2C` is skew-symmetric, then for all `X`, `X'` the matrix
`X'ᵀ M X + Xᵀ Ṁ X + Xᵀ M X' − 2 Xᵀ (C X + M X')` is skew-symmetric. -/
private theorem skew_congr {M Md C X X' : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M)
    (hs : (Md - (2 : ℝ) • C)ᵀ = -(Md - (2 : ℝ) • C)) :
    (X'ᵀ * M * X + Xᵀ * Md * X + Xᵀ * M * X' - (2 : ℝ) • (Xᵀ * (C * X + M * X')))ᵀ =
      -(X'ᵀ * M * X + Xᵀ * Md * X + Xᵀ * M * X' - (2 : ℝ) • (Xᵀ * (C * X + M * X'))) := by
  have e : X'ᵀ * M * X + Xᵀ * Md * X + Xᵀ * M * X' - (2 : ℝ) • (Xᵀ * (C * X + M * X')) =
      Xᵀ * (Md - (2 : ℝ) • C) * X + X'ᵀ * M * X - Xᵀ * M * X' := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc]
    module
  rw [e, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, hs, hM,
    Matrix.transpose_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  module

/-- `C̃` in the form `Xᵀ (C X + M X')` with `X = J⁻¹`, `X' = −X J̇ X`. -/
private theorem workspaceC_eq_mul (q v : Fin n → ℝ) :
    P.workspaceC f q v = ((jac f q)⁻¹)ᵀ * (P.C q v * (jac f q)⁻¹ +
      P.M q * (-((jac f q)⁻¹ * jacDot f q v * (jac f q)⁻¹))) := by
  unfold workspaceC
  noncomm_ring

/-- **MLS Lemma 4.11(2), p. 197, at every configuration and rate:** with symmetric link inertias,
`M̃˙ − 2C̃` is skew-symmetric, where `M̃˙ = workspaceMdot f θ θ̇` and `C̃ = workspaceC f θ θ̇`. No
invertibility is needed for the algebra; `workspaceMdot` is the actual derivative of `M̃` where `J`
is invertible (`hasDerivAt_workspaceM_comp`). -/
theorem skew_workspaceMdot_sub_two_workspaceC (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (q v : Fin n → ℝ) :
    (P.workspaceMdot f q v - (2 : ℝ) • P.workspaceC f q v)ᵀ =
      -(P.workspaceMdot f q v - (2 : ℝ) • P.workspaceC f q v) := by
  have hM : (P.M q)ᵀ = P.M q := (P.chain.massMatrix_isSymm h q).eq
  have hs : (P.Mdot q v - (2 : ℝ) • P.C q v)ᵀ = -(P.Mdot q v - (2 : ℝ) • P.C q v) :=
    Christoffel.skew_rate_sub_two_coriolisMatrix (Christoffel.partials_isSymm
      (P.chain.massMatrix_isSymm h) (P.chain.hasFDerivAt_massMatrix q)) v
  rw [workspaceC_eq_mul]
  exact skew_congr hM hs

/-- **MLS Lemma 4.11(2), p. 197, along a motion.** With symmetric link inertias, a `C²` map `f`,
a motion `θ` with velocity `θ'` at `t` and `J(θ(t))` invertible, every actual derivative `M̃˙` of
`s ↦ M̃(θ(s))` at `t` (entry by entry) makes `M̃˙ − 2 C̃(θ(t), θ')` skew-symmetric. The proof is by
congruence from MLS Lemma 4.2(2) for the joint-space `Ṁ − 2C`
(`InertialChain.skew_deriv_sub_two_coriolisMatrix_massMatrixDeriv`, E013). -/
theorem skew_deriv_workspaceM_sub_two_workspaceC (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hf : ContDiff ℝ 2 f) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hJ : IsUnit (jac f (θ t)).det) {Mtdot : Matrix (Fin n) (Fin n) ℝ}
    (hMtdot : ∀ i j, HasDerivAt (fun s => P.workspaceM f (θ s) i j) (Mtdot i j) t) :
    (Mtdot - (2 : ℝ) • P.workspaceC f (θ t) θ')ᵀ =
      -(Mtdot - (2 : ℝ) • P.workspaceC f (θ t) θ') := by
  have hMt : Mtdot = P.workspaceMdot f (θ t) θ' := by
    ext i j
    exact (hMtdot i j).unique (P.hasDerivAt_workspaceM_comp f hf hθ hJ i j)
  have hM : (P.M (θ t))ᵀ = P.M (θ t) := (P.chain.massMatrix_isSymm h (θ t)).eq
  have hs : (P.Mdot (θ t) θ' - (2 : ℝ) • P.C (θ t) θ')ᵀ =
      -(P.Mdot (θ t) θ' - (2 : ℝ) • P.C (θ t) θ') :=
    P.chain.skew_deriv_sub_two_coriolisMatrix_massMatrixDeriv h (fun k => hasDerivAt_pi.mp hθ k)
      (P.hasDerivAt_M_comp hθ)
  rw [hMt, workspaceC_eq_mul]
  exact skew_congr hM hs

/-! ### Workspace computed torque (MLS p. 198) -/

/-- **The workspace computed torque law of MLS p. 198, with the effective `C̃` and `Ñ`:**
`τ = Jᵀ F`, `F = M̃(θ)(ẍ_d − K_v ė − K_p e) + C̃(θ, θ̇) ẋ + Ñ(θ, θ̇)`, with `x = f(θ)`, `ẋ = J θ̇`,
`e = x − x_d`, `ė = ẋ − ẋ_d`, for a desired workspace trajectory `x_d` with velocity `x_d'` and
acceleration `x_d''`, as a feedback law `u(t, θ, θ̇)`. MLS prints `C(θ, θ̇) ẋ + N(θ, θ̇)` in place
of `C̃ ẋ + Ñ`; with the printed terms the error equation does not follow from (4.55). -/
def workspaceComputedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (xd xd' xd'' : ℝ → Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun t q v => (jac f q)ᵀ *ᵥ
    (P.workspaceM f q *ᵥ (xd'' t - Kv *ᵥ (jac f q *ᵥ v - xd' t) - Kp *ᵥ (f q - xd t)) +
      P.workspaceC f q v *ᵥ (jac f q *ᵥ v) + P.workspaceN f q v)

/-- **MLS p. 198: the workspace error equation at one time.** With symmetric link inertias,
`M(θ(t))` positive definite and `J(θ(t))` invertible, along a motion whose velocity `θ'` near `t`
and acceleration `θ''` at `t` are actual derivatives, the equations of motion (4.47) hold at `t`
under the workspace computed torque law exactly when `ë + K_v ė + K_p e = 0` at `t`, with
`e = f(θ) − x_d`, `ė = J θ' − x_d'`, `ë = J̇ θ' + J θ'' − x_d''`. -/
theorem equationsOfMotionAt_workspaceComputedTorque_iff (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (xd xd' xd'' : ℝ → Fin n → ℝ)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hM : (P.M (θ t)).PosDef)
    (hJ : IsUnit (jac f (θ t)).det) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) :
    P.EquationsOfMotionAt θ (P.workspaceComputedTorque f Kp Kv xd xd' xd'' t (θ t) (θ' t)) t ↔
      (jacDot f (θ t) (θ' t) *ᵥ θ' t + jac f (θ t) *ᵥ θ'' - xd'' t) +
          Kv *ᵥ (jac f (θ t) *ᵥ θ' t - xd' t) + Kp *ᵥ (f (θ t) - xd t) = 0 := by
  rw [P.equationsOfMotionAt_iff_workspace f h hθ hθ' hJ, workspaceComputedTorque,
    inv_transpose_mulVec_transpose_mulVec hJ, add_left_inj, add_left_inj]
  have hMt := P.workspaceM_posDef f hM hJ
  set a := jacDot f (θ t) (θ' t) *ᵥ θ' t + jac f (θ t) *ᵥ θ''
  set w := xd'' t - Kv *ᵥ (jac f (θ t) *ᵥ θ' t - xd' t) - Kp *ᵥ (f (θ t) - xd t)
  have herr : (a - xd'' t) + Kv *ᵥ (jac f (θ t) *ᵥ θ' t - xd' t) + Kp *ᵥ (f (θ t) - xd t) =
      a - w := by
    simp only [w]
    abel
  rw [herr, sub_eq_zero]
  constructor
  · intro hMw
    rw [← Control.PosDef.inv_mulVec_mulVec hMt a, hMw, Control.PosDef.inv_mulVec_mulVec hMt]
  · intro hw
    rw [hw]

/-- The joint acceleration of the closed loop under the workspace computed torque law gives the
commanded workspace acceleration: `J̇ v + J a = w` for `a = M⁻¹ (u − C v − N)`. -/
private theorem workspace_accel {q : Fin n → ℝ} (hM : (P.M q).PosDef)
    (hJ : IsUnit (jac f q).det) (v w : Fin n → ℝ) :
    jacDot f q v *ᵥ v + jac f q *ᵥ ((P.M q)⁻¹ *ᵥ ((jac f q)ᵀ *ᵥ
      (P.workspaceM f q *ᵥ w + P.workspaceC f q v *ᵥ (jac f q *ᵥ v) + P.workspaceN f q v) -
        P.C q v *ᵥ v - P.N q v)) = w := by
  set F := P.workspaceM f q *ᵥ w + P.workspaceC f q v *ᵥ (jac f q *ᵥ v) + P.workspaceN f q v
  set a := (P.M q)⁻¹ *ᵥ ((jac f q)ᵀ *ᵥ F - P.C q v *ᵥ v - P.N q v)
  have hMa : P.M q *ᵥ a + P.C q v *ᵥ v + P.N q v = (jac f q)ᵀ *ᵥ F := by
    simp only [a]
    rw [Control.PosDef.mulVec_inv_mulVec hM]
    abel
  have key := P.workspaceDynamics_eq f hJ v a
  rw [hMa, inv_transpose_mulVec_transpose_mulVec hJ] at key
  have hMt := P.workspaceM_posDef f hM hJ
  have h2 : P.workspaceM f q *ᵥ (jacDot f q v *ᵥ v + jac f q *ᵥ a) = P.workspaceM f q *ᵥ w := by
    simp only [F] at key
    exact add_right_cancel (add_right_cancel key)
  rw [← Control.PosDef.inv_mulVec_mulVec hMt (jacDot f q v *ᵥ v + jac f q *ᵥ a), h2,
    Control.PosDef.inv_mulVec_mulVec hMt]

/-- **MLS p. 198: the closed-loop workspace error solves the linear error system.** With `f` of
class `C²`, `M(q)` positive definite for every `q`, and a desired workspace trajectory with actual
derivatives `x_d' = ẋ_d`, `x_d'' = ẍ_d` at every time, every solution `x = (θ, θ̇)` from `t₀` of
(4.47) under the workspace computed torque law on which `J(θ(s))` is invertible for every `s > t₀`
gives a workspace error `(e, ė) = (f(θ) − x_d, J(θ) θ̇ − x_d')` that solves
`d/dt (e, ė) = (ė, −K_v ė − K_p e)` from `t₀`. -/
theorem isSolution_errorField_workspace (hf : ContDiff ℝ 2 f) (hM : ∀ q, (P.M q).PosDef)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) {xd xd' xd'' : ℝ → Fin n → ℝ}
    (hd : ∀ t, HasDerivAt xd (xd' t) t) (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) {t₀ : ℝ}
    {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : Stability.IsSolution (P.field (P.workspaceComputedTorque f Kp Kv xd xd' xd'')) t₀ x)
    (hJ : ∀ s, t₀ < s → IsUnit (jac f (x s).1).det) :
    Stability.IsSolution (Control.errorField Kp Kv) t₀
      (fun t => (f (x t).1 - xd t, jac f (x t).1 *ᵥ (x t).2 - xd' t)) := by
  have hdc : Continuous xd := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hdc' : Continuous xd' := continuous_iff_continuousAt.mpr fun t => (hd' t).continuousAt
  have hd2 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJv : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => jac f p.1 *ᵥ p.2 := by
    simp only [jac_mulVec]
    exact ((hf.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply continuous_snd
  refine ⟨(((hf.continuous.comp continuous_fst).comp_continuousOn hx.1).sub
    hdc.continuousOn).prodMk ((hJv.comp_continuousOn hx.1).sub hdc'.continuousOn),
    fun t ht => ?_⟩
  set u := P.workspaceComputedTorque f Kp Kv xd xd' xd''
  have hfst : HasDerivAt (fun s => (x s).1) (x t).2 t := (hx.2 t ht).fst
  have hsnd : HasDerivAt (fun s => (x s).2) (P.field u t (x t)).2 t := (hx.2 t ht).snd
  have h1 := (hasDerivAt_comp (hd2 _) hfst).sub (hd t)
  have h2 := (hasDerivAt_jac_mulVec_comp hf (θ := fun s => (x s).1) (θ' := fun s => (x s).2)
    hfst hsnd).sub (hd' t)
  have hacc : jacDot f (x t).1 (x t).2 *ᵥ (x t).2 + jac f (x t).1 *ᵥ (P.field u t (x t)).2 =
      xd'' t - Kv *ᵥ (jac f (x t).1 *ᵥ (x t).2 - xd' t) - Kp *ᵥ (f (x t).1 - xd t) := by
    simp only [field, u, workspaceComputedTorque]
    exact P.workspace_accel f (hM _) (hJ t ht) _ _
  rw [hacc] at h2
  convert h1.prodMk h2 using 1
  simp only [Control.errorField, Prod.mk.injEq, true_and]
  abel

/-- **MLS p. 198: workspace computed torque gives exponential tracking in workspace coordinates.**
With `f` of class `C²`, `M(q)` positive definite for every `q`, and `K_p`, `K_v` symmetric positive
definite, there are constants `m, α > 0`, depending only on `K_p` and `K_v`, such that for every
desired workspace trajectory with actual derivatives `x_d' = ẋ_d`, `x_d'' = ẍ_d` at every time,
every solution `x = (θ, θ̇)` from `t₀ ≥ 0` of (4.47) under the workspace computed torque law on
which `J(θ(s))` is invertible for every `s > t₀` satisfies, for `t ≥ t₀`,
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` with `e = f(θ) − x_d`, `ė = J(θ) θ̇ − ẋ_d`
(sup norm). -/
theorem workspaceComputedTorque_tracking (hf : ContDiff ℝ 2 f) (hM : ∀ q, (P.M q).PosDef)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin n → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.workspaceComputedTorque f Kp Kv xd xd' xd'')) t₀ x →
      (∀ s, t₀ < s → IsUnit (jac f (x s).1).det) →
      ∀ t, t₀ ≤ t → ‖(f (x t).1 - xd t, jac f (x t).1 *ᵥ (x t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) *
          ‖(f (x t₀).1 - xd t₀, jac f (x t₀).1 *ᵥ (x t₀).2 - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, hexp⟩ := Control.globallyExponentiallyStable_errorField hKp hKv
  refine ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x hx hJ t ht => ?_⟩
  simpa using hexp t₀ ht₀ _ (P.isSolution_errorField_workspace f hf hM Kp Kv hd hd' hx hJ) t ht

end ManipulatorModel
end RoboLean
