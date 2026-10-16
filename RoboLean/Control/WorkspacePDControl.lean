import RoboLean.Control.RobotPDControl
import RoboLean.Control.WorkspaceControl

/-!
# The workspace PD law (MLS §5.4, p. 198, with Proposition 4.9 and Lemma 4.11)

**What MLS states.** After the workspace computed torque law, p. 198: "These two properties [Lemma
4.11: `M̃` symmetric positive definite, `M̃˙ − 2C̃` skew-symmetric] allow us to immediately extend
the control laws in the previous section to workspace coordinates. … The PD control law can be
similarly extended to workspace coordinates." No formula is printed. The workspace map is "a smooth
and invertible mapping" `f : Q → ℝᵖ`, `n = p` (p. 196), the workspace dynamics are (4.55),
`M̃(θ) ẍ + C̃(θ, θ̇) ẋ + Ñ(θ, θ̇) = F`, `τ = Jᵀ F` (p. 198), and Proposition 4.9 (p. 193) is the PD
statement being extended.

**Formalized.** The extension of PD control with compensation of `N` (Proposition 4.9 as the library
states it) to workspace coordinates: `F = Ñ(θ, θ̇) − K_v ẋ − K_p (x − x_d)`, `τ = Jᵀ F`, with
`x = f(θ)`, `ẋ = J(θ) θ̇` and a constant workspace set point `x_d` (`workspacePDTorque`); where `J`
is invertible this is `τ = N − Jᵀ K_v J θ̇ − Jᵀ K_p (f(θ) − x_d)` (`workspacePDTorque_eq`).

* Along every motion satisfying the equations of motion under the law, at every time where `J` is
  invertible, the workspace energy `½ ẋᵀ M̃ ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` has the derivative
  `−ẋᵀ K_v ẋ` (`hasDerivAt_workspacePDEnergy`): the energy identity of Proposition 4.9 for the
  matrices `(M̃, C̃)` along the motion, with Lemma 4.11(2) as the skew property. No inverse of `f`
  is used.
* For `f` with a differentiable global inverse `g` (MLS's "smooth and invertible", p. 196), the
  workspace system `(M̃, C̃, Ñ)` written in `x` is a robot (`workspaceRobot`): `M(x) = M̃(g(x))`,
  `C(x, ẋ) = C̃(g(x), J⁻¹ẋ)`, `N(x, ẋ) = Ñ(g(x), J⁻¹ẋ)`. It has the skew property by Lemma 4.11(2)
  (`workspaceRobot_hasSkewProperty`); joint solutions under `τ = Jᵀ F` and workspace solutions under
  `F` correspond (`isSolution_workspaceRobot_of_isSolution`,
  `isSolution_of_isSolution_workspaceRobot`); a flow of the joint closed loop gives a flow of the
  workspace one (`exists_hasFlow_workspaceRobot`). Proposition 4.9 for robots then gives global
  asymptotic stability of `(x_d, 0)` in workspace coordinates
  (`globallyAsymptoticallyStableAt_workspacePD`), and for the joint closed loop the workspace error
  tends to zero (`tendsto_workspacePD`) and is Lyapunov stable (`stable_workspacePD`).

**Hypotheses.** `f` of class `C²`; `g` differentiable with `f ∘ g = id` and `g ∘ f = id` (then `J`
is invertible everywhere, `isUnit_det_jac_of_inverse`); symmetric link inertias; `M(q)` positive
definite for every `q`; `M̃` uniformly positive definite (`λ‖v‖² ≤ vᵀ M̃(θ) v`, MLS p. 191's
condition for the effective inertia); `K_p`, `K_v` symmetric positive definite; a solution flow of
the joint closed loop. A global inverse excludes maps such as the planar arm's xy position (singular
at `sin θ₂ = 0`); the energy identity holds without it. Exact model cancellation is assumed, as in
MLS. State `(θ, θ̇)` or `(x, ẋ)` in `ℝⁿ × ℝⁿ`, sup norm.

**Not formalized.** MLS's Exercise 9 (p. 209) reads: "Show that the workspace version of the PD
control law results in exponential trajectory tracking", that is, the augmented PD law of
Proposition 4.10 (p. 194, titled "Stability of the PD control law") in workspace coordinates. The
statement here is the set-point extension of Proposition 4.9; the tracking extension of
Proposition 4.10 to robots and to workspace coordinates is not formalized.
-/

noncomputable section

open Matrix Filter Topology Set
open RoboLean.MapJacobian

namespace RoboLean
namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n) (f : (Fin n → ℝ) → Fin n → ℝ)

/-! ### The law and the energy identity -/

/-- **The workspace PD law with compensation of `Ñ` (MLS p. 198, "The PD control law can be
similarly extended to workspace coordinates", applied to Proposition 4.9 as formalized, p. 193):**
`τ = Jᵀ F`, `F = Ñ(θ, θ̇) − K_v ẋ − K_p (x − x_d)`, with `x = f(θ)`, `ẋ = J(θ) θ̇` and a constant
workspace set point `x_d`, as a feedback law `u(t, θ, θ̇)`. -/
def workspacePDTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (xd : Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun _ q v => (jac f q)ᵀ *ᵥ (P.workspaceN f q v - Kv *ᵥ (jac f q *ᵥ v) - Kp *ᵥ (f q - xd))

/-- `Jᵀ (J⁻ᵀ w) = w` where `J` is invertible (MLS p. 198, `τ = Jᵀ F`). -/
private lemma transpose_mulVec_inv_transpose_mulVec' {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : IsUnit J.det) (w : Fin n → ℝ) : Jᵀ *ᵥ ((J⁻¹)ᵀ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hJ,
    Matrix.transpose_one, Matrix.one_mulVec]

/-- `J⁻ᵀ (Jᵀ w) = w` where `J` is invertible (MLS p. 197, `F = J⁻ᵀ τ`). -/
private lemma inv_transpose_mulVec_transpose_mulVec' {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : IsUnit J.det) (w : Fin n → ℝ) : (J⁻¹)ᵀ *ᵥ (Jᵀ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ,
    Matrix.transpose_one, Matrix.one_mulVec]

/-- **The workspace PD law in joint terms (MLS pp. 197–198):** where `J(θ)` is invertible,
`Jᵀ Ñ = N`, so the law is `τ = N(θ, θ̇) − Jᵀ K_v J θ̇ − Jᵀ K_p (f(θ) − x_d)`. -/
theorem workspacePDTorque_eq (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (xd : Fin n → ℝ)
    {q : Fin n → ℝ} (hJ : IsUnit (jac f q).det) (t : ℝ) (v : Fin n → ℝ) :
    P.workspacePDTorque f Kp Kv xd t q v =
      P.N q v - (jac f q)ᵀ *ᵥ (Kv *ᵥ (jac f q *ᵥ v)) - (jac f q)ᵀ *ᵥ (Kp *ᵥ (f q - xd)) := by
  rw [workspacePDTorque, workspaceN, Matrix.mulVec_sub, Matrix.mulVec_sub,
    transpose_mulVec_inv_transpose_mulVec' hJ]

/-- **The Lyapunov function of Proposition 4.9 (MLS p. 193) in workspace coordinates (p. 198):**
`W(θ, θ̇) = ½ ẋᵀ M̃(θ) ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` with `x = f(θ)`, `ẋ = J(θ) θ̇`. -/
def workspacePDEnergy (Kp : Matrix (Fin n) (Fin n) ℝ) (xd q v : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((jac f q *ᵥ v) ⬝ᵥ (P.workspaceM f q *ᵥ (jac f q *ᵥ v))) +
    (1 / 2 : ℝ) * ((f q - xd) ⬝ᵥ (Kp *ᵥ (f q - xd)))

/-- **The energy identity of Proposition 4.9 for the workspace PD law (MLS pp. 193, 197–198).** With
symmetric link inertias, `f` of class `C²` and `K_p` symmetric, along a motion `θ` whose velocity
`θ'` near `t` and acceleration `θ''` at `t` are actual derivatives, with `J(θ(t))` invertible and
the equations of motion (4.47) holding at `t` under the workspace PD law, the workspace energy
`½ ẋᵀ M̃ ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` has the derivative `−ẋᵀ K_v ẋ` at `t`, `ẋ = J(θ(t)) θ'(t)`.
The skew property used is Lemma 4.11(2), p. 197. -/
theorem hasDerivAt_workspacePDEnergy (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hf : ContDiff ℝ 2 f) {Kp : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm)
    (Kv : Matrix (Fin n) (Fin n) ℝ) (xd : Fin n → ℝ) {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ}
    {t : ℝ} (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hJ : IsUnit (jac f (θ t)).det)
    (hE : P.EquationsOfMotionAt θ (P.workspacePDTorque f Kp Kv xd t (θ t) (θ' t)) t) :
    HasDerivAt (fun s => P.workspacePDEnergy f Kp xd (θ s) (θ' s))
      (-((jac f (θ t) *ᵥ θ' t) ⬝ᵥ (Kv *ᵥ (jac f (θ t) *ᵥ θ' t)))) t := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hθt := hθ.self_of_nhds
  have hM := P.hasDerivAt_workspaceM_comp f hf hθt hJ
  have hE' := (P.equationsOfMotionAt_iff_workspace f h hθ hθ' hJ _).mp hE
  simp only [workspacePDTorque] at hE'
  rw [inv_transpose_mulVec_transpose_mulVec' hJ] at hE'
  refine Control.hasDerivAt_pdEnergy_along hKp xd (x := fun s => f (θ s))
    (x' := fun s => jac f (θ s) *ᵥ θ' s) (Mt := fun s => P.workspaceM f (θ s))
    (hasDerivAt_comp (hd _) hθt) (hasDerivAt_jac_mulVec_comp hf hθt hθ') hM
    (P.workspaceM_isSymm f h _) (P.skew_deriv_workspaceM_sub_two_workspaceC f h hf hθt hJ hM) ?_
  have h0 := sub_eq_zero.mpr hE'
  rw [← h0]
  abel

/-! ### The workspace system as a robot (MLS pp. 196–198, 303) -/

/-- The chain rule for `f ∘ g = id`: `J(g(y)) Dg(y) v = v` (MLS p. 196, `θ̇ = J⁻¹ ẋ`). -/
private lemma jac_mulVec_fderiv_of_inverse {g : (Fin n → ℝ) → Fin n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y)
    (y v : Fin n → ℝ) : jac f (g y) *ᵥ fderiv ℝ g y v = v := by
  have hcomp := (hf (g y)).hasFDerivAt.comp y (hg y).hasFDerivAt
  have hid : f ∘ g = id := funext hfg
  rw [hid] at hcomp
  have := hcomp.unique (hasFDerivAt_id y)
  rw [jac_mulVec]
  simpa using DFunLike.congr_fun this v

/-- **A differentiable inverse makes the Jacobian invertible (MLS p. 196, "smooth and
invertible"):** if `f` and `g` are differentiable with `f ∘ g = id` and `g ∘ f = id`, then
`J(θ) = ∂f/∂θ` is invertible at every `θ`. -/
theorem isUnit_det_jac_of_inverse {g : (Fin n → ℝ) → Fin n → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    (q : Fin n → ℝ) : IsUnit (jac f q).det := by
  have key := jac_mulVec_fderiv_of_inverse f hf hg hfg (f q)
  rw [hgf] at key
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp fun v => ⟨_, key v⟩)

/-- **The velocity of `g ∘ x` is `J⁻¹ ẋ` (MLS p. 196, `θ̇ = J⁻¹ ẋ`):** for `f` and `g`
differentiable with `f ∘ g = id` and `g ∘ f = id`, a workspace motion `x` with velocity `v` at `t`
gives the joint motion `θ = g ∘ x` with velocity `J(θ(t))⁻¹ v` at `t`. -/
theorem hasDerivAt_inverse_comp {g : (Fin n → ℝ) → Fin n → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    {x : ℝ → Fin n → ℝ} {v : Fin n → ℝ} {t : ℝ} (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => g (x s)) ((jac f (g (x t)))⁻¹ *ᵥ v) t := by
  have hJ := isUnit_det_jac_of_inverse f hf hg hfg hgf (g (x t))
  have h1 := (hg (x t)).hasFDerivAt.comp_hasDerivAt t hx
  have hv : (jac f (g (x t)))⁻¹ *ᵥ v = fderiv ℝ g (x t) v := by
    rw [velocity_eq_inv_mulVec hJ (fderiv ℝ g (x t) v), jac_mulVec_fderiv_of_inverse f hf hg hfg]
  rw [hv]
  exact h1

/-- **The workspace system `(M̃, C̃, Ñ)` of MLS eq. (4.55), p. 197, as a robot in the workspace
coordinates `x` (MLS p. 303),** for an inverse `g` of the workspace map `f` (MLS's "smooth and
invertible", p. 196): `M(x) = M̃(g(x))`, `C(x, ẋ) = C̃(g(x), J⁻¹ẋ)`, `N(x, ẋ) = Ñ(g(x), J⁻¹ẋ)`, with
`J = J(g(x))`, so that `θ = g(x)` and `θ̇ = J⁻¹ ẋ`. -/
def workspaceRobot (g : (Fin n → ℝ) → Fin n → ℝ) : Control.RobotSystem n where
  M := fun x => P.workspaceM f (g x)
  C := fun x v => P.workspaceC f (g x) ((jac f (g x))⁻¹ *ᵥ v)
  N := fun x v => P.workspaceN f (g x) ((jac f (g x))⁻¹ *ᵥ v)

/-- **MLS Lemma 4.11(1), p. 197, for the workspace robot:** with `M(q)` positive definite for every
`q` and `J` invertible everywhere, the workspace robot's inertia `M̃(g(x))` is positive definite at
every `x`. -/
theorem workspaceRobot_M_posDef (g : (Fin n → ℝ) → Fin n → ℝ) (hM : ∀ q, (P.M q).PosDef)
    (hJ : ∀ q, IsUnit (jac f q).det) (x : Fin n → ℝ) : ((P.workspaceRobot f g).M x).PosDef := by
  exact P.workspaceM_posDef f (hM (g x)) (hJ (g x))

/-- The Jacobian matrix of a `C²` map is continuous (MLS p. 196, `J = ∂f/∂θ`). -/
private lemma continuous_jac (hf : ContDiff ℝ 2 f) : Continuous (jac f) :=
  continuous_matrix fun i _ =>
    (continuous_apply i).comp ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- `θ ↦ J(θ)⁻¹` is continuous where `J` is invertible everywhere (MLS p. 197). -/
private lemma continuous_jac_inv (hf : ContDiff ℝ 2 f) (hJ : ∀ q, IsUnit (jac f q).det) :
    Continuous fun q => (jac f q)⁻¹ :=
  continuous_iff_continuousAt.mpr fun q =>
    (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (hJ q).ne_zero)).comp (continuous_jac f hf).continuousAt

/-- **The workspace robot's inertia is continuous (MLS p. 197, `M̃ = J⁻ᵀ M J⁻¹`)** for `f` of class
`C²`, `g` continuous and `J` invertible everywhere. -/
theorem continuous_workspaceRobot_M {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hJ : ∀ q, IsUnit (jac f q).det) :
    Continuous (P.workspaceRobot f g).M := by
  have hi := (continuous_jac_inv f hf hJ).comp hg
  exact (hi.matrix_transpose.matrix_mul (P.continuous_M.comp hg)).matrix_mul hi

/-- **The workspace robot's inertia has a derivative along every workspace motion (MLS p. 197, the
`M̃˙` of Lemma 4.11(2)),** for `f` of class `C²` and `g` a differentiable inverse of `f`. -/
theorem differentiableAlongMotions_workspaceRobot {g : (Fin n → ℝ) → Fin n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y)
    (hgf : ∀ q, g (f q) = q) : Control.DifferentiableAlongMotions (P.workspaceRobot f g).M := by
  intro x x' t hx
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hθ := hasDerivAt_inverse_comp f hd hg hfg hgf hx
  exact ⟨_, P.hasDerivAt_workspaceM_comp f hf hθ (isUnit_det_jac_of_inverse f hd hg hfg hgf _)⟩

/-- **MLS Lemma 4.11(2), p. 197, as the skew property of the workspace robot (MLS p. 300):** with
symmetric link inertias, `f` of class `C²` and `g` a differentiable inverse of `f`, along every
workspace motion `M̃˙ − 2C̃` is skew-symmetric. -/
theorem workspaceRobot_hasSkewProperty (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f) (hg : Differentiable ℝ g)
    (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q) :
    (P.workspaceRobot f g).HasSkewProperty := by
  intro x x' t Md hx hMd
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hθ := hasDerivAt_inverse_comp f hd hg hfg hgf hx
  exact P.skew_deriv_workspaceM_sub_two_workspaceC f h hf hθ
    (isUnit_det_jac_of_inverse f hd hg hfg hgf _) hMd

/-! ### Joint and workspace solutions (MLS p. 198, `τ = Jᵀ F`) -/

/-- **A workspace feedback law applied through `τ = Jᵀ F` (MLS p. 198):** for `F(t, x, ẋ)`, the
joint feedback law `τ(t, θ, θ̇) = J(θ)ᵀ F(t, f(θ), J(θ) θ̇)`. -/
def workspaceTorque (F : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ) :
    ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun t q v => (jac f q)ᵀ *ᵥ F t (f q) (jac f q *ᵥ v)

/-- The workspace state `(f(θ), J(θ) θ̇)` depends continuously on `(θ, θ̇)` (MLS p. 196). -/
private lemma continuous_workspaceState (hf : ContDiff ℝ 2 f) :
    Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => (f p.1, jac f p.1 *ᵥ p.2) :=
  (hf.continuous.comp continuous_fst).prodMk
    (((continuous_jac f hf).comp continuous_fst).matrix_mulVec continuous_snd)

/-- The joint state `(g(x), J⁻¹ ẋ)` depends continuously on `(x, ẋ)` (MLS p. 196). -/
private lemma continuous_jointState {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hJ : ∀ q, IsUnit (jac f q).det) :
    Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => (g p.1, (jac f (g p.1))⁻¹ *ᵥ p.2) :=
  (hg.comp continuous_fst).prodMk
    (((continuous_jac_inv f hf hJ).comp (hg.comp continuous_fst)).matrix_mulVec continuous_snd)

/-- `J (J⁻¹ ẋ) = ẋ` where `J` is invertible everywhere (MLS p. 196). -/
private lemma jac_mulVec_inv_mulVec_of (hJ : ∀ q, IsUnit (jac f q).det) (q V : Fin n → ℝ) :
    jac f q *ᵥ ((jac f q)⁻¹ *ᵥ V) = V := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hJ q), Matrix.one_mulVec]

/-- `J⁻¹ (J θ̇) = θ̇` where `J` is invertible everywhere (MLS p. 196). -/
private lemma inv_mulVec_jac_mulVec_of (hJ : ∀ q, IsUnit (jac f q).det) (q v : Fin n → ℝ) :
    (jac f q)⁻¹ *ᵥ (jac f q *ᵥ v) = v :=
  (velocity_eq_inv_mulVec (hJ q) v).symm

/-- The joint acceleration under `τ = Jᵀ F` gives the workspace acceleration of (4.55): with
`a = M⁻¹ (Jᵀ F − C v − N)`, `J̇ v + J a = M̃⁻¹ (F − C̃ J v − Ñ)` (MLS pp. 197–198). -/
private lemma workspace_accel_inv {q : Fin n → ℝ} (hM : (P.M q).PosDef)
    (hJ : IsUnit (jac f q).det) (v Fv : Fin n → ℝ) :
    jacDot f q v *ᵥ v + jac f q *ᵥ ((P.M q)⁻¹ *ᵥ ((jac f q)ᵀ *ᵥ Fv - P.C q v *ᵥ v - P.N q v)) =
      (P.workspaceM f q)⁻¹ *ᵥ
        (Fv - P.workspaceC f q v *ᵥ (jac f q *ᵥ v) - P.workspaceN f q v) := by
  have hMt := P.workspaceM_posDef f hM hJ
  set w := (P.workspaceM f q)⁻¹ *ᵥ
    (Fv - P.workspaceC f q v *ᵥ (jac f q *ᵥ v) - P.workspaceN f q v) with hw
  have hF : P.workspaceM f q *ᵥ w + P.workspaceC f q v *ᵥ (jac f q *ᵥ v) +
      P.workspaceN f q v = Fv := by
    rw [hw, Control.PosDef.mulVec_inv_mulVec hMt]
    abel
  set a := (P.M q)⁻¹ *ᵥ ((jac f q)ᵀ *ᵥ Fv - P.C q v *ᵥ v - P.N q v) with ha
  have hMa : P.M q *ᵥ a + P.C q v *ᵥ v + P.N q v = (jac f q)ᵀ *ᵥ Fv := by
    rw [ha, Control.PosDef.mulVec_inv_mulVec hM]
    abel
  have key := P.workspaceDynamics_eq f hJ v a
  rw [hMa, inv_transpose_mulVec_transpose_mulVec' hJ, ← hF] at key
  have h2 := add_right_cancel (add_right_cancel key)
  rw [← Control.PosDef.inv_mulVec_mulVec hMt (jacDot f q v *ᵥ v + jac f q *ᵥ a), h2,
    Control.PosDef.inv_mulVec_mulVec hMt]

/-- The workspace acceleration of (4.55) gives the joint acceleration under `τ = Jᵀ F`: with
`θ̇ = J⁻¹ ẋ`, `θ̈ = (d/dt)(J⁻¹) ẋ + J⁻¹ ẍ` solves `M θ̈ + C θ̇ + N = Jᵀ F` (MLS pp. 196–198). -/
private lemma joint_accel_of_workspace {q : Fin n → ℝ} (hM : (P.M q).PosDef)
    (hJ : IsUnit (jac f q).det) (V Fv : Fin n → ℝ) :
    (-((jac f q)⁻¹ * jacDot f q ((jac f q)⁻¹ *ᵥ V) * (jac f q)⁻¹)) *ᵥ V +
        (jac f q)⁻¹ *ᵥ ((P.workspaceM f q)⁻¹ *ᵥ (Fv - P.workspaceC f q ((jac f q)⁻¹ *ᵥ V) *ᵥ V -
          P.workspaceN f q ((jac f q)⁻¹ *ᵥ V))) =
      (P.M q)⁻¹ *ᵥ ((jac f q)ᵀ *ᵥ Fv - P.C q ((jac f q)⁻¹ *ᵥ V) *ᵥ ((jac f q)⁻¹ *ᵥ V) -
        P.N q ((jac f q)⁻¹ *ᵥ V)) := by
  have hMt := P.workspaceM_posDef f hM hJ
  have hJw : jac f q *ᵥ ((jac f q)⁻¹ *ᵥ V) = V := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec]
  set vd := (P.workspaceM f q)⁻¹ *ᵥ (Fv - P.workspaceC f q ((jac f q)⁻¹ *ᵥ V) *ᵥ V -
    P.workspaceN f q ((jac f q)⁻¹ *ᵥ V)) with hvd
  set a := (-((jac f q)⁻¹ * jacDot f q ((jac f q)⁻¹ *ᵥ V) * (jac f q)⁻¹)) *ᵥ V +
    (jac f q)⁻¹ *ᵥ vd with ha
  have hacc : jacDot f q ((jac f q)⁻¹ *ᵥ V) *ᵥ ((jac f q)⁻¹ *ᵥ V) + jac f q *ᵥ a = vd := by
    have e1 : jac f q *ᵥ ((jac f q)⁻¹ *ᵥ vd) = vd := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec]
    have e2 : jac f q *ᵥ (((jac f q)⁻¹ * jacDot f q ((jac f q)⁻¹ *ᵥ V) * (jac f q)⁻¹) *ᵥ V) =
        jacDot f q ((jac f q)⁻¹ *ᵥ V) *ᵥ ((jac f q)⁻¹ *ᵥ V) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc,
        Matrix.mul_nonsing_inv _ hJ, one_mul]
    rw [ha, Matrix.mulVec_add, Matrix.neg_mulVec, Matrix.mulVec_neg, e2, e1]
    abel
  have hvd' : P.workspaceM f q *ᵥ vd + P.workspaceC f q ((jac f q)⁻¹ *ᵥ V) *ᵥ V +
      P.workspaceN f q ((jac f q)⁻¹ *ᵥ V) = Fv := by
    rw [hvd, Control.PosDef.mulVec_inv_mulVec hMt]
    abel
  have key := P.workspaceDynamics_eq f hJ ((jac f q)⁻¹ *ᵥ V) a
  rw [hacc, hJw, hvd'] at key
  have hMa : P.M q *ᵥ a + P.C q ((jac f q)⁻¹ *ᵥ V) *ᵥ ((jac f q)⁻¹ *ᵥ V) +
      P.N q ((jac f q)⁻¹ *ᵥ V) = (jac f q)ᵀ *ᵥ Fv := by
    rw [key, transpose_mulVec_inv_transpose_mulVec' hJ]
  rw [← hMa]
  have hs : P.M q *ᵥ a + P.C q ((jac f q)⁻¹ *ᵥ V) *ᵥ ((jac f q)⁻¹ *ᵥ V) +
      P.N q ((jac f q)⁻¹ *ᵥ V) - P.C q ((jac f q)⁻¹ *ᵥ V) *ᵥ ((jac f q)⁻¹ *ᵥ V) -
      P.N q ((jac f q)⁻¹ *ᵥ V) = P.M q *ᵥ a := by
    abel
  rw [hs, Control.PosDef.inv_mulVec_mulVec hM]

/-- **Joint solutions give workspace solutions (MLS eq. (4.55), p. 197).** With `M(q)` positive
definite for every `q`, `f` of class `C²`, `g ∘ f = id` and `J` invertible everywhere: if
`z = (θ, θ̇)` solves the joint system under `τ = Jᵀ F` from `t₀`, then `(f(θ), J(θ) θ̇)` solves the
workspace robot's system under `F` from `t₀`. -/
theorem isSolution_workspaceRobot_of_isSolution (hM : ∀ q, (P.M q).PosDef)
    {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hgf : ∀ q, g (f q) = q) (hJ : ∀ q, IsUnit (jac f q).det)
    {F : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ} {t₀ : ℝ}
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : Stability.IsSolution (P.field (workspaceTorque f F)) t₀ z) :
    Stability.IsSolution ((P.workspaceRobot f g).field F) t₀
      (fun t => (f (z t).1, jac f (z t).1 *ᵥ (z t).2)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  refine ⟨(continuous_workspaceState f hf).comp_continuousOn hz.1, fun t ht => ?_⟩
  have hfst : HasDerivAt (fun s => (z s).1) (z t).2 t := (hz.2 t ht).fst
  have h1 := hasDerivAt_comp (hd _) hfst
  have h2 := hasDerivAt_jac_mulVec_comp hf (θ := fun s => (z s).1) (θ' := fun s => (z s).2) hfst
    (hz.2 t ht).snd
  convert h1.prodMk h2 using 1
  simp only [Control.RobotSystem.field, workspaceRobot, field, workspaceTorque, hgf,
    inv_mulVec_jac_mulVec_of f hJ, Prod.mk.injEq, true_and]
  exact (P.workspace_accel_inv f (hM _) (hJ _) _ _).symm

/-- **Workspace solutions give joint solutions (MLS p. 196, `θ = g(x)`, `θ̇ = J⁻¹ ẋ`).** With `M(q)`
positive definite for every `q`, `f` of class `C²` and `g` a differentiable inverse of `f`: if
`y = (x, ẋ)` solves the workspace robot's system under `F` from `t₀`, then `(g(x), J(g(x))⁻¹ ẋ)`
solves the joint system under `τ = Jᵀ F` from `t₀`. -/
theorem isSolution_of_isSolution_workspaceRobot (hM : ∀ q, (P.M q).PosDef)
    {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    {F : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ} {t₀ : ℝ}
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hy : Stability.IsSolution ((P.workspaceRobot f g).field F) t₀ y) :
    Stability.IsSolution (P.field (workspaceTorque f F)) t₀
      (fun t => (g (y t).1, (jac f (g (y t).1))⁻¹ *ᵥ (y t).2)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJ : ∀ q, IsUnit (jac f q).det := isUnit_det_jac_of_inverse f hd hg hfg hgf
  refine ⟨(continuous_jointState f hf hg.continuous hJ).comp_continuousOn hy.1, fun t ht => ?_⟩
  have hX : HasDerivAt (fun s => (y s).1) (y t).2 t := (hy.2 t ht).fst
  have hθ := hasDerivAt_inverse_comp f hd hg hfg hgf hX
  have hθ' := Control.hasDerivAt_matrix_mulVec (hasDerivAt_jac_inv_comp hf hθ (hJ _))
    (hy.2 t ht).snd
  convert hθ.prodMk hθ' using 1
  simp only [Control.RobotSystem.field, workspaceRobot, field, workspaceTorque, hfg,
    jac_mulVec_inv_mulVec_of f hJ, Prod.mk.injEq, true_and]
  exact (P.joint_accel_of_workspace f (hM _) (hJ _) _ _).symm

/-- **The workspace PD law is PD control of the workspace robot applied through `τ = Jᵀ F` (MLS p.
198):** for `g ∘ f = id` and `J` invertible everywhere, the joint law `workspacePDTorque` is
`workspaceTorque` of the workspace robot's PD law with compensation of `N`. -/
theorem workspacePDTorque_eq_workspaceTorque {g : (Fin n → ℝ) → Fin n → ℝ}
    (hgf : ∀ q, g (f q) = q) (hJ : ∀ q, IsUnit (jac f q).det)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (xd : Fin n → ℝ) :
    P.workspacePDTorque f Kp Kv xd =
      workspaceTorque f ((P.workspaceRobot f g).pdCompensatedTorque Kp Kv xd) := by
  funext t q v
  simp only [workspacePDTorque, workspaceTorque, Control.RobotSystem.pdCompensatedTorque,
    workspaceRobot, hgf, inv_mulVec_jac_mulVec_of f hJ]

/-- **A flow of the joint closed loop gives a flow of the workspace closed loop (the standing
existence assumption of MLS p. 179, transported by `x = f(θ)`, `ẋ = J θ̇`).** With `M(q)` positive
definite for every `q`, `f` of class `C²` and `g` a differentiable inverse of `f`: a flow of the
joint system under the workspace PD law gives a flow of the workspace robot's closed loop (4.52). -/
theorem exists_hasFlow_workspaceRobot (hM : ∀ q, (P.M q).PosDef)
    {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (xd : Fin n → ℝ)
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.field (P.workspacePDTorque f Kp Kv xd) 0) φ) :
    ∃ ψ, Stability.HasFlow ((P.workspaceRobot f g).pdClosedLoop Kp Kv xd) ψ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJ : ∀ q, IsUnit (jac f q).det := isUnit_det_jac_of_inverse f hd hg hfg hgf
  have hhk : ∀ y : (Fin n → ℝ) × (Fin n → ℝ),
      (f (g y.1), jac f (g y.1) *ᵥ ((jac f (g y.1))⁻¹ *ᵥ y.2)) = y := fun y => by
    rw [hfg, jac_mulVec_inv_mulVec_of f hJ]
  have hto : ∀ t₀ (x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      Stability.IsSolution (fun _ => P.field (P.workspacePDTorque f Kp Kv xd) 0) t₀ x →
      Stability.IsSolution (fun _ => (P.workspaceRobot f g).pdClosedLoop Kp Kv xd) t₀
        (fun t => (f (x t).1, jac f (x t).1 *ᵥ (x t).2)) := by
    intro t₀ x hx
    have hx' : Stability.IsSolution
        (P.field (workspaceTorque f ((P.workspaceRobot f g).pdCompensatedTorque Kp Kv xd)))
        t₀ x := by
      rw [← P.workspacePDTorque_eq_workspaceTorque f hgf hJ]
      exact hx
    exact P.isSolution_workspaceRobot_of_isSolution f hM hf hgf hJ hx'
  have hfrom : ∀ t₀ (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)),
      Stability.IsSolution (fun _ => (P.workspaceRobot f g).pdClosedLoop Kp Kv xd) t₀ y →
      Stability.IsSolution (fun _ => P.field (P.workspacePDTorque f Kp Kv xd) 0) t₀
        (fun t => (g (y t).1, (jac f (g (y t).1))⁻¹ *ᵥ (y t).2)) := by
    intro t₀ y hy
    have := P.isSolution_of_isSolution_workspaceRobot f hM hf hg hfg hgf
      (F := (P.workspaceRobot f g).pdCompensatedTorque Kp Kv xd) hy
    rw [← P.workspacePDTorque_eq_workspaceTorque f hgf hJ] at this
    exact this
  refine ⟨fun t y => (f (φ t (g y.1, (jac f (g y.1))⁻¹ *ᵥ y.2)).1,
    jac f (φ t (g y.1, (jac f (g y.1))⁻¹ *ᵥ y.2)).1 *ᵥ (φ t (g y.1, (jac f (g y.1))⁻¹ *ᵥ y.2)).2),
    ⟨fun y => ?_, fun y => ?_, fun t₀ ht₀ y hy t ht => ?_, fun t ht => ?_⟩⟩
  · simp only [hφ.map_zero]
    exact hhk y
  · exact hto 0 _ (hφ.isSolution _)
  · have := hφ.eq_of_isSolution t₀ ht₀ _ (hfrom t₀ y hy) t ht
    rw [← this]
    exact (hhk (y t)).symm
  · exact (continuous_workspaceState f hf).comp
      ((hφ.continuous t ht).comp (continuous_jointState f hf hg.continuous hJ))

/-! ### The workspace PD law: Proposition 4.9 in workspace coordinates -/

/-- **The workspace PD law (MLS p. 198 with Proposition 4.9, p. 193): global asymptotic stability in
workspace coordinates.** With symmetric link inertias, `M(q)` positive definite for every `q`, `f`
of class `C²` with a differentiable inverse `g`, `M̃` uniformly positive definite, `K_p`, `K_v`
symmetric positive definite and a flow of the joint closed loop under the workspace PD law, the set
point `(x_d, 0)` of the workspace robot under PD control with compensation of `N` is globally
asymptotically stable at every `t₀ ≥ 0` (state `(x, ẋ)`, sup norm). -/
theorem globallyAsymptoticallyStableAt_workspacePD (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.workspaceM f q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) (xd : Fin n → ℝ)
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.field (P.workspacePDTorque f Kp Kv xd) 0) φ) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt
      ((P.workspaceRobot f g).field ((P.workspaceRobot f g).pdCompensatedTorque Kp Kv xd))
      (xd, 0) t₀ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJ : ∀ q, IsUnit (jac f q).det := isUnit_det_jac_of_inverse f hd hg hfg hgf
  obtain ⟨ψ, hψ⟩ := P.exists_hasFlow_workspaceRobot f hM hf hg hfg hgf Kp Kv xd hφ
  obtain ⟨lam, hlam, hb⟩ := hMu
  exact (P.workspaceRobot f g).globallyAsymptoticallyStableAt_pdCompensatedTorque
    (P.workspaceRobot_M_posDef f g hM hJ) (P.continuous_workspaceRobot_M f hf hg.continuous hJ)
    (P.differentiableAlongMotions_workspaceRobot f hf hg hfg hgf)
    (P.workspaceRobot_hasSkewProperty f h hf hg hfg hgf) ⟨lam, hlam, fun q v => hb (g q) v⟩ hKp
    hKv hψ ht₀

/-- **The workspace PD law (MLS p. 198 with Proposition 4.9, p. 193): the workspace error of the
joint closed loop tends to zero.** Under the hypotheses of
`globallyAsymptoticallyStableAt_workspacePD`, every solution `(θ, θ̇)` from `t₀ ≥ 0` of the
manipulator under the workspace PD law has `(f(θ(t)), J(θ(t)) θ̇(t)) → (x_d, 0)`. -/
theorem tendsto_workspacePD (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.workspaceM f q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) (xd : Fin n → ℝ)
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.field (P.workspacePDTorque f Kp Kv xd) 0) φ) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : Stability.IsSolution (P.field (P.workspacePDTorque f Kp Kv xd)) t₀ z) :
    Tendsto (fun t => (f (z t).1, jac f (z t).1 *ᵥ (z t).2)) atTop (𝓝 (xd, 0)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJ : ∀ q, IsUnit (jac f q).det := isUnit_det_jac_of_inverse f hd hg hfg hgf
  have hz' : Stability.IsSolution
      (P.field (workspaceTorque f ((P.workspaceRobot f g).pdCompensatedTorque Kp Kv xd))) t₀ z := by
    rw [← P.workspacePDTorque_eq_workspaceTorque f hgf hJ]
    exact hz
  exact (P.globallyAsymptoticallyStableAt_workspacePD f h hM hf hg hfg hgf hMu hKp hKv xd hφ
    ht₀).2 _ (P.isSolution_workspaceRobot_of_isSolution f hM hf hgf hJ hz')

/-- **The workspace PD law (MLS p. 198 with Proposition 4.9, p. 193): Lyapunov stability of the
workspace error of the joint closed loop.** Under the hypotheses of
`globallyAsymptoticallyStableAt_workspacePD`, for every `ε > 0` there is `δ > 0` such that every
solution `(θ, θ̇)` from `t₀ ≥ 0` under the workspace PD law with `‖(f(θ(t₀)) − x_d, J θ̇(t₀))‖ < δ`
satisfies `‖(f(θ(t)) − x_d, J θ̇(t))‖ < ε` for all `t ≥ t₀` (sup norm). -/
theorem stable_workspacePD (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.workspaceM f q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) (xd : Fin n → ℝ)
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.field (P.workspacePDTorque f Kp Kv xd) 0) φ) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.workspacePDTorque f Kp Kv xd)) t₀ z →
      ‖(f (z t₀).1 - xd, jac f (z t₀).1 *ᵥ (z t₀).2)‖ < δ →
      ∀ t, t₀ ≤ t → ‖(f (z t).1 - xd, jac f (z t).1 *ᵥ (z t).2)‖ < ε := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJ : ∀ q, IsUnit (jac f q).det := isUnit_det_jac_of_inverse f hd hg hfg hgf
  intro ε hε
  obtain ⟨δ, hδ, hst⟩ := (P.globallyAsymptoticallyStableAt_workspacePD f h hM hf hg hfg hgf hMu
    hKp hKv xd hφ ht₀).1 ε hε
  refine ⟨δ, hδ, fun z hz h0 t ht => ?_⟩
  have hz' : Stability.IsSolution
      (P.field (workspaceTorque f ((P.workspaceRobot f g).pdCompensatedTorque Kp Kv xd))) t₀ z := by
    rw [← P.workspacePDTorque_eq_workspaceTorque f hgf hJ]
    exact hz
  have := hst _ (P.isSolution_workspaceRobot_of_isSolution f hM hf hgf hJ hz')
    (by simpa using h0) t ht
  simpa using this

end ManipulatorModel
end RoboLean
