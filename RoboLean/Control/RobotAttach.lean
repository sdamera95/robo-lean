import RoboLean.Control.RobotControl
import RoboLean.Control.WorkspacePDControl
import RoboLean.Dynamics.HandControl
import RoboLean.Dynamics.StackedFingers

/-!
# The `attach` operation on robots (MLS §6.5.2, pp. 303–305, Figure 6.11)

**What MLS states (pp. 304–305).** "The arguments to the attach operation are a list of robots,
which we refer to as fingers, together with a single object which we refer to as the payload. In
addition, we are given a constraint between the configuration variables of the fingers and those of
the object ... of the form `h(θ, x) = 0`. ... we use the Lagrange-d'Alembert equations to write the
dynamics in terms of the payload variables `x ∈ ℝᵖ`. Let `(M_f, C_f, N_f)` be the (block-diagonal)
parameters for the fingers and `(M_p, C_p, N_p)` be those of the payload. The dynamic parameters for
the constrained robot are given by" `M̃ := M_p + G J⁻ᵀ M_f J⁻¹ G`,
`C̃ := C_p + G J⁻ᵀ C_f J⁻¹ G + G J⁻ᵀ M_f (d/dt)(J⁻¹ G)`, `Ñ := N_p + G J⁻ᵀ N_f`, "where `J = ∂h/∂θ`,
`Gᵀ = −∂h/∂x`, and we assume that `J` is invertible for the purposes of exposition". The data flow
of Figure 6.11 sends a force command `F_d` to the fingers as `τ_d = Jᵀ G⁺ F_d` and reads the force
`F = G J⁻ᵀ τ`; "the attach operation can be used to ... change from joint space to workspace
coordinates" (p. 305).

**Formalized.**

* `RobotSystem.stack`: the list of fingers as one robot with block-diagonal `M_f`, `C_f` and stacked
  `N_f` (MLS (6.16)); its equations are the fingers' (`stack_equations_iff`); positive definiteness,
  the skew property, differentiability along motions and continuity pass to the stack.
* `AttachConstraint n p`: the finger configuration `θ = σ(x)` on the constraint, `J(x)`, `G(x)` and
  the rate `Bd(x, ẋ)` of `J⁻¹ Gᵀ`; the finger velocity `θ̇ = J⁻¹ Gᵀ ẋ` and acceleration
  `θ̈ = J⁻¹ Gᵀ ẍ + Bd ẋ`. For a holonomic constraint `h` (`IsHolonomic`, `J = ∂h/∂θ`, `Gᵀ = −∂h/∂x`
  at `(σ(x), x)`) the finger motion obeys the grasp constraint (6.18) `J θ̇ = Gᵀ ẋ`
  (`IsHolonomic.constraint`); `HasRate` says that `Bd` is the actual derivative of `J⁻¹ Gᵀ` along
  motions.
* `RobotSystem.attach F P A`: the composite robot on the payload coordinates, with the printed
  parameters read with `Gᵀ` where p. 305 prints `G` (the dimensions require it; (6.22), p. 278,
  prints `Gᵀ`). It is `Composite.handRobot` with the finger fields evaluated on the constraint
  (`attach_eq_handRobot`). Lemma 6.1 for `attach`: positive definiteness from the payload or, the
  book's route, from the fingers with `J` invertible and `G` onto (`attach_M_posDef`,
  `attach_M_posDef_of_surjective`); the skew property from those of the parts
  (`attach_hasSkewProperty`); differentiability along motions and continuity
  (`attach_differentiableAlongMotions`, `attach_continuous_M`). So every Chapter 4 controller
  applies to the attached robot.
* The equations of the attached robot are the constrained equations of fingers and payload with the
  constraint force `λ` (MLS (6.24), sign of p. 267): `∃ λ, M_f θ̈ + C_f θ̇ + N_f + Jᵀ λ = τ` and
  `M_p ẍ + C_p ẋ + N_p = G λ` exactly when `M̃ ẍ + C̃ ẋ + Ñ = G J⁻ᵀ τ` (`attach_equations_iff`).
* Figure 6.11: the command `τ_d = Jᵀ G⁺ F_d` produces `F = F_d`
  (`effectiveForce_attachTorqueCommand`); reading the payload velocity from the fingers,
  `ẋ = G⁺ᵀ J θ̇` (MLS p. 310, `ẋ_b ← G⁺ᵀ ẋ_f`; `velocity_eq_of_constraint`).
* Workspace coordinates (p. 305): attaching a manipulator to the zero payload through `θ = g(x)`,
  `J = ∂f/∂θ`, `G = I` gives exactly the workspace robot of MLS (4.55)
  (`ManipulatorModel.toRobotSystem_attach_workspaceAttach`).

**Hypotheses MLS does not state**, explicit where used: `J(x)` invertible; the finger configuration
`σ(x)` on the constraint as data (MLS reads the payload configuration from the fingers by solving
`h(θ, x) = 0`; with `J` invertible `θ` is locally a function of `x`, which is taken here as given);
`M_f` symmetric, `M_p`, `M_f` differentiable along motions, the derivative of `σ` along motions and
the rate `Bd`. Inputs and outputs other than forces and velocities are not modeled; nothing here
concerns a physical hand. Configurations `Fin n → ℝ` (fingers) and `Fin p → ℝ` (payload).
-/

noncomputable section

open Matrix Filter Topology Set
open RoboLean.MapJacobian RoboLean.Composite

namespace RoboLean
namespace Control

/-- **The constraint data of the `attach` operation (MLS printed pp. 304–305):** the finger
configuration `θ = σ(x)` that solves the constraint `h(θ, x) = 0` at the payload configuration `x`,
`J(x) = ∂h/∂θ`, `G(x)` with `Gᵀ = −∂h/∂x` (both at `(σ(x), x)`), and `Bd(x, ẋ)`, the rate
`(d/dt)(J⁻¹ Gᵀ)` along a motion with velocity `ẋ` (MLS p. 305's `(d/dt)(J⁻¹ G)`). -/
structure AttachConstraint (n p : ℕ) where
  /-- The finger configuration on the constraint, `θ = σ(x)` (MLS p. 305). -/
  σ : (Fin p → ℝ) → Fin n → ℝ
  /-- `J = ∂h/∂θ` at `(σ(x), x)` (MLS p. 305). -/
  J : (Fin p → ℝ) → Matrix (Fin n) (Fin n) ℝ
  /-- `G` with `Gᵀ = −∂h/∂x` at `(σ(x), x)` (MLS p. 305). -/
  G : (Fin p → ℝ) → Matrix (Fin p) (Fin n) ℝ
  /-- The rate `(d/dt)(J⁻¹ Gᵀ)` at `(x, ẋ)` (MLS p. 305). -/
  Bd : (Fin p → ℝ) → (Fin p → ℝ) → Matrix (Fin n) (Fin p) ℝ

namespace AttachConstraint

variable {n p : ℕ} (A : AttachConstraint n p)

/-- **The finger velocity on the constraint (MLS p. 278, `θ̇ = J_h⁻¹ Gᵀ ẋ`):** `J(x)⁻¹ G(x)ᵀ ẋ`. -/
def fingerVelocity (x v : Fin p → ℝ) : Fin n → ℝ :=
  ((A.J x)⁻¹ * (A.G x)ᵀ) *ᵥ v

/-- **The finger acceleration on the constraint (MLS p. 278, eliminating `θ̈`):**
`J(x)⁻¹ G(x)ᵀ ẍ + Bd(x, ẋ) ẋ`. -/
def fingerAcceleration (x v a : Fin p → ℝ) : Fin n → ℝ :=
  ((A.J x)⁻¹ * (A.G x)ᵀ) *ᵥ a + A.Bd x v *ᵥ v

/-- **The constraint data come from a holonomic constraint (MLS p. 304, `h(θ, x) = 0`; `J = ∂h/∂θ`,
`Gᵀ = −∂h/∂x`, p. 305):** for `h` on the composite configuration `q ∈ ℝᴺ` relabeled by `e` (payload
coordinates first), at every `x` the point `q = (x, σ(x))` is on `h = 0`, `J(x)` is the block of
`∂h/∂q` for the finger columns and `G(x)ᵀ` minus the block for the payload columns. -/
def IsHolonomic {N : ℕ} (e : Fin p ⊕ Fin n ≃ Fin N) (h : (Fin N → ℝ) → Fin n → ℝ) : Prop :=
  ∀ x, h (Constrained.splitJoin e x (A.σ x)) = 0 ∧
    A.J x = Constrained.colsSnd (jac h (Constrained.splitJoin e x (A.σ x))) e ∧
    (A.G x)ᵀ = -Constrained.colsFst (jac h (Constrained.splitJoin e x (A.σ x))) e

/-- The composite motion `s ↦ (x(s), θ(s))` has the velocity `(ẋ, θ̇)` (MLS p. 272, `q = (q₁, q₂)`).
-/
private theorem hasDerivAt_splitJoin {N : ℕ} (e : Fin p ⊕ Fin n ≃ Fin N) {x : ℝ → Fin p → ℝ}
    {θ : ℝ → Fin n → ℝ} {x' : Fin p → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hx : HasDerivAt x x' t)
    (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => Constrained.splitJoin e (x s) (θ s))
      (Constrained.splitJoin e x' θ') t := by
  refine hasDerivAt_pi.mpr fun j => ?_
  simp only [Constrained.splitJoin]
  rcases e.symm j with a | b
  · exact hasDerivAt_pi.mp hx a
  · exact hasDerivAt_pi.mp hθ b

variable {A} in
/-- **The finger motion of a holonomic constraint obeys the grasp constraint (MLS eq. (6.18), p.
277, and (6.27)–(6.28), p. 284):** if the constraint data come from `h`, `h` is differentiable at
`(x(t), σ(x(t)))`, the payload motion `x` has velocity `x'` at `t` and the finger motion `σ ∘ x` has
velocity `θ'` at `t`, then `J θ' = Gᵀ x'`. -/
theorem IsHolonomic.constraint {N : ℕ} {e : Fin p ⊕ Fin n ≃ Fin N}
    {h : (Fin N → ℝ) → Fin n → ℝ} (hA : A.IsHolonomic e h) {x : ℝ → Fin p → ℝ}
    {x' : Fin p → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hh : DifferentiableAt ℝ h (Constrained.splitJoin e (x t) (A.σ (x t))))
    (hx : HasDerivAt x x' t) (hθ : HasDerivAt (fun s => A.σ (x s)) θ' t) :
    A.J (x t) *ᵥ θ' = (A.G (x t))ᵀ *ᵥ x' := by
  have h := hybrid_constraint e (q := fun s => Constrained.splitJoin e (x s) (A.σ (x s))) hh
    (hasDerivAt_splitJoin e hx hθ) (Eventually.of_forall fun s => (hA (x s)).1)
  rw [Constrained.splitSnd_splitJoin, Constrained.splitFst_splitJoin] at h
  rw [(hA (x t)).2.1, (hA (x t)).2.2]
  exact h

variable {A} in
/-- **With `J` invertible the finger velocity is `J⁻¹ Gᵀ ẋ` (MLS p. 278):** under the hypotheses of
`IsHolonomic.constraint` and `J(x(t))` invertible, `θ' = fingerVelocity (x(t)) x'`. -/
theorem IsHolonomic.eq_fingerVelocity {N : ℕ} {e : Fin p ⊕ Fin n ≃ Fin N}
    {h : (Fin N → ℝ) → Fin n → ℝ} (hA : A.IsHolonomic e h) {x : ℝ → Fin p → ℝ}
    {x' : Fin p → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hh : DifferentiableAt ℝ h (Constrained.splitJoin e (x t) (A.σ (x t))))
    (hx : HasDerivAt x x' t) (hθ : HasDerivAt (fun s => A.σ (x s)) θ' t)
    (hJ : IsUnit (A.J (x t)).det) : θ' = A.fingerVelocity (x t) x' := by
  rw [fingerVelocity, ← Matrix.mulVec_mulVec, ← hA.constraint hh hx hθ, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]

/-- **`Bd` is the rate of `J⁻¹ Gᵀ` along every motion (MLS p. 305, `(d/dt)(J⁻¹ G)`):** for every
payload motion `x` with velocity `x'` at `t`, the entries of `s ↦ J(x(s))⁻¹ G(x(s))ᵀ` have the
derivative `Bd(x(t), x')` at `t`. -/
def HasRate : Prop :=
  ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}, HasDerivAt x x' t →
    ∀ i j, HasDerivAt (fun s => ((A.J (x s))⁻¹ * (A.G (x s))ᵀ) i j) (A.Bd (x t) x' i j) t

/-- **The finger acceleration is the derivative of the finger velocity (MLS p. 278,
`θ̈ = J_h⁻¹ Gᵀ ẍ + (d/dt)(J_h⁻¹ Gᵀ) ẋ`):** with `HasRate`, along a payload motion with velocity
`x'(t)` and acceleration `a` at `t`, `s ↦ fingerVelocity (x(s)) (x'(s))` has the derivative
`fingerAcceleration (x(t)) (x'(t)) a` at `t`. -/
theorem hasDerivAt_fingerVelocity (hB : A.HasRate) {x x' : ℝ → Fin p → ℝ} {a : Fin p → ℝ}
    {t : ℝ} (hx : HasDerivAt x (x' t) t) (hx' : HasDerivAt x' a t) :
    HasDerivAt (fun s => A.fingerVelocity (x s) (x' s))
      (A.fingerAcceleration (x t) (x' t) a) t := by
  have h := Control.hasDerivAt_matrix_mulVec_rect
    (A := fun s => (A.J (x s))⁻¹ * (A.G (x s))ᵀ) (hB hx) hx'
  rw [fingerAcceleration, add_comm]
  exact h

/-- **The force command of Figure 6.11 (MLS p. 306, `τ_d = Jᵀ G⁺ F_d`):** the joint torques sent to
the fingers for a payload force command `F_d`, (6.36) with `f_N = 0`. -/
def torqueCommand (x Fd : Fin p → ℝ) : Fin n → ℝ :=
  graspTorque (A.J x) (A.G x) Fd 0

/-- **The commanded force is produced (MLS Figure 6.11, p. 306, with (6.36), p. 301):** for `J(x)`
invertible and `G(x)` onto, `G J⁻ᵀ τ_d = F_d`. -/
theorem effectiveForce_torqueCommand {x : Fin p → ℝ} (hJ : IsUnit (A.J x).det)
    (hG : Function.Surjective (A.G x).mulVec) (Fd : Fin p → ℝ) :
    effectiveForce (A.J x) (A.G x) (A.torqueCommand x Fd) = Fd := by
  exact effectiveForce_graspTorque hJ hG Fd (Matrix.mulVec_zero _)

/-- **Reading the payload velocity from the fingers (MLS p. 310, `ẋ_b ← G⁺ᵀ ẋ_f`):** for `G` onto, a
payload velocity `v` and finger velocity `θ'` with `J θ' = Gᵀ v` give `v = (G⁺)ᵀ (J θ')`,
`G⁺ = Gᵀ(GGᵀ)⁻¹`. -/
theorem velocity_eq_of_constraint {J : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin p) (Fin n) ℝ}
    (hG : Function.Surjective G.mulVec) {v : Fin p → ℝ} {θ' : Fin n → ℝ}
    (h : J *ᵥ θ' = Gᵀ *ᵥ v) : v = (rightPinv G)ᵀ *ᵥ (J *ᵥ θ') := by
  rw [h, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, mul_rightPinv hG, Matrix.transpose_one,
    Matrix.one_mulVec]

end AttachConstraint

namespace RobotSystem

section Stack

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {N : ℕ}

/-- **A list of robots as one robot (MLS p. 304, "a list of robots, which we refer to as fingers",
with "the (block-diagonal) parameters for the fingers", eq. (6.16), p. 276):** the joints relabeled
by `e : (Σ i, Fin (n i)) ≃ Fin N`, `M_f = diag(M_{fᵢ}(θ_{fᵢ}))`,
`C_f = diag(C_{fᵢ}(θ_{fᵢ}, θ̇_{fᵢ}))`, `N_f = (N_{fᵢ}(θ_{fᵢ}, θ̇_{fᵢ}))`. -/
def stack (e : (Σ i, Fin (n i)) ≃ Fin N) (R : (i : ι) → RobotSystem (n i)) : RobotSystem N where
  M θ := stackMat e fun i => (R i).M (fingerCoords e θ i)
  C θ v := stackMat e fun i => (R i).C (fingerCoords e θ i) (fingerCoords e v i)
  N θ v := stackVec e fun i => (R i).N (fingerCoords e θ i) (fingerCoords e v i)

omit [Fintype ι] in
/-- The stacked matrix at the relabeled joints `e (i, a)`, `e (k, b)` is the block-diagonal entry
(MLS p. 276). -/
private theorem stackMat_apply_e (e : (Σ i, Fin (n i)) ≃ Fin N)
    (A : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ) (c d : Σ i, Fin (n i)) :
    stackMat e A (e c) (e d) = Matrix.blockDiagonal' A c d := by
  simp [stackMat]

omit [Fintype ι] in
/-- A stacked matrix curve has the stacked entrywise derivative (MLS p. 276, `Ṁ_f` block by block).
-/
private theorem hasDerivAt_stackMat (e : (Σ i, Fin (n i)) ≃ Fin N)
    {A : ℝ → (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ}
    {Ad : (i : ι) → Matrix (Fin (n i)) (Fin (n i)) ℝ} {t : ℝ}
    (h : ∀ i a b, HasDerivAt (fun s => A s i a b) (Ad i a b) t) (j l : Fin N) :
    HasDerivAt (fun s => stackMat e (A s) j l) (stackMat e Ad j l) t := by
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective l
  simp only [stackMat_apply_e]
  by_cases hik : i = k
  · subst hik
    simp only [Matrix.blockDiagonal'_apply_eq]
    exact h i a b
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hik]
    exact hasDerivAt_const t 0

omit [Fintype ι] [DecidableEq ι] in
/-- Finger `i`'s joints move with finger `i`'s part of the velocity (MLS p. 276). -/
private theorem hasDerivAt_fingerCoords (e : (Σ i, Fin (n i)) ≃ Fin N) {θ : ℝ → Fin N → ℝ}
    {θ' : Fin N → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t) (i : ι) :
    HasDerivAt (fun s => fingerCoords e (θ s) i) (fingerCoords e θ' i) t :=
  hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mp hθ (e ⟨i, a⟩)

/-- **The stacked robot's equations are the fingers' (MLS eq. (6.16), p. 276):**
`M_f θ̈ + C_f θ̇ + N_f = τ` exactly when every finger's equation holds with `τ_{fᵢ}`. -/
theorem stack_equations_iff (e : (Σ i, Fin (n i)) ≃ Fin N) (R : (i : ι) → RobotSystem (n i))
    (θ θ' θ'' τ : Fin N → ℝ) :
    (stack e R).M θ *ᵥ θ'' + (stack e R).C θ θ' *ᵥ θ' + (stack e R).N θ θ' = τ ↔
      ∀ i, (R i).M (fingerCoords e θ i) *ᵥ fingerCoords e θ'' i +
          (R i).C (fingerCoords e θ i) (fingerCoords e θ' i) *ᵥ fingerCoords e θ' i +
          (R i).N (fingerCoords e θ i) (fingerCoords e θ' i) = fingerCoords e τ i := by
  exact stacked_dynamics_iff e (fun i => (R i).M (fingerCoords e θ i))
    (fun i => (R i).C (fingerCoords e θ i) (fingerCoords e θ' i))
    (fun i => (R i).N (fingerCoords e θ i) (fingerCoords e θ' i)) θ' θ'' τ

/-- **The stacked inertia is positive definite (MLS p. 276 with Lemma 4.2(1), p. 171)** when every
finger's is, at every configuration. -/
theorem stack_M_posDef (e : (Σ i, Fin (n i)) ≃ Fin N) {R : (i : ι) → RobotSystem (n i)}
    (hR : ∀ i q, ((R i).M q).PosDef) (θ : Fin N → ℝ) : ((stack e R).M θ).PosDef := by
  exact stackMat_posDef e fun i => hR i _

omit [Fintype ι] in
/-- **The stacked robot has the skew property when every finger has (MLS p. 276 with Lemma 4.2(2),
p. 171; p. 300).** -/
theorem stack_hasSkewProperty (e : (Σ i, Fin (n i)) ≃ Fin N) {R : (i : ι) → RobotSystem (n i)}
    (hR : ∀ i, (R i).HasSkewProperty) : (stack e R).HasSkewProperty := by
  intro θ θ' t Md hθ hMd
  have hfin : ∀ i a b, HasDerivAt (fun s => (R i).M (fingerCoords e (θ s) i) a b)
      (Md (e ⟨i, a⟩) (e ⟨i, b⟩)) t := fun i a b => by
    simpa [stack, stackMat_apply_e] using hMd (e ⟨i, a⟩) (e ⟨i, b⟩)
  have hMd' : Md = stackMat e fun i => Matrix.of fun a b => Md (e ⟨i, a⟩) (e ⟨i, b⟩) := by
    ext j l
    exact (hMd j l).unique (hasDerivAt_stackMat e (A := fun s i => (R i).M (fingerCoords e (θ s) i))
      (Ad := fun i => Matrix.of fun a b => Md (e ⟨i, a⟩) (e ⟨i, b⟩)) hfin j l)
  rw [hMd']
  exact skew_stackMat_sub_two e fun i => hR i (hasDerivAt_fingerCoords e hθ i) (hfin i)

omit [Fintype ι] in
/-- **The stacked inertia has a derivative along every motion when every finger's has (MLS p. 276,
the `Ṁ_f` of p. 279).** -/
theorem stack_differentiableAlongMotions (e : (Σ i, Fin (n i)) ≃ Fin N)
    {R : (i : ι) → RobotSystem (n i)} (hR : ∀ i, DifferentiableAlongMotions (R i).M) :
    DifferentiableAlongMotions (stack e R).M := by
  intro θ θ' t hθ
  choose Md hMd using fun i => hR i (hasDerivAt_fingerCoords e hθ i)
  exact ⟨stackMat e Md, hasDerivAt_stackMat e (A := fun s i => (R i).M (fingerCoords e (θ s) i))
    hMd⟩

omit [Fintype ι] in
/-- The stacked inertia is continuous when every finger's is (MLS p. 276). -/
theorem stack_continuous_M (e : (Σ i, Fin (n i)) ≃ Fin N) {R : (i : ι) → RobotSystem (n i)}
    (hR : ∀ i, Continuous (R i).M) : Continuous (stack e R).M := by
  refine continuous_matrix fun j l => ?_
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective j
  obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective l
  simp only [stack, stackMat_apply_e]
  by_cases hik : i = k
  · subst hik
    simp only [Matrix.blockDiagonal'_apply_eq]
    exact ((hR i).comp (fingerProj e i).continuous).matrix_elem a b
  · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hik]
    exact continuous_const

end Stack

variable {n p : ℕ}

/-- **The `attach` operation (MLS printed pp. 304–305, Figure 6.11):** fingers `F` (one robot, e.g.
`stack`) and a payload `P` constrained by `A` give the robot on the payload coordinates with
`M̃ = M_p + G J⁻ᵀ M_f J⁻¹ Gᵀ`, `C̃ = C_p + G J⁻ᵀ (C_f J⁻¹ Gᵀ + M_f Bd)`, `Ñ = N_p + G J⁻ᵀ N_f`, the
finger fields evaluated at `θ = σ(x)`, `θ̇ = J⁻¹ Gᵀ ẋ` (p. 305 prints `J⁻¹ G` for `J⁻¹ Gᵀ`). -/
def attach (F : RobotSystem n) (P : RobotSystem p) (A : AttachConstraint n p) : RobotSystem p where
  M x := effectiveMass (P.M x) (F.M (A.σ x)) (A.J x) (A.G x)
  C x v := effectiveCoriolis (P.C x v) (F.C (A.σ x) (A.fingerVelocity x v)) (F.M (A.σ x)) (A.J x)
    (A.G x) (A.Bd x v)
  N x v := effectiveN (P.N x v) (F.N (A.σ x) (A.fingerVelocity x v)) (A.J x) (A.G x)

/-- **`attach` is the hand robot of (6.21)–(6.22) with the finger fields on the constraint (MLS p.
305 with p. 278),** by definition. -/
theorem attach_eq_handRobot (F : RobotSystem n) (P : RobotSystem p) (A : AttachConstraint n p) :
    F.attach P A = handRobot P.M P.C P.N (fun x => F.M (A.σ x))
      (fun x v => F.C (A.σ x) (A.fingerVelocity x v))
      (fun x v => F.N (A.σ x) (A.fingerVelocity x v))
      A.J A.G A.Bd :=
  rfl

/-- **MLS Lemma 6.1(1), p. 279, for `attach`, from the payload:** with `M_p(x)` positive definite
and `M_f(θ)` positive semidefinite everywhere, the attached inertia is positive definite at every
`x`. -/
theorem attach_M_posDef {F : RobotSystem n} {P : RobotSystem p} (A : AttachConstraint n p)
    (hP : ∀ x, (P.M x).PosDef) (hF : ∀ θ, (F.M θ).PosSemidef) (x : Fin p → ℝ) :
    ((F.attach P A).M x).PosDef := by
  exact effectiveMass_posDef (hP x) (hF _) _ _

/-- **MLS Lemma 6.1(1), p. 279, for `attach`, the book's route:** with `M_p(x)` positive
semidefinite (possibly `0`), `M_f(σ(x))` positive definite, `J(x)` invertible and `G(x)` onto, the
attached inertia is positive definite at `x`. -/
theorem attach_M_posDef_of_surjective {F : RobotSystem n} {P : RobotSystem p}
    {A : AttachConstraint n p} {x : Fin p → ℝ} (hP : (P.M x).PosSemidef)
    (hF : (F.M (A.σ x)).PosDef) (hJ : IsUnit (A.J x).det)
    (hG : Function.Surjective (A.G x).mulVec) :
    ((F.attach P A).M x).PosDef := by
  exact effectiveMass_posDef_of_surjective hP hF hJ hG

/-- **MLS Lemma 6.1(2), p. 279, for `attach`: the attached robot has the skew property (MLS p. 300,
"These properties hold for all of the systems given in this chapter").** Hypotheses: `M_f(θ)`
symmetric; `M_p`, `M_f` differentiable along motions; payload and fingers with the skew property;
the finger motion `σ ∘ x` with velocity `J⁻¹ Gᵀ ẋ` along every payload motion (the grasp constraint
(6.18) with `J` invertible); `Bd` the rate of `J⁻¹ Gᵀ` along motions. -/
theorem attach_hasSkewProperty {F : RobotSystem n} {P : RobotSystem p} {A : AttachConstraint n p}
    (hFs : ∀ θ, (F.M θ).IsSymm) (hPd : DifferentiableAlongMotions P.M)
    (hFd : DifferentiableAlongMotions F.M) (hP : P.HasSkewProperty) (hF : F.HasSkewProperty)
    (hσ : ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}, HasDerivAt x x' t →
      HasDerivAt (fun s => A.σ (x s)) (A.fingerVelocity (x t) x') t)
    (hB : A.HasRate) : (F.attach P A).HasSkewProperty := by
  intro x x' t Md hx hMd
  obtain ⟨Mod, hMod⟩ := hPd hx
  obtain ⟨Mfd, hMfd⟩ := hFd (hσ hx)
  exact skew_deriv_effectiveMass_sub_two_effectiveCoriolis (Mo := fun s => P.M (x s))
    (Mf := fun s => F.M (A.σ (x s))) (J := fun s => A.J (x s)) (G := fun s => A.G (x s))
    hMod hMfd (hB hx) (hFs _) (hP hx hMod) (hF (hσ hx) hMfd) hMd

/-- **The attached inertia has a derivative along every motion (MLS p. 279, `M̃˙`)** under the
differentiability hypotheses of `attach_hasSkewProperty`. -/
theorem attach_differentiableAlongMotions {F : RobotSystem n} {P : RobotSystem p}
    {A : AttachConstraint n p} (hPd : DifferentiableAlongMotions P.M)
    (hFd : DifferentiableAlongMotions F.M)
    (hσ : ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}, HasDerivAt x x' t →
      HasDerivAt (fun s => A.σ (x s)) (A.fingerVelocity (x t) x') t)
    (hB : A.HasRate) : DifferentiableAlongMotions (F.attach P A).M := by
  intro x x' t hx
  obtain ⟨Mod, hMod⟩ := hPd hx
  obtain ⟨Mfd, hMfd⟩ := hFd (hσ hx)
  exact ⟨_, hasDerivAt_effectiveMass (Mo := fun s => P.M (x s))
    (Mf := fun s => F.M (A.σ (x s))) (J := fun s => A.J (x s)) (G := fun s => A.G (x s))
    hMod hMfd (hB hx)⟩

/-- **The attached inertia is continuous (MLS p. 305)** when `M_p`, `M_f`, `σ`, `x ↦ J(x)⁻¹` and `G`
are. -/
theorem attach_continuous_M {F : RobotSystem n} {P : RobotSystem p} {A : AttachConstraint n p}
    (hP : Continuous P.M) (hF : Continuous F.M) (hσ : Continuous A.σ)
    (hJ : Continuous fun x => (A.J x)⁻¹) (hG : Continuous A.G) :
    Continuous (F.attach P A).M := by
  have hGt : Continuous fun x => (A.G x)ᵀ := hG.matrix_transpose
  exact hP.add (((((hG.matrix_mul hJ.matrix_transpose).matrix_mul (hF.comp hσ)).matrix_mul
    hJ).matrix_mul hGt))

/-- **The attached robot's equations are the constrained equations of fingers and payload (MLS p.
305, "we use the Lagrange-d'Alembert equations to write the dynamics in terms of the payload
variables"; the multiplier form (6.24), p. 280, with the sign of p. 267).** At a payload state
`(x, v)` with acceleration `a`, the fingers at `θ = σ(x)` with `θ̇ = J⁻¹ Gᵀ v` and
`θ̈ = J⁻¹ Gᵀ a + Bd v`, and `J(x)` invertible: there is a constraint force `λ` with
`M_f θ̈ + C_f θ̇ + N_f + Jᵀ λ = τ` and `M_p a + C_p v + N_p = G λ` exactly when
`M̃ a + C̃ v + Ñ = G J⁻ᵀ τ`. -/
theorem attach_equations_iff (F : RobotSystem n) (P : RobotSystem p) (A : AttachConstraint n p)
    {x v a : Fin p → ℝ} (hJ : IsUnit (A.J x).det) (τ : Fin n → ℝ) :
    (∃ lam : Fin n → ℝ,
      F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
          F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
          F.N (A.σ x) (A.fingerVelocity x v) + (A.J x)ᵀ *ᵥ lam = τ ∧
        P.M x *ᵥ a + P.C x v *ᵥ v + P.N x v = A.G x *ᵥ lam) ↔
      (F.attach P A).M x *ᵥ a + (F.attach P A).C x v *ᵥ v + (F.attach P A).N x v =
        effectiveForce (A.J x) (A.G x) τ := by
  have key := effective_dynamics_eq (P.M x) (P.C x v) (P.N x v) (F.M (A.σ x))
    (F.C (A.σ x) (A.fingerVelocity x v)) (A.J x) (F.N (A.σ x) (A.fingerVelocity x v)) (A.G x)
    (A.Bd x v) (x' := v) (x'' := a) (θ' := A.fingerVelocity x v)
    (θ'' := A.fingerAcceleration x v a) rfl rfl
  have key' : (F.attach P A).M x *ᵥ a + (F.attach P A).C x v *ᵥ v + (F.attach P A).N x v =
      (P.M x *ᵥ a + P.C x v *ᵥ v + P.N x v) + (A.G x * ((A.J x)⁻¹)ᵀ) *ᵥ
        (F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
          F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
          F.N (A.σ x) (A.fingerVelocity x v)) :=
    key.symm
  rw [key', effectiveForce]
  constructor
  · rintro ⟨lam, h1, h2⟩
    rw [h2, contactForce_eq hJ h1]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    abel
  · intro h
    refine ⟨(A.J x)⁻¹ᵀ *ᵥ (τ - (F.M (A.σ x) *ᵥ A.fingerAcceleration x v a +
      F.C (A.σ x) (A.fingerVelocity x v) *ᵥ A.fingerVelocity x v +
      F.N (A.σ x) (A.fingerVelocity x v))), ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hJ,
        Matrix.transpose_one, Matrix.one_mulVec]
      abel
    · rw [Matrix.mulVec_mulVec, Matrix.mulVec_sub, ← h]
      abel

end RobotSystem
end Control

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n) (f : (Fin n → ℝ) → Fin n → ℝ)

/-- **Changing from joint space to workspace coordinates by `attach` (MLS p. 305, "we can change
from joint space to workspace coordinates"; §4.5.4, p. 196):** the constraint `θ = g(x)` with
`J = ∂f/∂θ` at `g(x)`, `G = I` and the rate `(d/dt) J⁻¹ = −J⁻¹ J̇ J⁻¹` with `J̇ = jacDot f θ θ̇`,
`θ̇ = J⁻¹ ẋ`, for a workspace map `f` with inverse `g`. -/
def workspaceAttach (g : (Fin n → ℝ) → Fin n → ℝ) : Control.AttachConstraint n n where
  σ := g
  J x := jac f (g x)
  G _ := 1
  Bd x v := -((jac f (g x))⁻¹ * jacDot f (g x) ((jac f (g x))⁻¹ *ᵥ v) * (jac f (g x))⁻¹)

/-- **Attaching the manipulator to the zero payload through `workspaceAttach` gives the workspace
robot (MLS p. 305 with eq. (4.55), p. 197):** `M̃ = J⁻ᵀ M J⁻¹`, `C̃ = J⁻ᵀ (C − M J⁻¹ J̇) J⁻¹`,
`Ñ = J⁻ᵀ N` at `θ = g(x)`, `θ̇ = J⁻¹ ẋ`, with no hypothesis. -/
theorem toRobotSystem_attach_workspaceAttach (g : (Fin n → ℝ) → Fin n → ℝ) :
    P.toRobotSystem.attach 0 (workspaceAttach f g) = P.workspaceRobot f g := by
  have hv : ∀ x v : Fin n → ℝ,
      (workspaceAttach f g).fingerVelocity x v = (jac f (g x))⁻¹ *ᵥ v := fun x v => by
    simp [Control.AttachConstraint.fingerVelocity, workspaceAttach]
  simp only [Control.RobotSystem.attach, workspaceRobot, hv]
  congr 1
  · funext x
    simp [workspaceAttach, workspaceM, effectiveMass_one, toRobotSystem]
  · funext x v
    simp only [workspaceAttach, workspaceC, effectiveCoriolis_one, toRobotSystem,
      Control.RobotSystem.zero_C, zero_add]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
      sub_eq_add_neg]
  · funext x v
    simp [workspaceAttach, workspaceN, effectiveN, toRobotSystem]

end ManipulatorModel
end RoboLean
