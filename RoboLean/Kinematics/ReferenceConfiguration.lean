import RoboLean.Kinematics.Jacobian

/-!
# Choice of base frame, tool frame and reference configuration

MLS §3.2.3, printed p. 91 ("Choice of base frame and reference configuration"), and
Exercise 8, p. 148. The product-of-exponentials description of a chain depends on the base
frame and on the reference configuration. This module states the three changes as
operations on `SerialChain` and proves how the forward kinematics and the spatial Jacobian
transform.

* `SerialChain.changeBase g`: a new base frame `S'` with `g_{s's} = g`; the twists become
  `Ad_g ξᵢ` and `g_{s't}(θ) = g g_st(θ)`.
* `SerialChain.baseAtTool`: the base frame placed at the tool frame of the reference
  configuration (p. 91), so that `g_{s't}(0) = I` and `g_{s't}(θ) = exp(ξ̂₁'θ₁) ⋯ exp(ξ̂ₙ'θₙ)`.
* `SerialChain.shiftReference θ₀`: the configuration `θ₀` taken as the new reference
  configuration ("by adding or subtracting a fixed offset from each joint variable", p. 91);
  the new joint twists are the twists of the joint axes at `θ₀`, which are the columns of the
  spatial Jacobian `Jˢ(θ₀)` (MLS eq. (3.54), p. 116), and the new reference tool pose is
  `g_st(θ₀)`.
* `SerialChain.changeTool h`: a new tool frame moving with the end-effector,
  `g_{st'} = g_st h`; the spatial Jacobian and hence the spatial velocity are unchanged
  (Exercise 8).

Conventions: twists `(v, ω)`, Lean joint `i` is the book's joint `i + 1`, real joint lift.
-/

noncomputable section

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-- The chain described from a new base frame `S'` with `g_{s's} = g` (MLS p. 91, other
choices of base frame): joint twists `Ad_g ξᵢ` (MLS eq. (2.58), p. 55) and reference tool pose
`g g_st(0)`; the joint space is unchanged. -/
def changeBase (c : SerialChain n) (g : RigidTransform) : SerialChain n where
  twist i := Twist.adjoint g (c.twist i)
  toolRef := g * c.toolRef
  admissible := c.admissible

/-- **MLS p. 91.** Changing the base frame by `g_{s's} = g` conjugates the product of
exponentials: `∏ exp((Ad_g ξᵢ)^ θᵢ) = g (∏ exp(ξ̂ᵢθᵢ)) g⁻¹` (MLS p. 94, `g e^{ξ̂θ} g⁻¹ = e^{(Ad_g ξ)^θ}`),
for every real joint vector. -/
theorem poe_changeBase (c : SerialChain n) (g : RigidTransform) (θ : Fin n → ℝ) :
    (c.changeBase g).poe θ = g * c.poe θ * g⁻¹ := by
  have h := map_list_prod (MulAut.conj g) (c.jointMotions θ)
  simp only [MulAut.conj_apply] at h
  rw [poe, poe, h, jointMotions, jointMotions, List.map_ofFn]
  congr 2
  funext i
  simp [changeBase, Twist.exp_adjoint]

/-- **MLS p. 91.** The forward kinematics from the new base frame is
`g_{s't}(θ) = g_{s's} g_st(θ)`, for every real joint vector. -/
theorem fk_changeBase (c : SerialChain n) (g : RigidTransform) (θ : Fin n → ℝ) :
    (c.changeBase g).fk θ = g * c.fk θ := by
  rw [fk, poe_changeBase, fk]
  simp only [changeBase]
  group

/-- The chain described from the base frame that coincides with the tool frame at `θ = 0`,
MLS p. 91: `changeBase` by `g_{s's} = g_st(0)⁻¹`. -/
def baseAtTool (c : SerialChain n) : SerialChain n :=
  c.changeBase c.toolRef⁻¹

/-- **MLS p. 91.** With the base frame at the reference tool frame, `g_{s't}(0) = I`. -/
theorem baseAtTool_toolRef (c : SerialChain n) : c.baseAtTool.toolRef = 1 := by
  simp [baseAtTool, changeBase]

/-- **MLS p. 91, the displayed formula.** With the base frame at the reference tool frame the
forward kinematics is the bare product of exponentials,
`g_{s't}(θ) = exp(ξ̂₁'θ₁) ⋯ exp(ξ̂ₙ'θₙ)`, and it equals `g_st(0)⁻¹ g_st(θ)`, for every real
joint vector. -/
theorem fk_baseAtTool (c : SerialChain n) (θ : Fin n → ℝ) :
    c.baseAtTool.fk θ = c.baseAtTool.poe θ ∧ c.baseAtTool.fk θ = c.toolRef⁻¹ * c.fk θ := by
  refine ⟨by rw [fk, baseAtTool_toolRef, mul_one], ?_⟩
  exact fk_changeBase c _ θ

/-- The chain with the configuration `θ₀` as its reference configuration, MLS p. 91: the
joint twists are the twists of the joint axes at `θ₀`, the columns `ξᵢ'` of the spatial
Jacobian `Jˢ(θ₀)` (MLS eq. (3.54), p. 116), the reference tool pose is `g_st(θ₀)`, and the
joint space is shifted by `θ₀`. -/
def shiftReference (c : SerialChain n) (θ₀ : Fin n → ℝ) : SerialChain n where
  twist := c.spatialJacobian θ₀
  toolRef := c.fk θ₀
  admissible := {θ | θ + θ₀ ∈ c.admissible}

/-- **MLS p. 91 ("by adding or subtracting a fixed offset from each joint variable, we can
define any configuration of the manipulator as the reference configuration").** The chain
with reference configuration `θ₀` has forward kinematics `θ ↦ g_st(θ + θ₀)`, for every real
`θ` and `θ₀`; its joint twists are the twists of the joint axes in the configuration `θ₀`. -/
theorem fk_shiftReference (c : SerialChain n) (θ₀ θ : Fin n → ℝ) :
    (c.shiftReference θ₀).fk θ = c.fk (θ + θ₀) := by
  induction n with
  | zero => simp [shiftReference, fk, poe, jointMotions]
  | succ n ih =>
    set h₀ := Twist.exp (c.twist 0) (θ₀ 0)
    have htail : (c.shiftReference θ₀).tail.fk (Fin.tail θ) =
        ((c.tail.shiftReference (Fin.tail θ₀)).changeBase h₀).fk (Fin.tail θ) := by
      simp only [fk, poe, jointMotions]
      congr 1
      · congr 1
        congr 1
        funext i
        simp [tail, shiftReference, changeBase, Fin.tail, spatialJacobian_succ, h₀]
      · simp [tail, shiftReference, changeBase, h₀, fk, poe, jointMotions, Fin.tail,
          mul_assoc]
    rw [fk_succ, htail, fk_changeBase, ih, fk_succ]
    simp only [shiftReference, spatialJacobian_zero, h₀, ← mul_assoc, ← Twist.exp_add]
    rfl

/-- The chain with a new tool frame `T'` moving with the end-effector, `g_{tt'} = h`
(MLS Exercise 8, p. 148): the reference tool pose becomes `g_st(0) h`. -/
def changeTool (c : SerialChain n) (h : RigidTransform) : SerialChain n where
  twist := c.twist
  toolRef := c.toolRef * h
  admissible := c.admissible

/-- **MLS Exercise 8, p. 148.** With a new tool frame moving with the end-effector,
`g_{st'}(θ) = g_st(θ) h`, for every real joint vector. -/
theorem fk_changeTool (c : SerialChain n) (h : RigidTransform) (θ : Fin n → ℝ) :
    (c.changeTool h).fk θ = c.fk θ * h := by
  simp only [fk, changeTool, mul_assoc]
  rfl

/-- **MLS Exercise 8, p. 148, Jacobian form.** The spatial Jacobian (MLS eq. (3.54),
p. 116) does not depend on the tool frame. -/
theorem spatialJacobian_changeTool (c : SerialChain n) (h : RigidTransform)
    (θ : Fin n → ℝ) : (c.changeTool h).spatialJacobian θ = c.spatialJacobian θ :=
  rfl

/-- **MLS Exercise 8, p. 148: the spatial velocity of a manipulator does not depend on the
location of the tool frame, as long as it moves with the end-effector.** Along a joint
trajectory with derivatives `θ̇` at `t`, the spatial velocity `ġ g⁻¹` (MLS eq. (2.53), p. 53)
of `t ↦ g_st(θ(t)) h` equals that of `t ↦ g_st(θ(t))`. -/
theorem spatialVelocity_changeTool (c : SerialChain n) (h : RigidTransform)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D D' : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t)
    (hD' : HasDerivAt (fun s => ((c.changeTool h).fk (θ s)).toHomogeneous) D' t) :
    RigidTransform.spatialVelocity (fun s => (c.changeTool h).fk (θ s)) D' t hD' =
      RigidTransform.spatialVelocity (fun s => c.fk (θ s)) D t hD := by
  rw [spatialVelocity_fk _ hθ, spatialVelocity_fk _ hθ, spatialJacobian_changeTool]

end SerialChain

end RoboLean
