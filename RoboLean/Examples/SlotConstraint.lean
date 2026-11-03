import RoboLean.Control.ConstrainedManipulator
import RoboLean.Examples.WorkspaceControl

/-!
# A planar manipulator moving in a slot (MLS §6.3, pp. 203–205, and Exercise 12, pp. 209–210)

The slot is the line through `q = (l, 0)` at angle `α` to the `x`-axis, with normal
`n = (sin α, −cos α)`; it is the set of points with `(p − q) · n = 0` (p. 203). Here:

* the slot in workspace coordinates `w = p(θ) ∈ ℝ²` (Exercise 12(b)): the constraint
  `h(w) = (w − q) · n` and the parameterization `w = f(s) = (l + s cos α, s sin α)` of p. 204, with
  Jacobian `K(s) = (cos α, sin α)` constant, satisfy the hypotheses of (4.56)–(4.57)
  (`isSurfaceParametrization_slot`); the hybrid law (4.63) in these coordinates is
  `F = M K (s̈_d − K_v ė_s − K_p e_s) + C K ṡ + N + λ n` (`hybridTorque_slot`), and for every robot
  in workspace coordinates it gives exponential tracking along the slot with constraint multiplier
  `λ` (`slot_tracking`);
* the slot in joint coordinates (p. 203): the two printed forms of `h(θ)` agree
  (`slotJointConstraint_eq`), its gradient is the printed `∇h(θ)` (`jac_slotJointConstraint`), and
  `∇h(θ) = J_p(θ)ᵀ n` with `J_p` the Jacobian of the end-effector position
  (`jac_slotJointConstraint_eq`).

**Corrected printing.** The computed torque on p. 204 is printed in joint torques with the normal
term `λ n`, where `n ∈ ℝ²` is the workspace normal; the normal torque of (4.63) is
`λ ∇h(θ) = λ J_p(θ)ᵀ n`, which differs from `λ n` in general. The term `λ n` is the normal force in
workspace coordinates, as in Exercise 12. The elbow-down parameterization `f(s)` of p. 204 and its
Jacobian "after some simplification" are not formalized; the slot is handled through Exercise 12's
workspace route, which the book recommends on p. 205.
-/

noncomputable section

open Matrix Set

namespace RoboLean.Examples

open MapJacobian Control

/-- The slot constraint in workspace coordinates, `h(w) = (w − q) · n` with `q = (l, 0)` and
`n = (sin α, −cos α)` (MLS p. 203; Exercise 12(b), p. 209). -/
def slotConstraint (l α : ℝ) (w : Fin 2 → ℝ) : Fin 1 → ℝ :=
  ![(w 0 - l) * Real.sin α - w 1 * Real.cos α]

/-- The position along the slot, `f(s) = (l + s cos α, s sin α)`, `s = 0` at `q = (l, 0)` (MLS
p. 204; Exercise 12(b), p. 209). -/
def slotPath (l α : ℝ) (s : Fin 1 → ℝ) : Fin 2 → ℝ :=
  ![l + s 0 * Real.cos α, s 0 * Real.sin α]

/-- The normal to the slot, `n = (sin α, −cos α)` (MLS p. 203). -/
def slotNormal (α : ℝ) : Fin 2 → ℝ :=
  ![Real.sin α, -Real.cos α]

/-- Supporting lemma: the Jacobian matrix of an affine map `q ↦ A q + c` is `A` (MLS p. 196 for
the linear part). -/
private theorem jac_affine {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (θ : Fin n → ℝ) : jac (fun q => A *ᵥ q + c) θ = A := by
  simp only [jac, fderiv_add_const]
  exact jac_linear A θ

/-- Supporting lemma: the rate of the Jacobian of an affine map is zero (MLS p. 196). -/
private theorem jacDot_affine {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (θ v : Fin n → ℝ) : jacDot (fun q => A *ᵥ q + c) θ v = 0 := by
  have e : fderiv ℝ (fun q => A *ᵥ q + c) = fderiv ℝ (fun q => A *ᵥ q) := by
    funext x; exact fderiv_add_const c
  simp only [jacDot, e]
  exact jacDot_linear A θ v

/-- Supporting lemma: the workspace slot constraint is affine (MLS p. 203). -/
private theorem slotConstraint_eq_affine (l α : ℝ) :
    slotConstraint l α = fun w => !![Real.sin α, -Real.cos α] *ᵥ w + ![-(l * Real.sin α)] := by
  funext w; ext i; fin_cases i
  simp [slotConstraint, dotProduct, Fin.sum_univ_two]; ring

/-- Supporting lemma: the slot parameterization is affine (MLS p. 204). -/
private theorem slotPath_eq_affine (l α : ℝ) :
    slotPath l α = fun s => !![Real.cos α; Real.sin α] *ᵥ s + ![l, 0] := by
  funext s; ext i; fin_cases i <;> simp [slotPath, dotProduct] <;> ring

/-- The gradient of the workspace slot constraint is the normal `n` (MLS p. 203; Exercise 12(b),
p. 209). -/
theorem jac_slotConstraint (l α : ℝ) (w : Fin 2 → ℝ) :
    jac (slotConstraint l α) w = !![Real.sin α, -Real.cos α] := by
  rw [slotConstraint_eq_affine]; exact jac_affine _ _ w

/-- The Jacobian of the slot parameterization, `K(s) = (cos α, sin α)` (MLS Exercise 12(b),
p. 209). -/
theorem jac_slotPath (l α : ℝ) (s : Fin 1 → ℝ) :
    jac (slotPath l α) s = !![Real.cos α; Real.sin α] := by
  rw [slotPath_eq_affine]; exact jac_affine _ _ s

/-- The rate of the Jacobian of the slot parameterization is zero, `K̇ = 0` (MLS Exercise 12,
p. 209). -/
theorem jacDot_slotPath (l α : ℝ) (s v : Fin 1 → ℝ) : jacDot (slotPath l α) s v = 0 := by
  rw [slotPath_eq_affine]; exact jacDot_affine _ _ s v

/-- **The slot satisfies the hypotheses of MLS (4.56)–(4.57), p. 200,** in workspace coordinates
(Exercise 12(b), p. 209): one independent smooth constraint `h(w) = (w − q) · n` on `ℝ²` and the
injective parameterization `f(s) = q + s (cos α, sin α)` onto its tangent line. -/
theorem isSurfaceParametrization_slot (l α : ℝ) :
    IsSurfaceParametrization (slotConstraint l α) (slotPath l α) := by
  have pyth := Real.sin_sq_add_cos_sq α
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rw [slotConstraint_eq_affine]; exact (contDiff_linear _).add contDiff_const
  · rw [slotPath_eq_affine]; exact (contDiff_linear _).add contDiff_const
  · intro s s' hss
    have h0 : l + s 0 * Real.cos α = l + s' 0 * Real.cos α := congrFun hss 0
    have h1 : s 0 * Real.sin α = s' 0 * Real.sin α := congrFun hss 1
    funext i; fin_cases i
    show s 0 = s' 0
    linear_combination (Real.cos α) * h0 + (Real.sin α) * h1 - (s 0 - s' 0) * pyth
  · intro s
    funext i; fin_cases i
    simp [slotConstraint, slotPath]; ring
  · intro s
    rw [jac_slotConstraint]
    apply linearIndependent_unique_iff.mpr
    intro h0
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp at h1 h2
    rw [h1, h2] at pyth
    norm_num at pyth
  · intro s v hv
    rw [jac_slotConstraint] at hv
    have hv0 := congrFun hv 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv0
    refine ⟨![v 0 * Real.cos α + v 1 * Real.sin α], ?_⟩
    rw [jac_slotPath]
    funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
    · linear_combination (-Real.sin α) * hv0 + v 0 * pyth
    · linear_combination (Real.cos α) * hv0 + v 1 * pyth

/-- **The hybrid law (4.63) for the slot in workspace coordinates (MLS p. 204 and Exercise 12,
p. 209):** `F = M K (s̈_d − K_v ė_s − K_p e_s) + C K ṡ + N + λ n`, with `K = (cos α, sin α)`,
`K̇ = 0`, scalar gains and the commanded normal force `λ`. -/
theorem hybridTorque_slot (R : RobotSystem 2) (l α : ℝ) (Kp Kv : Matrix (Fin 1) (Fin 1) ℝ)
    (sd sd' sd'' s s' : Fin 1 → ℝ) (lam : Fin 1 → ℝ) :
    R.hybridTorque (slotConstraint l α) (slotPath l α) Kp Kv sd sd' sd'' s s' lam =
      R.M (slotPath l α s) *ᵥ (!![Real.cos α; Real.sin α] *ᵥ
          (sd'' - Kv *ᵥ (s' - sd') - Kp *ᵥ (s - sd))) +
        R.C (slotPath l α s) (!![Real.cos α; Real.sin α] *ᵥ s') *ᵥ
          (!![Real.cos α; Real.sin α] *ᵥ s') +
        R.N (slotPath l α s) (!![Real.cos α; Real.sin α] *ᵥ s') + lam 0 • slotNormal α := by
  rw [RobotSystem.hybridTorque, jac_slotPath, jacDot_slotPath, jac_slotConstraint, Matrix.mul_zero,
    add_zero, ← Matrix.mulVec_mulVec]
  congr 1
  funext i; fin_cases i <;> simp [slotNormal, Matrix.mulVec, dotProduct, mul_comm]

/-- **Exponential tracking along the slot (MLS §6.3, pp. 203–205, through Exercise 12, p. 209):**
for every robot `(M, C, N)` in workspace coordinates `w ∈ ℝ²` with `M` positive definite and
positive gains, the hybrid law (4.63) gives exponential tracking of the slot position `s` and makes
the constraint multiplier equal to the commanded normal force `λ`, as in
`RobotSystem.hybridTorque_tracking`. -/
theorem slot_tracking (R : RobotSystem 2) (hM : ∀ q, (R.M q).PosDef) (l α : ℝ)
    {Kp Kv : Matrix (Fin 1) (Fin 1) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m₀ > 0, ∃ a > 0, ∀ {sd sd' sd'' : ℝ → Fin 1 → ℝ}, (∀ t, HasDerivAt sd (sd' t) t) →
      (∀ t, HasDerivAt sd' (sd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ (s s' s'' : ℝ → Fin 1 → ℝ)
      (lam μ : ℝ → Fin 1 → ℝ),
      ContinuousOn (fun t => (s t, s' t)) (Ici t₀) → (∀ t, t₀ < t → HasDerivAt s (s' t) t) →
      (∀ t, t₀ < t → HasDerivAt s' (s'' t) t) →
      (∀ t, t₀ < t → R.ConstrainedEquationsAt (slotConstraint l α) (slotPath l α (s t))
        (jac (slotPath l α) (s t) *ᵥ s' t)
        (jac (slotPath l α) (s t) *ᵥ s'' t + jacDot (slotPath l α) (s t) (s' t) *ᵥ s' t)
        (R.hybridTorque (slotConstraint l α) (slotPath l α) Kp Kv (sd t) (sd' t) (sd'' t) (s t)
          (s' t) (lam t)) (μ t)) →
      (∀ t, t₀ ≤ t → ‖(s t - sd t, s' t - sd' t)‖ ≤
        m₀ * Real.exp (-a * (t - t₀)) * ‖(s t₀ - sd t₀, s' t₀ - sd' t₀)‖) ∧
      ∀ t, t₀ < t → μ t = lam t :=
  R.hybridTorque_tracking (isSurfaceParametrization_slot l α) hM hKp hKv

/-- The slot constraint in joint coordinates of the planar two-link arm, MLS p. 203:
`h(θ) = (l₁ cos θ₁ + l₂ cos(θ₁ + θ₂) − l) sin α − (l₁ sin θ₁ + l₂ sin(θ₁ + θ₂)) cos α`, the
workspace constraint at the end-effector position `p(θ)` of `planarArmXY`. -/
def slotJointConstraint (l₁ l₂ l α : ℝ) (θ : Fin 2 → ℝ) : Fin 1 → ℝ :=
  slotConstraint l α (planarArmXY l₁ l₂ θ)

/-- The second printed form of the slot constraint, MLS p. 203:
`h(θ) = −l₁ sin(θ₁ − α) − l₂ sin(θ₁ + θ₂ − α) − l sin α`. -/
theorem slotJointConstraint_eq (l₁ l₂ l α : ℝ) (θ : Fin 2 → ℝ) :
    slotJointConstraint l₁ l₂ l α θ =
      ![-(l₁ * Real.sin (θ 0 - α)) - l₂ * Real.sin (θ 0 + θ 1 - α) - l * Real.sin α] := by
  funext i; fin_cases i
  simp [slotJointConstraint, slotConstraint, planarArmXY, Real.sin_sub]
  ring

/-- Supporting lemma: the chain rule for the joint-space slot constraint,
`∂h/∂θ = nᵀ J_p(θ)` (MLS pp. 203–204). -/
private theorem jac_slotJointConstraint_eq_mul (l₁ l₂ l α : ℝ) (θ : Fin 2 → ℝ) :
    jac (slotJointConstraint l₁ l₂ l α) θ =
      !![Real.sin α, -Real.cos α] * jac (planarArmXY l₁ l₂) θ := by
  set A : Matrix (Fin 1) (Fin 2) ℝ := !![Real.sin α, -Real.cos α]
  have hf : slotJointConstraint l₁ l₂ l α = fun q => A *ᵥ planarArmXY l₁ l₂ q + ![-(l * Real.sin α)] := by
    funext q; simp only [slotJointConstraint, slotConstraint_eq_affine, A]
  have hp : HasFDerivAt (planarArmXY l₁ l₂) (fderiv ℝ (planarArmXY l₁ l₂) θ) θ :=
    ((contDiff_planarArmXY l₁ l₂).differentiable (by norm_num) θ).hasFDerivAt
  have hd : HasFDerivAt (slotJointConstraint l₁ l₂ l α)
      ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).comp
        (fderiv ℝ (planarArmXY l₁ l₂) θ)) θ := by
    rw [hf]
    exact ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).hasFDerivAt.comp θ hp).add_const _
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, jac_mulVec, hd.fderiv, ← Matrix.mulVec_mulVec,
    jac_mulVec]
  rfl

/-- **`∇h(θ) = J_p(θ)ᵀ n` (MLS pp. 203–204):** the gradient of the joint-space slot constraint is
the transposed Jacobian of the end-effector position applied to the workspace normal, so the
normal torque of (4.63) is `λ J_pᵀ n`. -/
theorem jac_slotJointConstraint_eq (l₁ l₂ l α : ℝ) (θ : Fin 2 → ℝ) :
    (jac (slotJointConstraint l₁ l₂ l α) θ)ᵀ *ᵥ ![1] =
      (jac (planarArmXY l₁ l₂) θ)ᵀ *ᵥ slotNormal α := by
  rw [jac_slotJointConstraint_eq_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext i; fin_cases i <;> simp [slotNormal, Matrix.mulVec, dotProduct]

/-- **The gradient of the slot constraint printed on MLS p. 204:**
`∇h(θ) = (−l₁ cos(θ₁ − α) − l₂ cos(θ₁ + θ₂ − α), −l₂ cos(θ₁ + θ₂ − α))`, as the row of `∂h/∂θ`. -/
theorem jac_slotJointConstraint (l₁ l₂ l α : ℝ) (θ : Fin 2 → ℝ) :
    jac (slotJointConstraint l₁ l₂ l α) θ =
      !![-(l₁ * Real.cos (θ 0 - α)) - l₂ * Real.cos (θ 0 + θ 1 - α),
        -(l₂ * Real.cos (θ 0 + θ 1 - α))] := by
  rw [jac_slotJointConstraint_eq_mul, jac_planarArmXY]
  ext i j; fin_cases i; fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub] <;> ring

end RoboLean.Examples
