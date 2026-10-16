import RoboLean.Control.WorkspaceControl
import RoboLean.Examples.PlanarTwoLinkControl

/-!
# Workspace coordinates for the planar two-link arm (MLS §5.4, Lemma 4.11, Example 4.8, pp. 196–199)

MLS Example 4.8 (printed pp. 198–199) controls "a planar two degree of freedom robot" with "as our
workspace variables the xy position of the end-effector"; it is a numerical comparison (Figures
4.10–4.11) with no printed link lengths, masses, gains or step size, so it is not reproduced. Here
the workspace map of that setting is defined for the dynamic arm of MLS Figure 4.4
(`planarTwoLinkArm`), and the hypotheses of the general workspace theorems
(`RoboLean.Control.WorkspaceControl`) are discharged for it:

* `planarArmXY l₁ l₂` is the end-effector position
  `(l₁ cos θ₁ + l₂ cos(θ₁ + θ₂), l₁ sin θ₁ + l₂ sin(θ₁ + θ₂))`, in the frame of `planarTwoLinkArm`:
  the arm lies along `+x` at `θ = 0`, joint 2 at `(l₁, 0, 0)`, and `l₂` is the distance from joint 2
  to the end effector. The kinematic arm `planarTwoLink` of Chapter 3 lies along `+y` at `θ = 0`;
  the two conventions are kept, and this map is not `planarTwoLinkPosition`;
* its Jacobian matrix is computed (`jac_planarArmXY`) and `det J = l₁ l₂ sin θ₂`
  (`det_jac_planarArmXY`), so `J` is invertible exactly off the folded and stretched
  configurations `sin θ₂ = 0` when `l₁, l₂ ≠ 0` (the singular configurations relative to `x` of
  MLS p. 198);
* Lemma 4.11 for the arm with positive masses and principal moments, at every configuration and
  along every motion with `sin θ₂ ≠ 0` (`planarTwoLinkModel_workspaceM_posDef`,
  `planarTwoLinkModel_skew_deriv_workspaceM`);
* exponential tracking in xy coordinates under the workspace computed torque law, for every
  closed-loop solution that stays off `sin θ₂ = 0`
  (`planarTwoLinkArm_workspaceComputedTorque_tracking`), and for linear coordinates `x = A θ`
  with `A` invertible, for every closed-loop solution
  (`planarTwoLinkArm_linearWorkspace_tracking`).

These are instances showing that the hypotheses of the general theorems can be met; they are not
separate results, and nothing here concerns a physical arm. Lean joint `0` is the book's joint 1,
so `θ 0 = θ₁` and `θ 1 = θ₂`.
-/

noncomputable section

open Matrix Filter Topology
open RoboLean.MapJacobian

namespace RoboLean.Examples

/-- **The xy position of the end effector of the planar two-link arm (MLS Example 4.8, p. 198,
"the xy position of the end-effector"; arm of Figure 4.4, p. 164)** in the frame of
`planarTwoLinkArm` (`+x` at `θ = 0`, joint 2 at `(l₁, 0, 0)`):
`x = l₁ cos θ₁ + l₂ cos(θ₁ + θ₂)`, `y = l₁ sin θ₁ + l₂ sin(θ₁ + θ₂)`, with `l₂` the distance from
joint 2 to the end effector. -/
def planarArmXY (l₁ l₂ : ℝ) (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![l₁ * Real.cos (q 0) + l₂ * Real.cos (q 0 + q 1),
    l₁ * Real.sin (q 0) + l₂ * Real.sin (q 0 + q 1)]

variable (m₁ m₂ r₁ r₂ l₁ l₂ : ℝ) (I₁ I₂ : Fin 3 → ℝ)

/-- The xy map of the planar arm is `C²` (it is smooth), as the workspace theorems of MLS
pp. 196–198 require. -/
theorem contDiff_planarArmXY : ContDiff ℝ 2 (planarArmXY l₁ l₂) := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i
  · simp only [planarArmXY]
    simp
    fun_prop
  · simp [planarArmXY]
    fun_prop

/-- **The Jacobian matrix of the xy map of the planar arm (MLS p. 196, `J = ∂f/∂θ`):**
`J(θ) = [[−l₁ s₁ − l₂ s₁₂, −l₂ s₁₂], [l₁ c₁ + l₂ c₁₂, l₂ c₁₂]]`, rows `x`, `y`, columns `θ₁`,
`θ₂`. -/
theorem jac_planarArmXY (q : Fin 2 → ℝ) :
    jac (planarArmXY l₁ l₂) q =
      !![-(l₁ * Real.sin (q 0)) - l₂ * Real.sin (q 0 + q 1), -(l₂ * Real.sin (q 0 + q 1));
        l₁ * Real.cos (q 0) + l₂ * Real.cos (q 0 + q 1), l₂ * Real.cos (q 0 + q 1)] := by
  have p0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 q
  have p1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 q
  have h0 := (p0.cos.const_mul l₁).add ((p0.add p1).cos.const_mul l₂)
  have h1 := (p0.sin.const_mul l₁).add ((p0.add p1).sin.const_mul l₂)
  set e₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
  set e₁ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
  set L : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) :=
    ![l₁ • (-Real.sin (q 0) • e₀) + l₂ • (-Real.sin (q 0 + q 1) • (e₀ + e₁)),
      l₁ • (Real.cos (q 0) • e₀) + l₂ • (Real.cos (q 0 + q 1) • (e₀ + e₁))]
  have hL : ∀ i, HasFDerivAt (fun x => planarArmXY l₁ l₂ x i) (L i) q := by
    intro i
    fin_cases i
    · convert h0 using 1
      · funext x
        simp [planarArmXY]
      · rfl
    · convert h1 using 1
      · funext x
        simp [planarArmXY]
      · rfl
  ext i j
  rw [jac_apply_of_hasFDerivAt hL]
  fin_cases i <;> fin_cases j <;> simp [L, e₀, e₁]
  ring

/-- **The singular configurations of the xy coordinates (MLS p. 198):**
`det J(θ) = l₁ l₂ sin θ₂`. -/
theorem det_jac_planarArmXY (q : Fin 2 → ℝ) :
    (jac (planarArmXY l₁ l₂) q).det = l₁ * l₂ * Real.sin (q 1) := by
  rw [jac_planarArmXY, Matrix.det_fin_two_of, show q 0 + q 1 = q 1 + q 0 by ring, Real.sin_add,
    Real.cos_add]
  linear_combination (l₁ * l₂ * Real.sin (q 1)) * Real.sin_sq_add_cos_sq (q 0)

/-- With nonzero link lengths, the Jacobian matrix of the xy map is invertible exactly where
`sin θ₂ ≠ 0` (MLS p. 198, singular configurations relative to `x`). -/
theorem isUnit_det_jac_planarArmXY_iff {l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (q : Fin 2 → ℝ) : IsUnit (jac (planarArmXY l₁ l₂) q).det ↔ Real.sin (q 1) ≠ 0 := by
  rw [det_jac_planarArmXY, isUnit_iff_ne_zero]
  constructor
  · intro h hs
    exact h (by rw [hs, mul_zero])
  · intro hs
    exact mul_ne_zero (mul_ne_zero hl₁ hl₂) hs

/-- Symmetric link inertias of the planar arm as a model (MLS p. 162). -/
private theorem planarTwoLinkModel_isSymm (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia k).IsSymm :=
  planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂

/-- `M(θ)` of the planar arm as a model is positive definite for positive masses and moments. -/
private theorem planarTwoLinkModel_posDef {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
  rw [planarTwoLinkModel_M]
  exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂

/-- **MLS Lemma 4.11(1), p. 197, for the planar arm in xy coordinates.** With positive masses and
principal moments, nonzero link lengths `l₁, l₂`, any gravity data and joint forces, the effective
inertia `M̃(θ) = J⁻ᵀ M J⁻¹` is positive definite at every configuration with `sin θ₂ ≠ 0`. -/
theorem planarTwoLinkModel_workspaceM_posDef {m₁ m₂ l₁ l₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (hl₁ : l₁ ≠ 0)
    (hl₂ : l₂ ≠ 0) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    {q : Fin 2 → ℝ} (hq : Real.sin (q 1) ≠ 0) :
    ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceM (planarArmXY l₁ l₂) q).PosDef :=
  ManipulatorModel.workspaceM_posDef _ _
    (planarTwoLinkModel_posDef r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne q)
    ((isUnit_det_jac_planarArmXY_iff hl₁ hl₂ q).mpr hq)

/-- **MLS Lemma 4.11(2), p. 197, for the planar arm in xy coordinates.** For all parameters with
nonzero link lengths `l₁, l₂`, any gravity data and joint forces, along every motion `θ` with
velocity `θ'` at `t` and `sin θ₂(t) ≠ 0`, every actual derivative `M̃˙` of `s ↦ M̃(θ(s))` makes
`M̃˙ − 2 C̃(θ(t), θ')` skew-symmetric. -/
theorem planarTwoLinkModel_skew_deriv_workspaceM {l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {θ : ℝ → Fin 2 → ℝ}
    {θ' : Fin 2 → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t) (hq : Real.sin (θ t 1) ≠ 0)
    {Mtdot : Matrix (Fin 2) (Fin 2) ℝ}
    (hMtdot : ∀ i j, HasDerivAt (fun s => (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up
      Ne).workspaceM (planarArmXY l₁ l₂) (θ s) i j) (Mtdot i j) t) :
    (Mtdot - (2 : ℝ) • (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceC
        (planarArmXY l₁ l₂) (θ t) θ')ᵀ =
      -(Mtdot - (2 : ℝ) • (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceC
        (planarArmXY l₁ l₂) (θ t) θ') :=
  ManipulatorModel.skew_deriv_workspaceM_sub_two_workspaceC _ _
    (planarTwoLinkModel_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne) (contDiff_planarArmXY l₁ l₂) hθ
    ((isUnit_det_jac_planarArmXY_iff hl₁ hl₂ _).mpr hq) hMtdot

/-- **Workspace computed torque for the planar arm in xy coordinates (MLS p. 198, the setting of
Example 4.8).** With positive masses and principal moments, nonzero link lengths `l₁, l₂`, any
gravity data and joint forces, and `K_p = K_v = I`, there are `m, α > 0` such that every solution
of the arm under the workspace computed torque law (with `C̃`, `Ñ`) for every twice-differentiable
desired xy trajectory, which stays off the singular configurations (`sin θ₂(s) ≠ 0` for `s > t₀`),
tracks it in xy coordinates with error at most `m e^{−α(t − t₀)}` times the initial error. -/
theorem planarTwoLinkArm_workspaceComputedTorque_tracking {m₁ m₂ l₁ l₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (hl₁ : l₁ ≠ 0)
    (hl₂ : l₂ ≠ 0) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin 2 → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceComputedTorque
          (planarArmXY l₁ l₂) 1 1 xd xd' xd'')) t₀ x →
      (∀ s, t₀ < s → Real.sin ((x s).1 1) ≠ 0) →
      ∀ t, t₀ ≤ t → ‖(planarArmXY l₁ l₂ (x t).1 - xd t,
          jac (planarArmXY l₁ l₂) (x t).1 *ᵥ (x t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(planarArmXY l₁ l₂ (x t₀).1 - xd t₀,
          jac (planarArmXY l₁ l₂) (x t₀).1 *ᵥ (x t₀).2 - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := ManipulatorModel.workspaceComputedTorque_tracking
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne) (planarArmXY l₁ l₂)
    (contDiff_planarArmXY l₁ l₂) (planarTwoLinkModel_posDef r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne)
    Matrix.PosDef.one Matrix.PosDef.one
  refine ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x hx hs t ht => ?_⟩
  exact htrack hd hd' t₀ ht₀ x hx
    (fun s hs' => (isUnit_det_jac_planarArmXY_iff hl₁ hl₂ _).mpr (hs s hs')) t ht

/-- **Workspace computed torque for the planar arm in linear coordinates `x = A θ` (MLS p. 198).**
With positive masses and principal moments, any gravity data and joint forces, an invertible
`A`, and `K_p = K_v = I`, there are `m, α > 0` such that every closed-loop solution under the
workspace computed torque law for every twice-differentiable desired trajectory `x_d` tracks it,
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` with `e = A θ − x_d`, `ė = A θ̇ − ẋ_d`;
here `J = A` is invertible everywhere, so no condition on the solution is needed. -/
theorem planarTwoLinkArm_linearWorkspace_tracking {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ)
    (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : IsUnit A.det) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin 2 → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceComputedTorque
          (fun q => A *ᵥ q) 1 1 xd xd' xd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖(A *ᵥ (x t).1 - xd t, A *ᵥ (x t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖(A *ᵥ (x t₀).1 - xd t₀, A *ᵥ (x t₀).2 - xd' t₀)‖ := by
  obtain ⟨m, hm, α, hα, htrack⟩ := ManipulatorModel.workspaceComputedTorque_tracking
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne) (fun q => A *ᵥ q) (contDiff_linear A)
    (planarTwoLinkModel_posDef r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne) Matrix.PosDef.one
    Matrix.PosDef.one
  refine ⟨m, hm, α, hα, fun hd hd' t₀ ht₀ x hx t ht => ?_⟩
  have h := htrack hd hd' t₀ ht₀ x hx (fun s _ => by rw [jac_linear]; exact hA) t ht
  simpa only [jac_linear] using h

end RoboLean.Examples
