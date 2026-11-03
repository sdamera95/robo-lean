import RoboLean.Examples.SlotConstraint

/-!
# The slot in joint and in workspace coordinates agree (MLS Exercise 12(c)–(d), pp. 209–210)

Exercise 12(d) asks to verify that the slot dynamics written through workspace coordinates
`w = p(θ)` agree with those of §6.3 written in joint coordinates, and in particular that `τ_N` and
`M̃(s)` are the same. For any joint-space parameterization `f` of the slot near a slot position
`s` with `p ∘ f` equal to the workspace path `s ↦ (l + s cos α, s sin α)` there (the elbow-down
solution of p. 204 where it is defined, or any other branch; the arm's reach is bounded, so such an
`f` is local), the chain rule gives `J_p(f(s)) J_f(s) = K`; where `J_p` is
invertible, the joint-space inertia `J_fᵀ M J_f` equals `Kᵀ M_w K` with the workspace inertia
`M_w = J_p⁻ᵀ M J_p⁻¹` of (4.55), and the joint-space normal torque `λ ∇h(θ)` is `J_pᵀ` applied to
the workspace normal force `λ n`. Conventions as in `Examples/SlotConstraint`; `J_p` is the Jacobian
of the end-effector map `planarArmXY`.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

open MapJacobian

/-- **Congruence of the two projected inertias (MLS Exercise 12(d), p. 210):** if `J_p J_f = K` and
`J_p` is invertible, then `J_fᵀ M J_f = Kᵀ (J_p⁻ᵀ M J_p⁻¹) K`. -/
theorem transpose_mul_mul_eq_of_mul_eq {n m : ℕ} {Jp M : Matrix (Fin n) (Fin n) ℝ}
    {Jf K : Matrix (Fin n) (Fin m) ℝ} (hJ : IsUnit Jp.det) (hK : Jp * Jf = K) :
    Jfᵀ * M * Jf = Kᵀ * ((Jp⁻¹)ᵀ * M * Jp⁻¹) * K := by
  subst hK
  have h1 : Jp⁻¹ * Jp = 1 := Matrix.nonsing_inv_mul _ hJ
  have h2 : Jpᵀ * (Jp⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rw [Matrix.transpose_mul]
  calc Jfᵀ * M * Jf = Jfᵀ * (Jpᵀ * (Jp⁻¹)ᵀ) * M * ((Jp⁻¹ * Jp) * Jf) := by
        rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
    _ = Jfᵀ * Jpᵀ * ((Jp⁻¹)ᵀ * M * Jp⁻¹) * (Jp * Jf) := by simp only [Matrix.mul_assoc]

/-- **The chain rule for a joint-space parameterization of the slot (MLS Exercise 12(b)–(c),
p. 209):** if `p(f(s')) = (l + s' cos α, s' sin α)` for all `s'` near `s` and `f` is differentiable at
`s`, then
`J_p(f(s)) J_f(s) = K = (cos α, sin α)`. -/
theorem jac_planarArmXY_mul_jac_eq (l₁ l₂ l α : ℝ) {f : (Fin 1 → ℝ) → Fin 2 → ℝ}
    {s : Fin 1 → ℝ} (hf : ∀ᶠ s' in nhds s, planarArmXY l₁ l₂ (f s') = slotPath l α s')
    (hfd : DifferentiableAt ℝ f s) :
    jac (planarArmXY l₁ l₂) (f s) * jac f s = !![Real.cos α; Real.sin α] := by
  have hp : DifferentiableAt ℝ (planarArmXY l₁ l₂) (f s) :=
    (contDiff_planarArmXY l₁ l₂).differentiable (by norm_num) _
  have hcomp : (fun s' => planarArmXY l₁ l₂ (f s')) =ᶠ[nhds s] slotPath l α := hf
  have hj : jac (slotPath l α) s = jac (fun s' => planarArmXY l₁ l₂ (f s')) s := by
    simp only [jac, hcomp.fderiv_eq]
  rw [← jac_slotPath l α s, hj]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, jac_mulVec, jac_mulVec,
    jac_mulVec, fderiv_fun_comp s hp hfd]
  rfl

/-- **MLS Exercise 12(d), p. 210, the inertia:** for a joint-space parameterization `f` of the slot
near `s` (`p ∘ f` the workspace path on a neighborhood of `s`), differentiable at `s`, with `J_p(f(s))` invertible, the joint-space
projected inertia `J_fᵀ M(f(s)) J_f` of §6.3 equals `Kᵀ M_w K` with the workspace inertia
`M_w = J_p⁻ᵀ M J_p⁻¹` of (4.55), for every inertia matrix `M`. -/
theorem slot_projectedInertia_eq (l₁ l₂ l α : ℝ) {f : (Fin 1 → ℝ) → Fin 2 → ℝ}
    {s : Fin 1 → ℝ} (hf : ∀ᶠ s' in nhds s, planarArmXY l₁ l₂ (f s') = slotPath l α s')
    (hfd : DifferentiableAt ℝ f s) (hJ : IsUnit (jac (planarArmXY l₁ l₂) (f s)).det)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (jac f s)ᵀ * M * jac f s =
      (!![Real.cos α; Real.sin α])ᵀ *
        (((jac (planarArmXY l₁ l₂) (f s))⁻¹)ᵀ * M * (jac (planarArmXY l₁ l₂) (f s))⁻¹) *
        !![Real.cos α; Real.sin α] := by
  exact transpose_mul_mul_eq_of_mul_eq hJ (jac_planarArmXY_mul_jac_eq l₁ l₂ l α hf hfd)

/-- **MLS Exercise 12(d), p. 210, the normal torque:** the joint-space normal torque `λ ∇h(θ)` of
§6.3 is the transposed end-effector Jacobian applied to the workspace normal force `λ n`, the
torque `τ = J_pᵀ F` that produces that force. -/
theorem slot_normalTorque_eq (l₁ l₂ l α : ℝ) (θ : Fin 2 → ℝ) (lam : ℝ) :
    (jac (slotJointConstraint l₁ l₂ l α) θ)ᵀ *ᵥ ![lam] =
      (jac (planarArmXY l₁ l₂) θ)ᵀ *ᵥ (lam • slotNormal α) := by
  have e : (![lam] : Fin 1 → ℝ) = lam • ![1] := by
    funext i; fin_cases i; simp
  rw [e, Matrix.mulVec_smul, jac_slotJointConstraint_eq, Matrix.mulVec_smul]

end RoboLean.Examples
