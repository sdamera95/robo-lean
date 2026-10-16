import RoboLean.Control.WorkspacePDControl
import RoboLean.Examples.WorkspaceControl

/-!
# The workspace PD law for the planar two-link arm in absolute link angles (MLS pp. 193, 196–198)

An instance showing that the hypotheses of the workspace PD law (`Control/WorkspacePDControl`) and
of PD control for robots (`Control/RobotPDControl`) can be met together with a nonzero Coriolis
matrix. The arm is the dynamic planar arm of MLS Figure 4.4 (p. 164, `planarTwoLinkModel`); the
workspace coordinates are the absolute link angles `x₁ = θ₁`, `x₂ = θ₁ + θ₂`, a linear map
`f(θ) = A θ` with `A = [[1, 0], [1, 1]]` and inverse `g(x) = A⁻¹ x`, `A⁻¹ = [[1, 0], [−1, 1]]`,
which is "smooth and invertible" in MLS's sense (p. 196). The effective inertia `M̃ = A⁻ᵀ M A⁻¹` is
uniformly positive definite, the workspace Coriolis matrix `C̃ = A⁻ᵀ C A⁻¹` is not zero, and the
joint closed loop under the workspace PD law is the joint PD closed loop with the gains `Aᵀ K_p A`,
`Aᵀ K_v A` and the set point `A⁻¹ x_d`, whose flow is constructed for the arm. With `K_p = K_v = I`
the set point `(x_d, 0)` is globally asymptotically stable in workspace coordinates, and every
closed-loop solution has `(A θ(t), A θ̇(t)) → (x_d, 0)`. These are instances, not separate results;
nothing here concerns a physical arm. Lean joint `0` is the book's joint 1. State sup norms.
-/

noncomputable section

open Matrix Filter Topology
open RoboLean.MapJacobian

namespace RoboLean.Examples

variable (r₁ r₂ l₁ : ℝ)

/-- **The absolute link angles of the planar two-link arm as linear workspace coordinates (MLS p.
196, a smooth and invertible map `f : Q → ℝᵖ` with `n = p = 2`):** `x = A θ`,
`A = [[1, 0], [1, 1]]`, so `x₁ = θ₁` and `x₂ = θ₁ + θ₂`. -/
def absoluteAngles : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 1, 1]

/-- **The inverse of the absolute-angle coordinates (MLS p. 196):** `A⁻¹ = [[1, 0], [−1, 1]]`, so
`θ₁ = x₁` and `θ₂ = x₂ − x₁`. -/
def absoluteAnglesInv : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; -1, 1]

/-- `A A⁻¹ = I` for the absolute-angle coordinates (MLS p. 196). -/
theorem absoluteAngles_mul_absoluteAnglesInv : absoluteAngles * absoluteAnglesInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [absoluteAngles, absoluteAnglesInv]

/-- `A⁻¹ A = I` for the absolute-angle coordinates (MLS p. 196). -/
theorem absoluteAnglesInv_mul_absoluteAngles : absoluteAnglesInv * absoluteAngles = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [absoluteAngles, absoluteAnglesInv]

/-- `A⁻¹` is `absoluteAnglesInv` (MLS p. 196). -/
private lemma inv_absoluteAngles : absoluteAngles⁻¹ = absoluteAnglesInv :=
  Matrix.inv_eq_right_inv absoluteAngles_mul_absoluteAnglesInv

/-- `f ∘ g = id` for the absolute-angle coordinates, `A (A⁻¹ x) = x` (MLS p. 196). -/
private lemma absoluteAngles_mulVec_absoluteAnglesInv_mulVec (x : Fin 2 → ℝ) :
    absoluteAngles *ᵥ (absoluteAnglesInv *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, absoluteAngles_mul_absoluteAnglesInv, Matrix.one_mulVec]

/-- `g ∘ f = id` for the absolute-angle coordinates, `A⁻¹ (A θ) = θ` (MLS p. 196). -/
private lemma absoluteAnglesInv_mulVec_absoluteAngles_mulVec (q : Fin 2 → ℝ) :
    absoluteAnglesInv *ᵥ (absoluteAngles *ᵥ q) = q := by
  rw [Matrix.mulVec_mulVec, absoluteAnglesInv_mul_absoluteAngles, Matrix.one_mulVec]

/-- The Jacobian matrix `J = A` of the absolute-angle coordinates is invertible (MLS p. 196). -/
private lemma isUnit_det_jac_absoluteAngles (q : Fin 2 → ℝ) :
    IsUnit (jac (fun q => absoluteAngles *ᵥ q) q).det := by
  rw [jac_linear]
  exact Matrix.isUnit_det_of_right_inverse absoluteAngles_mul_absoluteAnglesInv

/-- `‖v‖ ≤ 2 ‖A⁻¹ v‖` in the sup norm, since `A = [[1, 0], [1, 1]]` (MLS p. 196). -/
private lemma norm_le_two_mul_norm_absoluteAnglesInv_mulVec (v : Fin 2 → ℝ) :
    ‖v‖ ≤ 2 * ‖absoluteAnglesInv *ᵥ v‖ := by
  set w := absoluteAnglesInv *ᵥ v with hw
  have hv : v = absoluteAngles *ᵥ w := by
    rw [hw, absoluteAngles_mulVec_absoluteAnglesInv_mulVec]
  have h0 := norm_le_pi_norm w 0
  have h1 := norm_le_pi_norm w 1
  have hn := norm_nonneg w
  rw [Real.norm_eq_abs] at h0 h1
  rw [hv]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i
  · simp [absoluteAngles, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith
  · simp [absoluteAngles, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith [abs_add_le (w 0) (w 1)]

/-- `vᵀ M̃ v = (A⁻¹ v)ᵀ M (A⁻¹ v)` for `M̃ = A⁻ᵀ M A⁻¹` (MLS p. 197). -/
private lemma dotProduct_workspaceM_absoluteAngles (P : ManipulatorModel 2) (q v : Fin 2 → ℝ) :
    v ⬝ᵥ (P.workspaceM (fun q => absoluteAngles *ᵥ q) q *ᵥ v) =
      (absoluteAnglesInv *ᵥ v) ⬝ᵥ (P.M q *ᵥ (absoluteAnglesInv *ᵥ v)) := by
  rw [ManipulatorModel.workspaceM, jac_linear, inv_absoluteAngles, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **The effective inertia `M̃ = A⁻ᵀ M A⁻¹` of the planar arm in absolute angles is uniformly
positive definite (MLS p. 197, Lemma 4.11(1); p. 191's uniform condition):** with positive masses
and principal moments there is `λ > 0` with `λ‖v‖² ≤ vᵀ M̃(θ) v` for every `θ` and `v` (sup norm).
-/
theorem planarTwoLinkModel_workspaceM_absoluteAngles_uniformlyPosDef {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i)
    (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ lam > 0, ∀ q v : Fin 2 → ℝ, lam * ‖v‖ ^ 2 ≤
      v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceM
        (fun q => absoluteAngles *ᵥ q) q *ᵥ v) := by
  obtain ⟨lam, hlam, hb⟩ := planarTwoLinkArm_uniformlyPosDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  refine ⟨lam / 4, by positivity, fun q v => ?_⟩
  rw [dotProduct_workspaceM_absoluteAngles, planarTwoLinkModel_M]
  have h1 := hb q (absoluteAnglesInv *ᵥ v)
  have h2 := norm_le_two_mul_norm_absoluteAnglesInv_mulVec v
  have h3 : ‖v‖ ^ 2 ≤ 4 * ‖absoluteAnglesInv *ᵥ v‖ ^ 2 := by nlinarith [norm_nonneg v]
  nlinarith

/-- **The workspace PD law in absolute angles is joint PD control with congruent gains (MLS pp. 193,
198):** for the planar arm, the joint closed loop under the workspace PD law with `f(θ) = A θ` is
the closed loop (4.52) of PD control with compensation of `N` with the gains `Aᵀ K_p A`, `Aᵀ K_v A`
and the set point `A⁻¹ x_d`. -/
theorem planarTwoLinkModel_field_workspacePDTorque_absoluteAngles {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Kp Kv : Matrix (Fin 2) (Fin 2) ℝ) (xd : Fin 2 → ℝ) :
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspacePDTorque
          (fun q => absoluteAngles *ᵥ q) Kp Kv xd) 0 =
      (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdClosedLoop
        (absoluteAnglesᵀ * Kp * absoluteAngles) (absoluteAnglesᵀ * Kv * absoluteAngles)
        (absoluteAnglesInv *ᵥ xd) := by
  funext z
  rw [ManipulatorModel.pdClosedLoop]
  simp only [ManipulatorModel.field, ManipulatorModel.pdCompensatedTorque]
  rw [ManipulatorModel.workspacePDTorque_eq _ _ Kp Kv xd (isUnit_det_jac_absoluteAngles z.1),
    jac_linear]
  have e1 : (absoluteAnglesᵀ * Kv * absoluteAngles) *ᵥ z.2 =
      absoluteAnglesᵀ *ᵥ (Kv *ᵥ (absoluteAngles *ᵥ z.2)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hx : absoluteAngles *ᵥ z.1 - xd = absoluteAngles *ᵥ (z.1 - absoluteAnglesInv *ᵥ xd) := by
    rw [Matrix.mulVec_sub, absoluteAngles_mulVec_absoluteAnglesInv_mulVec]
  have e2 : (absoluteAnglesᵀ * Kp * absoluteAngles) *ᵥ (z.1 - absoluteAnglesInv *ᵥ xd) =
      absoluteAnglesᵀ *ᵥ (Kp *ᵥ (absoluteAngles *ᵥ z.1 - xd)) := by
    rw [hx]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, e2]

/-- **The workspace Coriolis matrix of the planar arm in absolute angles is not zero (MLS eqs.
(4.11), p. 165, and (4.55), p. 197):** for `m₂ l₁ r₂ ≠ 0`, the workspace robot's `C̃(x, ẋ)` at
`θ = (0, π/2)`, `θ̇ = (1, 0)` (that is `x = A θ`, `ẋ = A θ̇`) is not the zero matrix, so the skew
property of the instance is not trivial. -/
theorem planarTwoLinkModel_workspaceRobot_absoluteAngles_C_ne_zero {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (h : m₂ * l₁ * r₂ ≠ 0) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceRobot
        (fun q => absoluteAngles *ᵥ q) (fun x => absoluteAnglesInv *ᵥ x)).C
      (absoluteAngles *ᵥ ![0, Real.pi / 2]) (absoluteAngles *ᵥ ![1, 0]) ≠ 0 := by
  intro hC
  have h10 := congrFun (congrFun hC 1) 0
  simp only [ManipulatorModel.workspaceRobot, ManipulatorModel.workspaceC, jac_linear,
    jacDot_linear, inv_absoluteAngles, absoluteAnglesInv_mulVec_absoluteAngles_mulVec,
    Matrix.mul_zero, sub_zero, planarTwoLinkModel_C] at h10
  simp [absoluteAnglesInv, Matrix.mul_apply, Fin.sum_univ_two, Real.sin_pi_div_two] at h10
  apply h
  rcases h10 with (h0 | h0) | h0 <;> simp [h0]

/-- Symmetric link inertias of the planar arm as a model (MLS p. 162). -/
private lemma planarTwoLinkModel_linkInertia_isSymm' {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (g : ℝ)
    (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia k).IsSymm := by
  unfold planarTwoLinkModel
  exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂

/-- `M(θ)` of the planar arm as a model is positive definite (MLS Lemma 4.2(1), p. 171). -/
private lemma planarTwoLinkModel_M_posDef' {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
  rw [planarTwoLinkModel_M]
  exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂

/-- The congruent gain `Aᵀ I A` is positive definite (MLS p. 193, `K > 0`). -/
private lemma posDef_absoluteAngles_congr :
    (absoluteAnglesᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) * absoluteAngles).PosDef := by
  have hinj : Function.Injective absoluteAngles.mulVec := by
    intro a b hab
    have h := congrArg (absoluteAnglesInv *ᵥ ·) hab
    simpa only [absoluteAnglesInv_mulVec_absoluteAngles_mulVec] using h
  simpa using Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

/-- A joint flow under the workspace PD law in absolute angles exists (MLS p. 179). -/
private lemma exists_hasFlow_workspacePD_absoluteAngles {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ)
    (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (xd : Fin 2 → ℝ) :
    ∃ φ, Stability.HasFlow ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspacePDTorque
        (fun q => absoluteAngles *ᵥ q) 1 1 xd) 0) φ := by
  rw [planarTwoLinkModel_field_workspacePDTorque_absoluteAngles]
  exact planarTwoLinkArm_exists_hasFlow_pdClosedLoop m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂ g up Ne
    posDef_absoluteAngles_congr posDef_absoluteAngles_congr.posSemidef _

/-- **The workspace PD law for the planar two-link arm in absolute angles, every hypothesis
discharged (MLS p. 198 with Proposition 4.9, p. 193).** With positive masses and principal moments,
any gravity data and joint forces, and `K_p = K_v = I`, the set point `(x_d, 0)` of the workspace
robot under PD control with compensation of `N` is globally asymptotically stable at every `t₀ ≥ 0`
(state `(x, ẋ)`, sup norm). -/
theorem planarTwoLinkArm_globallyAsymptoticallyStableAt_workspacePD_absoluteAngles {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i)
    (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (xd : Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt
      (((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceRobot
          (fun q => absoluteAngles *ᵥ q) (fun x => absoluteAnglesInv *ᵥ x)).field
        (((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceRobot
          (fun q => absoluteAngles *ᵥ q) (fun x => absoluteAnglesInv *ᵥ x)).pdCompensatedTorque
            1 1 xd))
      (xd, 0) t₀ := by
  obtain ⟨φ, hφ⟩ := exists_hasFlow_workspacePD_absoluteAngles r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne xd
  exact ManipulatorModel.globallyAsymptoticallyStableAt_workspacePD _ _
    (planarTwoLinkModel_linkInertia_isSymm' r₁ r₂ l₁ g up Ne)
    (planarTwoLinkModel_M_posDef' r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne) (contDiff_linear _)
    ((contDiff_linear (k := 1) _).differentiable one_ne_zero)
    absoluteAngles_mulVec_absoluteAnglesInv_mulVec absoluteAnglesInv_mulVec_absoluteAngles_mulVec
    (planarTwoLinkModel_workspaceM_absoluteAngles_uniformlyPosDef r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up
      Ne) Matrix.PosDef.one Matrix.PosDef.one xd hφ ht₀

/-- **The workspace error of the planar arm under the workspace PD law in absolute angles tends to
zero (MLS p. 198 with Proposition 4.9, p. 193),** every hypothesis discharged: with positive masses
and principal moments, any gravity data and joint forces, and `K_p = K_v = I`, every closed-loop
solution `(θ, θ̇)` from `t₀ ≥ 0` has `(A θ(t), A θ̇(t)) → (x_d, 0)`. -/
theorem planarTwoLinkArm_tendsto_workspacePD_absoluteAngles {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ)
    (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (xd : Fin 2 → ℝ) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) {z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hz : Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspacePDTorque
        (fun q => absoluteAngles *ᵥ q) 1 1 xd)) t₀ z) :
    Tendsto (fun t => (absoluteAngles *ᵥ (z t).1, absoluteAngles *ᵥ (z t).2)) atTop
      (𝓝 (xd, 0)) := by
  obtain ⟨φ, hφ⟩ := exists_hasFlow_workspacePD_absoluteAngles r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne xd
  have h := ManipulatorModel.tendsto_workspacePD _ _
    (planarTwoLinkModel_linkInertia_isSymm' r₁ r₂ l₁ g up Ne)
    (planarTwoLinkModel_M_posDef' r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne) (contDiff_linear _)
    ((contDiff_linear (k := 1) _).differentiable one_ne_zero)
    absoluteAngles_mulVec_absoluteAnglesInv_mulVec absoluteAnglesInv_mulVec_absoluteAngles_mulVec
    (planarTwoLinkModel_workspaceM_absoluteAngles_uniformlyPosDef r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up
      Ne) Matrix.PosDef.one Matrix.PosDef.one xd hφ ht₀ hz
  simpa only [jac_linear] using h

end RoboLean.Examples
