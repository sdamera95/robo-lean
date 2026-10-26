import RoboLean.Control.RobotAugmentedPD
import RoboLean.Examples.PlanarTwoLinkControl
import RoboLean.Examples.RobotPDControl

/-!
# Augmented PD control for robots: instances (MLS Proposition 4.10, p. 194; p. 301; Exercise 9)

Instances showing that the hypotheses of the robot versions of MLS Proposition 4.10
(`Control/RobotAugmentedPD`) can be met, each with every hypothesis discharged and the gains
`K_p = K_v = I`:

* the planar two-link arm of MLS Figure 4.4 (p. 164, eqs. (4.10)–(4.11), p. 165) as a robot
  (`ManipulatorModel.toRobotSystem`), whose Coriolis matrix is not zero: semiglobal exponential
  tracking of every desired trajectory with bounded velocity
  (`planarTwoLinkRobot_augmentedPD_tracking`);
* a robot on `ℝ²` with constant inertia `M = I`, a constant skew-symmetric Coriolis matrix
  `C = [[0, −1], [1, 0]]` and `N = 0` (`gyroRobot`): it has the skew property and `C ≠ 0`, and
  its Coriolis matrix is bounded uniformly in the velocity, so the augmented PD law gives global
  exponential tracking of every desired trajectory (`gyroRobot_augmentedPD_tracking`);
* MLS Exercise 9 (p. 209) for the planar arm in the absolute link angles `x = A θ`,
  `A = [[1, 0], [1, 1]]`, the workspace coordinates of `Examples/RobotPDControl`: the workspace
  augmented PD law applied through `τ = Aᵀ F` gives semiglobal exponential tracking of the
  workspace error `(A θ − x_d, A θ̇ − ẋ_d)`
  (`planarTwoLinkArm_workspaceAugmentedPD_tracking_absoluteAngles`).

These are instances, not separate results; nothing here models a physical arm or a physical
gyroscopic system. Lean joint `0` is the book's joint 1. State `(x, ẋ) ∈ ℝ² × ℝ²`, sup norms.
-/

noncomputable section

open Matrix Filter Topology
open RoboLean.MapJacobian

namespace RoboLean.Examples

variable (r₁ r₂ l₁ : ℝ)

/-- Symmetric link inertias of the planar arm as a model (MLS p. 162). -/
private lemma planarTwoLinkModel_linkInertia_isSymm'' {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (g : ℝ)
    (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia k).IsSymm := by
  unfold planarTwoLinkModel
  exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂

/-- `M(θ)` of the planar arm as a model is positive definite (MLS Lemma 4.2(1), p. 171). -/
private lemma planarTwoLinkModel_M_posDef'' {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
  rw [planarTwoLinkModel_M]
  exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂

/-- **MLS Proposition 4.10 (p. 194) for the planar two-link arm as a robot (MLS p. 301), every
hypothesis discharged.** With positive masses and principal moments, any gravity data and joint
forces, `K_p = K_v = I` and a desired trajectory `x_d` with `ẋ_d = x_d'`, `ẍ_d = x_d''` and
`‖ẋ_d(t)‖ ≤ v_d` for `t ≥ 0`, the robot `toRobotSystem` of the arm (MLS eqs. (4.10)–(4.11), p. 165,
a nonzero Coriolis matrix) under the augmented PD law (4.53) has semiglobal exponential tracking:
there is `m > 0` and, for every `ρ > 0`, a rate `α > 0` such that every closed-loop solution from
`t₀ ≥ 0` with initial tracking error smaller than `ρ` satisfies
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀` (sup norm). -/
theorem planarTwoLinkRobot_augmentedPD_tracking {m₁ m₂ : ℝ} {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {xd xd' xd'' : ℝ → Fin 2 → ℝ}
    (hd : ∀ t, HasDerivAt xd (xd' t) t) (hd' : ∀ t, HasDerivAt xd' (xd'' t) t)
    (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖xd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).toRobotSystem.field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).toRobotSystem.augmentedPDTorque 1 1
          xd xd' xd'')) t₀ x →
      ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ < ρ → ∀ t, t₀ ≤ t →
        ‖((x t).1 - xd t, (x t).2 - xd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ := by
  set P := planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne with hP
  have hMu : ∃ lam > 0, ∀ q v : Fin 2 → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v) := by
    rw [hP, planarTwoLinkModel_M]
    exact planarTwoLinkArm_uniformlyPosDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMb : ∃ μ, ∀ q v w : Fin 2 → ℝ, |v ⬝ᵥ (P.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := by
    rw [hP, planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂
  exact P.toRobotSystem.augmentedPD_tracking
    (planarTwoLinkModel_M_posDef'' r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne) P.continuous_M
    P.toRobotSystem_differentiableAlongMotions
    (P.toRobotSystem_hasSkewProperty (planarTwoLinkModel_linkInertia_isSymm'' r₁ r₂ l₁ g up Ne))
    hMu hMb (planarTwoLinkModel_C_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne) Matrix.PosDef.one
    Matrix.PosDef.one hd hd' hvd

/-! ### A robot with a constant skew-symmetric Coriolis matrix -/

/-- **A robot on `ℝ²` in the sense of MLS p. 303 with constant inertia `M = I`, the constant
skew-symmetric Coriolis matrix `C = [[0, −1], [1, 0]]` and `N = 0`** (a "gyroscopic" coupling of the
two coordinates). An instance for MLS Proposition 4.10 (p. 194) and p. 301; it models no physical
system. -/
def gyroRobot : Control.RobotSystem 2 :=
  ⟨fun _ => 1, fun _ _ => !![0, -1; 1, 0], fun _ _ => 0⟩

/-- **`gyroRobot` has the skew property (MLS p. 300; Lemma 4.2(2), p. 171):** `M` is constant, so
every derivative `Ṁ` along a motion is `0`, and `Ṁ − 2C = −2C` is skew-symmetric. -/
theorem gyroRobot_hasSkewProperty : gyroRobot.HasSkewProperty := by
  intro x x' t Md _ hMd
  have h0 : Md = 0 := by
    ext i j
    exact (hMd i j).unique (hasDerivAt_const t _)
  subst h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gyroRobot]

/-- **The Coriolis matrix of `gyroRobot` is not zero (MLS p. 303)** at any configuration and
velocity, so its skew property is not trivial. -/
theorem gyroRobot_C_ne_zero (q v : Fin 2 → ℝ) : gyroRobot.C q v ≠ 0 := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  simp [gyroRobot] at h10

/-- **MLS Proposition 4.10 (p. 194) for `gyroRobot`, every hypothesis discharged: global
exponential tracking.** With `K_p = K_v = I` there are `m, α > 0` such that for every desired
trajectory with `ẋ_d = x_d'`, `ẍ_d = x_d''` (no bound on them) every closed-loop solution under the
augmented PD law (4.53) from `t₀ ≥ 0` satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖`
for `t ≥ t₀` (sup norm): the Coriolis matrix is bounded uniformly in the velocity
(`Control.RobotSystem.augmentedPD_tracking_of_bounded_C`). -/
theorem gyroRobot_augmentedPD_tracking :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin 2 → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution (gyroRobot.field (gyroRobot.augmentedPDTorque 1 1 xd xd' xd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖((x t).1 - xd t, (x t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ := by
  obtain ⟨lam, hlam, hl⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le
    (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef)
  obtain ⟨μ, -, hμ⟩ := Control.exists_abs_dotProduct_mulVec_le (1 : Matrix (Fin 2) (Fin 2) ℝ)
  obtain ⟨c, -, hc⟩ := Control.exists_abs_dotProduct_mulVec_le (!![0, -1; 1, 0] :
    Matrix (Fin 2) (Fin 2) ℝ)
  exact gyroRobot.augmentedPD_tracking_of_bounded_C (fun _ => Matrix.PosDef.one)
    continuous_const (fun _ => ⟨0, fun _ _ => hasDerivAt_const _ _⟩) gyroRobot_hasSkewProperty
    ⟨lam, hlam, fun _ v => hl v⟩ ⟨μ, fun _ v w => hμ v w⟩ ⟨c, fun _ _ v w => hc v w⟩
    Matrix.PosDef.one Matrix.PosDef.one

/-! ### MLS Exercise 9 for the planar arm in absolute link angles -/

/-- `A⁻¹` is `absoluteAnglesInv` (MLS p. 196). -/
private lemma inv_absoluteAngles' : absoluteAngles⁻¹ = absoluteAnglesInv :=
  Matrix.inv_eq_right_inv absoluteAngles_mul_absoluteAnglesInv

/-- `f ∘ g = id` for the absolute-angle coordinates, `A (A⁻¹ x) = x` (MLS p. 196). -/
private lemma absoluteAngles_mulVec_absoluteAnglesInv_mulVec' (x : Fin 2 → ℝ) :
    absoluteAngles *ᵥ (absoluteAnglesInv *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, absoluteAngles_mul_absoluteAnglesInv, Matrix.one_mulVec]

/-- `g ∘ f = id` for the absolute-angle coordinates, `A⁻¹ (A θ) = θ` (MLS p. 196). -/
private lemma absoluteAnglesInv_mulVec_absoluteAngles_mulVec' (q : Fin 2 → ℝ) :
    absoluteAnglesInv *ᵥ (absoluteAngles *ᵥ q) = q := by
  rw [Matrix.mulVec_mulVec, absoluteAnglesInv_mul_absoluteAngles, Matrix.one_mulVec]

/-- `‖A⁻¹ v‖ ≤ 2 ‖v‖` in the sup norm, since `A⁻¹ = [[1, 0], [−1, 1]]` (MLS p. 196). -/
private lemma norm_absoluteAnglesInv_mulVec_le (v : Fin 2 → ℝ) :
    ‖absoluteAnglesInv *ᵥ v‖ ≤ 2 * ‖v‖ := by
  have h0 := norm_le_pi_norm v 0
  have h1 := norm_le_pi_norm v 1
  have hn := norm_nonneg v
  rw [Real.norm_eq_abs] at h0 h1
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i
  · simp [absoluteAnglesInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith
  · simp [absoluteAnglesInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have := abs_add_le (-v 0) (v 1)
    rw [abs_neg] at this
    linarith

/-- `vᵀ (A⁻ᵀ B A⁻¹) w = (A⁻¹ v)ᵀ B (A⁻¹ w)`, the congruence of MLS p. 197. -/
private lemma dotProduct_congr_absoluteAnglesInv (B : Matrix (Fin 2) (Fin 2) ℝ)
    (v w : Fin 2 → ℝ) :
    v ⬝ᵥ ((absoluteAnglesInvᵀ * B * absoluteAnglesInv) *ᵥ w) =
      (absoluteAnglesInv *ᵥ v) ⬝ᵥ (B *ᵥ (absoluteAnglesInv *ᵥ w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- **The effective inertia of the planar arm in absolute angles is bounded (MLS p. 197,
`M̃ = A⁻ᵀ M A⁻¹`):** `|vᵀ M̃(θ) w| ≤ μ‖v‖‖w‖` for one `μ` (sup norm). -/
private lemma planarTwoLinkModel_workspaceM_absoluteAngles_bound {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ μ, ∀ q v w : Fin 2 → ℝ,
      |v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceM
        (fun q => absoluteAngles *ᵥ q) q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := by
  obtain ⟨μ, hμ⟩ := planarTwoLinkArm_massMatrix_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂
  refine ⟨4 * max μ 0, fun q v w => ?_⟩
  rw [ManipulatorModel.workspaceM, jac_linear, inv_absoluteAngles', planarTwoLinkModel_M,
    dotProduct_congr_absoluteAnglesInv]
  have hv := norm_absoluteAnglesInv_mulVec_le v
  have hw := norm_absoluteAnglesInv_mulVec_le w
  calc _ ≤ μ * ‖absoluteAnglesInv *ᵥ v‖ * ‖absoluteAnglesInv *ᵥ w‖ := hμ _ _ _
    _ ≤ max μ 0 * ‖absoluteAnglesInv *ᵥ v‖ * ‖absoluteAnglesInv *ᵥ w‖ := by
        gcongr
        exact le_max_left _ _
    _ ≤ max μ 0 * (2 * ‖v‖) * (2 * ‖w‖) := by gcongr
    _ = 4 * max μ 0 * ‖v‖ * ‖w‖ := by ring

/-- **The workspace robot's Coriolis matrix of the planar arm in absolute angles is bounded by the
velocity (MLS pp. 165, 197, `C̃ = A⁻ᵀ C A⁻¹` since `J̇ = 0`):** `|vᵀ C̃ w| ≤ δ‖u‖‖v‖‖w‖`. -/
private lemma planarTwoLinkModel_workspaceRobot_absoluteAngles_C_bound {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ δ, ∀ x u v w : Fin 2 → ℝ,
      |v ⬝ᵥ (((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceRobot
        (fun q => absoluteAngles *ᵥ q) (fun x => absoluteAnglesInv *ᵥ x)).C x u *ᵥ w)| ≤
        δ * ‖u‖ * ‖v‖ * ‖w‖ := by
  obtain ⟨δ, hδ⟩ := planarTwoLinkModel_C_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne
  refine ⟨8 * max δ 0, fun x u v w => ?_⟩
  simp only [ManipulatorModel.workspaceRobot, ManipulatorModel.workspaceC, jac_linear,
    jacDot_linear, inv_absoluteAngles', Matrix.mul_zero, sub_zero]
  rw [dotProduct_congr_absoluteAnglesInv]
  have hu := norm_absoluteAnglesInv_mulVec_le u
  have hv := norm_absoluteAnglesInv_mulVec_le v
  have hw := norm_absoluteAnglesInv_mulVec_le w
  calc _ ≤ δ * ‖absoluteAnglesInv *ᵥ u‖ * ‖absoluteAnglesInv *ᵥ v‖ *
        ‖absoluteAnglesInv *ᵥ w‖ := hδ _ _ _ _
    _ ≤ max δ 0 * ‖absoluteAnglesInv *ᵥ u‖ * ‖absoluteAnglesInv *ᵥ v‖ *
        ‖absoluteAnglesInv *ᵥ w‖ := by
        gcongr
        exact le_max_left _ _
    _ ≤ max δ 0 * (2 * ‖u‖) * (2 * ‖v‖) * (2 * ‖w‖) := by gcongr
    _ = 8 * max δ 0 * ‖u‖ * ‖v‖ * ‖w‖ := by ring

/-- **MLS Exercise 9 (p. 209) for the planar two-link arm in absolute link angles, every hypothesis
discharged.** With positive masses and principal moments, any gravity data and joint forces, the
workspace coordinates `x = A θ`, `A = [[1, 0], [1, 1]]` (MLS p. 196, inverse `A⁻¹ x`),
`K_p = K_v = I` and a desired workspace trajectory `x_d` with `ẋ_d = x_d'`, `ẍ_d = x_d''` and
`‖ẋ_d(t)‖ ≤ v_d` for `t ≥ 0`: there is `m > 0` and, for every `ρ > 0`, a rate `α > 0` such that
every joint solution `(θ, θ̇)` from `t₀ ≥ 0` under the workspace augmented PD law `τ = Aᵀ F` whose
initial workspace error `(A θ − x_d, A θ̇ − ẋ_d)` is smaller than `ρ` has workspace error at most
`m e^{−α(t − t₀)}` times the initial one for `t ≥ t₀` (sup norm). -/
theorem planarTwoLinkArm_workspaceAugmentedPD_tracking_absoluteAngles {m₁ m₂ : ℝ}
    {I₁ I₂ : Fin 3 → ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i)
    (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    {xd xd' xd'' : ℝ → Fin 2 → ℝ} (hd : ∀ t, HasDerivAt xd (xd' t) t)
    (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖xd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).workspaceAugmentedPDTorque
          (fun q => absoluteAngles *ᵥ q) (fun x => absoluteAnglesInv *ᵥ x) 1 1 xd xd' xd''))
        t₀ z →
      ‖(absoluteAngles *ᵥ (z t₀).1 - xd t₀, absoluteAngles *ᵥ (z t₀).2 - xd' t₀)‖ < ρ →
      ∀ t, t₀ ≤ t →
        ‖(absoluteAngles *ᵥ (z t).1 - xd t, absoluteAngles *ᵥ (z t).2 - xd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) *
            ‖(absoluteAngles *ᵥ (z t₀).1 - xd t₀, absoluteAngles *ᵥ (z t₀).2 - xd' t₀)‖ := by
  have h := ManipulatorModel.workspaceAugmentedPD_tracking _ _
    (planarTwoLinkModel_linkInertia_isSymm'' r₁ r₂ l₁ g up Ne)
    (planarTwoLinkModel_M_posDef'' r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up Ne) (contDiff_linear _)
    ((contDiff_linear (k := 1) _).differentiable one_ne_zero)
    absoluteAngles_mulVec_absoluteAnglesInv_mulVec' absoluteAnglesInv_mulVec_absoluteAngles_mulVec'
    (planarTwoLinkModel_workspaceM_absoluteAngles_uniformlyPosDef r₁ r₂ l₁ hm₁ hm₂ hI₁ hI₂ g up
      Ne) (planarTwoLinkModel_workspaceM_absoluteAngles_bound r₁ r₂ l₁ g up Ne)
    (planarTwoLinkModel_workspaceRobot_absoluteAngles_C_bound r₁ r₂ l₁ g up Ne)
    Matrix.PosDef.one Matrix.PosDef.one hd hd' hvd
  simpa only [jac_linear] using h

end RoboLean.Examples
