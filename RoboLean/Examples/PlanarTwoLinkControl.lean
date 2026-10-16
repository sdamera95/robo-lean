import RoboLean.Control.PDControl
import RoboLean.Control.ComputedTorque
import RoboLean.Control.PDAsymptotic
import RoboLean.Control.AugmentedPD
import RoboLean.Control.PDFlow
import RoboLean.Examples.PlanarTwoLinkDynamics

/-!
# The planar two-link arm under PD and computed torque control (MLS §5.2–5.3, pp. 190–195)

The arm of MLS Figure 4.4 (p. 164, `planarTwoLinkArm`) as a `ManipulatorModel 2`, with link
masses `m₁, m₂`, an arbitrary gravitational constant `g` and upward vector `up` (MLS treats the arm
as horizontal, `up = +z`, p. 165; any `up`, for example a vertical plane with `up = +y`, is allowed
here) and an arbitrary field `Nₑ` of further joint forces. For positive masses and principal
moments it satisfies every model hypothesis of the controller theorems: symmetric link inertias
and `M(θ)` positive definite at every configuration. With the gains `K_p = K_v = I` where a
statement fixes them:

* PD control with compensation of `N` makes `(θ_d, 0)` a Lyapunov-stable equilibrium
  (`planarTwoLinkArm_stableAt_pdCompensatedTorque`, MLS Proposition 4.9 as formalized);
* computed torque gives exponential tracking of every twice-differentiable desired trajectory
  (`planarTwoLinkArm_computedTorque_tracking`, MLS Proposition 4.8);
* `M(θ)` is uniformly positive definite in `θ`, `λ‖v‖² ≤ vᵀ M(θ) v` for one `λ > 0` (sup norm),
  the property MLS states on p. 191 (`planarTwoLinkArm_uniformlyPosDef`);
* given a solution flow of the closed loop, PD control with compensation of `N` makes `(θ_d, 0)`
  globally asymptotically stable
  (`planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque`, MLS Proposition 4.9 as
  formalized); the flow is constructed
  (`planarTwoLinkArm_exists_hasFlow_pdClosedLoop`, below), and the conclusion holds with no flow
  hypothesis (`planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque'`);
* the Coriolis matrix of the model is the printed matrix of MLS eq. (4.11), p. 165
  (`planarTwoLinkModel_C`);
* `M(θ)` is bounded, `|vᵀ M(θ) w| ≤ μ‖v‖‖w‖` for one `μ` (sup norm), with no sign hypothesis
  (`planarTwoLinkArm_massMatrix_bound`);
* `C(θ, u)` is bounded by the joint rate, `|vᵀ C(θ, u) w| ≤ δ‖u‖‖v‖‖w‖` for one `δ`
  (`planarTwoLinkModel_C_bound`);
* the augmented PD law (4.53) gives semiglobal exponential tracking of every twice-differentiable
  desired trajectory with bounded velocity (`planarTwoLinkArm_augmentedPD_tracking`, MLS
  Proposition 4.10 as formalized);
* for all gains and set points, the PD closed loop (4.52) is `C¹` and hence locally Lipschitz on
  the state `(θ, θ̇)` (`planarTwoLinkModel_contDiff_pdClosedLoop`,
  `planarTwoLinkModel_locallyLipschitz_pdClosedLoop`);
* the PD closed loop (4.52) has a solution flow, from local Lipschitz continuity and the energy
  `½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e` as a trapping Lyapunov function
  (`planarTwoLinkArm_exists_hasFlow_pdClosedLoop`, `ManipulatorModel.exists_hasFlow_pdClosedLoop`),
  so Proposition 4.9 as formalized holds for this arm with every hypothesis discharged
  (`planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque'`).

These are instances showing that the hypotheses of the general theorems can be met; they are not
separate results, and nothing here concerns a physical arm.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean.Examples

/-- **The planar two-link arm of MLS Figure 4.4 (p. 164) as a manipulator model (4.47)**, with link
masses `![m₁, m₂]`, gravitational constant `g`, upward vector `up` and further joint forces `Nₑ`. -/
def planarTwoLinkModel (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) : ManipulatorModel 2 where
  chain := planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  mass := ![m₁, m₂]
  gravity := g
  up := up
  jointForce := Ne

variable (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)

/-- The inertia matrix of the model is the arm's `M(θ)` (MLS eq. (4.10)). -/
theorem planarTwoLinkModel_M (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M =
      (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix := by
  funext q
  unfold ManipulatorModel.M planarTwoLinkModel
  rfl

/-- The link inertias of the planar arm `[[mᵢ I, 0], [0, diag(Iᵢ)]]` are symmetric (MLS p. 162). -/
theorem planarTwoLinkArm_linkInertia_isSymm (k : Fin 2) :
    ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkInertia k).IsSymm := by
  fin_cases k
  · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)
  · exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)

/-- **MLS Proposition 4.9 as formalized, for the planar two-link arm.** With positive masses and
principal moments, any gravity data and joint forces, and `K_p = K_v = I`, PD control with
compensation of `N` makes the set point `(θ_d, 0)` stable in the sense of Lyapunov at every
`t₀ ≥ 0`. -/
theorem planarTwoLinkArm_stableAt_pdCompensatedTorque (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (θd : Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.StableAt
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdCompensatedTorque 1 1 θd))
      (θd, 0) t₀ := by
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  exact ManipulatorModel.stableAt_pdCompensatedTorque _ hsymm hM Matrix.PosDef.one
    Matrix.PosSemidef.one θd ht₀

/-- **MLS Proposition 4.8 for the planar two-link arm.** With positive masses and principal
moments, any gravity data and joint forces, and `K_p = K_v = I`, there are `m, α > 0` such that
every solution of the arm under the computed torque law, for every twice-differentiable desired
trajectory, tracks it with error at most `m e^{−α(t − t₀)}` times the initial error. -/
theorem planarTwoLinkArm_computedTorque_tracking (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ m > 0, ∃ α > 0, ∀ {θd θd' θd'' : ℝ → Fin 2 → ℝ}, (∀ t, HasDerivAt θd (θd' t) t) →
      (∀ t, HasDerivAt θd' (θd'' t) t) → ∀ t₀, 0 ≤ t₀ →
      ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).computedTorque 1 1 θd θd' θd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  exact ManipulatorModel.computedTorque_tracking _ hM Matrix.PosDef.one Matrix.PosDef.one

/-- **`M(θ)` of the planar two-link arm is uniformly positive definite in `θ` (MLS p. 191).** With
positive masses and principal moments, there is one `λ > 0` with `λ‖v‖² ≤ vᵀ M(θ) v` for every
configuration `θ` and every `v` (sup norm on `Fin 2 → ℝ`). `M(θ)` is the printed matrix of MLS
eq. (4.10), p. 165, which depends on `θ` only through `cos θ₂ ∈ [−1, 1]`; the bound comes from
compactness of `[−1, 1]`. -/
theorem planarTwoLinkArm_uniformlyPosDef (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) :
    ∃ lam > 0, ∀ q v : Fin 2 → ℝ,
      lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q *ᵥ v) := by
  set A : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun c =>
    !![I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2) + 2 * (m₂ * l₁ * r₂) * c,
      I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * c;
      I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * c, I₂ 2 + m₂ * r₂ ^ 2] with hA
  have hcont : Continuous A := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hA] <;> fun_prop
  have hpos : ∀ c ∈ Set.Icc (-1 : ℝ) 1, (A c).PosDef := by
    intro c hc
    have h := planarTwoLinkArm_printedMassMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
      (Real.arccos c)
    rwa [Real.cos_arccos hc.1 hc.2] at h
  obtain ⟨lam, hlam, hb⟩ :=
    QuadraticBounds.exists_pos_mul_sq_norm_le_dotProduct_mulVec isCompact_Icc hcont hpos
  refine ⟨lam, hlam, fun q v => ?_⟩
  rw [planarTwoLinkArm_massMatrix]
  exact hb (Real.cos (q 1)) ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩ v

/-- **MLS Proposition 4.9 (p. 193) as formalized, for the planar two-link arm, given a flow.**
With positive masses and principal moments, any gravity data and joint forces, `K_p = K_v = I`,
and a solution flow `φ` of the closed loop (4.52), PD control with compensation of `N` makes the
set point `(θ_d, 0)` globally asymptotically stable at every `t₀ ≥ 0` (state `(θ, θ̇)`, sup norm).
The flow is a hypothesis: the flow of the planar arm's closed loop is not constructed in the
library (that needs local Lipschitz bounds on `M(θ)⁻¹` and `C(θ, θ̇)` and an extension of Mathlib's
local Picard–Lindelöf solutions to all forward time; neither is in the library or the pinned
Mathlib). -/
theorem planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (θd : Fin 2 → ℝ)
    {φ : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hφ : Stability.HasFlow ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdClosedLoop 1 1 θd)
      φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdCompensatedTorque 1 1 θd))
      (θd, 0) t₀ := by
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMu : ∃ lam > 0, ∀ q v : Fin 2 → ℝ,
      lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q *ᵥ v) := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_uniformlyPosDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  exact ManipulatorModel.globallyAsymptoticallyStableAt_pdCompensatedTorque _ hsymm hM hMu
    Matrix.PosDef.one Matrix.PosDef.one hφ ht₀

/-! ### The Coriolis matrix, bounds and augmented PD tracking (MLS §4.2, §5.3) -/

/-- **MLS eq. (4.11), p. 165, for the model:** the Coriolis matrix of `planarTwoLinkModel`, built
from the actual partial derivatives of `M` (`ManipulatorModel.C`), is the printed
`[[-β s₂ θ̇₂, -β s₂ (θ̇₁ + θ̇₂)], [β s₂ θ̇₁, 0]]` with `β = m₂ l₁ r₂`, `s₂ = sin θ₂` (`θ₂ = q 1`,
`θ̇ = v`). The partial derivatives agree with `planarTwoLinkArmMassDeriv` by uniqueness of the
Fréchet derivative. -/
theorem planarTwoLinkModel_C (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (q v : Fin 2 → ℝ) :
    (planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).C q v =
      !![-(m₂ * l₁ * r₂) * Real.sin (q 1) * v 1, -(m₂ * l₁ * r₂) * Real.sin (q 1) * (v 0 + v 1);
        m₂ * l₁ * r₂ * Real.sin (q 1) * v 0, 0] := by
  have hD : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrixDeriv q =
      planarTwoLinkArmMassDeriv m₂ r₂ l₁ q := by
    funext i j
    exact ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).hasFDerivAt_massMatrix q i j).unique
      (hasFDerivAt_planarTwoLinkArm_massMatrix m₁ m₂ r₁ r₂ l₁ I₁ I₂ q i j)
  unfold ManipulatorModel.C planarTwoLinkModel
  rw [hD]
  exact planarTwoLinkArm_coriolisMatrix m₂ r₂ l₁ q v

/-- **`M(θ)` of the planar two-link arm is bounded (MLS eq. (4.10), p. 165):** there is `μ` with
`|vᵀ M(θ) w| ≤ μ ‖v‖ ‖w‖` for every configuration `θ` and all `v, w` (sup norm on `Fin 2 → ℝ`).
The entries of `M(θ)` depend on `θ` only through `cos θ₂ ∈ [−1, 1]`; no sign hypothesis on the
parameters is needed. This is the upper bound on `M` used for MLS Proposition 4.10 (p. 194). -/
theorem planarTwoLinkArm_massMatrix_bound :
    ∃ μ, ∀ q v w : Fin 2 → ℝ,
      |v ⬝ᵥ ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).massMatrix q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := by
  set a := I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2)
  set b := m₂ * l₁ * r₂
  set d := I₂ 2 + m₂ * r₂ ^ 2
  refine ⟨|a| + 2 * |b| + 2 * (|d| + |b|) + |d|, fun q v w => ?_⟩
  refine (Control.abs_dotProduct_mulVec_le _ v w).trans ?_
  gcongr
  rw [planarTwoLinkArm_massMatrix]
  simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  have hbc : |b * Real.cos (q 1)| ≤ |b| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h1 : |a + 2 * b * Real.cos (q 1)| ≤ |a| + 2 * |b| := by
    rw [abs_le] at hbc ⊢
    constructor <;> linarith [neg_abs_le a, le_abs_self a]
  have h2 : |d + b * Real.cos (q 1)| ≤ |d| + |b| := by
    rw [abs_le] at hbc ⊢
    constructor <;> linarith [neg_abs_le d, le_abs_self d]
  linarith

/-- **The Coriolis matrix of the planar two-link arm is bounded by the joint rate (MLS
eq. (4.11), p. 165):** there is `δ` with `|vᵀ C(θ, u) w| ≤ δ ‖u‖ ‖v‖ ‖w‖` for every configuration
`θ` and all `u, v, w` (sup norm on `Fin 2 → ℝ`), from `|sin θ₂| ≤ 1` and the linearity of `C` in
the rate `u`. This is the bound on `C` used for MLS Proposition 4.10 (p. 194). -/
theorem planarTwoLinkModel_C_bound (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) :
    ∃ δ, ∀ q u v w : Fin 2 → ℝ,
      |v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).C q u *ᵥ w)| ≤
        δ * ‖u‖ * ‖v‖ * ‖w‖ := by
  set b := m₂ * l₁ * r₂
  refine ⟨4 * |b|, fun q u v w => ?_⟩
  refine (Control.abs_dotProduct_mulVec_le _ v w).trans ?_
  have hu : ∀ i, |u i| ≤ ‖u‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm u i
  have hs := Real.abs_sin_le_one (q 1)
  have hsum : ∑ i, ∑ j, |(planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).C q u i j| ≤
      4 * |b| * ‖u‖ := by
    rw [planarTwoLinkModel_C]
    simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', abs_mul, abs_neg,
      abs_zero]
    have e0 : |b| * |Real.sin (q 1)| * |u 0| ≤ |b| * 1 * ‖u‖ := by gcongr; exact hu 0
    have e1 : |b| * |Real.sin (q 1)| * |u 1| ≤ |b| * 1 * ‖u‖ := by gcongr; exact hu 1
    have h01 : |u 0 + u 1| ≤ 2 * ‖u‖ := by
      have := abs_add_le (u 0) (u 1)
      linarith [hu 0, hu 1]
    have e2 : |b| * |Real.sin (q 1)| * |u 0 + u 1| ≤ |b| * 1 * (2 * ‖u‖) := by gcongr
    have hb : |b| = |m₂| * |l₁| * |r₂| := by simp only [b, abs_mul]
    rw [hb] at e0 e1 e2 ⊢
    linarith
  calc (∑ i, ∑ j, |(planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).C q u i j|) * ‖v‖ * ‖w‖
      ≤ (4 * |b| * ‖u‖) * ‖v‖ * ‖w‖ := by gcongr
    _ = 4 * |b| * ‖u‖ * ‖v‖ * ‖w‖ := by ring

/-- **MLS Proposition 4.10 (p. 194) as formalized, for the planar two-link arm.** With positive
masses and principal moments, any gravity data and joint forces, the gains `K_p = K_v = I`, and a
twice-differentiable desired trajectory whose velocity is bounded for `t ≥ 0`, the augmented PD law
(4.53) gives semiglobal exponential tracking: there is `m > 0` and, for every `ρ > 0`, a rate
`α > 0` such that every closed-loop solution from `t₀ ≥ 0` with initial tracking error smaller
than `ρ` satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀` (state
`(θ, θ̇)`, sup norm). An instance of `ManipulatorModel.augmentedPD_tracking`: the bounds on `M` and
`C` that it assumes hold for this arm (`planarTwoLinkArm_uniformlyPosDef`,
`planarTwoLinkArm_massMatrix_bound`, `planarTwoLinkModel_C_bound`). -/
theorem planarTwoLinkArm_augmentedPD_tracking (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {θd θd' θd'' : ℝ → Fin 2 → ℝ}
    (hd : ∀ t, HasDerivAt θd (θd' t) t) (hd' : ∀ t, HasDerivAt θd' (θd'' t) t)
    (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖θd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ),
      Stability.IsSolution ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).augmentedPDTorque 1 1 θd θd' θd''))
        t₀ x →
      ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ < ρ → ∀ t, t₀ ≤ t →
        ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMu : ∃ lam > 0, ∀ q v : Fin 2 → ℝ,
      lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q *ᵥ v) := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_uniformlyPosDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMb : ∃ μ, ∀ q v w : Fin 2 → ℝ,
      |v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂
  exact ManipulatorModel.augmentedPD_tracking _ hsymm hM hMu hMb
    (planarTwoLinkModel_C_bound m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne) Matrix.PosDef.one
    Matrix.PosDef.one hd hd' hvd

/-! ### Smoothness of the PD closed loop (MLS eq. (4.52), p. 193) -/

/-- Entries of `A(z) w(z)` are `C¹` when the entries of `A` and `w` are. -/
private theorem contDiff_mulVec_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix (Fin 2) (Fin 2) ℝ} {w : E → Fin 2 → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 fun z => A z i j) (hw : ∀ j, ContDiff ℝ 1 fun z => w z j)
    (i : Fin 2) : ContDiff ℝ 1 fun z => (A z *ᵥ w z) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => (hA i j).mul (hw j)

/-- **The PD closed loop (4.52) of the planar two-link arm is `C¹` (MLS p. 193, with eqs. (4.10)
and (4.11), p. 165).** With positive masses and principal moments, for all gains `K_p, K_v` and
every set point `θ_d`, the autonomous field
`(q, v) ↦ (v, M(q)⁻¹(−K_v v − K_p (q − θ_d) − C(q, v) v))` on the state `(θ, θ̇)` is continuously
differentiable: `M(q)` and `C(q, v)` have trigonometric
entries and `det M(q) > 0` (positive definiteness, MLS Lemma 4.2(1), p. 171), so
`M(q)⁻¹ = (det M(q))⁻¹ adj M(q)` is `C¹`. -/
theorem planarTwoLinkModel_contDiff_pdClosedLoop (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (Kp Kv : Matrix (Fin 2) (Fin 2) ℝ)
    (θd : Fin 2 → ℝ) :
    ContDiff ℝ 1 ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdClosedLoop Kp Kv θd) := by
  set P := planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne with hP
  have hpos : ∀ q, (P.M q).PosDef := by
    rw [hP, planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hM : ∀ i j, ContDiff ℝ 1 fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => P.M z.1 i j := by
    intro i j
    simp only [hP, planarTwoLinkModel_M, planarTwoLinkArm_massMatrix]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hC : ∀ i j, ContDiff ℝ 1 fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => P.C z.1 z.2 i j := by
    intro i j
    simp only [hP, planarTwoLinkModel_C]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hdet : ContDiff ℝ 1 fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (P.M z.1).det := by
    simp only [Matrix.det_fin_two]
    exact ((hM 0 0).mul (hM 1 1)).sub ((hM 0 1).mul (hM 1 0))
  have hinv : ∀ i j, ContDiff ℝ 1 fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (P.M z.1)⁻¹ i j := by
    intro i j
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
      Matrix.adjugate_fin_two]
    refine (hdet.inv fun z => (hpos z.1).det_pos.ne').mul ?_
    fin_cases i <;> fin_cases j <;> simp
    · exact hM 1 1
    · exact (hM 0 1).neg
    · exact (hM 1 0).neg
    · exact hM 0 0
  have hfun : P.pdClosedLoop Kp Kv θd = fun z => (z.2,
      (P.M z.1)⁻¹ *ᵥ (-(Kv *ᵥ z.2) - Kp *ᵥ (z.1 - θd) - P.C z.1 z.2 *ᵥ z.2)) := by
    funext z
    exact P.pdClosedLoop_apply Kp Kv θd z.1 z.2
  rw [hfun]
  refine contDiff_snd.prodMk (contDiff_pi.2 fun i => contDiff_mulVec_apply hinv (fun j => ?_) i)
  simp only [Pi.sub_apply, Pi.neg_apply]
  have hv : ∀ k, ContDiff ℝ 1 fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => z.2 k := fun k => by fun_prop
  have he : ∀ k, ContDiff ℝ 1 fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (z.1 - θd) k := fun k => by
    simp only [Pi.sub_apply]
    fun_prop
  exact ((contDiff_mulVec_apply (A := fun _ => Kv) (fun _ _ => contDiff_const) hv j).neg.sub
    (contDiff_mulVec_apply (A := fun _ => Kp) (fun _ _ => contDiff_const) he j)).sub
    (contDiff_mulVec_apply hC hv j)

/-- **The PD closed loop (4.52) of the planar two-link arm is locally Lipschitz (MLS p. 193).**
With positive masses and principal moments, for all gains and every set point, the field
`(q, v) ↦ (v, M(q)⁻¹(−K_v v − K_p (q − θ_d) − C(q, v) v))` on the state `(θ, θ̇)` is locally
Lipschitz (sup norm), from `planarTwoLinkModel_contDiff_pdClosedLoop` and Mathlib's
`ContDiff.locallyLipschitz`. This is the local hypothesis of Picard–Lindelöf for the closed loop;
it does not by itself give solutions for all forward time. -/
theorem planarTwoLinkModel_locallyLipschitz_pdClosedLoop (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (Kp Kv : Matrix (Fin 2) (Fin 2) ℝ)
    (θd : Fin 2 → ℝ) :
    LocallyLipschitz ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdClosedLoop Kp Kv θd) :=
  (planarTwoLinkModel_contDiff_pdClosedLoop m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂ g up Ne Kp Kv
    θd).locallyLipschitz


/-! ### The flow of the PD closed loop (MLS p. 179, (4.52), p. 193) -/

/-- **The PD closed loop (4.52) of the planar two-link arm has a solution flow** (MLS's standing
existence and uniqueness assumption, p. 179, discharged). With positive masses and principal
moments, any gravity data and joint forces, `K_p` positive definite and `K_v` positive
semidefinite, the closed loop of PD control with compensation of `N` has a flow
(`Stability.HasFlow`): it is locally Lipschitz (`planarTwoLinkModel_locallyLipschitz_pdClosedLoop`)
and the energy `½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e`, with compact sublevel sets since `M` is uniformly positive
definite, does not increase along it (`ManipulatorModel.exists_hasFlow_pdClosedLoop`). State
`(θ, θ̇)`, sup norm. -/
theorem planarTwoLinkArm_exists_hasFlow_pdClosedLoop (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {Kp Kv : Matrix (Fin 2) (Fin 2) ℝ}
    (hKp : Kp.PosDef) (hKv : Kv.PosSemidef) (θd : Fin 2 → ℝ) :
    ∃ φ, Stability.HasFlow
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdClosedLoop Kp Kv θd) φ := by
  have hsymm : ∀ k, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).chain.linkInertia
      k).IsSymm := by
    unfold planarTwoLinkModel
    exact planarTwoLinkArm_linkInertia_isSymm m₁ m₂ r₁ r₂ l₁ I₁ I₂
  have hM : ∀ q, ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q).PosDef := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_massMatrix_posDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  have hMu : ∃ lam > 0, ∀ q v : Fin 2 → ℝ,
      lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).M q *ᵥ v) := by
    rw [planarTwoLinkModel_M]
    exact planarTwoLinkArm_uniformlyPosDef m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂
  exact ManipulatorModel.exists_hasFlow_pdClosedLoop _ hsymm hM hMu hKp hKv θd
    (planarTwoLinkModel_locallyLipschitz_pdClosedLoop m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁ hI₂ g up Ne
      Kp Kv θd)

/-- **MLS Proposition 4.9 (p. 193) as formalized, for the planar two-link arm, with every
hypothesis discharged.** With positive masses and principal moments, any gravity data and joint
forces, and `K_p = K_v = I`, PD control with compensation of `N` makes the set point `(θ_d, 0)`
globally asymptotically stable at every `t₀ ≥ 0` (state `(θ, θ̇)`, sup norm). The same conclusion
as `planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque`, whose flow hypothesis is
discharged by `planarTwoLinkArm_exists_hasFlow_pdClosedLoop`. -/
theorem planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque' (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (θd : Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt
      ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).field
        ((planarTwoLinkModel m₁ m₂ r₁ r₂ l₁ I₁ I₂ g up Ne).pdCompensatedTorque 1 1 θd))
      (θd, 0) t₀ := by
  obtain ⟨φ, hφ⟩ := planarTwoLinkArm_exists_hasFlow_pdClosedLoop m₁ m₂ r₁ r₂ l₁ I₁ I₂ hm₁ hm₂ hI₁
    hI₂ g up Ne Matrix.PosDef.one Matrix.PosSemidef.one θd
  exact planarTwoLinkArm_globallyAsymptoticallyStableAt_pdCompensatedTorque m₁ m₂ r₁ r₂ l₁ I₁ I₂
    hm₁ hm₂ hI₁ hI₂ g up Ne θd hφ ht₀

end RoboLean.Examples
