import RoboLean.Examples.ThreeLinkDynamics
import RoboLean.Examples.ThreeLinkGravityPD
import RoboLean.Cell.TrackingMove

/-!
# The three-link arm of the cell: a lower bound on its inertia matrix and the tube along a move

The arm is the three-link manipulator of MLS Example 4.3 (printed pp. 172–175, Figure 4.5) in
the library's form `Examples.threeLinkModel`, in gravity `g = 981/100` m/s² along `−z`, with the
design parameters (SI units) `l₀ = 2/5`, `l₁ = 17/40` m; masses `m₁ = 37/10`, `m₂ = 8393/1000`,
`m₃ = 49/10` kg; mass-centre offsets `r₁ = 17/80`, `r₂ = 3/10` m (`r₀ = 1/5` m, which enters
neither `M`, `C` nor `N`); principal moments about the mass centres `I₁ = (103/10000,
103/10000, 67/10000)`, `I₂ = (67/500, 3/200, 67/500)`, `I₃ = (39/500, 9/1000, 39/500)` kg m² in
the order `(I_x, I_y, I_z)` of the library's link frames (axes of the base frame at `θ = 0`,
where the arm lies along `+y`, so `I_y` is the moment about the link's own axis). The tool
length `l₂` does not enter the dynamics. These are design numbers, not a model of a commercial
arm.

**Formalized.**

* `cellArm` and its robot `cellRobot` (MLS p. 303).
* The inertia matrix (printed p. 173, `Examples.threeLinkArm_massMatrix`) is block diagonal, a
  yaw entry `M₀₀` and a `2 × 2` block in the shoulder and elbow. The block satisfies
  `(9/100) ‖w‖₂² ≤ wᵀ B w` at every configuration (its smallest eigenvalue is about `0.0933`,
  at the stretched elbow). The yaw entry is at least `307/10000` everywhere (the base link's
  moment about `z` plus the smaller moments of the other links), and at least `9/100` where the
  forearm's mass centre is at horizontal distance at least `1/8` m from the base axis,
  `17/40 cos θ₁ + 3/10 cos(θ₁ + θ₂) ≥ 1/8`. Hence `cellArm_inertia_lower` (`m₀ = 3/100`,
  every configuration) and `cellArm_inertia_lower_of_reach` (`m₀ = 9/100`).
* `cellArm_M_posDef`: `M(θ)` is positive definite at every configuration.
* `cellArm_move_tube`, `cellArm_move_tube_global`: the tube along a move (`move_tube`) for the
  arm's equations of motion under computed torque plus a disturbance torque;
  `cellArm_move_tube_accel` with the disturbance bounded at the acceleration level,
  `|(M(x)⁻¹ d)ᵢ| ≤ ω² δ`, without an inertia constant or a joint range.

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians). Exact model cancellation is assumed; nothing here concerns a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- **The cell's three-link arm (MLS Example 4.3, p. 172, as `Examples.threeLinkModel`)** with the
design parameters of the module docstring (SI units; gravity `981/100` along `−z`). -/
def cellArm : ManipulatorModel 3 :=
  Examples.threeLinkModel (37 / 10) (8393 / 1000) (49 / 10) (1 / 5) (17 / 80) (3 / 10) (2 / 5)
    (17 / 40) ![103 / 10000, 103 / 10000, 67 / 10000] ![67 / 500, 3 / 200, 67 / 500]
    ![39 / 500, 9 / 1000, 39 / 500] (981 / 100)

/-- **The cell's arm as a robot `(M, C, N)` (MLS p. 303).** -/
def cellRobot : Control.RobotSystem 3 :=
  cellArm.toRobotSystem

/-- The quadratic form of the cell arm's inertia matrix written out (from
`Examples.threeLinkArm_massMatrix`, MLS p. 173, with the design parameters). -/
private theorem cellArm_quadratic (θ v : Fin 3 → ℝ) :
    v ⬝ᵥ (cellArm.M θ *ᵥ v) =
      (3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 + 67 / 10000 +
        67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
        8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
        49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2) * v 0 ^ 2 +
      (67 / 500 + 39 / 500 + 49 / 10 * (17 / 40) ^ 2 + 8393 / 1000 * (17 / 80) ^ 2 +
        49 / 10 * (3 / 10) ^ 2 + 2 * (49 / 10) * (17 / 40) * (3 / 10) * Real.cos (θ 2)) * v 1 ^ 2 +
      2 * (39 / 500 + 49 / 10 * (3 / 10) ^ 2 + 49 / 10 * (17 / 40) * (3 / 10) * Real.cos (θ 2)) *
        v 1 * v 2 +
      (39 / 500 + 49 / 10 * (3 / 10) ^ 2) * v 2 ^ 2 := by
  simp only [cellArm, ManipulatorModel.M, Examples.threeLinkModel,
    Examples.threeLinkArm_massMatrix]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The shoulder–elbow block of the cell arm's inertia matrix is at least `9/100` times the
identity for every elbow cosine `c ∈ [−1, 1]`: the determinant condition of the block minus
`9/100` is a concave quadratic in `c`, positive at both ends. -/
private theorem cellArm_block_lower {c : ℝ} (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) (v₁ v₂ : ℝ) :
    9 / 100 * (v₁ ^ 2 + v₂ ^ 2) ≤
      (67 / 500 + 39 / 500 + 49 / 10 * (17 / 40) ^ 2 + 8393 / 1000 * (17 / 80) ^ 2 +
        49 / 10 * (3 / 10) ^ 2 + 2 * (49 / 10) * (17 / 40) * (3 / 10) * c) * v₁ ^ 2 +
      2 * (39 / 500 + 49 / 10 * (3 / 10) ^ 2 + 49 / 10 * (17 / 40) * (3 / 10) * c) * v₁ * v₂ +
      (39 / 500 + 49 / 10 * (3 / 10) ^ 2) * v₂ ^ 2 := by
  have hf : 0 ≤ (67 / 500 + 39 / 500 + 49 / 10 * (17 / 40) ^ 2 + 8393 / 1000 * (17 / 80) ^ 2 +
      49 / 10 * (3 / 10) ^ 2 + 2 * (49 / 10) * (17 / 40) * (3 / 10) * c - 9 / 100) *
      (429 / 1000) - (39 / 500 + 49 / 10 * (3 / 10) ^ 2 + 49 / 10 * (17 / 40) * (3 / 10) * c) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc₂) (by linarith : (0 : ℝ) ≤ c + 1)]
  nlinarith [sq_nonneg (429 / 1000 * v₂ +
    (39 / 500 + 49 / 10 * (3 / 10) ^ 2 + 49 / 10 * (17 / 40) * (3 / 10) * c) * v₁),
    mul_nonneg hf (sq_nonneg v₁)]

/-- The yaw entry of the cell arm's inertia matrix is at least `307/10000` plus the forearm mass
times the square of its mass centre's horizontal reach (from `sin² + cos² = 1`). -/
private theorem cellArm_yaw_lower (θ : Fin 3 → ℝ) :
    307 / 10000 + 49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 ≤
      3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 + 67 / 10000 +
        67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
        8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
        49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq (θ 1), Real.sin_sq_add_cos_sq (θ 1 + θ 2),
    sq_nonneg (Real.cos (θ 1)), sq_nonneg (Real.cos (θ 1 + θ 2))]

/-- The squared Euclidean norm of a joint vector of the arm, written out. -/
private theorem dotProduct_self_three (v : Fin 3 → ℝ) : v ⬝ᵥ v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [dotProduct, Fin.sum_univ_three]
  ring

/-- **A global lower bound on the cell arm's inertia matrix (MLS eq. (4.19) and p. 173 for the
matrix; the bound is a design statement, not from MLS):** `(3/100) ‖v‖₂² ≤ vᵀ M(θ) v` for every
configuration `θ` and every `v` (kg m²). -/
theorem cellArm_inertia_lower (θ v : Fin 3 → ℝ) :
    3 / 100 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (cellArm.M θ *ᵥ v) := by
  rw [cellArm_quadratic, dotProduct_self_three]
  have hyaw := cellArm_yaw_lower θ
  have hblock := cellArm_block_lower (Real.neg_one_le_cos (θ 2)) (Real.cos_le_one (θ 2)) (v 1) (v 2)
  nlinarith [mul_nonneg (sub_nonneg.2 hyaw) (sq_nonneg (v 0)), sq_nonneg (v 0), sq_nonneg (v 1),
    sq_nonneg (v 2), mul_nonneg (sq_nonneg (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)))
      (sq_nonneg (v 0))]

/-- **A lower bound on the cell arm's inertia matrix away from the vertical (MLS eq. (4.19) and
p. 173 for the matrix; the bound is a design statement, not from MLS):** if the forearm's mass
centre is at horizontal distance at least `1/8` m from the base axis,
`17/40 cos θ₁ + 3/10 cos(θ₁ + θ₂) ≥ 1/8`, then `(9/100) ‖v‖₂² ≤ vᵀ M(θ) v` for every `v`. -/
theorem cellArm_inertia_lower_of_reach {θ : Fin 3 → ℝ}
    (h : 1 / 8 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) (v : Fin 3 → ℝ) :
    9 / 100 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (cellArm.M θ *ᵥ v) := by
  rw [cellArm_quadratic, dotProduct_self_three]
  have hyaw := cellArm_yaw_lower θ
  have hblock := cellArm_block_lower (Real.neg_one_le_cos (θ 2)) (Real.cos_le_one (θ 2)) (v 1) (v 2)
  have hκ : 1 / 64 ≤ (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 := by
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hyaw) (sq_nonneg (v 0)), mul_nonneg (sub_nonneg.2 hκ)
    (sq_nonneg (v 0)), sq_nonneg (v 0)]

/-- **The cell arm's inertia matrix is positive definite at every configuration (MLS Lemma 4.2(1),
p. 171, for the cell arm; from `cellArm_inertia_lower` and the symmetry of the link inertias).** -/
theorem cellArm_M_posDef (θ : Fin 3 → ℝ) : (cellArm.M θ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun w hw => ?_
  · refine Matrix.isHermitian_iff_isSymm.mpr (InertialChain.massMatrix_isSymm _ (fun k => ?_) θ)
    fin_cases k <;> exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)
  · have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (w j))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hw))
    rw [star_trivial]
    linarith [cellArm_inertia_lower θ w]

/-- **A joint range that keeps the forearm away from the vertical (a design statement, not from
MLS):** if `|θ₁| ≤ π/3` and `|θ₁ + θ₂| ≤ π/2` (radians), then the forearm's mass centre is at
horizontal distance at least `1/8` m from the base axis,
`17/40 cos θ₁ + 3/10 cos(θ₁ + θ₂) ≥ 1/8` (in fact `≥ 17/80`). -/
theorem cellArm_reach_of_abs_le {θ : Fin 3 → ℝ} (h₁ : |θ 1| ≤ Real.pi / 3)
    (h₁₂ : |θ 1 + θ 2| ≤ Real.pi / 2) :
    1 / 8 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  have h1 : 1 / 2 ≤ Real.cos (θ 1) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [Real.pi_pos]) h₁
  have h2 : 0 ≤ Real.cos (θ 1 + θ 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le (θ 1 + θ 2)],
      by linarith [le_abs_self (θ 1 + θ 2)]⟩
  linarith

/-- **The tube along a move for the cell arm (a design statement, not from MLS; computed torque
of MLS eq. (4.49), p. 191, for the robot of p. 303).** The conclusion of `move_tube` for a motion
of `cellRobot` satisfying `M ẍ + C ẋ + N = F + d` at every `s ∈ (t₀, t₁]`, with `F` the robot's
computed torque for the gains `ω² I`, `2ω I` and the reference `moveRef a b t₀ T`, under
`‖d(s)‖₂ ≤ d̄ ≤ (9/100) ω² δ`, provided every configuration within `η > δ` of the reference
(each joint) at every `s ∈ (t₀, t₁]` keeps the forearm's mass centre at horizontal distance at
least `1/8` m from the base axis. -/
theorem cellArm_move_tube {ω δ η dbar t₀ t₁ T : ℝ} (hω : 0 < ω) (hδη : δ < η)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 9 / 100 * ω ^ 2 * δ) (hT : 0 < T) {a b : Fin 3 → ℝ}
    {x x' x'' d : ℝ → Fin 3 → ℝ}
    (hreach : ∀ s ∈ Ioc t₀ t₁, ∀ θ : Fin 3 → ℝ, (∀ i, |θ i - moveRef a b t₀ T s i| ≤ η) →
      1 / 8 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hd : ∀ s ∈ Ioc t₀ t₁, d s ⬝ᵥ d s ≤ dbar ^ 2)
    (hE : ∀ s ∈ Ioc t₀ t₁, cellRobot.M (x s) *ᵥ x'' s + cellRobot.C (x s) (x' s) *ᵥ x' s +
      cellRobot.N (x s) (x' s) = cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1)
        (moveRef a b t₀ T) (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) s (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) a 0) :
    (∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) ∧
      ∀ i, |x' t i - moveRefDeriv a b t₀ T t i| ≤ 2 * ω * δ) ∧
    ∀ t ∈ Icc (t₀ + T) t₁, InTube ω δ (x t) (x' t) b 0 ∧
      ∀ i, |x t i - b i| ≤ δ ∧ |x' t i| ≤ 2 * ω * δ :=
  move_tube (m₀ := 9 / 100) (Mt := fun s => cellRobot.M (x s))
    (Ct := fun s => cellRobot.C (x s) (x' s)) (Nt := fun s => cellRobot.N (x s) (x' s)) hω
    (by norm_num) hδη hdbar₀ hdbar hT hc hx hx'
    (fun s hs hnear v => cellArm_inertia_lower_of_reach (hreach s hs (x s) hnear) v) hd hE h₀

/-- **The tube along a move for the cell arm with the global inertia bound (a design statement,
not from MLS; computed torque of MLS eq. (4.49), p. 191, for the robot of p. 303):** the
conclusion of `cellArm_move_tube` without a joint-range hypothesis, under the smaller disturbance
budget `‖d(s)‖₂ ≤ d̄ ≤ (3/100) ω² δ`. -/
theorem cellArm_move_tube_global {ω δ dbar t₀ t₁ T : ℝ} (hω : 0 < ω)
    (hdbar₀ : 0 ≤ dbar) (hdbar : dbar ≤ 3 / 100 * ω ^ 2 * δ) (hT : 0 < T) {a b : Fin 3 → ℝ}
    {x x' x'' d : ℝ → Fin 3 → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hd : ∀ s ∈ Ioc t₀ t₁, d s ⬝ᵥ d s ≤ dbar ^ 2)
    (hE : ∀ s ∈ Ioc t₀ t₁, cellRobot.M (x s) *ᵥ x'' s + cellRobot.C (x s) (x' s) *ᵥ x' s +
      cellRobot.N (x s) (x' s) = cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1)
        (moveRef a b t₀ T) (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) s (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) a 0) :
    (∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) ∧
      ∀ i, |x' t i - moveRefDeriv a b t₀ T t i| ≤ 2 * ω * δ) ∧
    ∀ t ∈ Icc (t₀ + T) t₁, InTube ω δ (x t) (x' t) b 0 ∧
      ∀ i, |x t i - b i| ≤ δ ∧ |x' t i| ≤ 2 * ω * δ :=
  move_tube (η := δ + 1) (m₀ := 3 / 100) (Mt := fun s => cellRobot.M (x s))
    (Ct := fun s => cellRobot.C (x s) (x' s)) (Nt := fun s => cellRobot.N (x s) (x' s)) hω
    (by norm_num) (by linarith) hdbar₀ hdbar hT hc hx hx'
    (fun s _ _ v => cellArm_inertia_lower (x s) v) hd hE h₀

/-- **The tube along a move for the cell arm with the disturbance bounded at the acceleration
level (a design statement, not from MLS; computed torque of MLS eq. (4.49), p. 191, for the robot
of p. 303).** The conclusion of `cellArm_move_tube` for a motion of `cellRobot` satisfying
`M ẍ + C ẋ + N = F + d` at every `s ∈ (t₀, t₁]`, provided the acceleration the disturbance
produces, `M(x(s))⁻¹ d(s)`, is at most `ω² δ` in every joint (rad/s²) at every `s ∈ (t₀, t₁]`;
no joint range and no inertia constant enter (the arm's `M` is positive definite everywhere,
`cellArm_M_posDef`). -/
theorem cellArm_move_tube_accel {ω δ t₀ t₁ T : ℝ} (hω : 0 < ω) (hT : 0 < T) {a b : Fin 3 → ℝ}
    {x x' x'' d : ℝ → Fin 3 → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x (x' s) s) (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivAt x' (x'' s) s)
    (hacc : ∀ s ∈ Ioc t₀ t₁, ∀ i, |((cellRobot.M (x s))⁻¹ *ᵥ d s) i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, cellRobot.M (x s) *ᵥ x'' s + cellRobot.C (x s) (x' s) *ᵥ x' s +
      cellRobot.N (x s) (x' s) = cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1)
        (moveRef a b t₀ T) (moveRefDeriv a b t₀ T) (moveRefDeriv2 a b t₀ T) s (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) a 0) :
    (∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (moveRef a b t₀ T t) (moveRefDeriv a b t₀ T t) ∧
      ∀ i, |x' t i - moveRefDeriv a b t₀ T t i| ≤ 2 * ω * δ) ∧
    ∀ t ∈ Icc (t₀ + T) t₁, InTube ω δ (x t) (x' t) b 0 ∧
      ∀ i, |x t i - b i| ≤ δ ∧ |x' t i| ≤ 2 * ω * δ := by
  refine move_tube_accel (Mt := fun s => cellRobot.M (x s))
    (Ct := fun s => cellRobot.C (x s) (x' s)) (Nt := fun s => cellRobot.N (x s) (x' s)) hω hT hc
    hx hx' (fun s hs w hMw i => ?_) hE h₀
  have h := Control.PosDef.inv_mulVec_mulVec (cellArm_M_posDef (x s)) w
  change (cellRobot.M (x s))⁻¹ *ᵥ (cellRobot.M (x s) *ᵥ w) = w at h
  rw [hMw] at h
  rw [← h]
  exact hacc s hs i

end Cell
end RoboLean
