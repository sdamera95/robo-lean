import RoboLean.Cell.AssuredContractInstance

/-!
# The assured cell with the disturbance bounded by one torque per joint

The plant hypothesis of the assured cell theorem at the design point (gain `ω = 80` rad/s, tube
radius `δ = 3/100` rad) bounds the acceleration that the disturbance torque `d` produces,
`|(M(x)⁻¹ d)ᵢ| ≤ ω² δ = 192` rad/s² for every joint. Here that hypothesis is replaced by one
bound per joint on the disturbance torque itself, `|dᵢ(t)| ≤ bᵢ` (N m).

The inertia matrix of the cell arm (MLS eq. (4.19), p. 168, and the matrix of Example 4.3,
printed p. 173, with the cell's parameters) is block diagonal: the yaw entry `M₀₀(θ)` and a
`2 × 2` block `B` in the shoulder and the elbow that depends only on `c = cos θ₂`:
`B₁₁ = 12269177/6400000 + (2499/2000) c`, `B₁₂ = 519/1000 + (2499/4000) c`, `B₂₂ = 519/1000`,
with `det B = 4643792463/6400000000 − (6245001/16000000) c²`. By Cramer's rule
`(M⁻¹ d)₀ = d₀ / M₀₀`, `det B · (M⁻¹ d)₁ = B₂₂ d₁ − B₁₂ d₂` and
`det B · (M⁻¹ d)₂ = B₁₁ d₂ − B₁₂ d₁`. For `c ∈ [−1, 1]` the conditions
`B₂₂ b₁ + |B₁₂| b₂ ≤ A det B` and `|B₁₂| b₁ + B₁₁ b₂ ≤ A det B` are hardest at the straight elbow
`c = 1`, where `B₁₂ = 183/160`, `B₁₁ = 20265977/6400000` and
`det B = 2145792063/6400000000`; the straight elbow lies in every cell of the scene, so a joint
range does not help these two rows. The yaw entry is at least `307/10000` kg m² at every
configuration (the value with the arm pointing straight up), and at least `215869/320000` kg m²
where the forearm's mass centre is at horizontal distance at least `29/80` m from the base axis,
which holds within `1/10` rad of every cell.

**Formalized.**

* `cellArm_inv_mulVec_abs_le`: at every configuration `θ`, every torque `τ` with `|τᵢ| ≤ bᵢ`
  gives `|(M(θ)⁻¹ τ)ᵢ| ≤ A`, provided `b₀ ≤ (307/10000) A` and two linear conditions on
  `b₁, b₂` (the straight elbow); `cellArm_inv_mulVec_abs_le_of_reach`: the same with
  `b₀ ≤ (215869/320000) A` at the configurations of reach at least `29/80` m.
* `tube_invariant_on_accel_right_of_near`: the tube with right derivatives, the acceleration
  bound required only while every joint is within `η > δ` of the reference (first exit).
* `CellArmFollowsTorqueRightAt`, the per-period tracking predicate with the disturbance torque
  bounded per joint; `CellArmFollowsTorqueRightAt.accel` (with the configuration-free conditions
  it implies `CellArmFollowsAccelRightAt`); `cellArm_moveCorollary_torque_right`, the loop's move
  corollary for it.
* `cell_assured_contract_torque_right` and, at the design point with
  `b = (129, 149/10, 149/10)` N m, `cell_assured_contract_design_torque_right`: the assured cell
  with the supervisor's contract as premise and the disturbance torque bounded per joint.
* `demo_assured_contract_torque_right`: the demonstration run (tracked exactly, zero
  disturbance) meets every hypothesis of the design-point theorem.

Lean joint `k` is the book's joint `k + 1` (`θ 0` base yaw, `θ 1` shoulder, `θ 2` elbow, in
radians); torques in N m, accelerations in rad/s², time in seconds. The arm's numbers, the
scene, the loop and the bounds are design statements, not from MLS. Exact model cancellation is
assumed; nothing here concerns a physical arm.
-/

noncomputable section

open Matrix Set

namespace RoboLean
namespace Cell

/-- The cell arm's inertia matrix applied to a joint vector, written out (MLS p. 173,
`Examples.threeLinkArm_massMatrix`, with the cell's parameters): the yaw entry times `w₀`, and
the shoulder–elbow block times `(w₁, w₂)`. -/
private theorem cellArm_M_mulVec (θ w : Fin 3 → ℝ) :
    cellArm.M θ *ᵥ w =
      ![(3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 + 67 / 10000 +
          67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
          8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
          49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2) * w 0,
        (12269177 / 6400000 + 2499 / 2000 * Real.cos (θ 2)) * w 1 +
          (519 / 1000 + 2499 / 4000 * Real.cos (θ 2)) * w 2,
        (519 / 1000 + 2499 / 4000 * Real.cos (θ 2)) * w 1 + 519 / 1000 * w 2] := by
  ext i
  fin_cases i <;>
    simp [cellArm, ManipulatorModel.M, Examples.threeLinkModel, Examples.threeLinkArm_massMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- One row of a linear system solved by Cramer's rule: if `D w = P τa − Q τb` with `D > 0`,
`P ≥ 0`, `|τa| ≤ ba`, `|τb| ≤ bb` and `P ba ± Q bb ≤ A D`, then `|w| ≤ A`. -/
private theorem abs_le_of_cramer {D P Q w τa τb ba bb A : ℝ} (hD : 0 < D) (hP : 0 ≤ P)
    (hw : D * w = P * τa - Q * τb) (ha : |τa| ≤ ba) (hb : |τb| ≤ bb)
    (hplus : P * ba + Q * bb ≤ A * D) (hminus : P * ba - Q * bb ≤ A * D) : |w| ≤ A := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  have hPa₁ : P * τa ≤ P * ba := mul_le_mul_of_nonneg_left ha₂ hP
  have hPa₂ : P * -ba ≤ P * τa := mul_le_mul_of_nonneg_left ha₁ hP
  have hQb : |Q * τb| ≤ |Q| * bb := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg Q)
  obtain ⟨hQb₁, hQb₂⟩ := abs_le.mp hQb
  have hQ : |Q| * bb ≤ A * D - P * ba := by
    rcases abs_cases Q with ⟨hq, -⟩ | ⟨hq, -⟩ <;> rw [hq] <;> linarith
  have hup : D * w ≤ D * A := by nlinarith
  have hlo : D * -A ≤ D * w := by nlinarith
  exact abs_le.mpr ⟨le_of_mul_le_mul_left hlo hD, le_of_mul_le_mul_left hup hD⟩

/-- The yaw entry of the cell arm's inertia matrix is at least `307/10000` kg m² plus the forearm
mass times the square of its mass centre's horizontal reach (from `sin² + cos² = 1`). -/
private theorem cellArm_yaw_ge (θ : Fin 3 → ℝ) :
    307 / 10000 + 49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 ≤
      3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 + 67 / 10000 +
        67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
        8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
        49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq (θ 1), Real.sin_sq_add_cos_sq (θ 1 + θ 2),
    sq_nonneg (Real.cos (θ 1)), sq_nonneg (Real.cos (θ 1 + θ 2))]

/-- The determinant of the shoulder–elbow block is positive for every elbow cosine `c ∈ [−1, 1]`
(its least value there, at `c = ±1`, is `2145792063/6400000000`). -/
private theorem block_det_pos {c : ℝ} (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1) :
    0 < (12269177 / 6400000 + 2499 / 2000 * c) * (519 / 1000) -
      (519 / 1000 + 2499 / 4000 * c) ^ 2 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - c) (by linarith : (0 : ℝ) ≤ 1 + c)]

/-- The concavity step: a linear function `u + v c` that is at most
`(2145792063/6400000000) A` at `c = ±1` is at most `A det B(c)` on `[−1, 1]`, since
`det B(c) = 2145792063/6400000000 + (6245001/16000000)(1 − c)(1 + c)` and `A ≥ 0`. -/
private theorem le_mul_block_det {A c u v : ℝ} (hA : 0 ≤ A) (hc₁ : -1 ≤ c) (hc₂ : c ≤ 1)
    (hp : u + v ≤ 2145792063 / 6400000000 * A) (hm : u - v ≤ 2145792063 / 6400000000 * A) :
    u + v * c ≤ A * ((12269177 / 6400000 + 2499 / 2000 * c) * (519 / 1000) -
      (519 / 1000 + 2499 / 4000 * c) ^ 2) := by
  have h1 : (0 : ℝ) ≤ 1 + c := by linarith
  have h2 : (0 : ℝ) ≤ 1 - c := by linarith
  nlinarith [mul_nonneg h1 (sub_nonneg.2 hp), mul_nonneg h2 (sub_nonneg.2 hm),
    mul_nonneg hA (mul_nonneg h2 h1)]

/-- The common core of the two per-joint bounds: with a lower bound `m > 0` on the yaw entry at
`θ`, `b₀ ≤ m A` and the two conditions at the straight elbow, `|(M(θ)⁻¹ τ)ᵢ| ≤ A` for every
`τ` with `|τᵢ| ≤ bᵢ`. -/
private theorem inv_mulVec_abs_le_core {A m : ℝ} {b : Fin 3 → ℝ} (hb₁ : 0 ≤ b 1)
    (hb₂ : 0 ≤ b 2) (h₀ : b 0 ≤ m * A)
    (h₁ : 519 / 1000 * b 1 + 183 / 160 * b 2 ≤ 2145792063 / 6400000000 * A)
    (h₂ : 183 / 160 * b 1 + 20265977 / 6400000 * b 2 ≤ 2145792063 / 6400000000 * A)
    {θ : Fin 3 → ℝ} (hm : 0 < m)
    (hmθ : m ≤ 3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 +
      67 / 10000 + 67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
      8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
      49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2)
    (τ : Fin 3 → ℝ) (hτ : ∀ i, |τ i| ≤ b i) (i : Fin 3) :
    |((cellArm.M θ)⁻¹ *ᵥ τ) i| ≤ A := by
  have hMw : cellArm.M θ *ᵥ ((cellArm.M θ)⁻¹ *ᵥ τ) = τ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (cellArm_M_posDef θ).isUnit), Matrix.one_mulVec]
  generalize (cellArm.M θ)⁻¹ *ᵥ τ = w at hMw ⊢
  rw [cellArm_M_mulVec] at hMw
  have e0 := congrFun hMw 0
  have e1 := congrFun hMw 1
  have e2 := congrFun hMw 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e0 e1 e2
  have hA : 0 ≤ A := by linarith
  have hc₁ : -1 ≤ Real.cos (θ 2) := Real.neg_one_le_cos _
  have hc₂ : Real.cos (θ 2) ≤ 1 := Real.cos_le_one _
  have hD := block_det_pos hc₁ hc₂
  -- the yaw: `M₀₀ w₀ = τ₀` with `M₀₀ ≥ m`
  have hw0 : |w 0| ≤ A := by
    have hm0 : 0 < 3 / 200 * Real.sin (θ 1) ^ 2 + 9 / 1000 * Real.sin (θ 1 + θ 2) ^ 2 +
        67 / 10000 + 67 / 500 * Real.cos (θ 1) ^ 2 + 39 / 500 * Real.cos (θ 1 + θ 2) ^ 2 +
        8393 / 1000 * (17 / 80) ^ 2 * Real.cos (θ 1) ^ 2 +
        49 / 10 * (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2)) ^ 2 := by linarith
    have h := hτ 0
    rw [← e0, abs_mul, abs_of_pos hm0] at h
    refine le_of_mul_le_mul_left ?_ hm0
    nlinarith [abs_nonneg (w 0), mul_le_mul_of_nonneg_right hmθ hA]
  -- the shoulder: `det B · w₁ = B₂₂ τ₁ − B₁₂ τ₂`
  have hw1 : |w 1| ≤ A := by
    refine abs_le_of_cramer hD (by norm_num) (P := 519 / 1000)
      (Q := 519 / 1000 + 2499 / 4000 * Real.cos (θ 2)) (τa := τ 1) (τb := τ 2) ?_ (hτ 1) (hτ 2)
      ?_ ?_
    · rw [← e1, ← e2]
      ring
    · linarith [le_mul_block_det hA hc₁ hc₂ (u := 519 / 1000 * b 1 + 519 / 1000 * b 2)
        (v := 2499 / 4000 * b 2) (by linarith) (by linarith)]
    · linarith [le_mul_block_det hA hc₁ hc₂ (u := 519 / 1000 * b 1 - 519 / 1000 * b 2)
        (v := -(2499 / 4000 * b 2)) (by linarith) (by linarith)]
  -- the elbow: `det B · w₂ = B₁₁ τ₂ − B₁₂ τ₁`
  have hw2 : |w 2| ≤ A := by
    refine abs_le_of_cramer hD (by linarith)
      (P := 12269177 / 6400000 + 2499 / 2000 * Real.cos (θ 2))
      (Q := 519 / 1000 + 2499 / 4000 * Real.cos (θ 2)) (τa := τ 2) (τb := τ 1) ?_ (hτ 2) (hτ 1)
      ?_ ?_
    · rw [← e1, ← e2]
      ring
    · linarith [le_mul_block_det hA hc₁ hc₂
        (u := 12269177 / 6400000 * b 2 + 519 / 1000 * b 1)
        (v := 2499 / 2000 * b 2 + 2499 / 4000 * b 1) (by linarith) (by linarith)]
    · linarith [le_mul_block_det hA hc₁ hc₂
        (u := 12269177 / 6400000 * b 2 - 519 / 1000 * b 1)
        (v := 2499 / 2000 * b 2 - 2499 / 4000 * b 1) (by linarith) (by linarith)]
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2

/-- **The acceleration of a torque bounded per joint, for the cell arm, at every configuration
(MLS eq. (4.19), p. 168, and p. 173 for the inertia matrix; the bound is a design statement, not
from MLS).** Let `b₁, b₂ ≥ 0`, `b₀ ≤ (307/10000) A`, and at the straight elbow
`(519/1000) b₁ + (183/160) b₂ ≤ (2145792063/6400000000) A` and
`(183/160) b₁ + (20265977/6400000) b₂ ≤ (2145792063/6400000000) A`. Then for every
configuration `θ` (radians) and every joint torque `τ` with `|τᵢ| ≤ bᵢ` for every joint (N m),
the acceleration it produces satisfies `|(M(θ)⁻¹ τ)ᵢ| ≤ A` for every joint (rad/s²). -/
theorem cellArm_inv_mulVec_abs_le {A : ℝ} {b : Fin 3 → ℝ} (hb₁ : 0 ≤ b 1) (hb₂ : 0 ≤ b 2)
    (h₀ : b 0 ≤ 307 / 10000 * A)
    (h₁ : 519 / 1000 * b 1 + 183 / 160 * b 2 ≤ 2145792063 / 6400000000 * A)
    (h₂ : 183 / 160 * b 1 + 20265977 / 6400000 * b 2 ≤ 2145792063 / 6400000000 * A)
    (θ τ : Fin 3 → ℝ) (hτ : ∀ i, |τ i| ≤ b i) (i : Fin 3) :
    |((cellArm.M θ)⁻¹ *ᵥ τ) i| ≤ A :=
  inv_mulVec_abs_le_core hb₁ hb₂ h₀ h₁ h₂ (by norm_num)
    (by nlinarith [cellArm_yaw_ge θ,
      sq_nonneg (17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))]) τ hτ i

/-- **The acceleration of a torque bounded per joint, for the cell arm, away from the vertical
(MLS eq. (4.19), p. 168, and p. 173 for the inertia matrix; the bound is a design statement, not
from MLS).** As `cellArm_inv_mulVec_abs_le` with the yaw condition `b₀ ≤ (215869/320000) A`, at
every configuration `θ` (radians) whose forearm mass centre is at horizontal distance at least
`29/80` m from the base axis, `17/40 cos θ₁ + 3/10 cos(θ₁ + θ₂) ≥ 29/80`: every joint torque `τ`
with `|τᵢ| ≤ bᵢ` (N m) gives `|(M(θ)⁻¹ τ)ᵢ| ≤ A` for every joint (rad/s²). -/
theorem cellArm_inv_mulVec_abs_le_of_reach {A : ℝ} {b : Fin 3 → ℝ} (hb₁ : 0 ≤ b 1)
    (hb₂ : 0 ≤ b 2) (h₀ : b 0 ≤ 215869 / 320000 * A)
    (h₁ : 519 / 1000 * b 1 + 183 / 160 * b 2 ≤ 2145792063 / 6400000000 * A)
    (h₂ : 183 / 160 * b 1 + 20265977 / 6400000 * b 2 ≤ 2145792063 / 6400000000 * A)
    {θ : Fin 3 → ℝ} (hθ : 29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2))
    (τ : Fin 3 → ℝ) (hτ : ∀ i, |τ i| ≤ b i) (i : Fin 3) :
    |((cellArm.M θ)⁻¹ *ᵥ τ) i| ≤ A :=
  inv_mulVec_abs_le_core hb₁ hb₂ h₀ h₁ h₂ (by norm_num)
    (by nlinarith [cellArm_yaw_ge θ]) τ hτ i

/-- **Tube invariance with right derivatives and the acceleration bound required only near the
reference (a design statement, not from MLS; the law is MLS eq. (4.49), p. 191, along a motion
as on p. 301).** The statement of `tube_invariant_on_accel_right` with `δ < η`, where the bound
`|wᵢ| ≤ ω² δ` for every `w` with `M(s) w = d(s)` (rad/s²) is required only at the instants
`s ∈ (t₀, t₁]` where every joint is within `η` of the reference, `|xᵢ(s) − rᵢ(s)| ≤ η`. The
proof is a first-exit argument: up to and including the first time some joint reaches the
`η`-band the bound holds, so the tube of radius `δ < η` holds, which keeps every joint inside the
band. -/
theorem tube_invariant_on_accel_right_of_near {n : ℕ} {ω δ η t₀ t₁ : ℝ} (hω : 0 < ω)
    (hδη : δ < η) {r r' r'' : ℝ → Fin n → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    {x x' x'' d : ℝ → Fin n → ℝ} {Mt Ct : ℝ → Matrix (Fin n) (Fin n) ℝ} {Nt : ℝ → Fin n → ℝ}
    (hc : ContinuousOn (fun s => (x s, x' s)) (Icc t₀ t₁))
    (hx : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x (x' s) (Ici s) s)
    (hx' : ∀ s ∈ Ioc t₀ t₁, HasDerivWithinAt x' (x'' s) (Ici s) s)
    (hw : ∀ s ∈ Ioc t₀ t₁, (∀ i, |x s i - r s i| ≤ η) →
      ∀ w, Mt s *ᵥ w = d s → ∀ i, |w i| ≤ ω ^ 2 * δ)
    (hE : ∀ s ∈ Ioc t₀ t₁, Mt s *ᵥ x'' s + Ct s *ᵥ x' s + Nt s =
      Control.computedTorqueAlong ((ω ^ 2) • 1) ((2 * ω) • 1) (Mt s) (Ct s) (Nt s) (r s) (r' s)
        (r'' s) (x s) (x' s) + d s)
    (h₀ : InTube ω δ (x t₀) (x' t₀) (r t₀) (r' t₀)) :
    ∀ t ∈ Icc t₀ t₁, InTube ω δ (x t) (x' t) (r t) (r' t) ∧
      ∀ i, |x' t i - r' t i| ≤ 2 * ω * δ := by
  have hxc : ContinuousOn x (Icc t₀ t₁) := continuous_fst.comp_continuousOn hc
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hec : ContinuousOn (fun s => x s - r s) (Icc t₀ t₁) := hxc.sub hrc.continuousOn
  -- the closed band `|xᵢ − rᵢ| ≤ η` on `[t₀, t₁]`
  set K : Set ℝ := Icc t₀ t₁ ∩ (fun s => x s - r s) ⁻¹' (⋂ i, {v : Fin n → ℝ | |v i| ≤ η})
    with hK
  have hKmem : ∀ s, s ∈ K ↔ s ∈ Icc t₀ t₁ ∧ ∀ i, |x s i - r s i| ≤ η := by
    intro s
    simp only [hK, mem_inter_iff, mem_preimage, mem_iInter, mem_ofPred_eq, Pi.sub_apply]
  have hKc : IsClosed K := hec.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const)
  -- first exit: every joint stays within the band on `[t₀, t₁]`
  have hband : ∀ s ∈ Icc t₀ t₁, ∀ i, |x s i - r s i| ≤ η := by
    by_contra hcon
    simp only [not_forall, not_le] at hcon
    obtain ⟨s₁, hs₁, i₁, hi₁⟩ := hcon
    -- the closed set of times in `[t₀, t₁]` where some joint is at or beyond the band
    set S : Set ℝ := Icc t₀ t₁ ∩ (fun s => x s - r s) ⁻¹' (⋃ i, {v : Fin n → ℝ | η ≤ |v i|})
      with hS
    have hmem : ∀ s, s ∈ S ↔ s ∈ Icc t₀ t₁ ∧ ∃ i, η ≤ |x s i - r s i| := by
      intro s
      simp only [hS, mem_inter_iff, mem_preimage, mem_iUnion, mem_ofPred_eq, Pi.sub_apply]
    have hSc : IsClosed S := hec.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_iUnion_of_finite fun i => isClosed_le continuous_const (continuous_apply i).abs)
    have hne : S.Nonempty := ⟨s₁, (hmem s₁).2 ⟨hs₁, i₁, hi₁.le⟩⟩
    have hbdd : BddBelow S := ⟨t₀, fun s hs => ((hmem s).1 hs).1.1⟩
    obtain ⟨hτI, j, hj⟩ := (hmem _).1 (hSc.csInf_mem hne hbdd)
    -- `t₀` is before the first exit: at `t₀` the motion is in the tube of radius `δ < η`
    have hlt : t₀ < sInf S := by
      rcases hτI.1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hj
        linarith [(h₀ j).1]
    -- before the first exit every joint is within the band
    have hbefore : Ico t₀ (sInf S) ⊆ K := by
      intro s hs
      refine (hKmem s).2 ⟨⟨hs.1, hs.2.le.trans hτI.2⟩, fun i => ?_⟩
      by_contra hcon'
      exact notMem_of_lt_csInf hs.2 hbdd
        ((hmem s).2 ⟨⟨hs.1, hs.2.le.trans hτI.2⟩, i, (not_le.mp hcon').le⟩)
    -- at the first exit every joint is still within the band (closure of `[t₀, τ)`)
    have hτK : sInf S ∈ K := by
      have hcl : closure (Ico t₀ (sInf S)) ⊆ K := closure_minimal hbefore hKc
      rw [closure_Ico hlt.ne] at hcl
      exact hcl ⟨hlt.le, le_rfl⟩
    have hsub : ∀ s ∈ Ioc t₀ (sInf S), s ∈ Ioc t₀ t₁ := fun s hs => ⟨hs.1, hs.2.trans hτI.2⟩
    have hnear : ∀ s ∈ Ioc t₀ (sInf S), ∀ i, |x s i - r s i| ≤ η := by
      intro s hs
      rcases hs.2.lt_or_eq with h | h
      · exact ((hKmem s).1 (hbefore ⟨hs.1.le, h⟩)).2
      · rw [h]
        exact ((hKmem _).1 hτK).2
    have htube := tube_invariant_on_accel_right hω hr hr'
      (hc.mono (Icc_subset_Icc_right hτI.2)) (fun s hs => hx s (hsub s hs))
      (fun s hs => hx' s (hsub s hs)) (fun s hs => hw s (hsub s hs) (hnear s hs))
      (fun s hs => hE s (hsub s hs)) h₀ (sInf S) ⟨hlt.le, le_rfl⟩
    linarith [(htube.1 j).1]
  exact tube_invariant_on_accel_right hω hr hr' hc hx hx'
    (fun s hs => hw s hs (hband s (Ioc_subset_Icc_self hs))) hE h₀

/-- **The cell arm follows the move reference at time `t`, with the disturbance torque bounded
per joint and right derivatives (a design statement, not from MLS; computed torque of MLS
eq. (4.49), p. 191, for the robot of p. 303).** `x` has right derivative `v t` and `v` has right
derivative `acc t` at `t` (within `[t, ∞)`); the disturbance torque satisfies `|dᵢ(t)| ≤ bᵢ` for
every joint (N m); and the arm's equations of motion `M ẍ + C ẋ + N = F + d` hold at `t` with
`ẍ = acc t` and the robot's computed torque `F` for the gains `ω² I`, `2ω I` and the reference of
the move from `a` to `g` admitted at `t₀` with duration `T` (radians, seconds). -/
def CellArmFollowsTorqueRightAt (ω T : ℝ) (b : Fin 3 → ℝ) (x v acc d : ℝ → Fin 3 → ℝ)
    (a g : Fin 3 → ℝ) (t₀ t : ℝ) : Prop :=
  HasDerivWithinAt x (v t) (Ici t) t ∧ HasDerivWithinAt v (acc t) (Ici t) t ∧
    (∀ i, |d t i| ≤ b i) ∧
    cellRobot.M (x t) *ᵥ acc t + cellRobot.C (x t) (v t) *ᵥ v t + cellRobot.N (x t) (v t) =
      cellRobot.computedTorque ((ω ^ 2) • 1) ((2 * ω) • 1) (moveRef a g t₀ T)
        (moveRefDeriv a g t₀ T) (moveRefDeriv2 a g t₀ T) t (x t) (v t) + d t

/-- **The torque form of the tracking predicate implies the acceleration form at every
configuration (a design statement, not from MLS; `cellArm_inv_mulVec_abs_le`).** If the per-joint
torque bounds `b` (N m) meet the conditions of `cellArm_inv_mulVec_abs_le` for `A = ω² δ`
(rad/s²), every motion that satisfies `CellArmFollowsTorqueRightAt ω T b` at `t` satisfies
`CellArmFollowsAccelRightAt ω T δ` at `t`. -/
theorem CellArmFollowsTorqueRightAt.accel {ω T δ : ℝ} {b : Fin 3 → ℝ} (hb₁ : 0 ≤ b 1)
    (hb₂ : 0 ≤ b 2) (h₀ : b 0 ≤ 307 / 10000 * (ω ^ 2 * δ))
    (h₁ : 519 / 1000 * b 1 + 183 / 160 * b 2 ≤ 2145792063 / 6400000000 * (ω ^ 2 * δ))
    (h₂ : 183 / 160 * b 1 + 20265977 / 6400000 * b 2 ≤ 2145792063 / 6400000000 * (ω ^ 2 * δ))
    {x v acc d : ℝ → Fin 3 → ℝ} {a g : Fin 3 → ℝ} {t₀ t : ℝ}
    (h : CellArmFollowsTorqueRightAt ω T b x v acc d a g t₀ t) :
    CellArmFollowsAccelRightAt ω T δ x v acc d a g t₀ t :=
  ⟨h.1, h.2.1, cellArm_inv_mulVec_abs_le hb₁ hb₂ h₀ h₁ h₂ (x t) (d t) h.2.2.1, h.2.2.2⟩

/-- If the shoulder and the forearm are both within `π/3` of the horizontal,
`|θ₁| ≤ π/3` and `|θ₁ + θ₂| ≤ π/3` (radians), the forearm's mass centre is at horizontal
distance at least `29/80` m from the base axis. -/
private theorem cellArm_reach_of_abs_le_pi_div_three {θ : Fin 3 → ℝ}
    (h₁ : |θ 1| ≤ Real.pi / 3) (h₁₂ : |θ 1 + θ 2| ≤ Real.pi / 3) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  have hc : ∀ y : ℝ, |y| ≤ Real.pi / 3 → 1 / 2 ≤ Real.cos y := fun y hy => by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hy
  linarith [hc _ h₁, hc _ h₁₂]

end Cell

namespace Cell.Loop

open Set Supervisor

/-- Every configuration within `1/10` rad (each joint) of a point of the segment between two
waypoints linked by the supervisor's link test keeps the forearm's mass centre at horizontal
distance at least `29/80` m from the base axis: such a configuration lies in a cell inflated by
`1/10`, hence in the joint envelope (shoulder at most `51°` in magnitude, shoulder plus elbow at
most `57°` in magnitude). -/
private theorem cell_reach_linked {h T δa va : ℝ} {a g : Waypoint}
    (hag : (openCellParams h T δa va).linked a g) {p : Fin 3 → ℝ}
    (hp : p ∈ segment ℝ (DegPoint.toRad a) (DegPoint.toRad g)) {θ : Fin 3 → ℝ}
    (hθ : ∀ i, |θ i - p i| ≤ 1 / 10) :
    29 / 80 ≤ 17 / 40 * Real.cos (θ 1) + 3 / 10 * Real.cos (θ 1 + θ 2) := by
  obtain ⟨B, hB, ha, hb⟩ := sceneLinked_of_linked_eq_true hag
  have hpB : p ∈ B.radSet 0 :=
    (B.convex_radSet 0).segment_subset (DegBox.toRad_mem_radSet ha) (DegBox.toRad_mem_radSet hb) hp
  have hθE := radSet_subset_jointEnvelope B hB (DegBox.mem_radSet_of_abs_sub_le hpB hθ)
  have hπ := Real.pi_pos
  obtain ⟨h11, h12⟩ := hθE 1
  obtain ⟨h21, h22⟩ := hθE 2
  simp [DegPoint.toRad, degToRad, jointEnvelope] at h11 h12 h21 h22
  apply cellArm_reach_of_abs_le_pi_div_three
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- **The loop's move corollary for the cell arm with the disturbance torque bounded per joint
and right derivatives (a design statement, not from MLS; computed torque of MLS eq. (4.49),
p. 191, for the robot of p. 303).** For the loop data `openCellParams h T δa va` with `T > 0`,
`ω > 0`, `δ < 1/10` (rad), `(x, v)` continuous on `[0, ∞)` and per-joint torque bounds `b`
(N m) with `b₁, b₂ ≥ 0`, `b₀ ≤ (215869/320000) ω² δ` and the two conditions of
`cellArm_inv_mulVec_abs_le` at the straight elbow for `A = ω² δ`, the arm's motion satisfies
`Loop.MoveCorollary` for the quintic reference and the tracking predicate
`CellArmFollowsTorqueRightAt`. The yaw bound uses the cells: while every joint is within `1/10`
rad of the reference of a linked move, the forearm's reach is at least `29/80` m. -/
theorem cellArm_moveCorollary_torque_right (h T δa va : ℝ) (hT : 0 < T) {ω δ : ℝ}
    (hω : 0 < ω) (hδ : δ < 1 / 10) {b : Fin 3 → ℝ} (hb₁ : 0 ≤ b 1) (hb₂ : 0 ≤ b 2)
    (h₀ : b 0 ≤ 215869 / 320000 * (ω ^ 2 * δ))
    (h₁ : 519 / 1000 * b 1 + 183 / 160 * b 2 ≤ 2145792063 / 6400000000 * (ω ^ 2 * δ))
    (h₂ : 183 / 160 * b 1 + 20265977 / 6400000 * b 2 ≤ 2145792063 / 6400000000 * (ω ^ 2 * δ))
    {x v acc d : ℝ → Fin 3 → ℝ} (hc : ContinuousOn (fun s => (x s, v s)) (Ici 0)) :
    MoveCorollary (openCellParams h T δa va) (quinticMoveRef (n := 3) hT) δ ω
      (fun a g t₀ t => CellArmFollowsTorqueRightAt ω T b x v acc d (DegPoint.toRad a)
        (DegPoint.toRad g) t₀ t) x v := by
  intro a g hag t₀ t₁ ht₀ _ hf hin t ht
  have hin' : Cell.InTube ω δ (x t₀) (v t₀)
      (moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ T t₀)
      (moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ T t₀) := by
    rw [moveRef_of_le hT le_rfl, moveRefDeriv_of_le hT le_rfl]
    exact hin
  have htube := tube_invariant_on_accel_right_of_near (η := 1 / 10) hω hδ
    (hasDerivAt_moveRef (DegPoint.toRad a) (DegPoint.toRad g) t₀ T)
    (hasDerivAt_moveRefDeriv (DegPoint.toRad a) (DegPoint.toRad g) t₀ T)
    (Mt := fun s => cellRobot.M (x s)) (Ct := fun s => cellRobot.C (x s) (v s))
    (Nt := fun s => cellRobot.N (x s) (v s)) (hc.mono fun s hs => ht₀.trans hs.1)
    (fun s hs => (hf s hs).1) (fun s hs => (hf s hs).2.1) (fun s hs hnear w hMw i => ?_)
    (fun s hs => (hf s hs).2.2.2) hin'
  · exact (htube t ht).1
  · have hreach := cell_reach_linked hag (moveRef_mem_segment _ _ _ _ _) hnear
    have hw := Control.PosDef.inv_mulVec_mulVec (cellArm_M_posDef (x s)) w
    change (cellRobot.M (x s))⁻¹ *ᵥ (cellRobot.M (x s) *ᵥ w) = w at hw
    rw [hMw] at hw
    rw [← hw]
    exact cellArm_inv_mulVec_abs_le_of_reach hb₁ hb₂ h₀ h₁ h₂ hreach (d s) (hf s hs).2.2.1 i

/-- **The assured cell with the disturbance torque bounded per joint, with the supervisor's
contract as its premise.** The statement of `cell_assured_contract_right` with the plant
hypothesis on each period stated with per-joint torque bounds `b` (N m) instead of the
acceleration bound: `0 < h`, `0 < T`, `⌈T/h⌉ ≤ 25`, `0 < ω`, `δ ≤ min δ_a (1/20)`,
`2 ω δ ≤ v_a` (seconds, radians, radians per second); `b₁, b₂ ≥ 0`, `b₀ ≤ (215869/320000) ω² δ`,
`(519/1000) b₁ + (183/160) b₂ ≤ (2145792063/6400000000) ω² δ` and
`(183/160) b₁ + (20265977/6400000) b₂ ≤ (2145792063/6400000000) ω² δ`; on every period the arm
obeys its equations of motion with the computed torque tracking the quintic reference of the last
admitted move, with right derivatives, and `|dᵢ(t)| ≤ bᵢ` for every joint (`htrack`,
`CellArmFollowsTorqueRightAt`). The conclusions are those of `cell_assured_contract_right`. A
design statement, not from MLS. -/
theorem cell_assured_contract_torque_right {h T δa va ω δ : ℝ} {b : Fin 3 → ℝ} (hh : 0 < h)
    (hT : 0 < T) (hN : ⌈T / h⌉₊ ≤ 25) (hω : 0 < ω) (hδa : δ ≤ δa) (hva : 2 * ω * δ ≤ va)
    (hδ : δ ≤ 1 / 20) (hb₁ : 0 ≤ b 1) (hb₂ : 0 ≤ b 2)
    (h₀ : b 0 ≤ 215869 / 320000 * (ω ^ 2 * δ))
    (h₁ : 519 / 1000 * b 1 + 183 / 160 * b 2 ≤ 2145792063 / 6400000000 * (ω ^ 2 * δ))
    (h₂ : 183 / 160 * b 1 + 20265977 / 6400000 * b 2 ≤ 2145792063 / 6400000000 * (ω ^ 2 * δ))
    (hsup : Supervisor.Contract Instances.params)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams h T δa va) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * h) ((k + 1) * h),
      CellArmFollowsTorqueRightAt ω T b x v acc d (DegPoint.toRad (c (k + 1)).src)
        (DegPoint.toRad (c (k + 1)).goal) ((c (k + 1)).start * h) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube δ ω (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ k, run Instances.params (State.init Instances.params.home) (actsUpTo acts k) =
      some (c k).sup) ∧
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 1)).sup.commanded = [(c (k₀ + 1)).goal] ∧
      (∀ j, j < ⌈T / h⌉₊ → (c (k₀ + 1 + j)).sup.busy = true) ∧
      (c (k₀ + ⌈T / h⌉₊ + 1)).sup.busy = false ∧
      (c (k₀ + ⌈T / h⌉₊ + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      (c k).sup.commanded = [(c k).goal] ∧ (c (k + 1)).sup.current = (c k).goal ∧
      InTube δ ω (DegPoint.toRad (c k).goal) 0 (x (k * h)) (v (k * h)) ∧
      dist (sceneTool (x (k * h))) (sceneTool (DegPoint.toRad (c k).goal)) ≤ 73 / 50 * δ) := by
  have H := cell_open_hyps hh hT hN hω.le hδa hva hrun htrack
    (cellArm_moveCorollary_torque_right h T δa va hT hω (by linarith) hb₁ hb₂ h₀ h₁ h₂ hcont) h0
  have hc := hrun.loopContract hsup (fun _ _ hab => hab)
  obtain ⟨hclear, hfault, hfin, htool, htube⟩ :=
    H.assured hc (openCellParams_certify h T δa va) hδ sceneTool_lipschitz
  refine ⟨hrun.run_eq_apply, hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hfin k₀ hidle hbusy
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := htube k hbusy hidle
    exact ⟨hrun.commanded_eq_apply _ hbusy, h1, h2, htool k hbusy hidle⟩

/-- **The assured cell at the design point with the disturbance torque bounded per joint, with
the supervisor's contract as its premise.** With `h = 1/10` s, `T = 2` s, `ω = 80` rad/s,
`δ = δ_a = 3/100` rad and `v_a = 24/5` rad/s, for every run of the supervisor that meets the
contract `Supervisor.Contract Instances.params` (`hsup`), under the hypotheses of
`cell_assured_contract_design_tight_right` with the plant hypothesis on each period stated with
the disturbance torque bounded per joint, `|d₀(t)| ≤ 129`, `|d₁(t)| ≤ 149/10` and
`|d₂(t)| ≤ 149/10` N m (`CellArmFollowsTorqueRightAt`): the links keep `9/100` m from every
obstacle at every `t ≥ 0`, the supervisor never faults and its age stays below 25, a move admitted
at boundary `k₀` is finished at boundary `k₀ + 20`, and at each finish the tool is within
`219/5000` m of the goal's tool position. The other hypotheses are about the harness, that at
each boundary the actions sent are queue actions followed by the policy's action on the exact
sample, each accepted by the supervisor (`hrun`), and that the arm starts in the tube around home
at rest (`h0`); about the harness and the plant, that on each period the arm obeys its equations
of motion with the computed torque tracking the quintic reference of the last admitted move, with
the acceleration from the right (`htrack`); about the plant, that `(x, v)` is continuous on
`[0, ∞)` (`hcont`). A design statement, not from MLS. -/
theorem cell_assured_contract_design_torque_right (hsup : Supervisor.Contract Instances.params)
    {x v acc d : ℝ → Fin 3 → ℝ} {c : ℕ → CellState} {acts : ℕ → List Action}
    (hrun : IsCellRun (openCellParams (1 / 10) 2 (3 / 100) (24 / 5)) Instances.params x v c acts)
    (htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsTorqueRightAt 80 2 ![129, 149 / 10, 149 / 10] x v acc d
        (DegPoint.toRad (c (k + 1)).src) (DegPoint.toRad (c (k + 1)).goal)
        ((c (k + 1)).start * (1 / 10)) t)
    (hcont : ContinuousOn (fun s => (x s, v s)) (Ici 0))
    (h0 : InTube (3 / 100) 80 (DegPoint.toRad Instances.params.home) 0 (x 0) (v 0)) :
    (∀ t, 0 ≤ t → sceneClear (x t)) ∧
    (∀ k, (c k).sup.faulted = false ∧ (c k).sup.age < 25) ∧
    (∀ k₀, (c k₀).sup.busy = false → (c (k₀ + 1)).sup.busy = true →
      (c (k₀ + 20 + 1)).sup.busy = false ∧ (c (k₀ + 20 + 1)).sup.current = (c (k₀ + 1)).goal) ∧
    (∀ k, (c k).sup.busy = true → (c (k + 1)).sup.busy = false →
      dist (sceneTool (x (k * (1 / 10)))) (sceneTool (DegPoint.toRad (c k).goal)) ≤
        219 / 5000) := by
  obtain ⟨-, hclear, hfault, hfin, htool⟩ :=
    cell_assured_contract_torque_right (by norm_num) (by norm_num) (by rw [design_steps]; norm_num)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsup hrun htrack hcont h0
  refine ⟨hclear, hfault, fun k₀ hidle hbusy => ?_, fun k hbusy hidle => ?_⟩
  · obtain ⟨-, -, h2, h3⟩ := hfin k₀ hidle hbusy
    rw [design_steps] at h2 h3
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, -, h4⟩ := htool k hbusy hidle
    linarith

/-- **A moving arm meets the hypotheses of the torque form.** The demonstration run (the move
from home to the waypoint above the pick slot, tracked exactly with zero disturbance torque)
meets every hypothesis of `cell_assured_contract_design_torque_right`, with the supervisor's
contract given by the hand-written proof `Supervisor.contract_of_design`. So the links keep
`9/100` m from every obstacle at every `t ≥ 0` (s), the supervisor never faults, and at the
finish the tool is within `219/5000` m of the goal's tool position. A design statement, not from
MLS. -/
theorem demo_assured_contract_torque_right :
    (∀ t, 0 ≤ t → sceneClear (demoMotion t)) ∧
    (∀ k, (demoState k).sup.faulted = false ∧ (demoState k).sup.age < 25) ∧
    (∀ k, (demoState k).sup.busy = true → (demoState (k + 1)).sup.busy = false →
      dist (sceneTool (demoMotion (k * (1 / 10))))
        (sceneTool (DegPoint.toRad (demoState k).goal)) ≤ 219 / 5000) := by
  have htrack : ∀ k : ℕ, ∀ t ∈ Ioc ((k : ℝ) * (1 / 10)) ((k + 1) * (1 / 10)),
      CellArmFollowsTorqueRightAt 80 2 ![129, 149 / 10, 149 / 10] demoMotion demoVel demoAcc 0
        (DegPoint.toRad (demoState (k + 1)).src) (DegPoint.toRad (demoState (k + 1)).goal)
        ((demoState (k + 1)).start * (1 / 10)) t := by
    intro k t _
    obtain ⟨h1, h2, h3⟩ := demoState_succ_move k
    rw [h1, h2, h3]
    have h := demoMotion_follows_of (δ := 3 / 100) (by norm_num) t
    refine ⟨h.1.hasDerivWithinAt, h.2.1.hasDerivWithinAt, fun i => ?_, by simpa using h.2.2.2⟩
    fin_cases i <;> norm_num
  obtain ⟨hclear, hfault, -, htool⟩ := cell_assured_contract_design_torque_right
    (Supervisor.contract_of_design Instances.params)
    (demo_isCellRun_of (by norm_num) (by norm_num)).openCellParams_of_cellParams htrack
    demo_continuousOn (demo_inTube_zero (by norm_num))
  exact ⟨hclear, hfault, htool⟩

end Cell.Loop
end RoboLean
