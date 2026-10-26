import RoboLean.Dynamics.GraspChart
import RoboLean.Geometry.EulerAngles

/-!
# A chart of the object pose on all of `SE(3)`: position and ZYZ Euler angles (MLS §6.2, (6.18))

MLS Chapter 6, §2.1, printed p. 277 ("Letting `x ∈ ℝ⁶` be a local parameterization for
`x_o ∈ SE(3)`"), eq. (6.18), p. 277, Exercise 4(b), p. 314, and the ZYZ Euler angles of Chapter 2,
eqs. (2.19)–(2.20), printed pp. 31–32.

**What MLS states.** The composite dynamics (6.18)–(6.22) are written in a local parameterization
`x ∈ ℝ⁶` of the object pose (p. 277); MLS names no particular chart. ZYZ Euler angles are "an
example of a local parameterization of `SO(3)`", the rotation `R = R_z(α) R_y(β) R_z(γ)` of (2.19)
is recovered by (2.20) "when `sin β ≠ 0`", and "singularities in the parameterization ... occur at
`R = I`" (p. 32). Exercise 4(b) (p. 314) asks for the body-velocity Jacobian
`J(x) = [(φ⁻¹ ∂φ/∂x₁)^∨ ⋯ (φ⁻¹ ∂φ/∂x₆)^∨]` of a local parameterization `x_o = φ(x)`.

**Formalized.**

* The chart family `eulerChart R₀`: the six coordinates `ξ = (p, α, β, γ)` give the pose with
  position `p ∈ ℝ³` and orientation `R₀ R_z(α) R_y(β) R_z(γ)`, for a fixed rotation `R₀`; with
  `R₀ = I` it is the position plus the ZYZ Euler angles of (2.19).
* Its body-velocity Jacobian `eulerChartJacobian R₀ ξ = [[Rᵀ, 0], [0, E(β, γ)]]`, where the columns
  of `E(β, γ)` are `(−sin β cos γ, sin β sin γ, cos β)`, `(sin γ, cos γ, 0)` and `(0, 0, 1)` (the
  body angular velocity is `E(β, γ)(α̇, β̇, γ̇)`), discharges the hypothesis structure
  `IsBodyJacobian` along every motion, with no restriction on the coordinates
  (`isBodyJacobian_eulerChart`).
* The domain: the Jacobian is onto and one-to-one exactly off the singular set `sin β = 0`
  (`eulerChartJacobian_surjective`, `eulerChartJacobian_injective`,
  `not_injective_eulerChartJacobian`).
* Coverage: every pose is the value of a chart of the family at a point with `sin β ≠ 0`
  (`exists_eulerChart_eq`); on the open set of poses `g` with `zyzRadial(R₀⁻¹ R_g) > 0`
  (`isOpen_eulerDomain`) the coordinates of (2.20) applied to `R₀⁻¹ R_g` are an inverse of the chart
  that lands in `sin β > 0` (`eulerChart_eulerCoordinates`, `sin_eulerCoordinates_pos`), and that
  open set contains any given pose for a suitable `R₀` (`mem_eulerDomain_eulerCenter`).
* Consequences with no chart hypothesis: (6.18) from (5.15) along every motion in Euler coordinates
  (`graspingConstraint_eulerChart_iff`, `pfaffianAt_handPfaffian_eulerChart_iff`), and Exercise 4(b)
  with its converse and `M̄ > 0` off the singular set (`newtonEulerEquation_eulerChart_iff`,
  `chartMass_eulerChart_posDef`).

**Added hypothesis and singular set.** Wherever invertibility of the chart Jacobian is used the
hypothesis is `sin β ≠ 0`, `β` the middle Euler angle; the singular set `sin β = 0` contains every
coordinate value of the pose with `R₀⁻¹ R = I` (MLS p. 32: the identity is singular for ZYZ angles),
which is why a family of charts indexed by `R₀` is used. Coordinates are `Fin 6`, position first
(`finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6`), angles in the order `(α, β, γ)`; twist rows in the order
`(v, ω)`. Nothing here concerns a physical object.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Composite

/-! ### The chart -/

/-- **The position coordinates of the pose chart (MLS p. 277, a local parameterization `x ∈ ℝ⁶` of
`x_o ∈ SE(3)`):** the first three of the six coordinates, `p = (ξ₀, ξ₁, ξ₂)`. -/
def eulerPosition (ξ : Fin 6 → ℝ) : Fin 3 → ℝ :=
  fun i => ξ (finSumFinEquiv (m := 3) (n := 3) (Sum.inl i))

/-- **The Euler-angle coordinates of the pose chart (MLS eq. (2.19), p. 32):** the last three of the
six coordinates, `(α, β, γ) = (ξ₃, ξ₄, ξ₅)`. -/
def eulerAngles (ξ : Fin 6 → ℝ) : Fin 3 → ℝ :=
  fun i => ξ (finSumFinEquiv (m := 3) (n := 3) (Sum.inr i))

/-- **The orientation of the pose chart centered at `R₀` (MLS eq. (2.19), p. 32):**
`R₀ R_z(α) R_y(β) R_z(γ)` for the Euler angles `(α, β, γ)` of `ξ`. -/
def eulerRotation (R₀ : Rotation) (ξ : Fin 6 → ℝ) : Rotation :=
  R₀ * Rotation.zyz (eulerAngles ξ 0) (eulerAngles ξ 1) (eulerAngles ξ 2)

/-- **The pose chart centered at `R₀`: position plus ZYZ Euler angles (MLS p. 277, a local
parameterization of `SE(3)`; eq. (2.19), p. 32):**
`ξ = (p, α, β, γ) ↦ (R₀ R_z(α) R_y(β) R_z(γ), p)`. With `R₀ = I` it is the plain ZYZ chart. -/
def eulerChart (R₀ : Rotation) (ξ : Fin 6 → ℝ) : RigidTransform :=
  ⟨eulerRotation R₀ ξ, WithLp.toLp 2 (eulerPosition ξ)⟩

/-- **The angular part of the body-velocity Jacobian of ZYZ Euler angles (MLS Exercise 4(b), p. 314,
for the chart of eq. (2.19)):** the body angular velocity of `R_z(α) R_y(β) R_z(γ)` is
`E(β, γ) (α̇, β̇, γ̇)` with the columns `(−sin β cos γ, sin β sin γ, cos β)`, `(sin γ, cos γ, 0)`,
`(0, 0, 1)`. -/
def eulerAngularJacobian (β γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-Real.sin β * Real.cos γ, Real.sin γ, 0;
    Real.sin β * Real.sin γ, Real.cos γ, 0;
    Real.cos β, 0, 1]

/-- **The body-velocity Jacobian of the pose chart (MLS Exercise 4(b), p. 314:
`J(x) = [(φ⁻¹ ∂φ/∂x₁)^∨ ⋯ (φ⁻¹ ∂φ/∂x₆)^∨]`):** `[[Rᵀ, 0], [0, E(β, γ)]]` with `R` the chart's
orientation, rows in twist order `(v, ω)`, columns the six coordinates (position first). -/
def eulerChartJacobian (R₀ : Rotation) (ξ : Fin 6 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 6) ℝ :=
  (Matrix.fromBlocks (eulerRotation R₀ ξ).valᵀ 0 0
    (eulerAngularJacobian (eulerAngles ξ 1) (eulerAngles ξ 2))).submatrix id
    (finSumFinEquiv (m := 3) (n := 3)).symm

/-- The chart Jacobian acts as the block matrix `[[Rᵀ, 0], [0, E(β, γ)]]` on the coordinates
relabeled by `Fin 3 ⊕ Fin 3` (MLS Exercise 4(b), p. 314). -/
private theorem eulerChartJacobian_mulVec (R₀ : Rotation) (ξ v : Fin 6 → ℝ) :
    eulerChartJacobian R₀ ξ *ᵥ v = Matrix.fromBlocks (eulerRotation R₀ ξ).valᵀ 0 0
      (eulerAngularJacobian (eulerAngles ξ 1) (eulerAngles ξ 2)) *ᵥ
        (v ∘ finSumFinEquiv (m := 3) (n := 3)) := by
  rw [eulerChartJacobian, Matrix.submatrix_mulVec_equiv]
  rfl

/-- A pose curve has the derivative `[Ṙ ṗ; 0 0]` when its rotation and translation have the
derivatives `Ṙ` and `ṗ` (MLS eq. (2.60), p. 55). -/
private theorem hasDerivAt_toHomogeneous_blocks {g : ℝ → RigidTransform}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {v : Fin 3 → ℝ} {t : ℝ}
    (hR : HasDerivAt (fun s => (g s).rotation.val) A t)
    (hp : ∀ i, HasDerivAt (fun s => (g s).translation i) (v i) t) :
    HasDerivAt (fun s => (g s).toHomogeneous)
      (Matrix.fromBlocks A (Matrix.of fun i _ => v i) 0 0) t := by
  refine hasDerivAt_pi.mpr fun r => hasDerivAt_pi.mpr fun q => ?_
  rcases r with i | i <;> rcases q with j | j
  · simpa [RigidTransform.toHomogeneous] using hasDerivAt_pi.mp (hasDerivAt_pi.mp hR i) j
  · simpa [RigidTransform.toHomogeneous] using hp i
  · simpa [RigidTransform.toHomogeneous] using hasDerivAt_const t (0 : ℝ)
  · simpa [RigidTransform.toHomogeneous] using
      hasDerivAt_const t ((1 : Matrix (Fin 1) (Fin 1) ℝ) i j)

/-- A homogeneous-matrix curve has at most one derivative, entry by entry (MLS eq. (2.60), p. 55).
-/
private theorem homogeneous_hasDerivAt_unique {f : ℝ → HomogeneousMatrix}
    {D D' : HomogeneousMatrix} {t : ℝ} (h : HasDerivAt f D t) (h' : HasDerivAt f D' t) :
    D = D' := by
  ext r c
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp h r) c).unique
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp h' r) c)

open scoped Matrix.Norms.Operator in
/-- The derivative of `R₀ R_z(α) R_y(β) R_z(γ)` along angle curves, by the product rule (MLS eq.
(2.19), p. 32, with `d/dt e^{ω̂ θ} = θ̇ ω̂ e^{ω̂ θ}`). -/
private theorem hasDerivAt_eulerRotation_val (R₀ : Rotation) {x : ℝ → Fin 6 → ℝ}
    {x' : Fin 6 → ℝ} {t : ℝ} (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => (eulerRotation R₀ (x s)).val)
      (R₀.val * ((eulerAngles x' 0 • (Vec3.hat Rotation.zAxis *
          (Rotation.zRotation (eulerAngles (x t) 0)).val) *
          (Rotation.yRotation (eulerAngles (x t) 1)).val +
        (Rotation.zRotation (eulerAngles (x t) 0)).val * (eulerAngles x' 1 •
          (Vec3.hat Rotation.yAxis * (Rotation.yRotation (eulerAngles (x t) 1)).val))) *
          (Rotation.zRotation (eulerAngles (x t) 2)).val +
        (Rotation.zRotation (eulerAngles (x t) 0)).val *
          (Rotation.yRotation (eulerAngles (x t) 1)).val * (eulerAngles x' 2 •
          (Vec3.hat Rotation.zAxis * (Rotation.zRotation (eulerAngles (x t) 2)).val)))) t := by
  have hc := hasDerivAt_pi.mp hx
  have h := (((Rotation.hasDerivAt_exp_val_comp Rotation.zAxis
    (hc (finSumFinEquiv (m := 3) (n := 3) (Sum.inr 0)))).mul
    (Rotation.hasDerivAt_exp_val_comp Rotation.yAxis
    (hc (finSumFinEquiv (m := 3) (n := 3) (Sum.inr 1))))).mul
    (Rotation.hasDerivAt_exp_val_comp Rotation.zAxis
    (hc (finSumFinEquiv (m := 3) (n := 3) (Sum.inr 2))))).const_mul R₀.val
  simp only [Rotation.exp_yAxis] at h
  exact h

/-- `Rᵀ (R X) = X` for a rotation `R` (MLS eq. (2.1), p. 23). -/
private theorem transpose_mul_mul_cancel (R : Rotation) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    R.valᵀ * (R.val * X) = X := by
  rw [← Matrix.mul_assoc, R.transpose_mul, Matrix.one_mul]

/-- The body angular velocity of `R₀ A B C` with `Ȧ = a' ẑ^ A`, `Ḃ = b' ŷ^ B`, `Ċ = c' ẑ^ C`:
`Rᵀ Ṙ = (a' (ABC)⁻¹ẑ + b' (BC)⁻¹ŷ + c' C⁻¹ẑ)^` (MLS eq. (2.49), p. 52, for the chart of eq. (2.19),
p. 32). -/
private theorem transpose_mul_eulerDeriv (R₀ A B C : Rotation) (a' b' c' : ℝ) :
    (R₀ * (A * B * C)).valᵀ * (R₀.val * ((a' • (Vec3.hat Rotation.zAxis * A.val) * B.val +
        A.val * (b' • (Vec3.hat Rotation.yAxis * B.val))) * C.val +
        A.val * B.val * (c' • (Vec3.hat Rotation.zAxis * C.val)))) =
      Vec3.hat (a' • (A * B * C)⁻¹.act Rotation.zAxis + b' • (B * C)⁻¹.act Rotation.yAxis +
        c' • C⁻¹.act Rotation.zAxis) := by
  simp [Vec3.hat_act, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, transpose_mul_mul_cancel]

/-- **MLS Exercise 4(b), p. 314, for the pose chart:** along every motion `ξ` of the six coordinates
with velocity `ξ'`, the pose curve `s ↦ (R₀ R_z(α) R_y(β) R_z(γ), p)` has a derivative and its body
velocity (MLS eq. (2.60)) is `(Rᵀ ṗ, E(β, γ)(α̇, β̇, γ̇))`. No restriction on the coordinates is
needed. -/
theorem isBodyJacobian_eulerChart (R₀ : Rotation) :
    IsBodyJacobian (eulerChart R₀) (eulerChartJacobian R₀) := by
  have hder : ∀ {x : ℝ → Fin 6 → ℝ} {x' : Fin 6 → ℝ} {t : ℝ} (hx : HasDerivAt x x' t), _ :=
    fun {x x' t} hx => hasDerivAt_toHomogeneous_blocks (g := fun s => eulerChart R₀ (x s))
      (hasDerivAt_eulerRotation_val R₀ hx)
      (fun i => hasDerivAt_pi.mp hx (finSumFinEquiv (m := 3) (n := 3) (Sum.inl i)))
  refine ⟨fun hx => ⟨_, hder hx⟩, fun {x x' t D} hx hD => ?_⟩
  have hDD := homogeneous_hasDerivAt_unique hD (hder hx)
  subst hDD
  funext r
  rcases r with i | i
  · simp [Twist.coordinates, Rotation.act_apply, RigidTransform.translationDerivative,
      eulerChartJacobian_mulVec, Matrix.fromBlocks_mulVec, eulerChart, Function.comp_def]
  · have hhat := Rotation.hat_bodyAngularVelocity (RigidTransform.hasDerivAt_rotation hD)
    have hω := congrArg Vec3.vee (hhat.trans (transpose_mul_eulerDeriv R₀
      (Rotation.zRotation (eulerAngles (x t) 0)) (Rotation.yRotation (eulerAngles (x t) 1))
      (Rotation.zRotation (eulerAngles (x t) 2)) (eulerAngles x' 0) (eulerAngles x' 1)
      (eulerAngles x' 2)))
    rw [Vec3.vee_hat, Vec3.vee_hat] at hω
    have hω' : (RigidTransform.bodyVelocity (fun s => eulerChart R₀ (x s)) _ t hD).angular = _ :=
      hω
    rw [Twist.coordinates, Sum.elim_inr, hω', eulerChartJacobian_mulVec,
      Matrix.fromBlocks_mulVec]
    fin_cases i <;>
      simp [Rotation.act_apply, eulerAngularJacobian, Rotation.zRotation_matrix,
        Rotation.zMatrix, Rotation.yMatrix, Rotation.zAxis, Rotation.yAxis, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, Function.comp_def, eulerAngles] <;>
      ring

/-! ### The domain and the singular set (MLS p. 32) -/

/-- The determinant of the angular block is `det E(β, γ) = −sin β` (MLS p. 32; Exercise 4(b), p.
314). -/
private theorem det_eulerAngularJacobian (β γ : ℝ) :
    (eulerAngularJacobian β γ).det = -Real.sin β := by
  rw [Matrix.det_fin_three]
  simp [eulerAngularJacobian]
  linear_combination (-Real.sin β) * Real.sin_sq_add_cos_sq γ

/-- The block matrix `[[Rᵀ, 0], [0, E(β, γ)]]` has determinant `−sin β` (MLS p. 32; Exercise 4(b),
p. 314). -/
private theorem det_eulerBlocks (R₀ : Rotation) (ξ : Fin 6 → ℝ) :
    (Matrix.fromBlocks (eulerRotation R₀ ξ).valᵀ 0 0
      (eulerAngularJacobian (eulerAngles ξ 1) (eulerAngles ξ 2))).det =
      -Real.sin (eulerAngles ξ 1) := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, Rotation.det_eq_one,
    det_eulerAngularJacobian, one_mul]

/-- Off `sin β = 0` the block matrix `[[Rᵀ, 0], [0, E(β, γ)]]` is invertible (MLS p. 32; Exercise
4(b), p. 314). -/
private theorem isUnit_eulerBlocks (R₀ : Rotation) {ξ : Fin 6 → ℝ}
    (hβ : Real.sin (eulerAngles ξ 1) ≠ 0) :
    IsUnit (Matrix.fromBlocks (eulerRotation R₀ ξ).valᵀ 0 0
      (eulerAngularJacobian (eulerAngles ξ 1) (eulerAngles ξ 2))) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_eulerBlocks]
  exact (neg_ne_zero.mpr hβ).isUnit

/-- **Off the singular set the chart Jacobian is onto (MLS p. 32, "when `sin β ≠ 0`"; Exercise 4(b),
p. 314, "nonsingular").** -/
theorem eulerChartJacobian_surjective (R₀ : Rotation) {ξ : Fin 6 → ℝ}
    (hβ : Real.sin (eulerAngles ξ 1) ≠ 0) :
    Function.Surjective (eulerChartJacobian R₀ ξ).mulVec := by
  intro w
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr (isUnit_eulerBlocks R₀ hβ) w
  refine ⟨u ∘ (finSumFinEquiv (m := 3) (n := 3)).symm, ?_⟩
  rw [eulerChartJacobian_mulVec, Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id, hu]

/-- **Off the singular set the chart Jacobian is one-to-one (MLS p. 32; Exercise 4(b), p. 314).** -/
theorem eulerChartJacobian_injective (R₀ : Rotation) {ξ : Fin 6 → ℝ}
    (hβ : Real.sin (eulerAngles ξ 1) ≠ 0) :
    Function.Injective (eulerChartJacobian R₀ ξ).mulVec := by
  intro v w h
  have h' := Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_eulerBlocks R₀ hβ)
    (by simpa only [eulerChartJacobian_mulVec] using h)
  exact (finSumFinEquiv (m := 3) (n := 3)).surjective.injective_comp_right h'

/-- **On the singular set the chart Jacobian is not one-to-one (MLS p. 32, "singularities in the
parameterization").** For `sin β = 0` the rates `(α̇, γ̇) = (1, −cos β)` give no body velocity. -/
theorem not_injective_eulerChartJacobian (R₀ : Rotation) {ξ : Fin 6 → ℝ}
    (hβ : Real.sin (eulerAngles ξ 1) = 0) :
    ¬ Function.Injective (eulerChartJacobian R₀ ξ).mulVec := by
  intro hinj
  let v : Fin 6 → ℝ := fun j => Sum.elim 0 ![1, 0, -Real.cos (eulerAngles ξ 1)]
    ((finSumFinEquiv (m := 3) (n := 3)).symm j)
  have hv : eulerChartJacobian R₀ ξ *ᵥ v = eulerChartJacobian R₀ ξ *ᵥ 0 := by
    rw [Matrix.mulVec_zero, eulerChartJacobian_mulVec, Matrix.fromBlocks_mulVec]
    funext r
    rcases r with i | i
    · simp [v, Function.comp_def, Matrix.mulVec, dotProduct]
    · fin_cases i <;> simp [v, Function.comp_def, eulerAngularJacobian, hβ]
  have h0 := congrFun (hinj hv) (finSumFinEquiv (m := 3) (n := 3) (Sum.inr 0))
  simp [v] at h0

/-! ### Coverage of `SE(3)` by the chart family -/

/-- **The coordinates of a pose in the chart centered at `R₀` (MLS eq. (2.20), p. 32):** the
position of `g` and the Euler angles of (2.20) of the rotation `R₀⁻¹ R_g`. -/
def eulerCoordinates (R₀ : Rotation) (g : RigidTransform) : Fin 6 → ℝ :=
  fun j => Sum.elim (fun i => g.translation i)
    (fun i => ![Rotation.zyzAlpha (R₀⁻¹ * g.rotation), Rotation.zyzBeta (R₀⁻¹ * g.rotation),
      Rotation.zyzGamma (R₀⁻¹ * g.rotation)] i)
    ((finSumFinEquiv (m := 3) (n := 3)).symm j)

/-- The chart at the coordinates assembled from a position `p` and Euler angles `(α, β, γ)` is
`(R₀ R_z(α) R_y(β) R_z(γ), p)` (MLS eq. (2.19), p. 32). -/
private theorem eulerChart_sumElim (R₀ : Rotation) (p : Vec3) (α β γ : ℝ) :
    eulerChart R₀ (fun j => Sum.elim (fun i => p i) (fun i => ![α, β, γ] i)
      ((finSumFinEquiv (m := 3) (n := 3)).symm j)) = ⟨R₀ * Rotation.zyz α β γ, p⟩ := by
  have ha : eulerAngles (fun j => Sum.elim (fun i => p i) (fun i => ![α, β, γ] i)
      ((finSumFinEquiv (m := 3) (n := 3)).symm j)) = ![α, β, γ] := by
    funext i
    simp [eulerAngles]
  have hp : eulerPosition (fun j => Sum.elim (fun i => p i) (fun i => ![α, β, γ] i)
      ((finSumFinEquiv (m := 3) (n := 3)).symm j)) = WithLp.ofLp p := by
    funext i
    simp [eulerPosition]
  rw [eulerChart, eulerRotation, ha, hp]
  rfl

/-- The middle Euler angle of the assembled coordinates is `β` (MLS eq. (2.19), p. 32). -/
private theorem eulerAngles_sumElim_one (p : Vec3) (α β γ : ℝ) :
    eulerAngles (fun j => Sum.elim (fun i => p i) (fun i => ![α, β, γ] i)
      ((finSumFinEquiv (m := 3) (n := 3)).symm j)) 1 = β := by
  simp [eulerAngles]

/-- **MLS eq. (2.20), p. 32, as a local inverse of the pose chart:** where `zyzRadial(R₀⁻¹ R_g) > 0`
(MLS's `sin β ≠ 0` branch, `sin β > 0`), the chart centered at `R₀` maps the coordinates of `g` back
to `g`. -/
theorem eulerChart_eulerCoordinates (R₀ : Rotation) {g : RigidTransform}
    (hg : 0 < (R₀⁻¹ * g.rotation).zyzRadial) : eulerChart R₀ (eulerCoordinates R₀ g) = g := by
  unfold eulerCoordinates
  rw [eulerChart_sumElim, Rotation.zyz_inverse _ hg, mul_inv_cancel_left]

/-- **The local inverse lands off the singular set (MLS eq. (2.20), p. 32):** where
`zyzRadial(R₀⁻¹ R_g) > 0`, the middle Euler angle of the coordinates of `g` has `sin β > 0`. -/
theorem sin_eulerCoordinates_pos (R₀ : Rotation) {g : RigidTransform}
    (hg : 0 < (R₀⁻¹ * g.rotation).zyzRadial) :
    0 < Real.sin (eulerAngles (eulerCoordinates R₀ g) 1) := by
  unfold eulerCoordinates
  rwa [eulerAngles_sumElim_one, Rotation.sin_zyzBeta]

/-- **The domain of the local inverse is open (MLS p. 32):** the rotations `R` with
`zyzRadial(R₀⁻¹ R) > 0` form an open set of `SO(3)` (the topology of `Rotation` as a set of
matrices). -/
theorem isOpen_eulerDomain (R₀ : Rotation) :
    IsOpen {R : Rotation | 0 < (R₀⁻¹ * R).zyzRadial} := by
  have hc : ∀ i j, Continuous fun R : Rotation => (R₀⁻¹ * R).val i j := fun i j =>
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_elem i j :
      Continuous fun R : Rotation => (R₀.valᵀ * R.val) i j)
  exact isOpen_lt continuous_const
    (Real.continuous_sqrt.comp (((hc 2 0).pow 2).add ((hc 2 1).pow 2)))

/-- **A chart center for a given orientation (MLS p. 32):** `R₀ = R R_y(π/2)⁻¹`, so that `R` has the
Euler angles `(0, π/2, 0)` in the chart centered at `R₀`, far from the singular set. -/
def eulerCenter (R : Rotation) : Rotation :=
  R * (Rotation.zyz 0 (Real.pi / 2) 0)⁻¹

/-- **Every orientation lies in the open domain of the chart centered at `eulerCenter` (MLS p.
32):** `zyzRadial(R₀⁻¹ R) = 1 > 0` for `R₀ = eulerCenter R`. -/
theorem mem_eulerDomain_eulerCenter (R : Rotation) :
    0 < ((eulerCenter R)⁻¹ * R).zyzRadial := by
  rw [eulerCenter, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  simp [Rotation.zyzRadial, Rotation.zyz_val, Rotation.zyzMatrix]

/-- **The chart family covers `SE(3)` off the singular set (MLS p. 277, a local parameterization
near every pose; p. 32):** every pose is the value of some chart of the family at coordinates with
`sin β ≠ 0`. -/
theorem exists_eulerChart_eq (g : RigidTransform) :
    ∃ (R₀ : Rotation) (ξ : Fin 6 → ℝ), eulerChart R₀ ξ = g ∧ Real.sin (eulerAngles ξ 1) ≠ 0 := by
  exact ⟨eulerCenter g.rotation, eulerCoordinates _ g,
    eulerChart_eulerCoordinates _ (mem_eulerDomain_eulerCenter _),
    (sin_eulerCoordinates_pos _ (mem_eulerDomain_eulerCenter _)).ne'⟩

/-- The radial quantity of `R_z(α) R_y(β) R_z(γ)` is `|sin β|` (MLS eqs. (2.19)–(2.20), p. 32). -/
private theorem zyzRadial_zyz (α β γ : ℝ) :
    (Rotation.zyz α β γ).zyzRadial = |Real.sin β| := by
  rw [Rotation.zyzRadial, Rotation.zyz_val, ← Real.sqrt_sq_eq_abs]
  congr 1
  simp only [Rotation.zyzMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination Real.sin β ^ 2 * Real.sin_sq_add_cos_sq γ

/-- **The singular set and its complement in `SE(3)` (MLS p. 32: (2.20) applies "when
`sin β ≠ 0`"):** a pose `g` is the value of the chart centered at `R₀` at coordinates off the
singular set `sin β = 0` exactly when `zyzRadial(R₀⁻¹ R_g) > 0`, i.e. when `R₀⁻¹ R_g` does not map
the `z`-axis to `±` itself. For `R₀ = I` the poses reached only at singular coordinates are those
whose rotation maps the `z`-axis to `±` itself (the identity among them). -/
theorem exists_eulerChart_eq_iff (R₀ : Rotation) (g : RigidTransform) :
    (∃ ξ : Fin 6 → ℝ, eulerChart R₀ ξ = g ∧ Real.sin (eulerAngles ξ 1) ≠ 0) ↔
      0 < (R₀⁻¹ * g.rotation).zyzRadial := by
  constructor
  · rintro ⟨ξ, rfl, hs⟩
    change 0 < (R₀⁻¹ * (R₀ * Rotation.zyz _ _ _)).zyzRadial
    rw [inv_mul_cancel_left, zyzRadial_zyz]
    exact abs_pos.mpr hs
  · intro hg
    exact ⟨eulerCoordinates R₀ g, eulerChart_eulerCoordinates R₀ hg,
      (sin_eulerCoordinates_pos R₀ hg).ne'⟩

/-- MLS p. 32, "the map from `(α, β, γ)` to `SO(3)` is surjective": every rotation is
`R_z(α) R_y(β) R_z(γ)` for some angles, by (2.20) where `sin β ≠ 0` and by a rotation about the
`z`-axis (after a half turn about `y` when `R e_z = -e_z`) on the singular set. -/
private theorem exists_zyz_eq (S : Rotation) : ∃ α β γ : ℝ, Rotation.zyz α β γ = S := by
  by_cases hr : 0 < S.zyzRadial
  · exact ⟨_, _, _, Rotation.zyz_inverse S hr⟩
  have hle : S.val 2 0 ^ 2 + S.val 2 1 ^ 2 ≤ 0 :=
    Real.sqrt_eq_zero'.mp (le_antisymm (not_lt.mp hr) (Real.sqrt_nonneg _))
  have h20 : S.val 2 0 = 0 := by nlinarith [sq_nonneg (S.val 2 0), sq_nonneg (S.val 2 1)]
  have h21 : S.val 2 1 = 0 := by nlinarith [sq_nonneg (S.val 2 0), sq_nonneg (S.val 2 1)]
  have hrow : S.val 2 0 ^ 2 + S.val 2 1 ^ 2 + S.val 2 2 ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) S.mul_transpose
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h
  have hcol : S.val 0 2 ^ 2 + S.val 1 2 ^ 2 + S.val 2 2 ^ 2 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) S.transpose_mul
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, pow_two, add_assoc] using h
  have h22 : S.val 2 2 * S.val 2 2 = 1 := by
    rw [h20, h21] at hrow
    linear_combination hrow
  have h02 : S.val 0 2 = 0 := by nlinarith [sq_nonneg (S.val 0 2), sq_nonneg (S.val 1 2)]
  have h12 : S.val 1 2 = 0 := by nlinarith [sq_nonneg (S.val 0 2), sq_nonneg (S.val 1 2)]
  have hz : ‖Rotation.zAxis‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Rotation.zAxis, Fin.sum_univ_succ]
  rcases mul_self_eq_one_iff.mp h22 with h | h
  · have hfix : S.act Rotation.zAxis = Rotation.zAxis := by
      apply WithLp.ofLp_injective
      change S.val *ᵥ WithLp.ofLp Rotation.zAxis = WithLp.ofLp Rotation.zAxis
      ext i
      fin_cases i <;>
        simp [Rotation.zAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h02, h12, h]
    obtain ⟨γ, -, -, hγ⟩ := Rotation.exists_angle_exp_eq_of_fixed_axis S _ hz hfix
    refine ⟨0, 0, γ, ?_⟩
    rw [Rotation.zyz, ← Rotation.exp_yAxis]
    change Rotation.exp Rotation.zAxis 0 * Rotation.exp Rotation.yAxis 0 *
      Rotation.exp Rotation.zAxis γ = S
    simp [hγ]
  · let T := (Rotation.yRotation Real.pi)⁻¹ * S
    have hfix : T.act Rotation.zAxis = Rotation.zAxis := by
      apply WithLp.ofLp_injective
      change ((Rotation.yMatrix Real.pi)ᵀ * S.val) *ᵥ WithLp.ofLp Rotation.zAxis =
        WithLp.ofLp Rotation.zAxis
      ext i
      fin_cases i <;>
        simp [Rotation.yMatrix, Rotation.zAxis, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, h02, h12, h]
    obtain ⟨γ, -, -, hγ⟩ := Rotation.exists_angle_exp_eq_of_fixed_axis T _ hz hfix
    refine ⟨0, Real.pi, γ, ?_⟩
    rw [Rotation.zyz]
    change Rotation.exp Rotation.zAxis 0 * Rotation.yRotation Real.pi *
      Rotation.exp Rotation.zAxis γ = S
    rw [hγ, Rotation.exp_zero, one_mul, mul_inv_cancel_left]

/-- **Every pose is reached by the chart centered at `R₀` (MLS p. 32: "the map from `(α, β, γ)` to
`SO(3)` is surjective"):** the chart maps `ℝ⁶` onto `SE(3)`, the poses of the singular image
included (there at coordinates with `sin β = 0`). -/
theorem eulerChart_surjective (R₀ : Rotation) : Function.Surjective (eulerChart R₀) := by
  intro g
  obtain ⟨α, β, γ, h⟩ := exists_zyz_eq (R₀⁻¹ * g.rotation)
  refine ⟨fun j => Sum.elim (fun i => g.translation i) (fun i => ![α, β, γ] i)
    ((finSumFinEquiv (m := 3) (n := 3)).symm j), ?_⟩
  rw [eulerChart_sumElim, h, mul_inv_cancel_left]

/-! ### (6.18) and Exercise 4(b) in Euler coordinates, with no chart hypothesis -/

section Hand

variable {ι : Type*} [Fintype ι] {m n : ι → ℕ}

/-- **MLS eq. (6.18), p. 277, from (5.15), pp. 236–237, in Euler coordinates:** for a hand and the
pose chart centered at `R₀`, along every motion `x` of the six coordinates with velocity `ẋ` at `t`
and pose derivative `D`, the grasping constraint (5.15) at the pose `eulerChart R₀ (x t)` with the
object's body velocity holds exactly when `J_h(θ, φ(x)) θ̇ = Gᵀ(θ, x) ẋ` with `Gᵀ(θ, x) = Gᵀ J(x)`,
`J` the chart Jacobian. -/
theorem graspingConstraint_eulerChart_iff [DecidableEq ι] (h : HandGrasp ι m n) (R₀ : Rotation)
    {x : ℝ → Fin 6 → ℝ} {x' : Fin 6 → ℝ} {t : ℝ} {D : HomogeneousMatrix} (hx : HasDerivAt x x' t)
    (hD : HasDerivAt (fun s => (eulerChart R₀ (x s)).toHomogeneous) D t)
    (θ θ' : (i : ι) → Fin (n i) → ℝ) :
    h.GraspingConstraint θ (eulerChart R₀ (x t)) θ'
        (RigidTransform.bodyVelocity (fun s => eulerChart R₀ (x s)) D t hD) ↔
      h.handJacobianMatrix θ (eulerChart R₀ (x t)) *ᵥ ContactGrasp.stack θ' =
        (localGrasp h (eulerChartJacobian R₀ (x t)))ᵀ *ᵥ x' :=
  graspingConstraint_chart_iff h (isBodyJacobian_eulerChart R₀) hx hD θ θ'

/-- **MLS eq. (6.18), p. 277, as the Pfaffian constraint of the composite system, in Euler
coordinates:** for the composite configuration `q ∈ ℝᴺ` relabeled by `e` (six object coordinates and
`k` finger joints), the constraint `[J_h −Gᵀ] q̇ = 0` built from the hand and the pose chart
centered at `R₀` holds exactly when (5.15) holds at the pose `eulerChart R₀ (x(t))` with the
object's body velocity, along every motion; every theorem of the composite dynamics (6.20)–(6.25)
then applies to the hand in Euler coordinates with no chart hypothesis. -/
theorem pfaffianAt_handPfaffian_eulerChart_iff [DecidableEq ι] (h : HandGrasp ι m n) {k N : ℕ}
    (ec : (Σ i, Fin (m i)) ≃ Fin k) (ej : (Σ i, Fin (n i)) ≃ Fin k) (e : Fin 6 ⊕ Fin k ≃ Fin N)
    (R₀ : Rotation) {q q' : ℝ → Fin N → ℝ} {t : ℝ} {D : HomogeneousMatrix}
    (hq : HasDerivAt q (q' t) t)
    (hD : HasDerivAt (fun s => (eulerChart R₀ (Constrained.splitFst e (q s))).toHomogeneous) D t) :
    Constrained.PfaffianAt
        (handPfaffian e
          (fun y => chartHandJacobian h ec ej (eulerChart R₀) (Constrained.splitSnd e y)
            (Constrained.splitFst e y))
          (fun y => chartGrasp h ec (eulerChartJacobian R₀) (Constrained.splitFst e y)))
        (q t) (q' t) ↔
      h.GraspingConstraint (unstackJoints ej (Constrained.splitSnd e (q t)))
        (eulerChart R₀ (Constrained.splitFst e (q t)))
        (unstackJoints ej (Constrained.splitSnd e (q' t)))
        (RigidTransform.bodyVelocity (fun s => eulerChart R₀ (Constrained.splitFst e (q s))) D t
          hD) :=
  pfaffianAt_handPfaffian_chart_iff h ec ej e (isBodyJacobian_eulerChart R₀) hq hD

/-- **MLS Exercise 4(b), p. 314, in Euler coordinates:** along a motion `x` of the six coordinates
(velocity `x'` near `t`, acceleration `x''` at `t`), with `D s` the pose derivatives, `A` the body
acceleration at `t` and `Jd` the derivative of `s ↦ J(x(s))` at `t`, the Newton–Euler equation at
`t` implies `M̄ ẍ + C̄ ẋ = Jᵀ Fᵇ`, and the converse holds off the singular set, `sin β(t) ≠ 0`. -/
theorem newtonEulerEquation_eulerChart_iff (R₀ : Rotation) (m : ℝ)
    (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) {x x' : ℝ → Fin 6 → ℝ} {x'' : Fin 6 → ℝ}
    {D : ℝ → HomogeneousMatrix} {A : Twist} {Jd : Matrix (Fin 3 ⊕ Fin 3) (Fin 6) ℝ} {t : ℝ}
    (hx : ∀ᶠ s in 𝓝 t, HasDerivAt x (x' s) s) (hx' : HasDerivAt x' x'' t)
    (hD : ∀ s, HasDerivAt (fun r => (eulerChart R₀ (x r)).toHomogeneous) (D s) s)
    (hA : HasDerivAt (fun s => (RigidTransform.bodyVelocity (fun r => eulerChart R₀ (x r)) (D s) s
      (hD s)).coordinates) A.coordinates t)
    (hJd : ∀ i j, HasDerivAt (fun s => eulerChartJacobian R₀ (x s) i j) (Jd i j) t)
    (hβ : Real.sin (eulerAngles (x t) 1) ≠ 0) (F : Wrench) :
    RigidBody.NewtonEulerEquation m 𝓘
        (RigidTransform.bodyVelocity (fun r => eulerChart R₀ (x r)) (D t) t (hD t)) A F ↔
      chartMass (RigidBody.generalizedInertia m 𝓘) (eulerChartJacobian R₀ (x t)) *ᵥ x'' +
          chartCoriolis (RigidBody.generalizedInertia m 𝓘)
            (objectCoriolis m 𝓘
              (RigidTransform.bodyVelocity (fun r => eulerChart R₀ (x r)) (D t) t (hD t)))
            (eulerChartJacobian R₀ (x t)) Jd *ᵥ x' t =
        (eulerChartJacobian R₀ (x t))ᵀ *ᵥ F.coordinates := by
  have h := newtonEulerEquation_chart_iff (isBodyJacobian_eulerChart R₀) m 𝓘 hx hx' hD hA hJd F
  exact ⟨h.1, h.2 (eulerChartJacobian_surjective R₀ hβ)⟩

/-- **MLS p. 277, "`M_o(x) > 0`", in Euler coordinates (Exercise 4(b), p. 314):** for `m > 0` and a
positive definite inertia tensor `𝓘`, `M̄ = Jᵀ M J` is positive definite off the singular set
`sin β ≠ 0`. -/
theorem chartMass_eulerChart_posDef (R₀ : Rotation) {m : ℝ} {𝓘 : Matrix (Fin 3) (Fin 3) ℝ}
    (hm : 0 < m) (h𝓘 : 𝓘.PosDef) {ξ : Fin 6 → ℝ} (hβ : Real.sin (eulerAngles ξ 1) ≠ 0) :
    (chartMass (RigidBody.generalizedInertia m 𝓘) (eulerChartJacobian R₀ ξ)).PosDef :=
  chartMass_posDef (RigidBody.generalizedInertia_posDef hm h𝓘) (eulerChartJacobian_injective R₀ hβ)

end Hand

/-! ### (6.23): the dynamics in body velocity, read against a chart (MLS p. 279) -/

variable {n p k : ℕ}

/-- **MLS eq. (6.23), p. 279, against a chart: the local equations (6.21)–(6.22) are `Jφᵀ` times the
global ones.** Let the object's "global" parameters be `M_g`, `C_g`, `N_g` on `p` velocity
coordinates `V` (for `SE(3)`, `p = 6` and `V` the body velocity `Vᵇ_o`, with the constant
generalized inertia and the Coriolis matrix of Exercise 4(a)), let `G` be the global grasp map, and
let a chart have Jacobian `Jφ ∈ ℝ^{p×k}` with rate `Jd`, so that `V = Jφ ẋ` and `V̇ = Jφ ẍ + Jd ẋ`.
The local parameters of (6.21)–(6.22) are those of the chart, `M_o = Jφᵀ M_g Jφ`,
`C_o = Jφᵀ C_g Jφ + Jφᵀ M_g Jd`, `N_o = Jφᵀ N_g` (Exercise 4(b), p. 314), `G(x) = Jφᵀ G` (the chart
link), and `(d/dt)(J⁻¹ Gᵀ Jφ) = Bd Jφ + J⁻¹ Gᵀ Jd` for `Bd = (d/dt)(J⁻¹ Gᵀ)`. Then
`M̃_loc ẍ + C̃_loc ẋ + Ñ_loc − F_loc = Jφᵀ (M̃ V̇ + C̃ V + Ñ − F)`, where `M̃`, `C̃`, `Ñ`,
`F = G J⁻ᵀ τ` are (6.22) with the global parameters ("the global versions of the inertial
parameters"). -/
theorem effective_dynamics_chart_eq (Mg Cg : Matrix (Fin p) (Fin p) ℝ) (Ng : Fin p → ℝ)
    (Mf Cf J : Matrix (Fin n) (Fin n) ℝ) (Nf τ : Fin n → ℝ) (G : Matrix (Fin p) (Fin n) ℝ)
    (Bd : Matrix (Fin n) (Fin p) ℝ) (Jφ Jd : Matrix (Fin p) (Fin k) ℝ) (x' x'' : Fin k → ℝ) :
    effectiveMass (Jφᵀ * Mg * Jφ) Mf J (Jφᵀ * G) *ᵥ x'' +
        effectiveCoriolis (Jφᵀ * Cg * Jφ + Jφᵀ * Mg * Jd) Cf Mf J (Jφᵀ * G)
          (Bd * Jφ + J⁻¹ * Gᵀ * Jd) *ᵥ x' +
        effectiveN (Jφᵀ *ᵥ Ng) Nf J (Jφᵀ * G) - effectiveForce J (Jφᵀ * G) τ =
      Jφᵀ *ᵥ (effectiveMass Mg Mf J G *ᵥ (Jφ *ᵥ x'' + Jd *ᵥ x') +
        effectiveCoriolis Cg Cf Mf J G Bd *ᵥ (Jφ *ᵥ x') + effectiveN Ng Nf J G -
        effectiveForce J G τ) := by
  simp only [effectiveMass, effectiveCoriolis, effectiveN, effectiveForce, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- **MLS eq. (6.23), p. 279, is equivalent to (6.21) where the chart is nonsingular.** With the
local parameters of `effective_dynamics_chart_eq` and `Jφ` onto (for a chart of `SE(3)`, `k = p = 6`
and `Jφ` invertible): `M̃_loc ẍ + C̃_loc ẋ + Ñ_loc = F_loc` holds exactly when
`M̃ V̇ + C̃ V + Ñ = F` holds with `V = Jφ ẋ`, `V̇ = Jφ ẍ + Jd ẋ` and the global parameters. -/
theorem effective_dynamics_chart_iff (Mg Cg : Matrix (Fin p) (Fin p) ℝ) (Ng : Fin p → ℝ)
    (Mf Cf J : Matrix (Fin n) (Fin n) ℝ) (Nf τ : Fin n → ℝ) (G : Matrix (Fin p) (Fin n) ℝ)
    (Bd : Matrix (Fin n) (Fin p) ℝ) {Jφ : Matrix (Fin p) (Fin k) ℝ} (Jd : Matrix (Fin p) (Fin k) ℝ)
    (hJφ : Function.Surjective Jφ.mulVec) (x' x'' : Fin k → ℝ) :
    effectiveMass (Jφᵀ * Mg * Jφ) Mf J (Jφᵀ * G) *ᵥ x'' +
        effectiveCoriolis (Jφᵀ * Cg * Jφ + Jφᵀ * Mg * Jd) Cf Mf J (Jφᵀ * G)
          (Bd * Jφ + J⁻¹ * Gᵀ * Jd) *ᵥ x' +
        effectiveN (Jφᵀ *ᵥ Ng) Nf J (Jφᵀ * G) = effectiveForce J (Jφᵀ * G) τ ↔
      effectiveMass Mg Mf J G *ᵥ (Jφ *ᵥ x'' + Jd *ᵥ x') +
        effectiveCoriolis Cg Cf Mf J G Bd *ᵥ (Jφ *ᵥ x') + effectiveN Ng Nf J G =
          effectiveForce J G τ := by
  rw [← sub_eq_zero, effective_dynamics_chart_eq, ← sub_eq_zero (a := _ + _ + _),
    ← Matrix.mulVec_zero Jφᵀ]
  exact (transpose_mulVec_injective_of_surjective hJφ).eq_iff

/-- **The local `(d/dt)(J_h⁻¹ Gᵀ)` through a chart (MLS p. 278 with the chart link):** if the
entries of `s ↦ J_h(s)⁻¹ G(s)ᵀ` have the derivative `Bd` at `t` and those of `s ↦ Jφ(s)` the
derivative `Jd`, then the entries of `s ↦ J_h(s)⁻¹ (Jφ(s)ᵀ G(s))ᵀ` have the derivative
`Bd Jφ(t) + J_h(t)⁻¹ G(t)ᵀ Jd`, the rate used in `effective_dynamics_chart_eq`. -/
theorem hasDerivAt_inv_mul_chart_transpose {J : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G : ℝ → Matrix (Fin p) (Fin n) ℝ} {Jφ : ℝ → Matrix (Fin p) (Fin k) ℝ}
    {Bd : Matrix (Fin n) (Fin p) ℝ} {Jd : Matrix (Fin p) (Fin k) ℝ} {t : ℝ}
    (hB : ∀ i j, HasDerivAt (fun s => ((J s)⁻¹ * (G s)ᵀ) i j) (Bd i j) t)
    (hJφ : ∀ i j, HasDerivAt (fun s => Jφ s i j) (Jd i j) t) (i : Fin n) (a : Fin k) :
    HasDerivAt (fun s => ((J s)⁻¹ * ((Jφ s)ᵀ * G s)ᵀ) i a)
      ((Bd * Jφ t + (J t)⁻¹ * (G t)ᵀ * Jd) i a) t := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
  exact Control.hasDerivAt_matrix_mul hB hJφ i a

/-- **The pose-chart Jacobian with its rows relabeled to `Fin 6` (MLS Exercise 4(b), p. 314):** the
twist rows `(v, ω)` of `eulerChartJacobian` relabeled by `Fin 3 ⊕ Fin 3 ≃ Fin 6`, so that (6.23) can
be read with `p = k = 6` (`effective_dynamics_chart_iff`). -/
def eulerChartJacobianFin (R₀ : Rotation) (ξ : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  (eulerChartJacobian R₀ ξ).submatrix (finSumFinEquiv (m := 3) (n := 3)).symm id

/-- **The determinant of the relabeled chart Jacobian is `−sin β` (MLS p. 32; Exercise 4(b), p.
314):** the chart is nonsingular exactly off `sin β = 0`. -/
theorem det_eulerChartJacobianFin (R₀ : Rotation) (ξ : Fin 6 → ℝ) :
    (eulerChartJacobianFin R₀ ξ).det = -Real.sin (eulerAngles ξ 1) := by
  rw [eulerChartJacobianFin, eulerChartJacobian, Matrix.submatrix_submatrix, Function.id_comp,
    Function.comp_id, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_transpose, Rotation.det_eq_one, det_eulerAngularJacobian, one_mul]

end Composite
end RoboLean
