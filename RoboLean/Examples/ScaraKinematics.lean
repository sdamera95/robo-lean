import RoboLean.Examples.ScaraHand
import RoboLean.Examples.PlanarTwoLinkInverseKinematics
import RoboLean.Kinematics.ReferenceConfiguration

/-!
# SCARA kinematics: MLS Examples 3.1, 3.3, 3.6 and 3.10

MLS printed pp. 87–93, 106–107 and 122–123. The SCARA manipulator of Example 3.1 (Figure 3.3,
p. 88) has three revolute joints about `+z` through `q₁ = (0, 0, 0)`, `q₂ = (0, l₁, 0)`,
`q₃ = (0, l₁ + l₂, 0)` and a prismatic joint along `+z`; these are the twists of the library's
`scaraChain` (MLS Examples 3.1, 3.8 and 4.4). Example 3.1 places the tool at
`g_st(0) = (I, (0, l₁ + l₂, l₀))` (p. 87); `scaraKinematicChain l₀ l₁ l₂` is that chain.

* Example 3.1 / eq. (3.38): `g_st(θ) = (Rz(θ₁ + θ₂ + θ₃), (-l₁ s₁ - l₂ s₁₂, l₁ c₁ + l₂ c₁₂, l₀ + θ₄))`
  (eq. (3.4), p. 89, with the position repeated on p. 106).
* Example 3.3 (pp. 92–93): with the base frame at the reference tool frame the twists are the
  printed `ξ₁ = (-l₁ - l₂, 0, 0, 0, 0, 1)`, `ξ₂ = (-l₂, 0, 0, 0, 0, 1)`, `ξ₃ = (0, 0, 0, 0, 0, 1)`,
  `ξ₄ = (0, 0, 1, 0, 0, 0)`, `g_st(0) = I`, and the forward kinematics is (3.5). Here the chain of
  the printed twists is shown to be `SerialChain.baseAtTool` of Example 3.1's chain, and (3.5)
  follows from (3.4).
* Example 3.6 (pp. 106–107): `g_st(θ) = g_d` with `g_d` of the form (3.38) splits into
  `θ₄ = z - l₀`, the planar two-link position equation and the orientation equation; for
  positive link lengths and a target inside the annulus there are exactly the two printed
  solution branches modulo `2π`.
* Example 3.10 (pp. 122–123): the transpose of the spatial Jacobian is the printed `4 × 6`
  matrix, and at a configuration with `l₁ ≠ 0`, `l₂ ≠ 0`, `sin θ₂ ≠ 0` its null space is spanned
  by the printed wrenches `F_N1 = (0, 0, 0, 1, 0, 0)` and `F_N2 = (0, 0, 0, 0, 1, 0)`: the pure
  moments about the `x`- and `y`-axes are exactly the end-effector wrenches balanced without
  joint torques. The book states the spanning set without the configuration hypothesis; at
  `sin θ₂ = 0` (or a zero link length) the null space is three-dimensional.

Conventions: twists `(v, ω)`, wrenches `(f, τ)`, Lean joint `k` is the book's joint `k + 1`
(`θ 0 = θ₁`, …, `θ 3 = θ₄`), all lengths and angles real.
-/

noncomputable section

open Real
open scoped Matrix

namespace RoboLean

namespace Examples

/-! ### Private coordinate helpers -/

private theorem sk_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem sk_zRotation_act (t x y z : ℝ) :
    (Rotation.zRotation t).act (vec x y z) =
      vec (cos t * x - sin t * y) (sin t * x + cos t * y) z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem sk_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem sk_exp_z_applyPoint (qx qy qz t x y z : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec qx qy qz)) t).applyPoint (vec x y z) =
      vec (cos t * (x - qx) - sin t * (y - qy) + qx)
        (sin t * (x - qx) + cos t * (y - qy) + qy) z := by
  rw [Twist.exp_revolute_applyPoint _ _ sk_norm_zAxis]
  have : vec x y z - vec qx qy qz = vec (x - qx) (y - qy) (z - qz) := by
    ext i
    fin_cases i <;> simp [vec]
  rw [this, show Rotation.exp Rotation.zAxis t = Rotation.zRotation t from rfl, sk_zRotation_act]
  ext i
  fin_cases i <;> simp [vec]

private theorem sk_exp_prismatic_applyPoint (t x y z : ℝ) :
    (Twist.exp (Twist.prismatic Rotation.zAxis) t).applyPoint (vec x y z) = vec x y (z + t) := by
  rw [Twist.exp_prismatic]
  ext i
  fin_cases i <;> simp [RigidTransform.applyPoint, Rotation.zAxis, vec]

private theorem sk_translation (g : RigidTransform) : g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem sk_vec_eq_iff (a b c a' b' c' : ℝ) :
    vec a b c = vec a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Vec3 => v 0) h
    have h1 := congrArg (fun v : Vec3 => v 1) h
    have h2 := congrArg (fun v : Vec3 => v 2) h
    simp only [vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem sk_revolute_z (x y z : ℝ) :
    Twist.revolute Rotation.zAxis (vec x y z) = ⟨vec y (-x) 0, vec 0 0 1⟩ := by
  apply Twist.ext <;> ext i <;> fin_cases i <;>
    simp [Twist.revolute, Vec3.cross, cross_apply, Rotation.zAxis, vec]

/-- Rotations about `z` agree exactly when the angles agree modulo `2π`. -/
private theorem sk_zRotation_eq_iff (a b : ℝ) :
    Rotation.zRotation a = Rotation.zRotation b ↔ ∃ k : ℤ, a = b + k * (2 * π) := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    rw [Rotation.zRotation_val, Rotation.zRotation_val] at hv
    have hc := congrFun (congrFun hv 0) 0
    have hs := congrFun (congrFun hv 1) 0
    simp at hc hs
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    exact Rotation.exp_add_int_mul_two_pi _ sk_norm_zAxis b k

/-- The SCARA manipulator of MLS Example 3.1 (Figure 3.3, pp. 87–88): the joint twists of
`scaraChain l₁ l₂` and the reference tool pose `g_st(0) = (I, (0, l₁ + l₂, l₀))` printed on
p. 87. -/
def scaraKinematicChain (l₀ l₁ l₂ : ℝ) : SerialChain 4 :=
  { scaraChain l₁ l₂ with toolRef := ⟨1, vec 0 (l₁ + l₂) l₀⟩ }

/-- **MLS Example 3.1, eq. (3.4), p. 89 (and eq. (3.38), p. 106).** The forward kinematics of the
SCARA is `g_st(θ) = (Rz(θ₁ + θ₂ + θ₃), (-l₁ sin θ₁ - l₂ sin(θ₁ + θ₂), l₁ cos θ₁ + l₂ cos(θ₁ + θ₂),
l₀ + θ₄))`, for all real lengths and joint values. -/
theorem scaraKinematicChain_fk (l₀ l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraKinematicChain l₀ l₁ l₂).fk θ =
      ⟨Rotation.zRotation (θ 0 + θ 1 + θ 2),
        vec (-l₁ * sin (θ 0) - l₂ * sin (θ 0 + θ 1)) (l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1))
          (l₀ + θ 3)⟩ := by
  have hfk : (scaraKinematicChain l₀ l₁ l₂).fk θ =
      Twist.exp (Twist.revolute Rotation.zAxis (vec 0 0 0)) (θ 0) *
        (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 l₁ 0)) (θ 1) *
          (Twist.exp (Twist.revolute Rotation.zAxis (vec 0 (l₁ + l₂) 0)) (θ 2) *
            (Twist.exp (Twist.prismatic Rotation.zAxis) (θ 3) * 1))) * ⟨1, vec 0 (l₁ + l₂) l₀⟩ := by
    simp only [SerialChain.fk, SerialChain.poe, SerialChain.jointMotions, List.ofFn_succ,
      List.ofFn_zero, List.prod_cons, List.prod_nil]
    rfl
  apply RigidTransform.ext
  · rw [hfk]
    simp only [RigidTransform.mul_rotation, Twist.exp_rotation, Twist.revolute, Twist.prismatic,
      Rotation.exp_zero_axis, mul_one]
    simp only [Rotation.zRotation]
    rw [Rotation.exp_add, Rotation.exp_add, mul_assoc]
  · rw [sk_translation, hfk]
    simp only [RigidTransform.mul_applyPoint, RigidTransform.one_applyPoint]
    rw [show (⟨1, vec 0 (l₁ + l₂) l₀⟩ : RigidTransform).applyPoint (vec 0 0 0) =
        vec 0 (l₁ + l₂) l₀ from by
      ext i
      fin_cases i <;> simp [RigidTransform.applyPoint, vec]]
    rw [sk_exp_prismatic_applyPoint, sk_exp_z_applyPoint, sk_exp_z_applyPoint, sk_exp_z_applyPoint]
    apply sk_vec_eq
    · simp only [sin_add]
      ring
    · simp only [cos_add]
      ring
    · rfl

/-- The SCARA of MLS Example 3.3 (Figure 3.5, p. 92) with the base frame coincident with the tool
frame at `θ = 0`: the printed twists `ξ₁ = (-l₁ - l₂, 0, 0, 0, 0, 1)`, `ξ₂ = (-l₂, 0, 0, 0, 0, 1)`,
`ξ₃ = (0, 0, 0, 0, 0, 1)`, `ξ₄ = (0, 0, 1, 0, 0, 0)` and `g_st(0) = I`. -/
def scaraAlternateBaseChain (l₁ l₂ : ℝ) : SerialChain 4 where
  twist := ![⟨vec (-l₁ - l₂) 0 0, vec 0 0 1⟩, ⟨vec (-l₂) 0 0, vec 0 0 1⟩, ⟨vec 0 0 0, vec 0 0 1⟩,
    ⟨vec 0 0 1, vec 0 0 0⟩]
  toolRef := 1

/-- **MLS Example 3.3, p. 92, with p. 91.** The printed twists of Example 3.3 are the twists of
Example 3.1's SCARA described from the base frame at the reference tool frame
(`SerialChain.baseAtTool`, the base change by `g_st(0)⁻¹`), for every `l₀`; in particular
`g_st(0) = I`. -/
theorem scaraKinematicChain_baseAtTool (l₀ l₁ l₂ : ℝ) :
    (scaraKinematicChain l₀ l₁ l₂).baseAtTool = scaraAlternateBaseChain l₁ l₂ := by
  simp only [SerialChain.baseAtTool, SerialChain.changeBase, scaraAlternateBaseChain,
    scaraKinematicChain, scaraChain, SerialChain.mk.injEq]
  refine ⟨?_, inv_mul_cancel _, trivial⟩
  funext i
  have hp : ∀ x y z : ℝ, (⟨1, vec 0 (l₁ + l₂) l₀⟩ : RigidTransform)⁻¹.applyPoint (vec x y z) =
      vec x (y - (l₁ + l₂)) (z - l₀) := by
    intro x y z
    ext j
    fin_cases j <;> simp [RigidTransform.applyPoint, vec] <;> ring
  have hv : (⟨1, vec 0 (l₁ + l₂) l₀⟩ : RigidTransform)⁻¹.applyVector Rotation.zAxis =
      Rotation.zAxis := by
    simp [RigidTransform.applyVector]
  fin_cases i
  · change Twist.adjoint _ (Twist.revolute Rotation.zAxis (vec 0 0 0)) = _
    rw [Twist.adjoint_revolute, hp, hv, sk_revolute_z]
    congr 1
    apply sk_vec_eq <;> (norm_num; try ring)
  · change Twist.adjoint _ (Twist.revolute Rotation.zAxis (vec 0 l₁ 0)) = _
    rw [Twist.adjoint_revolute, hp, hv, sk_revolute_z]
    congr 1
    apply sk_vec_eq <;> ring
  · change Twist.adjoint _ (Twist.revolute Rotation.zAxis (vec 0 (l₁ + l₂) 0)) = _
    rw [Twist.adjoint_revolute, hp, hv, sk_revolute_z]
    congr 1
    apply sk_vec_eq <;> ring
  · change Twist.adjoint _ (Twist.prismatic Rotation.zAxis) = _
    rw [Twist.adjoint_prismatic, hv]
    apply Twist.ext <;> ext j <;> fin_cases j <;> simp [Twist.prismatic, Rotation.zAxis, vec]

/-- **MLS Example 3.3, eq. (3.5), p. 93.** With the base frame at the reference tool frame the
SCARA's forward kinematics is `g_st(θ) = (Rz(θ₁ + θ₂ + θ₃), (-l₁ sin θ₁ - l₂ sin(θ₁ + θ₂),
-l₁ - l₂ + l₁ cos θ₁ + l₂ cos(θ₁ + θ₂), θ₄))`, and `g_st(0) = I`. -/
theorem scaraAlternateBaseChain_fk (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    (scaraAlternateBaseChain l₁ l₂).fk θ =
      ⟨Rotation.zRotation (θ 0 + θ 1 + θ 2),
        vec (-l₁ * sin (θ 0) - l₂ * sin (θ 0 + θ 1))
          (-l₁ - l₂ + l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1)) (θ 3)⟩ := by
  rw [← scaraKinematicChain_baseAtTool 0, (SerialChain.fk_baseAtTool _ θ).2,
    scaraKinematicChain_fk]
  apply RigidTransform.ext
  · simp [scaraKinematicChain]
  · ext j
    fin_cases j <;> simp [scaraKinematicChain, vec]
    ring

/-- **MLS Example 3.6, eq. (3.38), pp. 106–107.** The SCARA reaches `g_d = (Rz(φ), (x, y, z))`
exactly when `θ₄ = z - l₀` (found "without any of the previously defined subproblems"), the
first two joints put the planar two-link arm of lengths `l₁, l₂` at `(x, y)`, and
`Rz(θ₁ + θ₂ + θ₃) = Rz(φ)`. -/
theorem scaraKinematicChain_fk_eq_iff (l₀ l₁ l₂ φ x y z : ℝ) (θ : Fin 4 → ℝ) :
    (scaraKinematicChain l₀ l₁ l₂).fk θ = ⟨Rotation.zRotation φ, vec x y z⟩ ↔
      θ 3 = z - l₀ ∧ planarTwoLinkPosition l₁ l₂ ![θ 0, θ 1] = vec x y 0 ∧
        Rotation.zRotation (θ 0 + θ 1 + θ 2) = Rotation.zRotation φ := by
  rw [scaraKinematicChain_fk, RigidTransform.ext_iff, planarTwoLinkPosition_eq]
  simp only [sk_vec_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨hR, hx, hy, hz⟩
    exact ⟨by linarith, ⟨by linarith, hy, trivial⟩, hR⟩
  · rintro ⟨hz, ⟨hx, hy, -⟩, hR⟩
    exact ⟨hR, by linarith, hy, by linarith⟩

/-- **MLS Example 3.6, p. 107: "a maximum of two possible solutions".** For positive link lengths
`l₁, l₂` and a target `(x, y)` at distance `r = √(x² + y²)` with `0 < r` and
`|l₁ - l₂| ≤ r ≤ l₁ + l₂`, the SCARA reaches `g_d = (Rz(φ), (x, y, z))` exactly when `θ₄ = z - l₀`,
`θ₃ = φ - θ₁ - θ₂` modulo `2π`, and `(θ₁, θ₂)` is on one of the two branches of the planar
two-link solution (MLS eq. (3.16), p. 98) for the point `(y, -x)` of Figure 3.7a's plane (the
SCARA's zero configuration points along `+y`; Lean `θ 0 = θ₁`, `θ 1 = θ₂`): modulo `2π`,
`θ₂ = π ± α` and `θ₁ = atan2(-x, y) ± β` with agreeing signs. The book's hypotheses are not
printed; positivity, `r ≠ 0` and the annulus condition are the ones of the planar solution. -/
theorem scaraKinematicChain_inverseKinematics_iff {l₀ l₁ l₂ φ x y z r : ℝ} (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (hr : r = √(x ^ 2 + y ^ 2)) (hr₀ : 0 < r) (h₁ : |l₁ - l₂| ≤ r)
    (h₂ : r ≤ l₁ + l₂) (θ : Fin 4 → ℝ) :
    (scaraKinematicChain l₀ l₁ l₂).fk θ = ⟨Rotation.zRotation φ, vec x y z⟩ ↔
      θ 3 = z - l₀ ∧ (∃ k : ℤ, θ 2 = φ - θ 0 - θ 1 + k * (2 * π)) ∧
        ((∃ k m : ℤ, θ 1 = π + planarTwoLinkAlpha l₁ l₂ r + k * (2 * π) ∧
            θ 0 = Rotation.atan2 (-x) y + planarTwoLinkBeta l₁ l₂ r + m * (2 * π)) ∨
          (∃ k m : ℤ, θ 1 = π - planarTwoLinkAlpha l₁ l₂ r + k * (2 * π) ∧
            θ 0 = Rotation.atan2 (-x) y - planarTwoLinkBeta l₁ l₂ r + m * (2 * π))) := by
  have hr' : r = √(y ^ 2 + (-x) ^ 2) := by rw [hr]; ring_nf
  have hik := planarTwoLink_inverseKinematics_iff hl₁ hl₂ hr' hr₀ h₁ h₂ ![θ 0, θ 1]
  rw [neg_neg] at hik
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hik
  rw [scaraKinematicChain_fk_eq_iff, hik, sk_zRotation_eq_iff]
  constructor
  · rintro ⟨h3, hb, k, hk⟩
    exact ⟨h3, ⟨k, by linarith⟩, hb⟩
  · rintro ⟨h3, ⟨k, hk⟩, hb⟩
    exact ⟨h3, hb, k, by linarith⟩

/-- The transpose of the SCARA's spatial Jacobian as printed in MLS Example 3.10, p. 122: four
rows (the joints) and six columns `(f, τ)`,
`[[0, 0, 0, 0, 0, 1], [l₁c₁, l₁s₁, 0, 0, 0, 1], [l₁c₁ + l₂c₁₂, l₁s₁ + l₂s₁₂, 0, 0, 0, 1],
[0, 0, 1, 0, 0, 0]]`. -/
def scaraPrintedJacobianTranspose (l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromCols
    !![0, 0, 0;
      l₁ * cos (θ 0), l₁ * sin (θ 0), 0;
      l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1), l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1), 0;
      0, 0, 1]
    !![0, 0, 1; 0, 0, 1; 0, 0, 1; 0, 0, 0]

/-- **MLS Example 3.10, p. 122.** The transpose of the SCARA's spatial Jacobian (MLS
eq. (3.54), p. 116) is the printed `4 × 6` matrix, at every configuration and for every tool
offset `l₀`. -/
theorem scaraKinematicChain_spatialJacobianMatrix_transpose (l₀ l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    ((scaraKinematicChain l₀ l₁ l₂).spatialJacobianMatrix θ)ᵀ =
      scaraPrintedJacobianTranspose l₁ l₂ θ := by
  have h : (scaraKinematicChain l₀ l₁ l₂).spatialJacobianMatrix θ =
      (scaraChain l₁ l₂).spatialJacobianMatrix θ := rfl
  rw [h, scaraChain_spatialJacobianMatrix]
  ext i r
  rcases r with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [scaraPrintedSpatialJacobian, scaraPrintedJacobianTranspose]

/-- **MLS Example 3.10, pp. 122–123: wrenches resisted by the structure.** At a configuration with
`l₁ ≠ 0`, `l₂ ≠ 0` and `sin θ₂ ≠ 0` (a hypothesis the book does not print), a spatial wrench
generates no joint torques, `(Jˢ)ᵀ F = 0` (MLS eq. (3.60), p. 121), exactly when it is a
combination of the printed `F_N1 = (0, 0, 0, 1, 0, 0)` and `F_N2 = (0, 0, 0, 0, 1, 0)`, the
pure moments about the `x`- and `y`-axes. -/
theorem scaraKinematicChain_balanced_iff (l₀ : ℝ) {l₁ l₂ : ℝ} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (θ : Fin 4 → ℝ) (hθ : sin (θ 1) ≠ 0) (F : Wrench) :
    (scaraKinematicChain l₀ l₁ l₂).spatialWrenchTorques θ F = 0 ↔
      ∃ a b : ℝ, F = a • ⟨vec 0 0 0, vec 1 0 0⟩ + b • ⟨vec 0 0 0, vec 0 1 0⟩ := by
  rw [← SerialChain.spatialJacobianMatrix_transpose_mulVec,
    scaraKinematicChain_spatialJacobianMatrix_transpose]
  have row : ∀ i, (scaraPrintedJacobianTranspose l₁ l₂ θ *ᵥ F.coordinates) i =
      ![F.torque 2, l₁ * cos (θ 0) * F.force 0 + l₁ * sin (θ 0) * F.force 1 + F.torque 2,
        (l₁ * cos (θ 0) + l₂ * cos (θ 0 + θ 1)) * F.force 0 +
          (l₁ * sin (θ 0) + l₂ * sin (θ 0 + θ 1)) * F.force 1 + F.torque 2, F.force 2] i := by
    intro i
    fin_cases i <;>
      simp [scaraPrintedJacobianTranspose, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_succ, Wrench.coordinates, Matrix.fromCols]
  have hs : sin (θ 1) = sin (θ 0 + θ 1) * cos (θ 0) - cos (θ 0 + θ 1) * sin (θ 0) := by
    rw [← sin_sub]
    ring_nf
  constructor
  · intro h
    have e0 := (row 0).symm.trans (congrFun h 0)
    have e1 := (row 1).symm.trans (congrFun h 1)
    have e2 := (row 2).symm.trans (congrFun h 2)
    have e3 := (row 3).symm.trans (congrFun h 3)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at e0 e1 e2 e3
    have hA : cos (θ 0) * F.force 0 + sin (θ 0) * F.force 1 = 0 := by
      have : l₁ * (cos (θ 0) * F.force 0 + sin (θ 0) * F.force 1) = 0 := by
        linear_combination e1 - e0
      exact (mul_eq_zero.mp this).resolve_left hl₁
    have hB : cos (θ 0 + θ 1) * F.force 0 + sin (θ 0 + θ 1) * F.force 1 = 0 := by
      have : l₂ * (cos (θ 0 + θ 1) * F.force 0 + sin (θ 0 + θ 1) * F.force 1) = 0 := by
        linear_combination e2 - e1
      exact (mul_eq_zero.mp this).resolve_left hl₂
    have hx : F.force 0 = 0 := by
      have : F.force 0 * sin (θ 1) = 0 := by
        rw [hs]
        linear_combination sin (θ 0 + θ 1) * hA - sin (θ 0) * hB
      exact (mul_eq_zero.mp this).resolve_right hθ
    have hy : F.force 1 = 0 := by
      have : F.force 1 * sin (θ 1) = 0 := by
        rw [hs]
        linear_combination cos (θ 0) * hB - cos (θ 0 + θ 1) * hA
      exact (mul_eq_zero.mp this).resolve_right hθ
    refine ⟨F.torque 0, F.torque 1, ?_⟩
    apply Wrench.ext <;> ext j <;> fin_cases j <;> simp [vec, hx, hy, e0, e3]
  · rintro ⟨a, b, rfl⟩
    funext i
    rw [row i]
    fin_cases i <;> simp [vec]

end Examples

end RoboLean
