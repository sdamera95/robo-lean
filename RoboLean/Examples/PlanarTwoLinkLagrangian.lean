import RoboLean.Dynamics.PotentialEnergy
import RoboLean.Examples.PlanarTwoLinkDynamics

/-!
# Lagrange's equations of the planar two-link arm (MLS §2.3, Figure 4.4)

MLS Chapter 4, §2.3, printed pp. 164–165, Figure 4.4 and eq. (4.11). The book treats the arm as
moving in the `xy` plane with no potential energy and "substitute[s] the Lagrangian `L = T` into
Lagrange's equations" (p. 165) to obtain

`[[α + 2β c₂, δ + β c₂], [δ + β c₂, δ]] (θ̈₁, θ̈₂) +
[[-β s₂ θ̇₂, -β s₂ (θ̇₁ + θ̇₂)], [β s₂ θ̇₁, 0]] (θ̇₁, θ̇₂) = (τ₁, τ₂)`,

`α = I_z1 + I_z2 + m₁ r₁² + m₂ (l₁² + r₂²)`, `β = m₂ l₁ r₂`, `δ = I_z2 + m₂ r₂²`.

Here the general open-chain theorem `InertialChain.lagrangeEquationsAt_iff` is applied to the
arm `planarTwoLinkArm` of `RoboLean.Examples.PlanarTwoLinkDynamics` with zero potential, and its
inertia and Coriolis matrices are replaced by the ones computed there; the result is the printed
(4.11). With `up = +z` (gravity along `-z`) the potential energy `InertialChain.potentialEnergy`
of the arm and its gravity term vanish identically, which is consistent with the book's `L = T`.

Lean joint `0` is the book's joint 1 (`θ 0 = θ₁`, `θ 1 = θ₂`) and `I_zi = Iᵢ 2`. This is one
instance (a convention check, not a general theorem), and nothing here concerns a physical arm.
-/

noncomputable section
open Matrix Filter Topology

namespace RoboLean.Examples

/-- **MLS §2.3, pp. 164–165, eq. (4.11): the equations of motion of the planar two-link arm.**
Substituting `L = T` (zero potential, motion in the `xy` plane) into Lagrange's equations
(Theorem 4.1, p. 158): along a trajectory `θ` whose velocity near `t` is `θ'` and whose
acceleration at `t` is `θ''`, Lagrange's equations with generalized force `τ` hold at `t`
exactly when `M(θ) θ̈ + C(θ, θ̇) θ̇ = τ`, with the printed `M` of (4.10) and `C` of (4.11)
(`α, β, δ` written out; `θ₂ = θ t 1`, `I_zi = Iᵢ 2`). -/
theorem planarTwoLinkArm_lagrangeEquationsAt_iff (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)
    {θ θ' : ℝ → Fin 2 → ℝ} {θ'' : Fin 2 → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (τ : Fin 2 → ℝ) :
    Lagrangian.LagrangeEquationsAt
        ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).lagrangian fun _ => 0) θ τ t ↔
      !![I₁ 2 + I₂ 2 + m₁ * r₁ ^ 2 + m₂ * (l₁ ^ 2 + r₂ ^ 2) +
          2 * (m₂ * l₁ * r₂) * Real.cos (θ t 1),
        I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos (θ t 1);
        I₂ 2 + m₂ * r₂ ^ 2 + m₂ * l₁ * r₂ * Real.cos (θ t 1),
        I₂ 2 + m₂ * r₂ ^ 2] *ᵥ θ'' +
        !![-(m₂ * l₁ * r₂) * Real.sin (θ t 1) * θ' t 1,
          -(m₂ * l₁ * r₂) * Real.sin (θ t 1) * (θ' t 0 + θ' t 1);
          m₂ * l₁ * r₂ * Real.sin (θ t 1) * θ' t 0, 0] *ᵥ θ' t = τ := by
  have hsymm : ∀ k, ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkInertia k).IsSymm := by
    intro k
    fin_cases k
    · exact RigidBody.generalizedInertia_isSymm m₁ (Matrix.isSymm_diagonal I₁)
    · exact RigidBody.generalizedInertia_isSymm m₂ (Matrix.isSymm_diagonal I₂)
  have hg : Lagrangian.gradient (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) = 0 := by
    funext i
    rfl
  rw [InertialChain.lagrangeEquationsAt_iff _ hsymm
    (fun i j => hasFDerivAt_planarTwoLinkArm_massMatrix m₁ m₂ r₁ r₂ l₁ I₁ I₂ (θ t) i j)
    (hasFDerivAt_const (0 : ℝ) (θ t)) hθ hθ' τ, planarTwoLinkArm_massMatrix,
    planarTwoLinkArm_coriolisMatrix, hg, add_zero]

private theorem norm_zAxis_eq_one : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem exp_zAxis_act_vec (t x y z : ℝ) :
    (Rotation.exp Rotation.zAxis t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  change (Rotation.zRotation t).act (vec x y z) = _
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem vec_add_vec (a b c a' b' c' : ℝ) :
    vec a b c + vec a' b' c' = vec (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem vec_sub_vec (a b c a' b' c' : ℝ) :
    vec a b c - vec a' b' c' = vec (a - a') (b - b') (c - c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem translation_eq_applyPoint (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

private theorem translation_applyPoint_eq (p x : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyPoint x = x + p := by
  simp [RigidTransform.applyPoint]

private theorem inner_zAxis_vec (a b c : ℝ) : inner ℝ Rotation.zAxis (vec a b c) = c := by
  simp [Rotation.zAxis, vec, PiLp.inner_apply, Fin.sum_univ_three]

private theorem planarTwoLinkArm_linkHeight_zAxis (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)
    (k : Fin 2) (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).linkHeight Rotation.zAxis k θ = 0 := by
  have h0 : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q norm_zAxis_eq_one
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
  · rw [InertialChain.linkHeight, InertialChain.linkPose_eq, translation_eq_applyPoint]
    simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
      Fin.val_one, List.take_succ_cons, List.take_zero, List.prod_cons, List.prod_nil, mul_one,
      RigidTransform.mul_applyPoint]
    simp only [planarTwoLinkArm, twoLinkDynamicsChain, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.succ_zero_eq_one, translation_applyPoint_eq,
      h0, vec_add_vec, vec_sub_vec, exp_zAxis_act_vec, inner_zAxis_vec]
    ring

/-- With upward direction `up = +z` (gravity along `-z`), the potential energy of the planar arm
of MLS Figure 4.4 vanishes at every configuration and for all link masses: every link mass
center stays in the `xy` plane. This is consistent with MLS using `L = T` on p. 165; it is a
consistency check, not a printed formula. -/
theorem planarTwoLinkArm_potentialEnergy_zAxis (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)
    (m : Fin 2 → ℝ) (g : ℝ) (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).potentialEnergy m g Rotation.zAxis θ = 0 := by
  simp [InertialChain.potentialEnergy, planarTwoLinkArm_linkHeight_zAxis]

/-- With upward direction `up = +z` (gravity along `-z`), the gravity term `N = ∂V/∂θ`
(MLS p. 174) of the planar arm of MLS Figure 4.4 is zero at every configuration, consistent with
MLS using `L = T` on p. 165; a consistency check, not a printed formula. -/
theorem planarTwoLinkArm_gravityTerm_zAxis (m₁ m₂ r₁ r₂ l₁ : ℝ) (I₁ I₂ : Fin 3 → ℝ)
    (m : Fin 2 → ℝ) (g : ℝ) (θ : Fin 2 → ℝ) :
    (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).gravityTerm m g Rotation.zAxis θ = 0 := by
  have hV : (planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).potentialEnergy m g Rotation.zAxis =
      fun _ => 0 := by
    funext q
    exact planarTwoLinkArm_potentialEnergy_zAxis m₁ m₂ r₁ r₂ l₁ I₁ I₂ m g q
  have hd : HasFDerivAt ((planarTwoLinkArm m₁ m₂ r₁ r₂ l₁ I₁ I₂).potentialEnergy m g
      Rotation.zAxis) (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) θ := by
    rw [hV]
    exact hasFDerivAt_const (0 : ℝ) θ
  rw [InertialChain.gravityTerm_eq_gradient _ hd]
  funext i
  rfl

end RoboLean.Examples
