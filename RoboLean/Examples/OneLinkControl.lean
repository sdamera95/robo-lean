import RoboLean.Control.PDAsymptotic
import RoboLean.Examples.RigidTransform

/-!
# A one-link revolute arm under PD control: every hypothesis discharged (MLS §5.3)

The first link of the planar arm of MLS Figure 4.4 (printed p. 164) on its own: one revolute joint
about `+z` through the base origin, the link frame at the mass center `(r, 0, 0)` with the base
orientation at `θ = 0` (aligned with the principal axes), and the generalized inertia
`[[m I, 0], [0, diag(I)]]` of MLS eq. (4.9), printed p. 162. Its inertia matrix, computed from the
general construction `M(θ) = Jᵀ 𝓜 J` of MLS eq. (4.19), printed p. 168, is the constant
`[I_z + m r²]` (`oneLinkArm_massMatrix`: MLS eq. (4.10), printed p. 165, restricted to one link).

As a manipulator model (4.47) (printed p. 190) with any gravity data, for example a pendulum in a
vertical plane with `up = +y`, and any further joint forces `Nₑ`, PD control with compensation of
`N` and gains `K_p = K_v = 1` makes the set point `(θ_d, 0)` globally asymptotically stable at
every `t₀ ≥ 0` (`oneLinkModel_globallyAsymptoticallyStableAt_pdCompensatedTorque`, MLS
Proposition 4.9, printed p. 193, as formalized in `RoboLean.Control.PDAsymptotic`). Here every
hypothesis of the general theorem is discharged, the solution flow of the closed loop included:
the inertia is constant, so the closed loop is affine and its flow is the matrix exponential
constructed in `ManipulatorModel.hasFlow_pdClosedLoop_of_const`.

Conventions: the state is `(θ, θ̇) ∈ ℝ¹ × ℝ¹` with the sup norm of the product; Lean joint `0` is
the book's joint 1; `I = ![I_x, I_y, I_z]`, so `I_z = I 2`; the tool pose is not used and is set to
the identity. This is an instance showing that the hypotheses of the general theorems can be met;
it is not a separate result, and nothing here concerns a physical arm.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

/-! ### Small coordinate helpers -/

private theorem oneLink_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem oneLink_revolute_angular (ω q : Vec3) : (Twist.revolute ω q).angular = ω := rfl

private theorem oneLink_revolute_linear (ω q : Vec3) :
    (Twist.revolute ω q).linear = -Vec3.cross ω q := rfl

private theorem oneLink_vec_add (a b c a' b' c' : ℝ) :
    vec a b c + vec a' b' c' = vec (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem oneLink_vec_sub (a b c a' b' c' : ℝ) :
    vec a b c - vec a' b' c' = vec (a - a') (b - b') (c - c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem oneLink_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem oneLink_zRotation_act_vec (t x y z : ℝ) :
    (Rotation.zRotation t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem oneLink_exp_revolute_z_applyPoint (a b t : ℝ) (x : Vec3) :
    (Twist.exp (Twist.revolute Rotation.zAxis (vec a b 0)) t).applyPoint x =
      (Rotation.zRotation t).act (x - vec a b 0) + vec a b 0 :=
  Twist.exp_revolute_applyPoint _ _ oneLink_norm_zAxis t x

private theorem oneLink_exp_revolute_z_applyVector (q : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyVector Rotation.zAxis =
      Rotation.zAxis := by
  rw [RigidTransform.applyVector, Twist.exp_rotation, oneLink_revolute_angular]
  change (Rotation.zRotation t).act Rotation.zAxis = Rotation.zAxis
  rw [show Rotation.zAxis = vec 0 0 1 from rfl, oneLink_zRotation_act_vec]
  simp

private theorem oneLink_translation_applyPoint (p x : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyPoint x = x + p := by
  simp [RigidTransform.applyPoint]

private theorem oneLink_translation_applyVector (p v : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyVector v = v := by
  simp [RigidTransform.applyVector]

private theorem oneLink_inv_applyPoint_of {g : RigidTransform} {x y : Vec3}
    (h : g.applyPoint x = y) : g⁻¹.applyPoint y = x := by
  rw [← h, RigidTransform.inv_applyPoint_applyPoint]

private theorem oneLink_inv_applyVector_of {g : RigidTransform} {v w : Vec3}
    (h : g.applyVector v = w) : g⁻¹.applyVector w = v := by
  rw [← h, ← RigidTransform.mul_applyVector, inv_mul_cancel, RigidTransform.one_applyVector]

/-! ### The arm as an inertial chain -/

/-- **The joint of the one-link arm** (the first joint of MLS Figure 4.4, printed p. 164): revolute
about `+z` through the base origin, base-frame twist at `θ = 0` in the order `(v, ω)` (MLS p. 87).
The tool pose is not used by the dynamics and is set to the identity. -/
def oneLinkChain : SerialChain 1 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 0 0)]
  toolRef := 1

/-- **The one-link revolute arm with inertial data** (the first link of MLS Figure 4.4, printed
p. 164): link frame at the mass center `(r, 0, 0)` with the base orientation at `θ = 0` (aligned
with the principal axes), and generalized inertia `[[m I, 0], [0, diag(I)]]` (MLS eq. (4.9),
printed p. 162), `I = ![I_x, I_y, I_z]`. -/
def oneLinkArm (m r : ℝ) (I : Fin 3 → ℝ) : InertialChain 1 where
  chain := oneLinkChain
  linkRef := ![⟨1, vec r 0 0⟩]
  linkInertia := ![RigidBody.generalizedInertia m (Matrix.diagonal I)]

/-- The body Jacobian of the link (MLS p. 168): the joint's twist in the link frame, a revolute
twist about `+z` through `(-r, 0, 0)`, at every configuration. -/
private theorem oneLinkArm_linkBodyJacobian (m r : ℝ) (I : Fin 3 → ℝ) (θ : Fin 1 → ℝ) :
    (oneLinkArm m r I).linkBodyJacobian 0 θ 0 =
      Twist.revolute Rotation.zAxis (vec (-r) 0 0) := by
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ le_rfl]
  have ht : (oneLinkArm m r I).chain.twist 0 = Twist.revolute Rotation.zAxis (vec 0 0 0) := rfl
  have hl : (oneLinkArm m r I).linkRef 0 = ⟨1, vec r 0 0⟩ := rfl
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
    zero_add, List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons,
    List.prod_nil, mul_one]
  rw [ht, hl, Twist.adjoint_revolute]
  congr 1
  · apply oneLink_inv_applyVector_of
    rw [RigidTransform.mul_applyVector, oneLink_translation_applyVector,
      oneLink_exp_revolute_z_applyVector]
  · apply oneLink_inv_applyPoint_of
    rw [RigidTransform.mul_applyPoint, oneLink_translation_applyPoint,
      oneLink_exp_revolute_z_applyPoint, oneLink_vec_add, oneLink_vec_sub,
      oneLink_zRotation_act_vec, oneLink_vec_add]
    apply oneLink_vec_eq <;> ring

/-- The generalized-inertia pairing of two in-plane revolute twists about `+z`
(MLS eq. (4.9), p. 162): the axes through `(a, b, 0)` and `(a', b', 0)` give
`m (a a' + b b') + I_z`. -/
private theorem oneLink_pairing_revolute_z (m : ℝ) (I : Fin 3 → ℝ) (a b a' b' : ℝ) :
    (Twist.revolute Rotation.zAxis (vec a b 0)).coordinates ⬝ᵥ
      (RigidBody.generalizedInertia m (Matrix.diagonal I) *ᵥ
        (Twist.revolute Rotation.zAxis (vec a' b' 0)).coordinates) =
      m * (a * a' + b * b') + I 2 := by
  have hv (x y : ℝ) : WithLp.ofLp (-Vec3.cross Rotation.zAxis (vec x y 0)) = ![y, -x, 0] := by
    ext i
    fin_cases i <;> simp [Vec3.cross, cross_apply, Rotation.zAxis, vec]
  have hz : WithLp.ofLp Rotation.zAxis = ![0, 0, 1] := rfl
  rw [RigidBody.coordinates_dotProduct_generalizedInertia_mulVec, oneLink_revolute_linear,
    oneLink_revolute_linear, oneLink_revolute_angular, oneLink_revolute_angular, hv, hv, hz]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.mulVec_diagonal, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-! ### The inertia matrix (MLS eqs. (4.10), (4.19)) -/

/-- **MLS eq. (4.10), printed p. 165, restricted to one link: the inertia matrix of the one-link
arm is constant.** The general construction `M(θ) = Jᵀ 𝓜 J` of MLS eq. (4.19), printed p. 168,
gives `M(θ) = [I_z + m r²]` at every configuration (`I_z = I 2`). -/
theorem oneLinkArm_massMatrix (m r : ℝ) (I : Fin 3 → ℝ) (θ : Fin 1 → ℝ) :
    (oneLinkArm m r I).massMatrix θ = !![I 2 + m * r ^ 2] := by
  have hM : (oneLinkArm m r I).linkInertia 0 =
      RigidBody.generalizedInertia m (Matrix.diagonal I) := rfl
  ext i j
  fin_cases i
  fin_cases j
  rw [InertialChain.massMatrix_apply, Fin.sum_univ_one, hM]
  simp only [Fin.zero_eta, Fin.isValue, oneLinkArm_linkBodyJacobian, oneLink_pairing_revolute_z,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val']
  ring

/-- The link inertia `[[m I, 0], [0, diag(I)]]` of the one-link arm is symmetric (MLS eq. (4.9),
printed p. 162), for all real `m` and `I`. -/
theorem oneLinkArm_linkInertia_isSymm (m r : ℝ) (I : Fin 3 → ℝ) (k : Fin 1) :
    ((oneLinkArm m r I).linkInertia k).IsSymm := by
  fin_cases k
  exact RigidBody.generalizedInertia_isSymm _ (Matrix.isSymm_diagonal _)

/-! ### The arm under PD control (MLS Proposition 4.9) -/

/-- **The one-link arm as a manipulator model (MLS eq. (4.47), printed p. 190)**, with link mass
`![m]`, gravitational constant `g`, upward vector `up` (gravity is `−g • up`; for example a
pendulum in a vertical plane with `up = +y`) and further joint forces `Nₑ`. -/
def oneLinkModel (m r : ℝ) (I : Fin 3 → ℝ) (g : ℝ) (up : Vec3)
    (Ne : (Fin 1 → ℝ) → (Fin 1 → ℝ) → Fin 1 → ℝ) : ManipulatorModel 1 where
  chain := oneLinkArm m r I
  mass := ![m]
  gravity := g
  up := up
  jointForce := Ne

/-- A `1 × 1` matrix with a positive entry is positive definite. -/
private theorem oneLink_posDef_of_pos {a : ℝ} (ha : 0 < a) :
    (!![a] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  have h : (!![a] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal ![a] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [h]
  exact Matrix.PosDef.diagonal fun i => by fin_cases i; simpa using ha

/-- **MLS Proposition 4.9 (printed p. 193) as formalized, for the one-link arm, with every
hypothesis discharged.** With `m ≥ 0` and `I_z = I 2 > 0`, any `r`, any gravity data and further
joint forces, and `K_p = K_v = 1`, PD control with compensation of `N` makes the set point
`(θ_d, 0)` globally asymptotically stable at every `t₀ ≥ 0` (state `(θ, θ̇)`, sup norm). The
inertia `M = [I_z + m r²]` is constant, so the solution flow of the closed loop is constructed
(`ManipulatorModel.hasFlow_pdClosedLoop_of_const`) rather than assumed. -/
theorem oneLinkModel_globallyAsymptoticallyStableAt_pdCompensatedTorque {m r : ℝ}
    {I : Fin 3 → ℝ} (hm : 0 ≤ m) (hI : 0 < I 2) (g : ℝ) (up : Vec3)
    (Ne : (Fin 1 → ℝ) → (Fin 1 → ℝ) → Fin 1 → ℝ) (θd : Fin 1 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt
      ((oneLinkModel m r I g up Ne).field ((oneLinkModel m r I g up Ne).pdCompensatedTorque 1 1 θd))
      (θd, 0) t₀ := by
  have hM0 : ∀ q, (oneLinkModel m r I g up Ne).M q = !![I 2 + m * r ^ 2] := fun q =>
    oneLinkArm_massMatrix m r I q
  have hpos : 0 < I 2 + m * r ^ 2 := by positivity
  exact ManipulatorModel.globallyAsymptoticallyStableAt_pdCompensatedTorque_of_const _
    (oneLinkArm_linkInertia_isSymm m r I) hM0 (oneLink_posDef_of_pos hpos) Matrix.PosDef.one
    Matrix.PosDef.one θd ht₀

end RoboLean.Examples
