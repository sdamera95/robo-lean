import RoboLean.Dynamics.MassMatrixDerivative
import RoboLean.Examples.RigidTransform

/-!
# Dynamics of the idealized SCARA manipulator (MLS Example 4.4)

MLS Chapter 4, Example 4.4, printed pp. 177–178, Figure 4.6. Three revolute joints about
vertical axes and a vertical prismatic joint, with the printed joint twists
`ξ₁ = (0, 0, 0, 0, 0, 1)`, `ξ₂ = (l₁, 0, 0, 0, 0, 1)`, `ξ₃ = (l₁ + l₂, 0, 0, 0, 0, 1)`,
`ξ₄ = (0, 0, 1, 0, 0, 0)` (linear first): the arm lies along `+y` at `θ = 0`, with joint axes
through `(0, 0, 0)`, `(0, l₁, 0)` and `(0, l₁ + l₂, 0)`.

**Link frames (a modeling choice of this file).** MLS states only that the link frames are
"initially aligned with the base frame and located at the centers of mass of the links"
(p. 177). Their positions are read from Figure 4.6 and from the printed constants `α, β, γ, δ`
(p. 178): link 1's mass center at distance `r₁` from axis 1 and link 2's at distance `r₂` from
axis 2, along `+y`; links 3 and 4 have their mass centers on axis 3. The heights `h₁, …, h₄` of
the frames are free parameters; `M(θ)` does not depend on them. So
`g_{sl₁}(0) = (I, (0, r₁, h₁))`, `g_{sl₂}(0) = (I, (0, l₁ + r₂, h₂))`,
`g_{sl₃}(0) = (I, (0, l₁ + l₂, h₃))`, `g_{sl₄}(0) = (I, (0, l₁ + l₂, h₄))`, and the link inertias
are `[[mᵢ I, 0], [0, diag(I_xi, I_yi, I_zi)]]`.

Computed from the general constructions and compared with the book: the inertia matrix
`M(θ)` of eq. (4.19) equals the printed one (p. 177) with the printed `α, β, γ, δ` (p. 178); the
Christoffel Coriolis matrix of eq. (4.23) from the actual partial derivatives of `M` equals the
printed `C(θ, θ̇)` (p. 178); and with gravity along `−z` the gravity term `N = ∂V/∂θ` is the
printed `(0, 0, 0, m₄ g)` (p. 178). The transformed-inertia display of p. 177 is the subject of
the ledger N05 observation and is not restated here.

Notation: Lean joint `k` is the book's joint `k + 1` (`θ 1 = θ₂`, `θ 3 = θ₄`); the inertia
diagonals are `Iᵢ = ![I_xi, I_yi, I_zi]`, so `I_zi = Iᵢ 2`. This is one instance (a convention
check on one chain, not a general theorem); nothing here concerns a physical manipulator.
-/

noncomputable section

open Matrix

namespace RoboLean.Examples

/-! ### Private coordinate helpers -/

private theorem sc_norm_zAxis : ‖Rotation.zAxis‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [Rotation.zAxis, Fin.sum_univ_succ]

private theorem sc_zAxis_eq : Rotation.zAxis = vec 0 0 1 := rfl

private theorem sc_exp_zAxis_act (t x y z : ℝ) :
    (Rotation.exp Rotation.zAxis t).act (vec x y z) =
      vec (Real.cos t * x - Real.sin t * y) (Real.sin t * x + Real.cos t * y) z := by
  change (Rotation.zRotation t).act (vec x y z) = _
  ext i
  fin_cases i <;>
    simp [Rotation.act_apply, Rotation.zRotation_val, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, vec]
  all_goals ring

private theorem sc_vec_add (a b c a' b' c' : ℝ) :
    vec a b c + vec a' b' c' = vec (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem sc_vec_sub (a b c a' b' c' : ℝ) :
    vec a b c - vec a' b' c' = vec (a - a') (b - b') (c - c') := by
  ext i
  fin_cases i <;> simp [vec]

private theorem sc_vec_eq {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') :
    vec a b c = vec a' b' c' := by
  rw [ha, hb, hc]

private theorem sc_translation_applyPoint (p x : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyPoint x = x + p := by
  simp [RigidTransform.applyPoint]

private theorem sc_translation_applyVector (p v : Vec3) :
    (⟨1, p⟩ : RigidTransform).applyVector v = v := by
  simp [RigidTransform.applyVector]

private theorem sc_exp_revolute_applyVector (ω q v : Vec3) (t : ℝ) :
    (Twist.exp (Twist.revolute ω q) t).applyVector v = (Rotation.exp ω t).act v := by
  rw [RigidTransform.applyVector, Twist.exp_rotation]
  rfl

private theorem sc_inv_applyPoint_of {g : RigidTransform} {x y : Vec3}
    (h : g.applyPoint x = y) : g⁻¹.applyPoint y = x := by
  rw [← h, RigidTransform.inv_applyPoint_applyPoint]

private theorem sc_inv_applyVector_of {g : RigidTransform} {v w : Vec3}
    (h : g.applyVector v = w) : g⁻¹.applyVector w = v := by
  rw [← h, ← RigidTransform.mul_applyVector, inv_mul_cancel, RigidTransform.one_applyVector]

/-- Six coordinates (linear first) of the revolute twist `(-ω × q, ω)` (MLS p. 87). -/
private theorem sc_revolute_coordinates (a b c x y z : ℝ) :
    (Twist.revolute (vec a b c) (vec x y z)).coordinates =
      Sum.elim ![c * y - b * z, a * z - c * x, b * x - a * y] ![a, b, c] := by
  funext r
  rcases r with i | i <;> fin_cases i <;>
    simp [Twist.coordinates, Twist.revolute, Vec3.cross, cross_apply, vec]

/-- The generalized-inertia pairing (MLS eq. (4.9), p. 162) of two six-vectors written by their
linear and angular coordinates, for a diagonal inertia tensor. -/
private theorem sc_pairing (m : ℝ) (I : Fin 3 → ℝ) (a b c d e f a' b' c' d' e' f' : ℝ) :
    (Sum.elim ![a, b, c] ![d, e, f] : Fin 3 ⊕ Fin 3 → ℝ) ⬝ᵥ
      (RigidBody.generalizedInertia m (Matrix.diagonal I) *ᵥ Sum.elim ![a', b', c'] ![d', e', f']) =
      m * (a * a' + b * b' + c * c') + (I 0 * d * d' + I 1 * e * e' + I 2 * f * f') := by
  rw [RigidBody.dotProduct_generalizedInertia_mulVec]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.mulVec_diagonal, Function.comp_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem sc_val_three : ((3 : Fin 4) : ℕ) = 3 := rfl

private theorem sc_smul_zAxis (t : ℝ) : t • Rotation.zAxis = vec 0 0 t := by
  ext i
  fin_cases i <;> simp [Rotation.zAxis, vec]

/-- Six coordinates (linear first) of the prismatic twist `(v, 0)` (MLS p. 87). -/
private theorem sc_prismatic_coordinates (a b c : ℝ) :
    (Twist.prismatic (vec a b c)).coordinates = Sum.elim ![a, b, c] ![0, 0, 0] := by
  funext r
  rcases r with i | i <;> fin_cases i <;> simp [Twist.coordinates, Twist.prismatic, vec]

private theorem sc_inner_zAxis_vec (a b c : ℝ) : inner ℝ Rotation.zAxis (vec a b c) = c := by
  simp [Rotation.zAxis, vec, PiLp.inner_apply, Fin.sum_univ_three]

private theorem sc_translation_eq_applyPoint (g : RigidTransform) :
    g.translation = g.applyPoint (vec 0 0 0) := by
  have : vec 0 0 0 = 0 := by
    ext i
    fin_cases i <;> rfl
  simp [RigidTransform.applyPoint, this]

/-- **The joints of MLS Example 4.4 (p. 177, Figure 4.6)**, base-frame twists at `θ = 0`: three
revolute joints about `+z` through `(0, 0, 0)`, `(0, l₁, 0)` and `(0, l₁ + l₂, 0)`, and a
prismatic joint along `+z`. The tool pose is not used by the dynamics and is set to the
identity. Lean joint `k` is the book's joint `k + 1`. -/
def scaraChain (l₁ l₂ : ℝ) : SerialChain 4 where
  twist := ![Twist.revolute Rotation.zAxis (vec 0 0 0), Twist.revolute Rotation.zAxis (vec 0 l₁ 0),
    Twist.revolute Rotation.zAxis (vec 0 (l₁ + l₂) 0), Twist.prismatic Rotation.zAxis]
  toolRef := 1

/-- **The joint twists of MLS Example 4.4 as printed on p. 177**, in six coordinates (linear
first): `ξ₁ = (0, 0, 0, 0, 0, 1)`, `ξ₂ = (l₁, 0, 0, 0, 0, 1)`, `ξ₃ = (l₁ + l₂, 0, 0, 0, 0, 1)`,
`ξ₄ = (0, 0, 1, 0, 0, 0)` (Lean twist `k` is the book's `ξ_{k+1}`). -/
theorem scaraChain_twist_coordinates (l₁ l₂ : ℝ) :
    ((scaraChain l₁ l₂).twist 0).coordinates = Sum.elim ![0, 0, 0] ![0, 0, 1] ∧
      ((scaraChain l₁ l₂).twist 1).coordinates = Sum.elim ![l₁, 0, 0] ![0, 0, 1] ∧
      ((scaraChain l₁ l₂).twist 2).coordinates = Sum.elim ![l₁ + l₂, 0, 0] ![0, 0, 1] ∧
      ((scaraChain l₁ l₂).twist 3).coordinates = Sum.elim ![0, 0, 1] ![0, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext r <;> rcases r with i | i <;> fin_cases i <;>
    simp [scaraChain, Twist.coordinates, Twist.revolute, Twist.prismatic, Vec3.cross, cross_apply,
      Rotation.zAxis, vec]

/-- **The SCARA manipulator of MLS Example 4.4 (pp. 177–178) with inertial data.** Link frames
aligned with the base frame at `θ = 0`, at the mass centers `(0, r₁, h₁)`, `(0, l₁ + r₂, h₂)`,
`(0, l₁ + l₂, h₃)`, `(0, l₁ + l₂, h₄)` (positions read from Figure 4.6 and the printed `α, β, γ`;
see the module docstring), with generalized inertias `[[mᵢ I, 0], [0, diag(Iᵢ)]]`
(MLS eq. (4.9)). -/
def scaraArm (m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ : ℝ) (I₁ I₂ I₃ I₄ : Fin 3 → ℝ) :
    InertialChain 4 where
  chain := scaraChain l₁ l₂
  linkRef := ![⟨1, vec 0 r₁ h₁⟩, ⟨1, vec 0 (l₁ + r₂) h₂⟩, ⟨1, vec 0 (l₁ + l₂) h₃⟩,
    ⟨1, vec 0 (l₁ + l₂) h₄⟩]
  linkInertia := ![RigidBody.generalizedInertia m₁ (Matrix.diagonal I₁),
    RigidBody.generalizedInertia m₂ (Matrix.diagonal I₂),
    RigidBody.generalizedInertia m₃ (Matrix.diagonal I₃),
    RigidBody.generalizedInertia m₄ (Matrix.diagonal I₄)]

/-- MLS p. 178: `α = I_z1 + r₁² m₁ + l₁² m₂ + l₁² m₃ + l₁² m₄`. -/
def scaraAlpha (m₁ m₂ m₃ m₄ r₁ l₁ : ℝ) (I₁ : Fin 3 → ℝ) : ℝ :=
  I₁ 2 + r₁ ^ 2 * m₁ + l₁ ^ 2 * m₂ + l₁ ^ 2 * m₃ + l₁ ^ 2 * m₄

/-- MLS p. 178: `β = I_z2 + I_z3 + I_z4 + l₂² m₃ + l₂² m₄ + m₂ r₂²`. -/
def scaraBeta (m₂ m₃ m₄ r₂ l₂ : ℝ) (I₂ I₃ I₄ : Fin 3 → ℝ) : ℝ :=
  I₂ 2 + I₃ 2 + I₄ 2 + l₂ ^ 2 * m₃ + l₂ ^ 2 * m₄ + m₂ * r₂ ^ 2

/-- MLS p. 178: `γ = l₁ l₂ m₃ + l₁ l₂ m₄ + l₁ m₂ r₂`. -/
def scaraGamma (m₂ m₃ m₄ r₂ l₁ l₂ : ℝ) : ℝ :=
  l₁ * l₂ * m₃ + l₁ * l₂ * m₄ + l₁ * m₂ * r₂

/-- MLS p. 178: `δ = I_z3 + I_z4`. -/
def scaraDelta (I₃ I₄ : Fin 3 → ℝ) : ℝ :=
  I₃ 2 + I₄ 2

variable (m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ : ℝ) (I₁ I₂ I₃ I₄ : Fin 3 → ℝ)

/-- Joint 1 in the frame of link 1 (MLS p. 177): the vertical axis through `(0, -r₁, -h₁)`. -/
private theorem sc_jac_zero_zero (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 0 θ 0 =
      Twist.revolute (vec 0 0 1)
        (vec 0 (-r₁) (-h₁)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, sc_translation_applyPoint, hz, sc_vec_add, sc_vec_sub,
        sc_exp_zAxis_act]
    apply sc_vec_eq <;> ring

/-- Joint 1 in the frame of link 2 (MLS p. 177). -/
private theorem sc_jac_one_zero (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 1 θ 0 =
      Twist.revolute (vec 0 0 1)
        (vec (-(l₁ * Real.sin (θ 1))) (-(Real.cos (θ 1) * l₁) - r₂)
          (-h₂)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_one,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, sc_translation_applyPoint, hz, sc_vec_add, sc_vec_sub,
        sc_exp_zAxis_act]
    apply sc_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 2 in the frame of link 2 (MLS p. 177): the vertical axis through `(0, -r₂, -h₂)`. -/
private theorem sc_jac_one_one (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 1 θ 1 =
      Twist.revolute (vec 0 0 1)
        (vec 0 (-r₂) (-h₂)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
      Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one,
      Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, sc_translation_applyPoint, hz, sc_vec_add, sc_vec_sub,
        sc_exp_zAxis_act]
    apply sc_vec_eq <;> ring

/-- Joint 1 in the frame of link 3 (MLS p. 177). -/
private theorem sc_jac_two_zero (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 2 θ 0 =
      Twist.revolute (vec 0 0 1)
        (vec (-(Real.cos (θ 1) * l₁ * Real.sin (θ 2)) - Real.cos (θ 2) * l₁ * Real.sin (θ 1) -
          l₂ * Real.sin (θ 2))
          (-(Real.cos (θ 1) * Real.cos (θ 2) * l₁) - Real.cos (θ 2) * l₂ +
          l₁ * Real.sin (θ 1) * Real.sin (θ 2)) (-h₃)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_two,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, sc_translation_applyPoint, hz, sc_vec_add, sc_vec_sub,
        sc_exp_zAxis_act]
    apply sc_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 2 in the frame of link 3 (MLS p. 177). -/
private theorem sc_jac_two_one (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 2 θ 1 =
      Twist.revolute (vec 0 0 1)
        (vec (-(l₂ * Real.sin (θ 2))) (-(Real.cos (θ 2) * l₂)) (-h₃)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one, Fin.val_two,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
      Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, sc_translation_applyPoint, hz, sc_vec_add, sc_vec_sub,
        sc_exp_zAxis_act]
    apply sc_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 3 in the frame of link 3 (MLS p. 177): the vertical axis through `(0, 0, -h₃)`. -/
private theorem sc_jac_two_two (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 2 θ 2 =
      Twist.revolute (vec 0 0 1)
        (vec 0 0 (-h₃)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_two,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
      Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, sc_translation_applyPoint, hz, sc_vec_add, sc_vec_sub,
        sc_exp_zAxis_act]
    apply sc_vec_eq <;> ring

/-- Joint 1 in the frame of link 4 (MLS p. 177). -/
private theorem sc_jac_three_zero (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 3 θ 0 =
      Twist.revolute (vec 0 0 1)
        (vec (-(Real.cos (θ 1) * l₁ * Real.sin (θ 2)) - Real.cos (θ 2) * l₁ * Real.sin (θ 1) -
          l₂ * Real.sin (θ 2))
          (-(Real.cos (θ 1) * Real.cos (θ 2) * l₁) - Real.cos (θ 2) * l₂ +
          l₁ * Real.sin (θ 1) * Real.sin (θ 2)) (-h₄ - θ 3)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, sc_val_three,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue, Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, Twist.exp_prismatic, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, Twist.exp_prismatic, sc_translation_applyPoint, hz,
        sc_smul_zAxis, sc_vec_add, sc_vec_sub, sc_exp_zAxis_act]
    apply sc_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 2 in the frame of link 4 (MLS p. 177). -/
private theorem sc_jac_three_one (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 3 θ 1 =
      Twist.revolute (vec 0 0 1)
        (vec (-(l₂ * Real.sin (θ 2))) (-(Real.cos (θ 2) * l₂)) (-h₄ - θ 3)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_one, sc_val_three,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
      Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, Twist.exp_prismatic, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, Twist.exp_prismatic, sc_translation_applyPoint, hz,
        sc_smul_zAxis, sc_vec_add, sc_vec_sub, sc_exp_zAxis_act]
    apply sc_vec_eq <;> first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Joint 3 in the frame of link 4 (MLS p. 177). -/
private theorem sc_jac_three_two (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 3 θ 2 =
      Twist.revolute (vec 0 0 1)
        (vec 0 0 (-h₄ - θ 3)) := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ (by decide)]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_two, sc_val_three,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
      Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Twist.adjoint_revolute]
  congr 1
  · apply sc_inv_applyVector_of
    simp only [RigidTransform.mul_applyVector, Twist.exp_prismatic, sc_translation_applyVector,
        sc_exp_revolute_applyVector, sc_exp_zAxis_act]
    simp only [sc_zAxis_eq]
    apply sc_vec_eq <;> ring
  · apply sc_inv_applyPoint_of
    simp only [RigidTransform.mul_applyPoint, Twist.exp_prismatic, sc_translation_applyPoint, hz,
        sc_smul_zAxis, sc_vec_add, sc_vec_sub, sc_exp_zAxis_act]
    apply sc_vec_eq <;> ring

/-- Joint 4 in the frame of link 4 (MLS p. 177): the vertical translation
`(0, 0, 1, 0, 0, 0)`. -/
private theorem sc_jac_three_three (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 3 θ 3 =
      Twist.prismatic (vec 0 0 1) := by
  rw [InertialChain.linkBodyJacobian_of_le _ _ _ le_rfl]
  simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, sc_val_three,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.prod_cons,
      List.prod_nil, mul_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
      Fin.reduceSucc]
  simp only [scaraArm, scaraChain, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Twist.adjoint_prismatic]
  congr 1
  apply sc_inv_applyVector_of
  simp only [RigidTransform.mul_applyVector, Twist.exp_prismatic, sc_translation_applyVector]
  simp only [sc_zAxis_eq]

private theorem sc_jac_zero_one (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 0 θ 1 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem sc_jac_zero_two (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 0 θ 2 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem sc_jac_zero_three (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 0 θ 3 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem sc_jac_one_two (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 1 θ 2 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem sc_jac_one_three (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 1 θ 3 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

private theorem sc_jac_two_three (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkBodyJacobian 2 θ 3 = 0 :=
  InertialChain.linkBodyJacobian_of_lt _ _ _ (by decide)

/-- **The inertia matrix of MLS Example 4.4, as printed on p. 177.** The general construction
`M(θ) = ∑ Jᵢᵀ 𝓜ᵢ Jᵢ` of eq. (4.19) gives, at every configuration,
`M(θ) = [[α + β + 2γ c₂, β + γ c₂, δ, 0], [β + γ c₂, β, δ, 0], [δ, δ, δ, 0], [0, 0, 0, m₄]]`
with the printed `α, β, γ, δ` of p. 178 and `c₂ = cos θ₂`. -/
theorem scaraArm_massMatrix (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).massMatrix θ =
      !![scaraAlpha m₁ m₂ m₃ m₄ r₁ l₁ I₁ + scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄ +
            2 * scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.cos (θ 1),
          scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄ + scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.cos (θ 1),
          scaraDelta I₃ I₄, 0;
        scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄ + scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.cos (θ 1),
          scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄, scaraDelta I₃ I₄, 0;
        scaraDelta I₃ I₄, scaraDelta I₃ I₄, scaraDelta I₃ I₄, 0;
        0, 0, 0, m₄] := by
  have hM0 : (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkInertia 0 =
      RigidBody.generalizedInertia m₁ (Matrix.diagonal I₁) := rfl
  have hM1 : (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkInertia 1 =
      RigidBody.generalizedInertia m₂ (Matrix.diagonal I₂) := rfl
  have hM2 : (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkInertia 2 =
      RigidBody.generalizedInertia m₃ (Matrix.diagonal I₃) := rfl
  have hM3 : (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkInertia 3 =
      RigidBody.generalizedInertia m₄ (Matrix.diagonal I₄) := rfl
  ext i j
  rw [InertialChain.massMatrix_apply, Fin.sum_univ_four, hM0, hM1, hM2, hM3]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, sc_jac_zero_zero,
        sc_jac_one_zero, sc_jac_one_one, sc_jac_two_zero, sc_jac_two_one, sc_jac_two_two,
        sc_jac_three_zero, sc_jac_three_one, sc_jac_three_two, sc_jac_three_three, sc_jac_zero_one,
        sc_jac_zero_two, sc_jac_zero_three, sc_jac_one_two, sc_jac_one_three, sc_jac_two_three,
        sc_revolute_coordinates, sc_prismatic_coordinates, sc_pairing, Twist.coordinates_zero,
        Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct, Matrix.of_apply, Matrix.cons_val,
        scaraAlpha, scaraBeta, scaraGamma, scaraDelta]
  all_goals first | ring1 | (ring_nf; simp only [Real.cos_sq']; ring_nf)

/-- Fréchet derivatives of the entries of the printed inertia matrix of MLS Example 4.4
(p. 177) at `θ`: only `θ₂ = θ 1` enters, with `∂M₁₁/∂θ₂ = -2γ s₂` and
`∂M₁₂/∂θ₂ = ∂M₂₁/∂θ₂ = -γ s₂`. -/
private def scMassDeriv (m₂ m₃ m₄ r₂ l₁ l₂ : ℝ) (θ : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → ((Fin 4 → ℝ) →L[ℝ] ℝ) :=
  let γs := scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.sin (θ 1)
  let P₁ : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  ![![(-(2 * γs)) • P₁, (-γs) • P₁, 0, 0], ![(-γs) • P₁, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- The entries of the inertia matrix of `scaraArm` have the Fréchet derivatives `scMassDeriv`
at every configuration (from `scaraArm_massMatrix`, MLS p. 177). -/
private theorem sc_hasFDerivAt_massMatrix (θ : Fin 4 → ℝ) (i j : Fin 4) :
    HasFDerivAt
      (fun q => (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).massMatrix q i j)
      (scMassDeriv m₂ m₃ m₄ r₂ l₁ l₂ θ i j) θ := by
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 1 θ
  simp only [scaraArm_massMatrix]
  fin_cases i <;> fin_cases j
  · refine ((hc.cos.const_mul (2 * scaraGamma m₂ m₃ m₄ r₂ l₁ l₂)).const_add
      (scaraAlpha m₁ m₂ m₃ m₄ r₁ l₁ I₁ + scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄)).congr_fderiv ?_
    ext v
    simp [scMassDeriv]
    ring
  · refine ((hc.cos.const_mul (scaraGamma m₂ m₃ m₄ r₂ l₁ l₂)).const_add
      (scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄)).congr_fderiv ?_
    ext v
    simp [scMassDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (scaraDelta I₃ I₄) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · refine ((hc.cos.const_mul (scaraGamma m₂ m₃ m₄ r₂ l₁ l₂)).const_add
      (scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄)).congr_fderiv ?_
    ext v
    simp [scMassDeriv]
    ring
  · exact hasFDerivAt_const (𝕜 := ℝ) (scaraBeta m₂ m₃ m₄ r₂ l₂ I₂ I₃ I₄) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (scaraDelta I₃ I₄) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (scaraDelta I₃ I₄) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (scaraDelta I₃ I₄) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (scaraDelta I₃ I₄) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ
  · exact hasFDerivAt_const (𝕜 := ℝ) m₄ θ

/-- **The Coriolis matrix of MLS Example 4.4, as printed on p. 178.** The Christoffel Coriolis
matrix of eq. (4.23), computed from the actual partial derivatives
`InertialChain.massMatrixDeriv` of the general `M(θ)`, is
`[[−γ s₂ θ̇₂, −γ s₂ (θ̇₁ + θ̇₂), 0, 0], [γ s₂ θ̇₁, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]`
with `s₂ = sin θ₂` (`θ̇ = θ'`, Lean index `k` for the book's `k + 1`). -/
theorem scaraArm_coriolisMatrix (θ θ' : Fin 4 → ℝ) :
    Christoffel.coriolisMatrix (Christoffel.partials
        ((scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).massMatrixDeriv θ)) θ' =
      !![-scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.sin (θ 1) * θ' 1,
          -scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.sin (θ 1) * (θ' 0 + θ' 1), 0, 0;
        scaraGamma m₂ m₃ m₄ r₂ l₁ l₂ * Real.sin (θ 1) * θ' 0, 0, 0, 0;
        0, 0, 0, 0;
        0, 0, 0, 0] := by
  have hD : (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).massMatrixDeriv θ =
      scMassDeriv m₂ m₃ m₄ r₂ l₁ l₂ θ := by
    funext i j
    exact (sc_hasFDerivAt_massMatrix m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄ θ i j).fderiv
  rw [hD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials, scMassDeriv,
      Fin.sum_univ_four, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-- The heights (with `up = +z`) of the link frames of `scaraArm` (MLS p. 178): the revolute
joints turn about vertical axes, so only the prismatic joint `θ₄ = θ 3` moves a frame
vertically. -/
private theorem sc_linkHeight (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkHeight Rotation.zAxis 0 θ = h₁ ∧
      (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkHeight Rotation.zAxis 1 θ =
        h₂ ∧
      (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkHeight Rotation.zAxis 2 θ =
        h₃ ∧
      (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).linkHeight Rotation.zAxis 3 θ =
        h₄ + θ 3 := by
  have hz : ∀ (q : Vec3) t x, (Twist.exp (Twist.revolute Rotation.zAxis q) t).applyPoint x =
      (Rotation.exp Rotation.zAxis t).act (x - q) + q :=
    fun q => Twist.exp_revolute_applyPoint _ q sc_norm_zAxis
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [InertialChain.linkHeight, InertialChain.linkPose_eq, sc_translation_eq_applyPoint]
    simp only [SerialChain.jointMotions, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_one,
        Fin.val_two, sc_val_three, List.take_succ_cons, List.take_zero, List.prod_cons,
        List.prod_nil, mul_one, RigidTransform.mul_applyPoint, Fin.isValue, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, Fin.reduceSucc]
    simp only [scaraArm, scaraChain, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Twist.exp_prismatic,
        sc_translation_applyPoint, hz, sc_smul_zAxis, sc_vec_add, sc_vec_sub, sc_exp_zAxis_act,
        sc_inner_zAxis_vec]
    ring

/-- **The potential energy of MLS Example 4.4 (p. 178: "only `θ₄` affects the potential
energy")**, with link masses `![m₁, m₂, m₃, m₄]`, gravitational constant `g` and `up = +z`:
`V(θ) = m₁ g h₁ + m₂ g h₂ + m₃ g h₃ + m₄ g (h₄ + θ₄)`. -/
theorem scaraArm_potentialEnergy (g : ℝ) (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).potentialEnergy ![m₁, m₂, m₃, m₄]
        g Rotation.zAxis θ =
      m₁ * g * h₁ + m₂ * g * h₂ + m₃ * g * h₃ + m₄ * g * (h₄ + θ 3) := by
  obtain ⟨h0, h1, h2, h3⟩ := sc_linkHeight m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄ θ
  rw [InertialChain.potentialEnergy, Fin.sum_univ_four, h0, h1, h2, h3]
  simp

/-- **The gravity term of MLS Example 4.4, as printed on p. 178:** `N = ∂V/∂θ = (0, 0, 0, m₄ g)`
for the potential of `scaraArm_potentialEnergy` (`up = +z`), an instance of the general gravity
term `InertialChain.gravityTerm` (MLS p. 174). -/
theorem scaraArm_gravityTerm (g : ℝ) (θ : Fin 4 → ℝ) :
    (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).gravityTerm ![m₁, m₂, m₃, m₄] g
        Rotation.zAxis θ = ![0, 0, 0, m₄ * g] := by
  have hV : (scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).potentialEnergy
      ![m₁, m₂, m₃, m₄] g Rotation.zAxis =
      fun q => m₁ * g * h₁ + m₂ * g * h₂ + m₃ * g * h₃ + m₄ * g * (h₄ + q 3) := by
    funext q
    exact scaraArm_potentialEnergy m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄ g q
  have hc := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 3 θ
  have hd := ((hc.const_add h₄).const_mul (m₄ * g)).const_add
    (m₁ * g * h₁ + m₂ * g * h₂ + m₃ * g * h₃)
  rw [← hV] at hd
  rw [InertialChain.gravityTerm_eq_gradient _ hd]
  funext i
  fin_cases i <;> simp [Lagrangian.gradient]

/-- **MLS Lemma 4.2(1) for the SCARA arm.** With positive masses and positive principal
moments of every link, the inertia matrix of the arm is positive definite at every
configuration: an instance of `InertialChain.massMatrix_posDef_of_joints` with three revolute
joints and one prismatic joint (MLS p. 87). -/
theorem scaraArm_massMatrix_posDef (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃) (hm₄ : 0 < m₄)
    (hI₁ : ∀ i, 0 < I₁ i) (hI₂ : ∀ i, 0 < I₂ i) (hI₃ : ∀ i, 0 < I₃ i) (hI₄ : ∀ i, 0 < I₄ i)
    (θ : Fin 4 → ℝ) :
    ((scaraArm m₁ m₂ m₃ m₄ r₁ r₂ l₁ l₂ h₁ h₂ h₃ h₄ I₁ I₂ I₃ I₄).massMatrix θ).PosDef := by
  refine InertialChain.massMatrix_posDef_of_joints _ (fun k => ?_) (fun j => ?_) θ
  · fin_cases k
    · exact RigidBody.generalizedInertia_posDef hm₁ (Matrix.PosDef.diagonal hI₁)
    · exact RigidBody.generalizedInertia_posDef hm₂ (Matrix.PosDef.diagonal hI₂)
    · exact RigidBody.generalizedInertia_posDef hm₃ (Matrix.PosDef.diagonal hI₃)
    · exact RigidBody.generalizedInertia_posDef hm₄ (Matrix.PosDef.diagonal hI₄)
  · fin_cases j
    · exact Or.inl ⟨Rotation.zAxis, vec 0 0 0, sc_norm_zAxis, rfl⟩
    · exact Or.inl ⟨Rotation.zAxis, vec 0 l₁ 0, sc_norm_zAxis, rfl⟩
    · exact Or.inl ⟨Rotation.zAxis, vec 0 (l₁ + l₂) 0, sc_norm_zAxis, rfl⟩
    · exact Or.inr ⟨Rotation.zAxis, sc_norm_zAxis, rfl⟩

end RoboLean.Examples
