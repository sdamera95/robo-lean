import RoboLean.Kinematics.SerialChain
import RoboLean.Geometry.RigidVelocityComposition

/-!
# Spatial and body manipulator Jacobians

MLS Chapter 3, §4.1, printed pp. 115–118, eqs. (3.51)–(3.56). For a joint trajectory
`θ : ℝ → (Fin n → ℝ)` with an actual derivative `θ̇` in every coordinate, the spatial
velocity `V̂ˢ = ġ g⁻¹` of the forward kinematics `g = SerialChain.fk` is computed from the
actual `HasDerivAt` evidence of the homogeneous pose curve (`RigidTransform.spatialVelocity`)
and proved equal to `∑ᵢ θ̇ᵢ ξᵢ'`, with the columns `ξᵢ'` of eq. (3.54). The derivative is
not assumed; it is derived from the exponential and product rules.

Representation: a Jacobian is the function `Fin n → Twist` of its columns, in the library
twist order `(v, ω)`; Lean column `i` is the book's column `i + 1`. Columns are what
eqs. (3.54)–(3.55) define, the adjoint acts linearly on `Twist`, and joint rates act by
`∑ i, θ̇ i • J i`. The `6 × n` real matrix of p. 116 is the derived view
`SerialChain.spatialJacobianMatrix`, whose rows are `Twist.coordinates` (linear first).

MLS p. 116 takes the joint twists to be unit twists; the statements here hold for every
twist. They concern the coordinate model only, not numerical differentiation or a
physical robot.
-/

noncomputable section

open scoped Matrix.Norms.Operator

namespace RoboLean
namespace SerialChain

variable {n : ℕ}

/-- The spatial manipulator Jacobian, MLS eq. (3.54), p. 116, as its columns:
`ξᵢ' = Ad_{exp(ξ₁θ₁) ⋯ exp(ξᵢ₋₁θᵢ₋₁)} ξᵢ`. Lean column `i` uses the product of the first
`i` joint motions; column `0` is `ξ₁` itself. Twist order `(v, ω)`. -/
def spatialJacobian (c : SerialChain n) (θ : Fin n → ℝ) : Fin n → Twist :=
  fun i => Twist.adjoint ((c.jointMotions θ).take i).prod (c.twist i)

/-- The body manipulator Jacobian, MLS eq. (3.55), p. 117, as its columns:
`ξᵢ† = Ad⁻¹_{exp(ξᵢθᵢ) ⋯ exp(ξₙθₙ) g_st(0)} ξᵢ`. Lean column `i` uses the joint motions
from joint `i` to the tip; the inverse adjoint is the adjoint of the inverse transform
(MLS p. 56). Twist order `(v, ω)`. -/
def bodyJacobian (c : SerialChain n) (θ : Fin n → ℝ) : Fin n → Twist :=
  fun i => Twist.adjoint (((c.jointMotions θ).drop i).prod * c.toolRef)⁻¹ (c.twist i)

/-- The first column of the spatial Jacobian is the first joint twist, MLS eq. (3.54). -/
@[simp] theorem spatialJacobian_zero (c : SerialChain (n + 1)) (θ : Fin (n + 1) → ℝ) :
    c.spatialJacobian θ 0 = c.twist 0 := by
  simp [spatialJacobian]

/-- MLS p. 116: column `i` of the spatial Jacobian is the joint twist moved by the
displacement of the link that carries the joint axis, i.e. the joint twist "transformed to
the current manipulator configuration". `linkPOE` is the link displacement of the
sequential-motion semantics in `SerialChain`. -/
theorem spatialJacobian_eq_adjoint_linkPOE (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    c.spatialJacobian θ i = Twist.adjoint (c.linkPOE θ i.castSucc) (c.twist i) := rfl

/-- MLS p. 116: the `i`th column of the spatial Jacobian depends only on the joint
coordinates of the joints before `i` ("independent of the configuration of later joints
in the chain"). -/
theorem spatialJacobian_congr (c : SerialChain n) {θ φ : Fin n → ℝ} (i : Fin n)
    (h : ∀ j : Fin n, j < i → θ j = φ j) :
    c.spatialJacobian θ i = c.spatialJacobian φ i := by
  simp only [spatialJacobian]
  congr 2
  apply List.ext_getElem (by simp [jointMotions])
  intro k h₁ h₂
  have hk : k < i := by
    simp only [List.length_take, jointMotions, List.length_ofFn] at h₁
    omega
  simp only [List.getElem_take, jointMotions, List.getElem_ofFn]
  rw [h ⟨k, by omega⟩ (by simpa [Fin.lt_def] using hk)]

/-- The higher columns of the spatial Jacobian are the columns of the chain without its
base joint, moved by the base joint motion (MLS eq. (3.54), p. 116). -/
theorem spatialJacobian_succ (c : SerialChain (n + 1)) (θ : Fin (n + 1) → ℝ) (i : Fin n) :
    c.spatialJacobian θ i.succ =
      Twist.adjoint (Twist.exp (c.twist 0) (θ 0)) (c.tail.spatialJacobian (Fin.tail θ) i) := by
  simp only [spatialJacobian, jointMotions_succ, Fin.val_succ, List.take_succ_cons,
    List.prod_cons, Twist.adjoint_mul]
  rfl

private theorem sum_spatialJacobian_succ (c : SerialChain (n + 1)) (θ θ' : Fin (n + 1) → ℝ) :
    ∑ i, θ' i • c.spatialJacobian θ i =
      θ' 0 • c.twist 0 + Twist.adjoint (Twist.exp (c.twist 0) (θ 0))
        (∑ i, Fin.tail θ' i • c.tail.spatialJacobian (Fin.tail θ) i) := by
  rw [Fin.sum_univ_succ, spatialJacobian_zero]
  congr 1
  have hmap : Twist.adjoint (Twist.exp (c.twist 0) (θ 0))
      (∑ i, Fin.tail θ' i • c.tail.spatialJacobian (Fin.tail θ) i) =
      ∑ i, Twist.adjoint (Twist.exp (c.twist 0) (θ 0))
        (Fin.tail θ' i • c.tail.spatialJacobian (Fin.tail θ) i) :=
    map_sum (Twist.adjointLinearMap (Twist.exp (c.twist 0) (θ 0))) _ Finset.univ
  rw [hmap]
  apply Finset.sum_congr rfl
  intro i _
  change θ' i.succ • c.spatialJacobian θ i.succ =
    Twist.adjoint _ (θ' i.succ • c.tail.spatialJacobian (Fin.tail θ) i)
  rw [Twist.adjoint_smul, spatialJacobian_succ]

private theorem hasDerivAt_poe_toHomogeneous :
    ∀ {n : ℕ} (c : SerialChain n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ},
      (∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) →
      HasDerivAt (fun s => (c.poe (θ s)).toHomogeneous)
        ((∑ i, θ' i • c.spatialJacobian (θ t) i).hat * (c.poe (θ t)).toHomogeneous) t
  | 0, c, θ, θ', t, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Twist.hat_zero, zero_mul]
    have h : ∀ φ : Fin 0 → ℝ, c.poe φ = 1 := fun φ => by simp [poe, jointMotions]
    simp only [h]
    exact hasDerivAt_const t _
  | n + 1, c, θ, θ', t, hθ => by
    have ih := hasDerivAt_poe_toHomogeneous c.tail (θ := fun s => Fin.tail (θ s))
      (θ' := Fin.tail θ') (fun i => hθ i.succ)
    have he := Twist.hasDerivAt_exp_toHomogeneous (c.twist 0) (θ t 0)
    have h0 : HasDerivAt (fun s => (Twist.exp (c.twist 0) (θ s 0)).toHomogeneous)
        (θ' 0 • ((c.twist 0).hat * (Twist.exp (c.twist 0) (θ t 0)).toHomogeneous)) t :=
      HasDerivAt.scomp (g₁ := fun s => (Twist.exp (c.twist 0) s).toHomogeneous) t he (hθ 0)
    have hprod := RigidTransform.hasDerivAt_toHomogeneous_mul h0 ih
    have hpoe : ∀ φ : Fin (n + 1) → ℝ,
        c.poe φ = Twist.exp (c.twist 0) (φ 0) * c.tail.poe (Fin.tail φ) := by
      intro φ
      simp only [poe, jointMotions_succ, List.prod_cons]
    simp only [hpoe]
    convert hprod using 1
    rw [sum_spatialJacobian_succ, Twist.hat_add, Twist.hat_smul, Twist.hat_adjoint,
      RigidTransform.toHomogeneous_mul, ← RigidTransform.toHomogeneous_inv]
    set E := (Twist.exp (c.twist 0) (θ t 0)).toHomogeneous
    set Ei := ((Twist.exp (c.twist 0) (θ t 0))⁻¹).toHomogeneous
    have hEi : Ei * E = 1 := RigidTransform.toHomogeneous_inv_mul _
    simp only [add_mul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ei E, hEi, Matrix.one_mul]

/-- **MLS eqs. (3.51)–(3.54), pp. 115–116: the forward-kinematics derivative.** For a joint
trajectory with actual derivatives `θ̇ᵢ`, the homogeneous forward-kinematics pose has the
actual derivative `(∑ᵢ θ̇ᵢ ξᵢ')^ g_st(θ)`, i.e. `ġ = V̂ˢ g`. All real joint values are
allowed, with derivatives on the full real line. -/
theorem hasDerivAt_fk_toHomogeneous (c : SerialChain n) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) :
    HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous)
      ((∑ i, θ' i • c.spatialJacobian (θ t) i).hat * (c.fk (θ t)).toHomogeneous) t := by
  have h := (hasDerivAt_poe_toHomogeneous c hθ).mul_const c.toolRef.toHomogeneous
  simp only [fk, RigidTransform.toHomogeneous_mul, Matrix.mul_assoc] at h ⊢
  exact h

/-- **Ledger K10, MLS eqs. (3.51)–(3.54), pp. 115–116.** The actual spatial velocity
`V̂ˢ = ġ g⁻¹` of the forward-kinematics curve, computed from any derivative `D` of the
homogeneous pose with its `HasDerivAt` evidence, equals `Jˢ(θ) θ̇ = ∑ᵢ θ̇ᵢ ξᵢ'`. The
derivative exists by `hasDerivAt_fk_toHomogeneous`, so the hypothesis `hD` is
satisfiable. Twist order `(v, ω)`. -/
theorem spatialVelocity_fk (c : SerialChain n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t) :
    RigidTransform.spatialVelocity (fun s => c.fk (θ s)) D t hD =
      ∑ i, θ' i • c.spatialJacobian (θ t) i := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_spatialVelocity, hD.unique (c.hasDerivAt_fk_toHomogeneous hθ),
    Matrix.mul_assoc, ← RigidTransform.toHomogeneous_inv,
    RigidTransform.toHomogeneous_mul_inv, Matrix.mul_one]

/-- **Ledger K11, MLS eq. (3.56), p. 117.** Each spatial Jacobian column is the adjoint of
the forward-kinematics pose applied to the corresponding body Jacobian column,
`Jˢ(θ) = Ad_{g_st(θ)} Jᵇ(θ)`, for every real joint vector. -/
theorem spatialJacobian_eq_adjoint_bodyJacobian (c : SerialChain n) (θ : Fin n → ℝ)
    (i : Fin n) :
    c.spatialJacobian θ i = Twist.adjoint (c.fk θ) (c.bodyJacobian θ i) := by
  rw [spatialJacobian, bodyJacobian, ← Twist.adjoint_mul]
  congr 1
  rw [fk, poe, ← List.prod_take_mul_prod_drop (c.jointMotions θ) i]
  group

/-- The inverse form of MLS eq. (3.56), p. 117: `Jᵇ(θ) = Ad_{g_st(θ)⁻¹} Jˢ(θ)`. -/
theorem bodyJacobian_eq_adjoint_inv_spatialJacobian (c : SerialChain n) (θ : Fin n → ℝ)
    (i : Fin n) :
    c.bodyJacobian θ i = Twist.adjoint (c.fk θ)⁻¹ (c.spatialJacobian θ i) := by
  rw [spatialJacobian_eq_adjoint_bodyJacobian, Twist.adjoint_inv_adjoint]

/-- **MLS eq. (3.55), p. 117: the body Jacobian realizes the body velocity.** The actual body
velocity `V̂ᵇ = g⁻¹ ġ` of the forward-kinematics curve equals `Jᵇ(θ) θ̇ = ∑ᵢ θ̇ᵢ ξᵢ†`, for any
derivative `D` with its `HasDerivAt` evidence (satisfiable by
`hasDerivAt_fk_toHomogeneous`). -/
theorem bodyVelocity_fk (c : SerialChain n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => c.fk (θ s)) D t hD =
      ∑ i, θ' i • c.bodyJacobian (θ t) i := by
  have hs := RigidTransform.spatialVelocity_eq_adjoint_body hD
  rw [c.spatialVelocity_fk hθ hD] at hs
  have hb := congrArg (Twist.adjoint (c.fk (θ t))⁻¹) hs
  rw [Twist.adjoint_inv_adjoint] at hb
  rw [← hb]
  have hmap : Twist.adjoint (c.fk (θ t))⁻¹ (∑ i, θ' i • c.spatialJacobian (θ t) i) =
      ∑ i, Twist.adjoint (c.fk (θ t))⁻¹ (θ' i • c.spatialJacobian (θ t) i) :=
    map_sum (Twist.adjointLinearMap (c.fk (θ t))⁻¹) _ Finset.univ
  rw [hmap]
  apply Finset.sum_congr rfl
  intro i _
  rw [Twist.adjoint_smul, bodyJacobian_eq_adjoint_inv_spatialJacobian]

/-- **Ledger K12, MLS p. 117 (velocity of the tool-frame origin).** The actual derivative of
the tool position `p(θ(t))` is `V̂ˢ (p, 1) = ωˢ × p + vˢ`, with `(vˢ, ωˢ) = Jˢ(θ) θ̇`.
The translational part `vˢ` alone is not `ṗ`; the term `ωˢ × p` is included. -/
theorem hasDerivAt_fk_translation (c : SerialChain n) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) :
    HasDerivAt (fun s => (c.fk (θ s)).translation)
      (Vec3.cross (∑ i, θ' i • c.spatialJacobian (θ t) i).angular (c.fk (θ t)).translation +
        (∑ i, θ' i • c.spatialJacobian (θ t) i).linear) t := by
  have hD := c.hasDerivAt_fk_toHomogeneous hθ
  have h := RigidTransform.hasDerivAt_applyPoint_spatial hD 0
  rw [c.spatialVelocity_fk hθ hD] at h
  simpa [RigidTransform.applyPoint] using h

/-- **MLS p. 117, body form of the tool-origin velocity.** The derivative of the tool
position is `R_st(θ) vᵇ`, where `vᵇ` is the linear part of `Jᵇ(θ) θ̇` (MLS:
`ṗ = R_st Vᵇ (0, 1)`). -/
theorem hasDerivAt_fk_translation_body (c : SerialChain n) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) :
    HasDerivAt (fun s => (c.fk (θ s)).translation)
      ((c.fk (θ t)).rotation.act (∑ i, θ' i • c.bodyJacobian (θ t) i).linear) t := by
  have hD := c.hasDerivAt_fk_toHomogeneous hθ
  have h := RigidTransform.hasDerivAt_translation hD
  convert h using 1
  rw [← c.bodyVelocity_fk hθ hD, RigidTransform.bodyVelocity_linear, Rotation.act_inv_act]

/-- The spatial Jacobian as the real `6 × n` matrix of MLS p. 116 (`Jˢ(θ) ∈ ℝ^{6×n}`): column
`i` holds `Twist.coordinates` of `ξᵢ'`, linear coordinates first. -/
def spatialJacobianMatrix (c : SerialChain n) (θ : Fin n → ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin n) ℝ :=
  Matrix.of fun r i => (c.spatialJacobian θ i).coordinates r

/-- The matrix view of the spatial Jacobian acts on joint rates as the column form:
`Jˢ(θ) θ̇` in six coordinates (MLS p. 115, `Vˢ = Jˢ(θ) θ̇`). -/
theorem spatialJacobianMatrix_mulVec (c : SerialChain n) (θ θ' : Fin n → ℝ) :
    Matrix.mulVec (c.spatialJacobianMatrix θ) θ' =
      (∑ i, θ' i • c.spatialJacobian θ i).coordinates := by
  funext r
  rcases r with k | k <;>
    simp [spatialJacobianMatrix, Matrix.mulVec, dotProduct, Twist.coordinates,
      Prod.fst_sum, Prod.snd_sum, mul_comm]

end SerialChain
end RoboLean
