import Mathlib.Analysis.Calculus.Deriv.Prod
import RoboLean.Kinematics.Jacobian
import RoboLean.Kinematics.SerialChainSmooth

/-!
# The manipulator Jacobians as derivatives of the forward kinematics

MLS Chapter 3, §4.1, printed pp. 115–117, eqs. (3.51)–(3.55). The book differentiates the forward
kinematics `g_st : ℝⁿ → SE(3)` as a matrix-valued function of `θ`: along a joint path,
`V̂ˢ = ġ g⁻¹ = Σᵢ (∂g/∂θᵢ) g⁻¹ θ̇ᵢ` "applying the chain rule" (eq. (3.51)), the spatial Jacobian
has the columns `(∂g/∂θᵢ g⁻¹)^∨` (eq. (3.52)), and for the product of exponentials
`(∂g/∂θᵢ g⁻¹)^∨ = Ad_{e^{ξ̂₁θ₁} ⋯ e^{ξ̂ᵢ₋₁θᵢ₋₁}} ξᵢ` (eqs. (3.53)–(3.54)); the body Jacobian
(3.55) is obtained by "a calculation similar".

**Formalized.** For every chain `c : SerialChain n` (arbitrary twists, real joint coordinates) and
every joint vector `θ`, with `g = c.fk θ` as its homogeneous matrix:

* each entry of `φ ↦ g(φ)` has the Fréchet derivative at `θ` whose value on a direction `v` is the
  entry of `(Jˢ(θ) v)^ g` (`SerialChain.hasFDerivAt_fk_toHomogeneous_apply`,
  `SerialChain.fderiv_fk_toHomogeneous_apply`), equivalently of `g (Jᵇ(θ) v)^`
  (`SerialChain.fderiv_fk_toHomogeneous_apply_body`), where `Jˢ(θ) v = Σᵢ vᵢ ξᵢ'` and
  `Jᵇ(θ) v = Σᵢ vᵢ ξᵢ†`;
* the matrix of partial derivatives `∂g/∂θᵢ` (`SerialChain.fkPartial`, the derivative in the
  coordinate direction `i`, entry by entry) is `ξ̂ᵢ' g` (`SerialChain.fkPartial_eq`), so
  `∂g/∂θᵢ g⁻¹ = (Ad_{e^{ξ̂₁θ₁} ⋯ e^{ξ̂ᵢ₋₁θᵢ₋₁}} ξᵢ)^` (eq. (3.53),
  `SerialChain.fkPartial_mul_inv`), the columns of the spatial Jacobian are
  `(∂g/∂θᵢ g⁻¹)^∨` (eq. (3.52), `SerialChain.spatialJacobian_eq_vee_fkPartial_mul_inv`) and those
  of the body Jacobian are `(g⁻¹ ∂g/∂θᵢ)^∨` (eq. (3.55),
  `SerialChain.bodyJacobian_eq_vee_inv_mul_fkPartial`);
* the chain rule (3.51): along a joint path with rates `θ̇` the entries of `g(θ(t))` have the
  derivative `Σᵢ θ̇ᵢ ∂g/∂θᵢ` (`SerialChain.hasDerivAt_fk_toHomogeneous_apply_comp`), which is the
  derivative `(Jˢ(θ) θ̇)^ g` of the trajectory form (`SerialChain.sum_smul_fkPartial`), and the
  spatial velocity is `Σᵢ (∂g/∂θᵢ g⁻¹) θ̇ᵢ` (`SerialChain.hat_spatialVelocity_fk_eq_sum`).

Conventions: the joint space `Fin n → ℝ` carries Mathlib's sup norm and the Fréchet derivative is
taken entry by entry of the `4 × 4` homogeneous matrix, so no norm on matrices enters those
statements; the trajectory statement reuses the matrix-valued `HasDerivAt` of
`hasDerivAt_fk_toHomogeneous` (the library's `L^∞` operator norm, whose topology is the product
topology); twists are in the library order `(v, ω)`; Lean column `i` is the book's column `i + 1`. MLS p. 116 takes unit
twists; nothing here needs it. Statements about the coordinate model only.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace SerialChain

variable {n : ℕ}

/-- The wedge map as a linear map `Twist →ₗ[ℝ] HomogeneousMatrix` (MLS eq. (2.31), p. 41). -/
private def hatLinear : Twist →ₗ[ℝ] HomogeneousMatrix where
  toFun := Twist.hat
  map_add' := Twist.hat_add
  map_smul' := Twist.hat_smul

/-- The wedge of a combination of twists times a matrix, entry by entry. -/
private theorem hat_sum_smul_mul_apply (v : Fin n → ℝ) (ξ : Fin n → Twist) (G : HomogeneousMatrix)
    (a b : HomogeneousIndex) :
    ((∑ i, v i • ξ i).hat * G) a b = ∑ i, v i * ((ξ i).hat * G) a b := by
  have h : (∑ i, v i • ξ i).hat = ∑ i, v i • (ξ i).hat := by
    change hatLinear (∑ i, v i • ξ i) = ∑ i, v i • hatLinear (ξ i)
    rw [map_sum]
    simp only [map_smul]
  rw [h, Finset.sum_mul, Matrix.sum_apply]
  simp only [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

/-- The straight joint path `s ↦ θ + s v` has derivative `v`, coordinate by coordinate. -/
private theorem hasDerivAt_line_apply (θ v : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun s : ℝ => (θ + s • v) i) (v i) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (θ i)

/-- **The entries of the forward kinematics are differentiable in `θ` (MLS eq. (3.3), p. 87,
differentiated on p. 115).** Every entry of the homogeneous matrix of `g_st(θ)` is a differentiable
function of `θ ∈ ℝⁿ`. -/
theorem differentiable_fk_toHomogeneous_apply (c : SerialChain n) (a b : HomogeneousIndex) :
    Differentiable ℝ fun θ : Fin n → ℝ => (c.fk θ).toHomogeneous a b :=
  (c.contDiff_fk_toHomogeneous a b (k := 1)).differentiable one_ne_zero

/-- **The derivative of the forward kinematics in a direction, spatial form (MLS eqs. (3.51)–(3.52),
p. 115, with (3.54), p. 116).** For every direction `v`, the derivative of the entry `(a, b)` of
`g_st` at `θ` applied to `v` is the entry of `(Jˢ(θ) v)^ g_st(θ)`, `Jˢ(θ) v = Σᵢ vᵢ ξᵢ'`. -/
theorem fderiv_fk_toHomogeneous_apply (c : SerialChain n) (θ v : Fin n → ℝ)
    (a b : HomogeneousIndex) :
    fderiv ℝ (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b) θ v =
      ((∑ i, v i • c.spatialJacobian θ i).hat * (c.fk θ).toHomogeneous) a b := by
  have hγ : HasDerivAt (fun s : ℝ => θ + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add θ
  have hf : HasFDerivAt (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b)
      (fderiv ℝ (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b) θ) (θ + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact (c.differentiable_fk_toHomogeneous_apply a b θ).hasFDerivAt
  have h1 := hf.comp_hasDerivAt (0 : ℝ) hγ
  have h2 := hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (c.hasDerivAt_fk_toHomogeneous (θ := fun s : ℝ => θ + s • v) (hasDerivAt_line_apply θ v)) a) b
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

/-- **The Fréchet derivative of the forward kinematics, spatial form (MLS eqs. (3.51)–(3.54),
pp. 115–116).** For every chain, joint vector `θ` and entry `(a, b)`, the entry `(a, b)` of
`φ ↦ g_st(φ)` has at `θ` the Fréchet derivative `v ↦ Σᵢ vᵢ (ξ̂ᵢ' g_st(θ))_{ab}`, the entry of
`(Jˢ(θ) v)^ g_st(θ)`. Twist order `(v, ω)`; sup norm on `Fin n → ℝ`. -/
theorem hasFDerivAt_fk_toHomogeneous_apply (c : SerialChain n) (θ : Fin n → ℝ)
    (a b : HomogeneousIndex) :
    HasFDerivAt (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b)
      (∑ i, ((c.spatialJacobian θ i).hat * (c.fk θ).toHomogeneous) a b •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) θ := by
  have h := (c.differentiable_fk_toHomogeneous_apply a b θ).hasFDerivAt
  convert h using 1
  ext v
  rw [fderiv_fk_toHomogeneous_apply, hat_sum_smul_mul_apply]
  simp [mul_comm]

/-- **The derivative of the forward kinematics in a direction, body form (MLS eq. (3.55),
p. 117).** For every direction `v`, the derivative of the entry `(a, b)` of `g_st` at `θ` applied
to `v` is the entry of `g_st(θ) (Jᵇ(θ) v)^`, `Jᵇ(θ) v = Σᵢ vᵢ ξᵢ†`. -/
theorem fderiv_fk_toHomogeneous_apply_body (c : SerialChain n) (θ v : Fin n → ℝ)
    (a b : HomogeneousIndex) :
    fderiv ℝ (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b) θ v =
      ((c.fk θ).toHomogeneous * (∑ i, v i • c.bodyJacobian θ i).hat) a b := by
  rw [fderiv_fk_toHomogeneous_apply]
  have hs : ∑ i, v i • c.spatialJacobian θ i =
      Twist.adjoint (c.fk θ) (∑ i, v i • c.bodyJacobian θ i) := by
    have hmap : Twist.adjoint (c.fk θ) (∑ i, v i • c.bodyJacobian θ i) =
        ∑ i, Twist.adjoint (c.fk θ) (v i • c.bodyJacobian θ i) :=
      map_sum (Twist.adjointLinearMap (c.fk θ)) _ Finset.univ
    rw [hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Twist.adjoint_smul, spatialJacobian_eq_adjoint_bodyJacobian]
  rw [hs, Twist.hat_adjoint, Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (Matrix.isUnit_det_of_right_inverse (RigidTransform.toHomogeneous_mul_inv (c.fk θ))),
    Matrix.mul_one]

/-- **The partial derivative `∂g_st/∂θᵢ` (MLS eqs. (3.51)–(3.52), p. 115).** The `4 × 4` matrix
whose entry `(a, b)` is the derivative of the entry `(a, b)` of `g_st` at `θ` in the coordinate
direction `i` (the vector `Pi.single i 1`). Lean index `i` is the book's joint `i + 1`. -/
def fkPartial (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) : HomogeneousMatrix :=
  Matrix.of fun a b => fderiv ℝ (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b) θ (Pi.single i 1)

/-- **The partial derivative is the column twist times the pose (MLS p. 116, the display before
eq. (3.53)).** `∂g_st/∂θᵢ = ξ̂ᵢ' g_st(θ)` with `ξᵢ'` the spatial Jacobian column of eq. (3.54). -/
theorem fkPartial_eq (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    c.fkPartial θ i = (c.spatialJacobian θ i).hat * (c.fk θ).toHomogeneous := by
  ext a b
  rw [fkPartial, Matrix.of_apply, fderiv_fk_toHomogeneous_apply, hat_sum_smul_mul_apply]
  simp [Pi.single_apply]

/-- **MLS eq. (3.53), p. 116.** `∂g_st/∂θᵢ g_st⁻¹ = (Ad_{e^{ξ̂₁θ₁} ⋯ e^{ξ̂ᵢ₋₁θᵢ₋₁}} ξᵢ)^`, the
product running over the joints before `i` (`(c.jointMotions θ).take i`). For every chain and every
real joint vector; no unit-twist premise. -/
theorem fkPartial_mul_inv (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    c.fkPartial θ i * ((c.fk θ)⁻¹).toHomogeneous =
      (Twist.adjoint ((c.jointMotions θ).take i).prod (c.twist i)).hat := by
  rw [fkPartial_eq, Matrix.mul_assoc, RigidTransform.toHomogeneous_mul_inv, Matrix.mul_one]
  rfl

/-- **MLS eqs. (3.52)–(3.54), pp. 115–116, matrix form.** `∂g_st/∂θᵢ g_st⁻¹ = ξ̂ᵢ'`, the hat of the
spatial Jacobian column of eq. (3.54). -/
theorem fkPartial_mul_inv_eq_hat_spatialJacobian (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    c.fkPartial θ i * ((c.fk θ)⁻¹).toHomogeneous = (c.spatialJacobian θ i).hat :=
  c.fkPartial_mul_inv θ i

/-- **MLS eq. (3.52), p. 115: the columns of the spatial Jacobian are `(∂g_st/∂θᵢ g_st⁻¹)^∨`.**
The library's column `ξᵢ'` (defined by eq. (3.54)) is the vee of `∂g_st/∂θᵢ g_st⁻¹`. -/
theorem spatialJacobian_eq_vee_fkPartial_mul_inv (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    c.spatialJacobian θ i = Twist.vee (c.fkPartial θ i * ((c.fk θ)⁻¹).toHomogeneous) := by
  rw [fkPartial_mul_inv, Twist.vee_hat]
  rfl

/-- **MLS eq. (3.55), p. 117, as a derivative: the columns of the body Jacobian are
`(g_st⁻¹ ∂g_st/∂θᵢ)^∨`.** `g_st⁻¹ ∂g_st/∂θᵢ = (ξᵢ†)^` with
`ξᵢ† = Ad⁻¹_{e^{ξ̂ᵢθᵢ} ⋯ e^{ξ̂ₙθₙ} g_st(0)} ξᵢ`. -/
theorem inv_mul_fkPartial (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    ((c.fk θ)⁻¹).toHomogeneous * c.fkPartial θ i = (c.bodyJacobian θ i).hat := by
  rw [fkPartial_eq, spatialJacobian_eq_adjoint_bodyJacobian, Twist.hat_adjoint,
    ← RigidTransform.toHomogeneous_inv]
  simp only [← Matrix.mul_assoc, RigidTransform.toHomogeneous_inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, RigidTransform.toHomogeneous_inv_mul, Matrix.mul_one]

/-- **MLS eq. (3.55), p. 117, vee form.** The library's body Jacobian column `ξᵢ†` is the vee of
`g_st⁻¹ ∂g_st/∂θᵢ`. -/
theorem bodyJacobian_eq_vee_inv_mul_fkPartial (c : SerialChain n) (θ : Fin n → ℝ) (i : Fin n) :
    c.bodyJacobian θ i = Twist.vee (((c.fk θ)⁻¹).toHomogeneous * c.fkPartial θ i) := by
  rw [inv_mul_fkPartial, Twist.vee_hat]

/-- **Consistency with the trajectory form (MLS eqs. (3.51)–(3.54), pp. 115–116).** The chain-rule
derivative `Σᵢ θ̇ᵢ ∂g_st/∂θᵢ` is the derivative `(Jˢ(θ) θ̇)^ g_st(θ)` of
`hasDerivAt_fk_toHomogeneous`. -/
theorem sum_smul_fkPartial (c : SerialChain n) (θ θ' : Fin n → ℝ) :
    ∑ i, θ' i • c.fkPartial θ i =
      (∑ i, θ' i • c.spatialJacobian θ i).hat * (c.fk θ).toHomogeneous := by
  ext a b
  rw [hat_sum_smul_mul_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, fkPartial_eq]

/-- **The derivative is the sum of the partial derivatives (MLS eq. (3.51), p. 115).** For every
direction `v`, the derivative of the entry `(a, b)` of `g_st` at `θ` applied to `v` is
`Σᵢ vᵢ (∂g_st/∂θᵢ)_{ab}`. -/
theorem fderiv_fk_toHomogeneous_apply_eq_sum (c : SerialChain n) (θ v : Fin n → ℝ)
    (a b : HomogeneousIndex) :
    fderiv ℝ (fun φ : Fin n → ℝ => (c.fk φ).toHomogeneous a b) θ v =
      ∑ i, v i * c.fkPartial θ i a b := by
  rw [fderiv_fk_toHomogeneous_apply, ← sum_smul_fkPartial, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- **MLS eq. (3.51), p. 115: the chain rule.** Along a joint path with actual derivatives
`θ̇ᵢ` at `t`, every entry of `g_st(θ(t))` has the actual derivative `Σᵢ θ̇ᵢ (∂g_st/∂θᵢ)_{ab}`,
by the chain rule applied to the Fréchet derivative of `g_st` at `θ(t)`. -/
theorem hasDerivAt_fk_toHomogeneous_apply_comp (c : SerialChain n) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t)
    (a b : HomogeneousIndex) :
    HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous a b)
      (∑ i, θ' i * c.fkPartial (θ t) i a b) t := by
  have hf := (c.differentiable_fk_toHomogeneous_apply a b (θ t)).hasFDerivAt
  have h := hf.comp_hasDerivAt t (hasDerivAt_pi.mpr hθ)
  rw [fderiv_fk_toHomogeneous_apply_eq_sum] at h
  exact h

/-- **MLS eq. (3.51), p. 115: the spatial velocity is `Σᵢ (∂g_st/∂θᵢ g_st⁻¹) θ̇ᵢ`.** Along a joint
path with rates `θ̇` at `t`, for any derivative `D` of the homogeneous pose with its `HasDerivAt`
evidence, the hat of the spatial velocity `ġ g⁻¹` (`RigidTransform.spatialVelocity`) is
`Σᵢ θ̇ᵢ (∂g_st/∂θᵢ g_st⁻¹)`. -/
theorem hat_spatialVelocity_fk_eq_sum (c : SerialChain n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) D t) :
    (RigidTransform.spatialVelocity (fun s => c.fk (θ s)) D t hD).hat =
      ∑ i, θ' i • (c.fkPartial (θ t) i * ((c.fk (θ t))⁻¹).toHomogeneous) := by
  rw [RigidTransform.hat_spatialVelocity, hD.unique (c.hasDerivAt_fk_toHomogeneous hθ),
    ← sum_smul_fkPartial, Finset.sum_mul, RigidTransform.toHomogeneous_inv]
  simp only [Matrix.smul_mul]

end SerialChain
end RoboLean
