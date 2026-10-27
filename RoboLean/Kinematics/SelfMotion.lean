import RoboLean.Kinematics.Jacobian

/-!
# Redundant manipulators: self-motions move in the null space of the Jacobian

MLS Chapter 3, §5.1, printed pp. 129–131. For a redundant manipulator, "if we keep the
end-effector configuration fixed, the robot is still free to move along any trajectory which
satisfies `g_st(θ(t)) = g_d` (3.62). The set of all `θ` which satisfy this equation is called the
self-motion manifold for the configuration `g_d`. Differentiating equation (3.62), we obtain
`Jˢ_st(θ(t)) θ̇ = (ġ_st g_st⁻¹)^∨ = 0`."

* `SerialChain.selfMotionSet c g` is the set `{θ | g_st(θ) = g_d}` of (3.62); no manifold structure
  is claimed (the book's "manifold" needs a rank hypothesis and an implicit-function argument);
* `SerialChain.sum_spatialJacobian_eq_zero_of_selfMotion`: along a joint trajectory that stays in
  the self-motion set near `t`, the joint rates lie in the null space of the spatial Jacobian;
* `SerialChain.spatialJacobianMatrix_mulVec_eq_zero_of_selfMotion`: the same in matrix form,
  `Jˢ θ̇ = 0`.

Joint coordinates are the real lift (ledger K01); the chain need not be redundant for these
statements, which hold for every serial chain.
-/

noncomputable section

open Filter

namespace RoboLean
namespace SerialChain

variable {n : ℕ}

/-- **MLS eq. (3.62), p. 130: the self-motion set** of the end-effector configuration `g_d`: the
joint vectors `θ` with `g_st(θ) = g_d` (product-of-exponentials forward kinematics, eq. (3.3)).
The book calls it the self-motion manifold; no manifold structure is claimed here. -/
def selfMotionSet (c : SerialChain n) (g : RigidTransform) : Set (Fin n → ℝ) :=
  {θ | c.fk θ = g}

/-- Membership in the self-motion set of MLS eq. (3.62), p. 130. -/
theorem mem_selfMotionSet_iff (c : SerialChain n) (g : RigidTransform) (θ : Fin n → ℝ) :
    θ ∈ c.selfMotionSet g ↔ c.fk θ = g := Iff.rfl

/-- **MLS p. 130, differentiating eq. (3.62): internal motions move in the null space of the
Jacobian.** If a joint trajectory `θ(s)` with joint rates `θ̇` at `t` keeps `g_st(θ(s)) = g_d` for
all `s` near `t`, then `Jˢ(θ(t)) θ̇ = ∑ᵢ θ̇ᵢ ξᵢ' = 0` (spatial Jacobian in column form,
eq. (3.54)). -/
theorem sum_spatialJacobian_eq_zero_of_selfMotion (c : SerialChain n) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t)
    {g : RigidTransform} (hself : ∀ᶠ s in nhds t, θ s ∈ c.selfMotionSet g) :
    ∑ i, θ' i • c.spatialJacobian (θ t) i = 0 := by
  have hconst : (fun s => (c.fk (θ s)).toHomogeneous) =ᶠ[nhds t] fun _ => g.toHomogeneous :=
    hself.mono fun s hs => by simp only [show c.fk (θ s) = g from hs]
  open scoped Matrix.Norms.Operator in
  have h0 : HasDerivAt (fun s => (c.fk (θ s)).toHomogeneous) 0 t :=
    (hasDerivAt_const t g.toHomogeneous).congr_of_eventuallyEq hconst
  open scoped Matrix.Norms.Operator in
  rw [← c.spatialVelocity_fk hθ h0]
  apply Twist.hat_injective
  rw [RigidTransform.hat_spatialVelocity, Matrix.zero_mul, Twist.hat_zero]

/-- **MLS p. 130, matrix form:** under the hypotheses of
`sum_spatialJacobian_eq_zero_of_selfMotion`, `Jˢ(θ(t)) θ̇ = 0` for the `6 × n` spatial Jacobian
matrix (rows `(v, ω)`): the joint rates are in its null space. -/
theorem spatialJacobianMatrix_mulVec_eq_zero_of_selfMotion (c : SerialChain n)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {g : RigidTransform}
    (hself : ∀ᶠ s in nhds t, θ s ∈ c.selfMotionSet g) :
    (c.spatialJacobianMatrix (θ t)).mulVec θ' = 0 := by
  rw [spatialJacobianMatrix_mulVec, c.sum_spatialJacobian_eq_zero_of_selfMotion hθ hself,
    Twist.coordinates_zero]

end SerialChain
end RoboLean
