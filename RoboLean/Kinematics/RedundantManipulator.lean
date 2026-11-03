import RoboLean.Kinematics.ForcePullback
import RoboLean.Dynamics.PseudoInverse
import RoboLean.Dynamics.Lagrangian

/-!
# Redundant manipulators: minimum-norm rates and statics (MLS §3.5)

MLS printed pp. 129–131.

* Minimum-norm redundancy resolution (p. 130): "One common solution is to choose the minimum
  joint velocity which gives the desired workspace velocity. This is achieved by choosing
  `θ̇ = J†(θ) V` where `J† = Jᵀ (J Jᵀ)⁻¹`". With the six rows `(v, ω)` of the spatial Jacobian
  numbered `0, …, 5` (`spatialJacobianRows`), `minNormRates` is `J† Vˢ` (the library's
  `Composite.rightPinv`). For a Jacobian of full row rank (the rows span `ℝ⁶`, a hypothesis the
  book does not print) these rates produce the end-effector velocity `Vˢ`, every other solution
  differs from them by an internal motion `Jˢ θ̇_N = 0` (p. 130, the self-motion rates), and they
  have the least Euclidean norm among all solutions.
* Statics (eq. (3.63), p. 131): "when a manipulator is in static equilibrium, the previous
  relationship `τ = Jᵀ F` still holds". The model: the environment applies the body wrench `Fₑ`
  at the end-effector, and its generalized force in Lagrange's equations (MLS eq. (4.5), p. 158)
  is `(Jᵇ)ᵀ Fₑ`, the force whose power is `Fₑ · Vᵇ` for every joint rate (the virtual-work
  identity of MLS p. 121, `SerialChain.sum_bodyWrenchTorques_mul_eq_pair_bodyVelocity`); with
  actuator torques `τ` the generalized force is `Υ = τ + (Jᵇ)ᵀ Fₑ`. Lagrange's equations then
  read `M θ̈ + C θ̇ + ∂V/∂θ = τ + (Jᵇ)ᵀ Fₑ`, and at rest they reduce to
  `τ = (Jᵇ)ᵀ F + ∂V/∂θ` with `F = -Fₑ` the wrench the end-effector exerts; without potential
  this is (3.63), for every number of joints. The spatial form uses `Fˢ = Ad_{g_st}^{-T} F`
  (MLS eq. (2.67), p. 63).

Conventions: twists `(v, ω)`, wrenches `(f, τ)`, Lean column `i` is the book's column `i + 1`,
real joint lift; the mechanical Lagrangian `½ θ̇ᵀ M(θ) θ̇ − V(θ)` of MLS eq. (4.20), p. 169.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-- The spatial Jacobian (MLS eq. (3.54), p. 116) as a `6 × n` matrix with its rows `(v, ω)`
numbered `0, …, 5` in order (`finSumFinEquiv`), the matrix form `Jˢ_st ∈ ℝ^{p×n}` of MLS p. 130
with `p = 6`. -/
def spatialJacobianRows (c : SerialChain n) (θ : Fin n → ℝ) : Matrix (Fin 6) (Fin n) ℝ :=
  (c.spatialJacobianMatrix θ).submatrix (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm id

/-- The minimum-norm joint rates `θ̇ = J†(θ) Vˢ`, `J† = Jᵀ (J Jᵀ)⁻¹`, of MLS p. 130, for a
spatial end-effector velocity `Vˢ` with coordinates `(v, ω)`. -/
def minNormRates (c : SerialChain n) (θ : Fin n → ℝ) (V : Twist) : Fin n → ℝ :=
  Composite.rightPinv (c.spatialJacobianRows θ) *ᵥ (V.coordinates ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm)

private theorem spatialJacobianRows_mulVec (c : SerialChain n) (θ x : Fin n → ℝ) :
    c.spatialJacobianRows θ *ᵥ x =
      (∑ i, x i • c.spatialJacobian θ i).coordinates ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm := by
  change (c.spatialJacobianMatrix θ *ᵥ x) ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm = _
  rw [spatialJacobianMatrix_mulVec]

private theorem spatialJacobianRows_surjective (c : SerialChain n) (θ : Fin n → ℝ)
    (hJ : Function.Surjective (c.spatialJacobianMatrix θ).mulVec) :
    Function.Surjective (c.spatialJacobianRows θ).mulVec := by
  intro b
  obtain ⟨x, hx⟩ := hJ (b ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6))
  refine ⟨x, ?_⟩
  change (c.spatialJacobianMatrix θ *ᵥ x) ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm = b
  rw [hx]
  funext k
  simp

private theorem sum_eq_iff_rows (c : SerialChain n) (θ x : Fin n → ℝ) (V : Twist) :
    ∑ i, x i • c.spatialJacobian θ i = V ↔
      c.spatialJacobianRows θ *ᵥ x = V.coordinates ∘ (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm := by
  rw [spatialJacobianRows_mulVec]
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Twist.coordinatesEquiv.injective
    funext r
    have := congrFun h ((finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) r)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
    exact this

/-- **MLS p. 130: `θ̇ = J† Vˢ` gives the desired workspace velocity.** If the spatial Jacobian
has full row rank (its matrix is onto `ℝ⁶`), the minimum-norm rates produce the end-effector
spatial velocity `Vˢ`: `Jˢ(θ) θ̇ = ∑ᵢ θ̇ᵢ ξᵢ' = Vˢ` (MLS eq. (3.54)). -/
theorem sum_minNormRates (c : SerialChain n) (θ : Fin n → ℝ)
    (hJ : Function.Surjective (c.spatialJacobianMatrix θ).mulVec) (V : Twist) :
    ∑ i, c.minNormRates θ V i • c.spatialJacobian θ i = V :=
  (c.sum_eq_iff_rows θ _ V).mpr
    (Composite.mulVec_rightPinv_mulVec (c.spatialJacobianRows_surjective θ hJ) _)

/-- **MLS p. 130: the general solution.** For a spatial Jacobian of full row rank, the joint rates
producing `Vˢ` are exactly the minimum-norm rates plus an internal motion, rates `θ̇_N` with
`Jˢ(θ) θ̇_N = 0` (the motions along the self-motion set, MLS eq. (3.62)). -/
theorem sum_eq_iff_exists_minNormRates (c : SerialChain n) (θ : Fin n → ℝ)
    (hJ : Function.Surjective (c.spatialJacobianMatrix θ).mulVec) (V : Twist) (θ' : Fin n → ℝ) :
    ∑ i, θ' i • c.spatialJacobian θ i = V ↔
      ∃ θN : Fin n → ℝ, ∑ i, θN i • c.spatialJacobian θ i = 0 ∧ θ' = c.minNormRates θ V + θN := by
  have h0 : ∀ θN : Fin n → ℝ, ∑ i, θN i • c.spatialJacobian θ i = 0 ↔
      c.spatialJacobianRows θ *ᵥ θN = 0 := by
    intro θN
    rw [c.sum_eq_iff_rows θ θN 0]
    constructor <;> intro h <;> rw [h] <;> funext k <;> simp [Twist.coordinates]
  rw [c.sum_eq_iff_rows θ θ' V,
    Composite.mulVec_eq_iff_exists_rightPinv (c.spatialJacobianRows_surjective θ hJ)]
  simp only [h0]
  rfl

/-- **MLS p. 130: `J† Vˢ` is "the minimum joint velocity which gives the desired workspace
velocity".** For a spatial Jacobian of full row rank and every joint rate `θ̇` with
`Jˢ(θ) θ̇ = Vˢ`, the squared Euclidean norm of the minimum-norm rates is at most that of `θ̇`. -/
theorem minNormRates_dotProduct_le (c : SerialChain n) (θ : Fin n → ℝ)
    (hJ : Function.Surjective (c.spatialJacobianMatrix θ).mulVec) {V : Twist} {θ' : Fin n → ℝ}
    (hθ' : ∑ i, θ' i • c.spatialJacobian θ i = V) :
    c.minNormRates θ V ⬝ᵥ c.minNormRates θ V ≤ θ' ⬝ᵥ θ' :=
  Composite.dotProduct_rightPinv_mulVec_le (c.spatialJacobianRows_surjective θ hJ)
    ((c.sum_eq_iff_rows θ θ' V).mp hθ')

/-- **MLS p. 131, with eq. (4.5), p. 158, and p. 121: Lagrange's equations with an end-effector
wrench.** With actuator torques `τ` and a body wrench `Fₑ` applied by the environment at the
end-effector, whose generalized force is `(Jᵇ)ᵀ Fₑ` (`bodyWrenchTorques`), Lagrange's equations
for the mechanical Lagrangian `½ θ̇ᵀ M(θ) θ̇ − V(θ)` with `Υ = τ + (Jᵇ)ᵀ Fₑ` are
`M(θ) θ̈ + C(θ, θ̇) θ̇ + ∂V/∂θ = τ + (Jᵇ(θ))ᵀ Fₑ`. Hypotheses as in
`Lagrangian.lagrangeEquationsAt_mechanical_iff` (MLS states only smoothness). -/
theorem lagrangeEquationsAt_endEffectorWrench_iff (c : SerialChain n)
    {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {V : (Fin n → ℝ) → ℝ} {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ}
    {t : ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t)) (hV : HasFDerivAt V V' (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (τ : Fin n → ℝ)
    (Fₑ : Wrench) :
    Lagrangian.LagrangeEquationsAt (Lagrangian.mechanical M V) θ
        (τ + c.bodyWrenchTorques (θ t) Fₑ) t ↔
      M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        Lagrangian.gradient V' = τ + c.bodyWrenchTorques (θ t) Fₑ :=
  Lagrangian.lagrangeEquationsAt_mechanical_iff hsymm hM hV hθ hθ' _

/-- **MLS eq. (3.63), p. 131: statics of a (redundant) manipulator.** The manipulator is at rest
at `θ₀` under actuator torques `τ` and an environment wrench `Fₑ` on the end-effector (Lagrange's
equations with `Υ = τ + (Jᵇ)ᵀ Fₑ` hold for the constant motion) exactly when
`τ = (Jᵇ(θ₀))ᵀ F + ∂V/∂θ(θ₀)` with `F = -Fₑ` the body wrench the end-effector exerts. Holds for
every number of joints, redundant or not; `M` symmetric with differentiable entries and `V`
differentiable at `θ₀`. -/
theorem static_equilibrium_iff (c : SerialChain n)
    {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {V : (Fin n → ℝ) → ℝ} {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ₀ : Fin n → ℝ}
    (hsymm : ∀ q, (M q).IsSymm) (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) θ₀)
    (hV : HasFDerivAt V V' θ₀) (t : ℝ) (τ : Fin n → ℝ) (Fₑ : Wrench) :
    Lagrangian.LagrangeEquationsAt (Lagrangian.mechanical M V) (fun _ => θ₀)
        (τ + c.bodyWrenchTorques θ₀ Fₑ) t ↔
      τ = c.bodyWrenchTorques θ₀ (-Fₑ) + Lagrangian.gradient V' := by
  have hneg : c.bodyWrenchTorques θ₀ (-Fₑ) = -c.bodyWrenchTorques θ₀ Fₑ := by
    funext i
    simp [bodyWrenchTorques, Wrench.pair, inner_neg_left]
    ring
  rw [c.lagrangeEquationsAt_endEffectorWrench_iff (θ := fun _ => θ₀) (θ' := fun _ => 0)
    (θ'' := 0) hsymm hM hV (Eventually.of_forall fun s => hasDerivAt_const s θ₀)
    (hasDerivAt_const t 0), hneg]
  simp only [mulVec_zero, zero_add]
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [h]
    abel

/-- **MLS eq. (3.63), p. 131, without potential: `τ = Jᵀ F` at static equilibrium.** With no
potential energy, the manipulator is at rest at `θ₀` under `τ` and the environment wrench `Fₑ`
exactly when `τ = (Jᵇ(θ₀))ᵀ F` for the body wrench `F = -Fₑ` the end-effector exerts, and
equivalently `τ = (Jˢ(θ₀))ᵀ Fˢ` for the same wrench in spatial coordinates
`Fˢ = Wrench.transform (g_st(θ₀)) F` ("either the body or spatial Jacobian can be used, as long
as the wrench `F` is represented appropriately"). -/
theorem static_equilibrium_iff_torque (c : SerialChain n)
    {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {θ₀ : Fin n → ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) θ₀) (t : ℝ) (τ : Fin n → ℝ)
    (Fₑ : Wrench) :
    (Lagrangian.LagrangeEquationsAt (Lagrangian.mechanical M fun _ => 0) (fun _ => θ₀)
        (τ + c.bodyWrenchTorques θ₀ Fₑ) t ↔ τ = c.bodyWrenchTorques θ₀ (-Fₑ)) ∧
      c.bodyWrenchTorques θ₀ (-Fₑ) =
        c.spatialWrenchTorques θ₀ (Wrench.transform (c.fk θ₀) (-Fₑ)) := by
  refine ⟨?_, (c.spatialWrenchTorques_transform θ₀ (-Fₑ)).symm⟩
  have hg : Lagrangian.gradient (0 : (Fin n → ℝ) →L[ℝ] ℝ) = 0 := by
    funext i
    simp [Lagrangian.gradient]
  rw [c.static_equilibrium_iff hsymm hM (hasFDerivAt_const 0 θ₀) t τ Fₑ, hg, add_zero]

end SerialChain

end RoboLean
