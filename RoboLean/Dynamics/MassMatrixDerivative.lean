import RoboLean.Dynamics.PotentialEnergy

/-!
# Differentiability of the manipulator inertia matrix and the product-of-exponentials formulas

MLS Chapter 4, §3.3, printed pp. 175–177, Proposition 4.3 and eqs. (4.27)–(4.30).

**Differentiability (the hypothesis-discharging part).** For every open chain
(`InertialChain n`: arbitrary joint twists, reference link poses and link inertias), every entry
`θ ↦ M(θ)ᵢⱼ` of the inertia matrix `M = ∑ₖ Jₖᵀ 𝓜ₖ Jₖ` (eq. (4.19)) is differentiable on `ℝⁿ`
(`differentiable_massMatrix`), and so is the gravitational potential energy
(`differentiable_potentialEnergy`). The proof differentiates the homogeneous matrices of the
joint motions `exp(θⱼ ξ̂ⱼ)`, their products and the inverse of the link-frame partial poses
(`Ring.inverse` on the operator-normed matrix algebra), and reads the body-Jacobian coordinates
off the hat matrix `g⁻¹ ξ̂ g`. Consequently the derivative hypotheses of
`InertialChain.skew_deriv_massMatrix_sub_two_coriolisMatrix` (Lemma 4.2(2)), of the open-chain
equations of motion and of the passivity balance are discharged for every chain
(`skew_deriv_sub_two_coriolisMatrix_massMatrixDeriv`, `lagrangeEquationsAt_potentialEnergy_iff`,
`hasDerivAt_energy_gravity`); the partial derivatives are `massMatrixDeriv`, the Fréchet
derivatives of the entries. Only first derivatives are established; no `C²` claim is made.

**The product-of-exponentials form (4.27)–(4.29).** `relativeMotion l j θ` is the rigid motion
whose adjoint is MLS's `A_{lj}` (4.27); the link-Jacobian columns are `Ad_{g_{sl_l}(0)⁻¹} A_{lj} ξⱼ`
(`linkBodyJacobian_eq_adjoint_relativeMotion`), and `M(θ)ᵢⱼ = ∑_{l ≥ max(i,j)} (A_{li} ξᵢ)ᵀ 𝓜'_l
(A_{lj} ξⱼ)` with the transformed inertia `𝓜'_l` of (4.28) (`massMatrix_apply_relativeMotion`).

**Not formalized:** the explicit bracket formula (4.30) for `∂Mᵢⱼ/∂θₖ` and the Coriolis formula
of (4.29) in terms of it (the Christoffel form of `C` from the actual partial derivatives is
available through `massMatrixDeriv`).

Lean link and joint `k` are the book's `k + 1`. Nothing here concerns numerics or a physical
manipulator.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean
namespace InertialChain

variable {n : ℕ}

private def entryCLM (a b : HomogeneousIndex) : HomogeneousMatrix →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem differentiable_exp_toHomogeneous (ξ : Twist) (l : Fin n) :
    Differentiable ℝ (fun θ : Fin n → ℝ => (Twist.exp ξ (θ l)).toHomogeneous) := by
  intro θ
  have h1 : DifferentiableAt ℝ (fun s : ℝ => NormedSpace.exp (s • ξ.hat)) (θ l) :=
    (hasDerivAt_exp_smul_const ξ.hat (θ l)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun θ : Fin n → ℝ => θ l) θ := differentiableAt_apply l θ
  have e : (fun θ : Fin n → ℝ => (Twist.exp ξ (θ l)).toHomogeneous) =
      fun θ => NormedSpace.exp ((θ l) • ξ.hat) := by
    funext θ
    exact Twist.toHomogeneous_exp ξ (θ l)
  rw [e]
  exact DifferentiableAt.comp (g := fun s : ℝ => NormedSpace.exp (s • ξ.hat))
    (f := fun θ : Fin n → ℝ => θ l) θ h1 h2

private theorem differentiable_list_prod (ls : List (Fin n))
    (F : Fin n → (Fin n → ℝ) → HomogeneousMatrix) (hF : ∀ l, Differentiable ℝ (F l)) :
    Differentiable ℝ (fun θ => (ls.map fun l => F l θ).prod) := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF a).mul ih

private theorem toHomogeneous_list_prod (L : List RigidTransform) :
    L.prod.toHomogeneous = (L.map RigidTransform.toHomogeneous).prod :=
  map_list_prod RigidTransform.toHomogeneousHom L

private theorem take_drop_jointMotions (c : SerialChain n) (θ : Fin n → ℝ) (a b : ℕ) :
    ((c.jointMotions θ).take a).drop b =
      (((List.finRange n).take a).drop b).map fun l => Twist.exp (c.twist l) (θ l) := by
  simp [SerialChain.jointMotions, List.ofFn_eq_map, List.map_take, List.map_drop]

private theorem coordinates_eq_hat (r : Fin 3 ⊕ Fin 3) :
    ∃ a b : HomogeneousIndex, ∀ η : Twist, η.coordinates r = η.hat a b := by
  rcases r with i | i
  · exact ⟨Sum.inl i, Sum.inr 0, fun η => rfl⟩
  · fin_cases i
    · exact ⟨Sum.inl 2, Sum.inl 1, fun η => by simp [Twist.coordinates, Twist.hat, Vec3.hat]⟩
    · exact ⟨Sum.inl 0, Sum.inl 2, fun η => by simp [Twist.coordinates, Twist.hat, Vec3.hat]⟩
    · exact ⟨Sum.inl 1, Sum.inl 0, fun η => by simp [Twist.coordinates, Twist.hat, Vec3.hat]⟩

variable (ch : InertialChain n)

private theorem differentiable_partialPose (k : Fin n) (b : ℕ) :
    Differentiable ℝ (fun θ : Fin n → ℝ =>
      ((((ch.chain.jointMotions θ).take (k.val + 1)).drop b).prod *
        ch.linkRef k).toHomogeneous) := by
  have e : (fun θ : Fin n → ℝ =>
      ((((ch.chain.jointMotions θ).take (k.val + 1)).drop b).prod *
        ch.linkRef k).toHomogeneous) = fun θ =>
      ((((List.finRange n).take (k.val + 1)).drop b).map fun l =>
        (Twist.exp (ch.chain.twist l) (θ l)).toHomogeneous).prod *
          (ch.linkRef k).toHomogeneous := by
    funext θ
    rw [RigidTransform.toHomogeneous_mul, toHomogeneous_list_prod, take_drop_jointMotions,
      List.map_map]
    rfl
  rw [e]
  exact (differentiable_list_prod _ _ fun l => differentiable_exp_toHomogeneous _ l).mul_const _

/-- **Differentiability of the link body Jacobians (MLS p. 168, eq. (4.27)).** Every
coordinate of every column `ξⱼ†(θ) = Ad⁻¹_{(exp(ξ̂ⱼθⱼ) ⋯ exp(ξ̂ₖθₖ) g_{sl_k}(0))} ξⱼ` of the body
Jacobian of link `k` is a differentiable function of the joint vector `θ`, for every open chain
(columns after `k` are zero). -/
theorem differentiable_linkBodyJacobian_coordinates (k j : Fin n) (r : Fin 3 ⊕ Fin 3) :
    Differentiable ℝ (fun θ => (ch.linkBodyJacobian k θ j).coordinates r) := by
  by_cases hj : j ≤ k
  · obtain ⟨a, b, hab⟩ := coordinates_eq_hat r
    set G : (Fin n → ℝ) → HomogeneousMatrix := fun θ =>
      ((((ch.chain.jointMotions θ).take (k.val + 1)).drop j.val).prod *
        ch.linkRef k).toHomogeneous with hGdef
    have hG : Differentiable ℝ G := ch.differentiable_partialPose k j.val
    have e : (fun θ => (ch.linkBodyJacobian k θ j).coordinates r) = fun θ =>
        entryCLM a b (Ring.inverse (G θ) * (ch.chain.twist j).hat * G θ) := by
      funext θ
      rw [ch.linkBodyJacobian_of_le k θ hj, hab, Twist.hat_adjoint,
        ← RigidTransform.toHomogeneous_inv
          ((((ch.chain.jointMotions θ).take (k.val + 1)).drop j.val).prod * ch.linkRef k)⁻¹,
        inv_inv, RigidTransform.toHomogeneous_inv, Matrix.nonsing_inv_eq_ringInverse]
      rfl
    rw [e]
    intro θ
    have hinv : DifferentiableAt ℝ (fun x => Ring.inverse (G x)) θ :=
      (hG θ).inverse (RigidTransform.isUnit_toHomogeneous _)
    exact (entryCLM a b).differentiableAt.comp θ (((hinv.mul_const _).mul (hG θ)))
  · have e : (fun θ => (ch.linkBodyJacobian k θ j).coordinates r) = fun _ => 0 := by
      funext θ
      rw [ch.linkBodyJacobian_of_lt k θ (not_le.mp hj), RigidBody.coordinates_zero]
      rfl
    rw [e]
    exact differentiable_const 0

/-- **MLS Proposition 4.3, p. 176, differentiability part: the manipulator inertia matrix of
every open chain is differentiable.** Each entry `θ ↦ M(θ)ᵢⱼ` of `M = ∑ₖ Jₖᵀ 𝓜ₖ Jₖ`
(eq. (4.19)) is differentiable on `ℝⁿ`, for arbitrary joint twists, reference link poses and
link inertias. (MLS states the explicit derivative (4.30); this theorem gives existence of the
derivative, from the differentiability of the twist exponential and of matrix inversion.) -/
theorem differentiable_massMatrix (i j : Fin n) :
    Differentiable ℝ (fun θ => ch.massMatrix θ i j) := by
  have h := ch.differentiable_linkBodyJacobian_coordinates
  simp only [massMatrix_apply, dotProduct, Matrix.mulVec]
  fun_prop

/-- **Differentiability of the link heights (MLS p. 169).** For every open chain and every
`up`, the height `h_k(θ) = ⟪up, p_k(θ)⟫` of the frame origin of link `k` is differentiable in
`θ`. -/
theorem differentiable_linkHeight (up : Vec3) (k : Fin n) :
    Differentiable ℝ (fun θ => ch.linkHeight up k θ) := by
  let L : HomogeneousMatrix →ₗ[ℝ] Vec3 :=
    { toFun := RigidTransform.translationDerivative
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP := ch.differentiable_partialPose k 0
  have e : (fun θ => ch.linkHeight up k θ) = fun θ =>
      innerSL ℝ up (L.toContinuousLinearMap
        ((((ch.chain.jointMotions θ).take (k.val + 1)).drop 0).prod *
          ch.linkRef k).toHomogeneous) := by
    funext θ
    rw [linkHeight, linkPose_eq, List.drop_zero, innerSL_apply_apply]
    rfl
  rw [e]
  intro θ
  exact (innerSL ℝ up).differentiableAt.comp θ
    (L.toContinuousLinearMap.differentiableAt.comp θ (hP θ))

/-- **Differentiability of the potential energy (MLS p. 169).** The gravitational potential
energy `V(θ) = ∑ₖ m_k g h_k(θ)` of every open chain is differentiable on `ℝⁿ`. -/
theorem differentiable_potentialEnergy (m : Fin n → ℝ) (g : ℝ) (up : Vec3) :
    Differentiable ℝ (ch.potentialEnergy m g up) := by
  have h := ch.differentiable_linkHeight up
  unfold potentialEnergy
  fun_prop

/-- **The gravity term of every open chain in its Jacobian form (MLS p. 174, eq. (4.25)).**
`N(θ) = ∂V/∂θ` equals `gravityJacobian`, with no hypothesis. -/
theorem gravityTerm_eq_gravityJacobian_everywhere (m : Fin n → ℝ) (g : ℝ) (up : Vec3)
    (θ : Fin n → ℝ) :
    ch.gravityTerm m g up θ = ch.gravityJacobian m g up θ :=
  ch.gravityTerm_eq_gravityJacobian (ch.differentiable_potentialEnergy m g up θ)

/-- **The partial derivatives of the manipulator inertia matrix (MLS eq. (4.30), p. 176, as
derivative data).** `massMatrixDeriv θ i j` is the Fréchet derivative at `θ` of the entry
`q ↦ M(q)ᵢⱼ`; `Christoffel.partials (massMatrixDeriv θ) k = ∂M/∂θₖ` at `θ`. -/
def massMatrixDeriv (θ : Fin n → ℝ) : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ) :=
  fun i j => fderiv ℝ (fun q => ch.massMatrix q i j) θ

/-- Every entry of the manipulator inertia matrix of an open chain has the Fréchet derivative
`massMatrixDeriv θ i j` at every `θ` (MLS Proposition 4.3, p. 176, differentiability part). This
discharges the derivative hypothesis of `skew_deriv_massMatrix_sub_two_coriolisMatrix` and of
`lagrangeEquationsAt_iff` for every chain. -/
theorem hasFDerivAt_massMatrix (θ : Fin n → ℝ) (i j : Fin n) :
    HasFDerivAt (fun q => ch.massMatrix q i j) (ch.massMatrixDeriv θ i j) θ :=
  (ch.differentiable_massMatrix i j θ).hasFDerivAt

/-- **MLS Lemma 4.2(2), p. 171, for every open chain, with no derivative hypothesis.** With
symmetric link inertias, along a joint trajectory with actual derivatives `θ̇` at `t`, every
actual derivative `Mdot` of `s ↦ M(θ(s))` makes `Mdot − 2C` skew-symmetric, where `C` is the
Christoffel Coriolis matrix (4.23) of the partial derivatives of `M` at `θ(t)`. -/
theorem skew_deriv_sub_two_coriolisMatrix_massMatrixDeriv (h : ∀ k, (ch.linkInertia k).IsSymm)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t) {Mdot : Matrix (Fin n) (Fin n) ℝ}
    (hMdot : ∀ i j, HasDerivAt (fun s => ch.massMatrix (θ s) i j) (Mdot i j) t) :
    (Mdot - (2 : ℝ) • Christoffel.coriolisMatrix
        (Christoffel.partials (ch.massMatrixDeriv (θ t))) θ')ᵀ =
      -(Mdot - (2 : ℝ) • Christoffel.coriolisMatrix
        (Christoffel.partials (ch.massMatrixDeriv (θ t))) θ') :=
  ch.skew_deriv_massMatrix_sub_two_coriolisMatrix h (ch.hasFDerivAt_massMatrix (θ t)) hθ hMdot

/-- **MLS eqs. (4.24)–(4.25), pp. 171–175: the equations of motion of every open chain in
uniform gravity, with no derivative hypothesis on the model.** With symmetric link inertias,
along a trajectory whose velocity `θ'` near `t` and acceleration `θ''` at `t` are actual
derivatives, Lagrange's equations for `L = ½ θ̇ᵀ M(θ) θ̇ − V(θ)`, `V = potentialEnergy m g up`,
with generalized force `Υ` hold at `t` exactly when `M(θ) θ̈ + C(θ, θ̇) θ̇ + N(θ) = Υ`, where `C`
is the Christoffel Coriolis matrix of the actual partial derivatives of `M` and `N` the gravity
term. -/
theorem lagrangeEquationsAt_potentialEnergy_iff (h : ∀ k, (ch.linkInertia k).IsSymm)
    (m : Fin n → ℝ) (g : ℝ) (up : Vec3) {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in nhds t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (Υ : Fin n → ℝ) :
    Lagrangian.LagrangeEquationsAt (ch.lagrangian (ch.potentialEnergy m g up)) θ Υ t ↔
      ch.massMatrix (θ t) *ᵥ θ'' +
          Christoffel.coriolisMatrix (Christoffel.partials (ch.massMatrixDeriv (θ t))) (θ' t) *ᵥ
            θ' t +
        ch.gravityTerm m g up (θ t) = Υ :=
  ch.lagrangeEquationsAt_gravity_iff h (ch.hasFDerivAt_massMatrix (θ t))
    (ch.differentiable_potentialEnergy m g up (θ t)) hθ hθ' Υ

/-- **MLS p. 172, passivity for every open chain in uniform gravity, with no derivative
hypothesis on the model.** With symmetric link inertias, along a solution of Lagrange's
equations with generalized force `Υ`, the total energy `T(θ, θ̇) + V(θ)` has derivative `θ̇ᵀ Υ`;
with `Υ = 0` it is conserved. -/
theorem hasDerivAt_energy_gravity (h : ∀ k, (ch.linkInertia k).IsSymm) (m : Fin n → ℝ)
    (g : ℝ) (up : Vec3) {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ᶠ s in nhds t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) {Υ : Fin n → ℝ}
    (hL : Lagrangian.LagrangeEquationsAt (ch.lagrangian (ch.potentialEnergy m g up)) θ Υ t) :
    HasDerivAt (fun s => ch.kineticEnergy (θ s) (θ' s) + ch.potentialEnergy m g up (θ s))
      (θ' t ⬝ᵥ Υ) t :=
  ch.hasDerivAt_energy h (ch.hasFDerivAt_massMatrix (θ t))
    (ch.differentiable_potentialEnergy m g up (θ t)).hasFDerivAt hθ hθ' hL

/-! ### The product-of-exponentials form of the inertia matrix (MLS eqs. (4.27)–(4.29)) -/

private theorem adjoint_exp_self (ξ : Twist) (t : ℝ) : Twist.adjoint (Twist.exp ξ t) ξ = ξ := by
  apply Twist.hat_injective
  rw [Twist.hat_adjoint, ← RigidTransform.toHomogeneous_inv]
  have hc : Commute (Twist.exp ξ t).toHomogeneous ξ.hat := by
    rw [Twist.toHomogeneous_exp]
    exact (((Commute.refl ξ.hat).smul_right t).exp_right).symm
  rw [hc.eq, mul_assoc, RigidTransform.toHomogeneous_mul_inv, mul_one]

/-- **MLS eq. (4.27), p. 176: the rigid motion behind `A_{lj}`.** For Lean joints `j ≤ l`,
`A_{lj} = Ad⁻¹_{(exp(ξ̂_{j+1}θ_{j+1}) ⋯ exp(ξ̂_l θ_l))}` is the adjoint of this transform, the
inverse of the product of the joint motions strictly after joint `j` up to joint `l` (book
indices shifted by one); for `j = l` the product is empty and `A_{ll} = I`. The case `l < j`,
where MLS sets `A_{lj} = 0`, is handled by restricting the sums below to `j ≤ l`. -/
def relativeMotion (l j : Fin n) (θ : Fin n → ℝ) : RigidTransform :=
  ((((ch.chain.jointMotions θ).take (l.val + 1)).drop (j.val + 1)).prod)⁻¹

/-- **MLS p. 176, after eq. (4.27): the columns of the link body Jacobian in terms of
`A_{lj}`.** For `j ≤ l`, column `j` of the body Jacobian of link `l` is
`Ad_{g_{sl_l}(0)⁻¹} A_{lj} ξⱼ`. The book's `A_{lj}` starts at joint `j + 1`; the factor
`exp(ξ̂ⱼθⱼ)` drops out because `Ad_{exp(ξ̂ⱼθⱼ)} ξⱼ = ξⱼ`. -/
theorem linkBodyJacobian_eq_adjoint_relativeMotion (θ : Fin n → ℝ) {l j : Fin n}
    (hj : j ≤ l) :
    ch.linkBodyJacobian l θ j =
      Twist.adjoint (ch.linkRef l)⁻¹
        (Twist.adjoint (ch.relativeMotion l j θ) (ch.chain.twist j)) := by
  have hlen : j.val < ((ch.chain.jointMotions θ).take (l.val + 1)).length := by
    simp only [SerialChain.jointMotions, List.length_take, List.length_ofFn]
    have := Fin.le_def.mp hj
    omega
  have hget : ((ch.chain.jointMotions θ).take (l.val + 1))[j.val] =
      Twist.exp (ch.chain.twist j) (θ j) := by
    simp [SerialChain.jointMotions]
  rw [ch.linkBodyJacobian_of_le l θ hj, List.drop_eq_getElem_cons hlen, List.prod_cons, hget,
    relativeMotion, mul_assoc, _root_.mul_inv_rev, _root_.mul_inv_rev, Twist.adjoint_mul,
    Twist.adjoint_mul, ← Twist.exp_neg, adjoint_exp_self, ← Twist.adjoint_mul]

/-- **MLS Proposition 4.3, eq. (4.29), p. 176: the inertia matrix in product-of-exponentials
form.** `M(θ)ᵢⱼ = ∑_{l ≥ max(i, j)} (A_{li} ξᵢ)ᵀ 𝓜'_l (A_{lj} ξⱼ)`, with
`𝓜'_l = Ad_{g_{sl_l}(0)⁻¹}ᵀ 𝓜_l Ad_{g_{sl_l}(0)⁻¹}` the transformed link inertia of eq. (4.28)
(`RigidBody.transformInertia`), for every open chain. -/
theorem massMatrix_apply_relativeMotion (θ : Fin n → ℝ) (i j : Fin n) :
    ch.massMatrix θ i j =
      ∑ l ∈ Finset.univ.filter (fun l => i ≤ l ∧ j ≤ l),
        (Twist.adjoint (ch.relativeMotion l i θ) (ch.chain.twist i)).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (Twist.adjoint (ch.relativeMotion l j θ) (ch.chain.twist j)).coordinates) := by
  rw [massMatrix_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : i ≤ l ∧ j ≤ l
  · rw [ite_eq_left h, RigidBody.coordinates_dotProduct_transformInertia_mulVec,
      ← ch.linkBodyJacobian_eq_adjoint_relativeMotion θ h.1,
      ← ch.linkBodyJacobian_eq_adjoint_relativeMotion θ h.2]
  · rw [ite_eq_right h]
    rcases not_and_or.mp h with hi | hj
    · rw [ch.linkBodyJacobian_of_lt l θ (not_le.mp hi), RigidBody.coordinates_zero,
        zero_dotProduct]
    · rw [ch.linkBodyJacobian_of_lt l θ (not_le.mp hj), RigidBody.coordinates_zero,
        Matrix.mulVec_zero, dotProduct_zero]

end InertialChain
end RoboLean
