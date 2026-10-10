import RoboLean.Dynamics.PotentialEnergy
import RoboLean.Geometry.TwistBracket

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

**The bracket formula (4.30).** `relativeAdjoint l j θ` is MLS's `A_{lj}` with the printed
convention `A_{lj} = 0` for `l < j` (the adjoint of `relativeMotion l j θ` for `j ≤ l`). Along the
coordinate line `s ↦ θ + s eₖ` the relative motion splits at joint `k`,
`g_{lj} = g_{lk} exp(−sξ̂ₖ) g_{kj}` (MLS p. 177, proof of Proposition 4.3), so
`∂(A_{lj} ξⱼ)/∂θₖ = A_{lk} [A_{kj} ξⱼ, ξₖ]` (`hasDerivAt_relativeAdjoint_coordinates`), and

`∂Mᵢⱼ/∂θₖ = ∑_{l ≥ max(i,j)} ([A_{ki} ξᵢ, ξₖ]ᵀ A_{lk}ᵀ 𝓜'_l A_{lj} ξⱼ`
`+ ξᵢᵀ A_{li}ᵀ 𝓜'_l A_{lk} [A_{kj} ξⱼ, ξₖ])`

(`massMatrixDeriv_single`, `partials_massMatrixDeriv`), where the bracket is `Twist.bracket`,
the vee of `ξ̂₁ ξ̂₂ − ξ̂₂ ξ̂₁`, as in MLS eq. (4.26): the printed formula holds as printed in the
library's bracket convention, with no sign change. The Coriolis line of (4.29) is the Christoffel
matrix (4.23) of these partial derivatives (`coriolisMatrix_massMatrixDeriv_apply`).

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
`exp(ξ̂ⱼθⱼ)` drops out because `Ad_{exp(ξ̂ⱼθⱼ)} ξⱼ = ξⱼ` (`Twist.adjoint_exp_self`). -/
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
    Twist.adjoint_mul, ← Twist.exp_neg, Twist.adjoint_exp_self, ← Twist.adjoint_mul]

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

/-- The joint motions with Lean indices in `[a, b)`, multiplied in order: the product
`exp(ξ̂_a θ_a) ⋯ exp(ξ̂_{b−1} θ_{b−1})` of MLS p. 177 (empty for `b ≤ a`). -/
private def segment (θ : Fin n → ℝ) (a b : ℕ) : RigidTransform :=
  (((ch.chain.jointMotions θ).take b).drop a).prod

private theorem take_drop_split {α : Type*} (L : List α) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) (hb : b ≤ L.length) :
    (L.take c).drop a = (L.take b).drop a ++ (L.take c).drop b := by
  calc (L.take c).drop a = ((L.take c).take b ++ (L.take c).drop b).drop a := by
        rw [List.take_append_drop]
    _ = ((L.take c).take b).drop a ++ (L.take c).drop b :=
        List.drop_append_of_le_length (by simp; omega)
    _ = (L.take b).drop a ++ (L.take c).drop b := by
        rw [List.take_take, Nat.min_eq_left hbc]

private theorem take_succ_drop {α : Type*} (L : List α) (k : ℕ) (hk : k < L.length) :
    (L.take (k + 1)).drop k = [L[k]] := by
  rw [List.drop_take, Nat.add_sub_cancel_left]
  conv_lhs => rw [List.drop_eq_getElem_cons hk]
  rfl

private theorem segment_split (θ : Fin n → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hb : b ≤ n) : ch.segment θ a c = ch.segment θ a b * ch.segment θ b c := by
  rw [segment, segment, segment, take_drop_split _ hab hbc (by simpa [SerialChain.jointMotions]),
    List.prod_append]

private theorem segment_single (θ : Fin n → ℝ) (k : Fin n) :
    ch.segment θ k.val (k.val + 1) = Twist.exp (ch.chain.twist k) (θ k) := by
  rw [segment, take_succ_drop _ _ (by simp [SerialChain.jointMotions]), List.prod_singleton]
  simp [SerialChain.jointMotions]

private theorem segment_self (θ : Fin n → ℝ) (a : ℕ) : ch.segment θ a a = 1 := by
  rw [segment, List.drop_eq_nil_of_le (by simp), List.prod_nil]

private theorem segment_congr {θ θ' : Fin n → ℝ} {a b : ℕ}
    (h : ∀ m : Fin n, a ≤ m.val → m.val < b → θ' m = θ m) :
    ch.segment θ' a b = ch.segment θ a b := by
  rw [segment, segment]
  congr 1
  apply List.ext_getElem
  · simp [SerialChain.jointMotions]
  · intro i h₁ h₂
    simp only [List.getElem_drop, List.getElem_take, SerialChain.jointMotions, List.getElem_ofFn]
    simp only [SerialChain.jointMotions, List.length_drop, List.length_take, List.length_ofFn] at h₁
    rw [h ⟨a + i, by omega⟩ (by simp) (by simp; omega)]

private theorem relativeMotion_eq_segment (l j : Fin n) (θ : Fin n → ℝ) :
    ch.relativeMotion l j θ = (ch.segment θ (j.val + 1) (l.val + 1))⁻¹ := rfl

/-- **MLS eq. (4.27), p. 176, the case `i = j`:** `A_{kk} = I`, because the product of joint
motions strictly after joint `k` up to joint `k` is empty. -/
theorem relativeMotion_self (k : Fin n) (θ : Fin n → ℝ) : ch.relativeMotion k k θ = 1 := by
  rw [relativeMotion_eq_segment, segment_self, inv_one]

/-- **The splitting step of the proof of MLS Proposition 4.3, p. 177**, along the coordinate
line `θ + s eₖ`. For Lean joints `j < k ≤ l`,
`g_{lj}(θ + s eₖ) = g_{lk}(θ) exp(−s ξ̂ₖ) g_{kj}(θ)`, where `g_{lj}` is the rigid motion
`relativeMotion l j` whose adjoint is `A_{lj}` (MLS writes `g_{lj} = g_{lk} g_{kj}`); only the
factor of joint `k` depends on `θₖ`, and `exp(ξ̂ₖ(θₖ + s)) = exp(ξ̂ₖθₖ) exp(ξ̂ₖs)`. -/
theorem relativeMotion_add_single_of_lt_of_le (θ : Fin n → ℝ) {l j k : Fin n} (hjk : j < k)
    (hkl : k ≤ l) (s : ℝ) :
    ch.relativeMotion l j (θ + s • Pi.single k 1) =
      ch.relativeMotion l k θ * Twist.exp (ch.chain.twist k) (-s) * ch.relativeMotion k j θ := by
  have hjk' : j.val + 1 ≤ k.val := hjk
  have hkl' : k.val ≤ l.val := hkl
  have hl : l.val < n := l.isLt
  rw [relativeMotion_eq_segment, relativeMotion_eq_segment, relativeMotion_eq_segment,
    ch.segment_split _ hjk' (by omega : k.val ≤ l.val + 1) (by omega),
    ch.segment_split _ (by omega : k.val ≤ k.val + 1) (by omega : k.val + 1 ≤ l.val + 1)
      (by omega),
    ch.segment_split θ hjk' (by omega : k.val ≤ k.val + 1) (by omega),
    ch.segment_single, ch.segment_single]
  have h1 : ch.segment (θ + s • Pi.single k 1) (j.val + 1) k.val =
      ch.segment θ (j.val + 1) k.val :=
    ch.segment_congr fun m _ hm => by
      have : m ≠ k := fun h => by rw [h] at hm; omega
      simp [this]
  have h2 : ch.segment (θ + s • Pi.single k 1) (k.val + 1) (l.val + 1) =
      ch.segment θ (k.val + 1) (l.val + 1) :=
    ch.segment_congr fun m hm _ => by
      have : m ≠ k := fun h => by rw [h] at hm; omega
      simp [this]
  have h3 : (θ + s • Pi.single k (1 : ℝ) : Fin n → ℝ) k = θ k + s := by simp
  rw [h1, h2, h3, Twist.exp_add, Twist.exp_neg]
  group

/-- **MLS p. 177, proof of Proposition 4.3: "for all other values of `k`".** Unless
`j < k ≤ l`, the rigid motion `g_{lj}` behind `A_{lj}` does not depend on `θₖ`: it is unchanged
along the coordinate line `θ + s eₖ`. -/
theorem relativeMotion_add_single_of_not (θ : Fin n → ℝ) {l j k : Fin n}
    (h : ¬ (j < k ∧ k ≤ l)) (s : ℝ) :
    ch.relativeMotion l j (θ + s • Pi.single k 1) = ch.relativeMotion l j θ := by
  rw [relativeMotion_eq_segment, relativeMotion_eq_segment,
    ch.segment_congr fun m hm1 hm2 => ?_]
  have : m ≠ k := by
    intro hmk
    subst hmk
    exact h ⟨Fin.lt_def.mpr (by omega), Fin.le_def.mpr (by omega)⟩
  simp [this]

end InertialChain

namespace Twist

/-- **The derivative of the adjoint action along a joint motion (MLS p. 177, proof of
Proposition 4.3).** For every rigid transform `G` and twists `ξ`, `η`, the coordinates of
`Ad_G Ad_{exp(−sξ̂)} η` have derivative at `s = 0` equal to those of `Ad_G [η, ξ]`, with the
bracket `[η, ξ] = (η̂ξ̂ − ξ̂η̂)∨` of MLS eq. (4.26) (`Twist.bracket`): the derivative of
`exp(−sξ̂) η̂ exp(sξ̂)` at `0` is `η̂ξ̂ − ξ̂η̂`. -/
theorem hasDerivAt_coordinates_adjoint_exp_neg (G : RigidTransform) (ξ η : Twist)
    (r : Fin 3 ⊕ Fin 3) :
    HasDerivAt (fun s : ℝ => (adjoint G (adjoint (exp ξ (-s)) η)).coordinates r)
      ((adjoint G (bracket η ξ)).coordinates r) 0 := by
  obtain ⟨a, b, hab⟩ := InertialChain.coordinates_eq_hat r
  have e : (fun s : ℝ => (adjoint G (adjoint (exp ξ (-s)) η)).coordinates r) =
      fun s => InertialChain.entryCLM a b (G.toHomogeneous * (NormedSpace.exp (s • -ξ.hat) *
        η.hat * NormedSpace.exp (s • ξ.hat)) * G.toHomogeneous⁻¹) := by
    funext s
    have h1 : (exp ξ (-s)).toHomogeneous = NormedSpace.exp (s • -ξ.hat) := by
      rw [toHomogeneous_exp, smul_neg, neg_smul]
    have h2 : (exp ξ (-s)).toHomogeneous⁻¹ = NormedSpace.exp (s • ξ.hat) := by
      rw [← RigidTransform.toHomogeneous_inv, exp_neg, inv_inv, toHomogeneous_exp]
    rw [hab, hat_adjoint, hat_adjoint, h2, h1]
    rfl
  rw [e]
  have hA := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-ξ.hat) (0 : ℝ)
  have hB := hasDerivAt_exp_smul_const (𝕂 := ℝ) ξ.hat (0 : ℝ)
  have hP := (((hA.mul_const η.hat).mul hB).const_mul G.toHomogeneous).mul_const
    G.toHomogeneous⁻¹
  refine ((InertialChain.entryCLM a b).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hP).congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  change (G.toHomogeneous * (-ξ.hat * η.hat + η.hat * ξ.hat) * G.toHomogeneous⁻¹) a b = _
  rw [hab, hat_adjoint, hat_bracket,
    show -ξ.hat * η.hat + η.hat * ξ.hat = η.hat * ξ.hat - ξ.hat * η.hat by noncomm_ring]

end Twist

namespace InertialChain

variable {n : ℕ} (ch : InertialChain n)

/-! ### The bracket formula for the partial derivatives of the inertia matrix (MLS eq. (4.30)) -/

/-- **MLS eq. (4.27), p. 176: `A_{lj}` with the printed zero case.** For Lean joints `j ≤ l`,
`A_{lj} ξ = Ad_{g_{lj}} ξ` with `g_{lj} = relativeMotion l j θ` the inverse of the product of
the joint motions strictly after joint `j` up to joint `l` (`A_{ll} = I`); for `l < j`,
`A_{lj} = 0` as printed. Lean indices are the book's minus one. -/
def relativeAdjoint (l j : Fin n) (θ : Fin n → ℝ) (ξ : Twist) : Twist :=
  if j ≤ l then Twist.adjoint (ch.relativeMotion l j θ) ξ else 0

/-- `A_{lj} = Ad_{g_{lj}}` for `j ≤ l` (MLS eq. (4.27), p. 176). -/
theorem relativeAdjoint_of_le {l j : Fin n} (h : j ≤ l) (θ : Fin n → ℝ) (ξ : Twist) :
    ch.relativeAdjoint l j θ ξ = Twist.adjoint (ch.relativeMotion l j θ) ξ :=
  ite_eq_left h

/-- `A_{lj} = 0` for `l < j` (MLS eq. (4.27), p. 176). -/
theorem relativeAdjoint_of_lt {l j : Fin n} (h : l < j) (θ : Fin n → ℝ) (ξ : Twist) :
    ch.relativeAdjoint l j θ ξ = 0 :=
  ite_eq_right (not_le.mpr h)

/-- `A_{lj}` is linear; in particular `A_{lj} 0 = 0` (MLS eq. (4.27), p. 176). -/
theorem relativeAdjoint_zero (l j : Fin n) (θ : Fin n → ℝ) : ch.relativeAdjoint l j θ 0 = 0 := by
  unfold relativeAdjoint
  split_ifs <;> simp [Twist.adjoint_zero]

/-- `A_{kk} = I` (MLS eq. (4.27), p. 176). -/
theorem relativeAdjoint_self (k : Fin n) (θ : Fin n → ℝ) (ξ : Twist) :
    ch.relativeAdjoint k k θ ξ = ξ := by
  rw [relativeAdjoint_of_le _ le_rfl, relativeMotion_self, Twist.adjoint_one]

/-- **MLS p. 177, proof of Proposition 4.3: `∂(A_{lj} ξⱼ)/∂θₖ = A_{lk} [A_{kj} ξⱼ, ξₖ]`**, for
all Lean joints `l, j, k` and every coordinate, as an actual derivative along the coordinate line
`s ↦ θ + s eₖ` at `s = 0`. The printed case split is absorbed by the zero convention: for
`j < k ≤ l` the splitting `g_{lj} = g_{lk} exp(−sξ̂ₖ) g_{kj}` gives the bracket; otherwise
`A_{lj}` does not depend on `θₖ` and the right side vanishes (`A_{kj} = 0` for `k < j`,
`[ξₖ, ξₖ] = 0` for `k = j`, `A_{lk} = 0` for `l < k`). -/
theorem hasDerivAt_relativeAdjoint_coordinates (θ : Fin n → ℝ) (l j k : Fin n)
    (r : Fin 3 ⊕ Fin 3) :
    HasDerivAt (fun s : ℝ =>
        (ch.relativeAdjoint l j (θ + s • Pi.single k 1) (ch.chain.twist j)).coordinates r)
      ((ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k j θ (ch.chain.twist j))
        (ch.chain.twist k))).coordinates r) 0 := by
  by_cases hm : j < k ∧ k ≤ l
  · have e : (fun s : ℝ =>
        (ch.relativeAdjoint l j (θ + s • Pi.single k 1) (ch.chain.twist j)).coordinates r) =
        fun s => (Twist.adjoint (ch.relativeMotion l k θ) (Twist.adjoint
          (Twist.exp (ch.chain.twist k) (-s))
            (Twist.adjoint (ch.relativeMotion k j θ) (ch.chain.twist j)))).coordinates r := by
      funext s
      rw [relativeAdjoint_of_le _ (hm.1.le.trans hm.2),
        ch.relativeMotion_add_single_of_lt_of_le θ hm.1 hm.2, Twist.adjoint_mul,
        Twist.adjoint_mul]
    rw [e, relativeAdjoint_of_le _ hm.2, relativeAdjoint_of_le _ hm.1.le]
    exact Twist.hasDerivAt_coordinates_adjoint_exp_neg _ _ _ r
  · have e : (fun s : ℝ =>
        (ch.relativeAdjoint l j (θ + s • Pi.single k 1) (ch.chain.twist j)).coordinates r) =
        fun _ => (ch.relativeAdjoint l j θ (ch.chain.twist j)).coordinates r := by
      funext s
      unfold relativeAdjoint
      rw [ch.relativeMotion_add_single_of_not θ hm]
    have h0 : (ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k j θ
        (ch.chain.twist j)) (ch.chain.twist k))).coordinates r = 0 := by
      rcases not_and_or.mp hm with hjk | hkl
      · rcases (not_lt.mp hjk).lt_or_eq with hlt | heq
        · rw [relativeAdjoint_of_lt _ hlt, Twist.bracket_zero_left, relativeAdjoint_zero,
            RigidBody.coordinates_zero]
          rfl
        · subst heq
          rw [relativeAdjoint_self, Twist.bracket_self, relativeAdjoint_zero,
            RigidBody.coordinates_zero]
          rfl
      · unfold relativeAdjoint
        rw [ite_eq_right hkl, RigidBody.coordinates_zero]
        rfl
    rw [e, h0]
    exact hasDerivAt_const _ _

/-- **MLS Proposition 4.3, eq. (4.29), p. 176, with the printed zero convention:**
`M(θ)ᵢⱼ = ∑_{l ≥ max(i,j)} (A_{li} ξᵢ)ᵀ 𝓜'_l (A_{lj} ξⱼ)` written with `relativeAdjoint`
(`massMatrix_apply_relativeMotion` with `A_{lj} = 0` for `l < j` made explicit). -/
theorem massMatrix_apply_relativeAdjoint (θ : Fin n → ℝ) (i j : Fin n) :
    ch.massMatrix θ i j =
      ∑ l ∈ Finset.univ.filter (fun l => i ≤ l ∧ j ≤ l),
        (ch.relativeAdjoint l i θ (ch.chain.twist i)).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l j θ (ch.chain.twist j)).coordinates) := by
  rw [massMatrix_apply_relativeMotion]
  refine Finset.sum_congr rfl fun l hl => ?_
  obtain ⟨hi, hj⟩ := (Finset.mem_filter.mp hl).2
  rw [relativeAdjoint_of_le _ hi, relativeAdjoint_of_le _ hj]

private theorem hasDerivAt_dotProduct_mulVec {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    {x y : ℝ → ι → ℝ} {x' y' : ι → ℝ} {t : ℝ}
    (hx : ∀ r, HasDerivAt (fun s => x s r) (x' r) t)
    (hy : ∀ r, HasDerivAt (fun s => y s r) (y' r) t) :
    HasDerivAt (fun s => x s ⬝ᵥ (P *ᵥ y s)) (x' ⬝ᵥ (P *ᵥ y t) + x t ⬝ᵥ (P *ᵥ y')) t := by
  simp only [dotProduct, Matrix.mulVec]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun r _ =>
    (hx r).mul (HasDerivAt.fun_sum fun c _ => (hy c).const_mul (P r c))

/-- **MLS eq. (4.30), p. 176, as an actual derivative along a coordinate line.** For every open
chain, the entry `Mᵢⱼ` along `s ↦ θ + s eₖ` has derivative at `s = 0`
`∑_{l ≥ max(i,j)} ([A_{ki} ξᵢ, ξₖ]ᵀ A_{lk}ᵀ 𝓜'_l A_{lj} ξⱼ + ξᵢᵀ A_{li}ᵀ 𝓜'_l A_{lk}`
`[A_{kj} ξⱼ, ξₖ])`,
written as pairings `(A_{lk} [A_{ki} ξᵢ, ξₖ]) ⬝ 𝓜'_l (A_{lj} ξⱼ) + (A_{li} ξᵢ) ⬝ 𝓜'_l
(A_{lk} [A_{kj} ξⱼ, ξₖ])` in six coordinates, with `𝓜'_l = Ad_{g_{sl_l}(0)⁻¹}ᵀ 𝓜_l
Ad_{g_{sl_l}(0)⁻¹}` of (4.28) and `A` as in `relativeAdjoint`. -/
theorem hasDerivAt_massMatrix_add_single (θ : Fin n → ℝ) (i j k : Fin n) :
    HasDerivAt (fun s : ℝ => ch.massMatrix (θ + s • Pi.single k 1) i j)
      (∑ l ∈ Finset.univ.filter (fun l => i ≤ l ∧ j ≤ l),
        ((ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k i θ (ch.chain.twist i))
            (ch.chain.twist k))).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l j θ (ch.chain.twist j)).coordinates) +
        (ch.relativeAdjoint l i θ (ch.chain.twist i)).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k j θ
              (ch.chain.twist j)) (ch.chain.twist k))).coordinates))) 0 := by
  have e : (fun s : ℝ => ch.massMatrix (θ + s • Pi.single k 1) i j) = fun s =>
      ∑ l ∈ Finset.univ.filter (fun l => i ≤ l ∧ j ≤ l),
        (ch.relativeAdjoint l i (θ + s • Pi.single k 1) (ch.chain.twist i)).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l j (θ + s • Pi.single k 1) (ch.chain.twist j)).coordinates) := by
    funext s
    exact ch.massMatrix_apply_relativeAdjoint _ i j
  rw [e]
  refine HasDerivAt.fun_sum fun l _ => ?_
  have h := hasDerivAt_dotProduct_mulVec (RigidBody.transformInertia (ch.linkRef l)⁻¹
    (ch.linkInertia l)) (ch.hasDerivAt_relativeAdjoint_coordinates θ l i k)
    (ch.hasDerivAt_relativeAdjoint_coordinates θ l j k)
  simpa using h

/-- **MLS Proposition 4.3, eq. (4.30), p. 176: the bracket formula for `∂Mᵢⱼ/∂θₖ`.** For every
open chain (arbitrary joint twists, reference link poses and link inertias), every configuration
and all Lean joints `i, j, k`, the Fréchet derivative of the entry `Mᵢⱼ` in the direction `eₖ`
is
`∑_{l ≥ max(i,j)} ([A_{ki} ξᵢ, ξₖ]ᵀ A_{lk}ᵀ 𝓜'_l A_{lj} ξⱼ + ξᵢᵀ A_{li}ᵀ 𝓜'_l A_{lk}`
`[A_{kj} ξⱼ, ξₖ])` with `A_{lj}` of (4.27) including `A_{lj} = 0` for `l < j`
(`relativeAdjoint`), `𝓜'_l` of (4.28) (`RigidBody.transformInertia (linkRef l)⁻¹`), and the
bracket of (4.26) (`Twist.bracket`, the vee of `ξ̂₁ξ̂₂ − ξ̂₂ξ̂₁`). The sum runs over `l` with
`i ≤ l` and `j ≤ l`, the printed `l = max(i, j), …, n` in Lean indices. -/
theorem massMatrixDeriv_single (θ : Fin n → ℝ) (i j k : Fin n) :
    ch.massMatrixDeriv θ i j (Pi.single k 1) =
      ∑ l ∈ Finset.univ.filter (fun l => i ≤ l ∧ j ≤ l),
        ((ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k i θ (ch.chain.twist i))
            (ch.chain.twist k))).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l j θ (ch.chain.twist j)).coordinates) +
        (ch.relativeAdjoint l i θ (ch.chain.twist i)).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k j θ
              (ch.chain.twist j)) (ch.chain.twist k))).coordinates)) := by
  have hline : HasDerivAt (fun s : ℝ => θ + s • Pi.single k (1 : ℝ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ))).const_add θ
  have h := (ch.hasFDerivAt_massMatrix θ i j).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact h.unique (ch.hasDerivAt_massMatrix_add_single θ i j k)

/-- **MLS eq. (4.30), p. 176, as the partial-derivative matrices used by the Christoffel
symbols:** `(∂M/∂θₖ)ᵢⱼ = Christoffel.partials (massMatrixDeriv θ) k i j` is the bracket formula
of `massMatrixDeriv_single`. -/
theorem partials_massMatrixDeriv (θ : Fin n → ℝ) (i j k : Fin n) :
    Christoffel.partials (ch.massMatrixDeriv θ) k i j =
      ∑ l ∈ Finset.univ.filter (fun l => i ≤ l ∧ j ≤ l),
        ((ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k i θ (ch.chain.twist i))
            (ch.chain.twist k))).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l j θ (ch.chain.twist j)).coordinates) +
        (ch.relativeAdjoint l i θ (ch.chain.twist i)).coordinates ⬝ᵥ
          (RigidBody.transformInertia (ch.linkRef l)⁻¹ (ch.linkInertia l) *ᵥ
            (ch.relativeAdjoint l k θ (Twist.bracket (ch.relativeAdjoint k j θ
              (ch.chain.twist j)) (ch.chain.twist k))).coordinates)) :=
  ch.massMatrixDeriv_single θ i j k

/-- **MLS Proposition 4.3, eq. (4.29), second line, p. 176:**
`Cᵢⱼ(θ, θ̇) = ½ ∑ₖ (∂Mᵢⱼ/∂θₖ + ∂Mᵢₖ/∂θⱼ − ∂Mₖⱼ/∂θᵢ) θ̇ₖ` for the Christoffel Coriolis matrix
(eq. (4.23)) of the actual partial derivatives of the inertia matrix of every open chain; each
partial derivative is given by the bracket formula (4.30) (`massMatrixDeriv_single`). -/
theorem coriolisMatrix_massMatrixDeriv_apply (θ θ' : Fin n → ℝ) (i j : Fin n) :
    Christoffel.coriolisMatrix (Christoffel.partials (ch.massMatrixDeriv θ)) θ' i j =
      (1 / 2 : ℝ) * ∑ k, (ch.massMatrixDeriv θ i j (Pi.single k 1) +
        ch.massMatrixDeriv θ i k (Pi.single j 1) - ch.massMatrixDeriv θ k j (Pi.single i 1)) *
          θ' k := by
  simp only [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials,
    Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end InertialChain
end RoboLean
