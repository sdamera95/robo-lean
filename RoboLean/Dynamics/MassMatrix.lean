import RoboLean.Dynamics.RigidBodyInertia
import RoboLean.Kinematics.Jacobian

/-!
# Link Jacobians, the manipulator mass matrix and the kinetic energy of an open chain

MLS Chapter 4, §3.1, printed p. 168. For an open chain with `n` joints, a frame `Lᵢ` is
attached to the mass center of link `i`, with pose

`g_{slᵢ}(θ) = exp(ξ̂₁θ₁) ⋯ exp(ξ̂ᵢθᵢ) g_{slᵢ}(0)`

relative to the base frame `S`. Its body velocity is `Vᵇ_{slᵢ} = Jᵢ(θ) θ̇`, where the link body
Jacobian `Jᵢ = [ξ₁† ⋯ ξᵢ† 0 ⋯ 0]` has columns
`ξⱼ† = Ad⁻¹_{(exp(ξ̂ⱼθⱼ) ⋯ exp(ξ̂ᵢθᵢ) g_{slᵢ}(0))} ξⱼ` for `j ≤ i`. With the generalized
inertia `𝓜ᵢ` of link `i` in `Lᵢ` (eq. (4.9)), the link kinetic energy is
`Tᵢ = ½ θ̇ᵀ Jᵢᵀ 𝓜ᵢ Jᵢ θ̇` (4.17), the total kinetic energy is `T = ∑ᵢ Tᵢ = ½ θ̇ᵀ M(θ) θ̇` (4.18),
and the manipulator inertia matrix is `M(θ) = ∑ᵢ Jᵢᵀ 𝓜ᵢ Jᵢ` (4.19).

Indexing: Lean link `k : Fin n` is the link distal to Lean joint `k`, which is the book's
link `k + 1` (Lean joint `k` is the book's joint `k + 1`, as in `SerialChain`). Its frame is
moved by Lean joints `0, …, k`.

Construction: the frame of link `k` is the tool frame of `InertialChain.linkChain k`, the
chain whose joints after `k` are frozen (their twists replaced by `0`, so their motions are the
identity) and whose reference tool pose is `g_{sl_k}(0)`. Its body Jacobian, defined in
`RoboLean.Kinematics.Jacobian`, is then exactly the printed `n`-column `Jₖ` with zero columns
after `k` (`linkBodyJacobian_of_le`, `linkBodyJacobian_of_lt`), and E009's
`SerialChain.bodyVelocity_fk` gives `Vᵇ = Jₖ θ̇` for actual trajectories.

Positivity: MLS Lemma 4.2 (p. 171) states that `M(θ)` is symmetric and positive definite,
with the proof idea that the kinetic energy vanishes only at rest. Here symmetry needs
symmetric link inertias, semidefiniteness needs positive semidefinite link inertias, and
definiteness needs positive definite link inertias together with injectivity of the stacked
Jacobian `θ̇ ↦ (Jₖ θ̇)ₖ` (`massMatrix_posDef`, the assessment's inference; MLS lists no such
hypothesis). The stacked Jacobian is injective at every configuration as soon as every joint
twist is nonzero (`stackedJacobianInjective_of_twist_ne_zero`), which holds for the book's
unit-axis revolute and unit-direction prismatic joints. These are statements about the
coordinate model; physical realizability of the inertial parameters is not addressed.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

/-- An open-chain manipulator with inertial data, MLS §3.1, p. 168: the serial chain (joint
twists in base coordinates at `θ = 0`, MLS p. 87), the reference poses `g_{sl_k}(0)` of the link
frames `L_k` relative to the base frame `S`, and the generalized inertia `𝓜_k` of each link
expressed in its own frame `L_k` (eq. (4.9) when `L_k` is at the mass center). Lean link
`k : Fin n` is the link distal to Lean joint `k` (the book's link `k + 1`). The chain's tool
pose `chain.toolRef` is not used by the dynamics. No positivity is built in. -/
structure InertialChain (n : ℕ) where
  /-- The joints and their reference twists (MLS p. 87). -/
  chain : SerialChain n
  /-- The reference pose `g_{sl_k}(0)` of the frame of link `k` (MLS p. 168). -/
  linkRef : Fin n → RigidTransform
  /-- The generalized inertia `𝓜_k` of link `k` in its frame `L_k` (MLS p. 168, eq. (4.9)). -/
  linkInertia : Fin n → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ

namespace InertialChain

variable {n : ℕ} (ch : InertialChain n)

/-! ### Link frames and link body Jacobians (MLS p. 168) -/

/-- The chain that carries the frame of link `k` (MLS p. 168): the joints `0, …, k` keep their
twists, the joints after `k` are frozen (twist `0`, motion the identity), and the reference
tool pose is `g_{sl_k}(0)`. Its forward kinematics is the link pose `g_{sl_k}(θ)`. -/
def linkChain (k : Fin n) : SerialChain n where
  twist j := if j ≤ k then ch.chain.twist j else 0
  toolRef := ch.linkRef k

/-- The pose `g_{sl_k}(θ)` of the frame of link `k` relative to the base frame (MLS p. 168), as
the forward kinematics of `linkChain k`; `linkPose_eq` gives the printed product. -/
def linkPose (k : Fin n) (θ : Fin n → ℝ) : RigidTransform :=
  (ch.linkChain k).fk θ

/-- The body Jacobian `J_k = J^b_{sl_k}(θ)` of the frame of link `k` (MLS p. 168), as the
columns of the E009 body Jacobian (eq. (3.55)) of `linkChain k`. Twist order `(v, ω)`; Lean
column `j` is the book's column `j + 1`. -/
def linkBodyJacobian (k : Fin n) (θ : Fin n → ℝ) : Fin n → Twist :=
  (ch.linkChain k).bodyJacobian θ

private theorem linkChain_jointMotions (k : Fin n) (θ : Fin n → ℝ) :
    (ch.linkChain k).jointMotions θ =
      (ch.chain.jointMotions θ).take (k.val + 1) ++ List.replicate (n - (k.val + 1)) 1 := by
  apply List.ext_getElem
  · simp only [SerialChain.jointMotions, List.length_ofFn, List.length_append,
      List.length_take, List.length_replicate]
    omega
  · intro i h₁ h₂
    simp only [SerialChain.jointMotions, List.length_ofFn] at h₁
    by_cases hi : i ≤ k.val
    · have hlt : i < ((ch.chain.jointMotions θ).take (k.val + 1)).length := by
        simp only [SerialChain.jointMotions, List.length_take, List.length_ofFn]
        omega
      rw [List.getElem_append_left hlt, List.getElem_take]
      simp only [SerialChain.jointMotions, List.getElem_ofFn, linkChain]
      rw [ite_eq_left (by simpa [Fin.le_def] using hi)]
    · have hge : ((ch.chain.jointMotions θ).take (k.val + 1)).length ≤ i := by
        simp only [SerialChain.jointMotions, List.length_take, List.length_ofFn]
        omega
      rw [List.getElem_append_right hge, List.getElem_replicate]
      simp only [SerialChain.jointMotions, List.getElem_ofFn, linkChain]
      rw [ite_eq_right (by simpa [Fin.le_def] using hi), Twist.exp_zero_twist]

/-- **MLS p. 168: the link pose.** `g_{sl_k}(θ) = exp(ξ̂₁θ₁) ⋯ exp(ξ̂_{k+1}θ_{k+1}) g_{sl_k}(0)`,
the ordered product of the first `k + 1` joint motions of the chain (Lean joints `0..k`)
applied to the reference link pose. -/
theorem linkPose_eq (k : Fin n) (θ : Fin n → ℝ) :
    ch.linkPose k θ = ((ch.chain.jointMotions θ).take (k.val + 1)).prod * ch.linkRef k := by
  rw [linkPose, SerialChain.fk, SerialChain.poe, linkChain_jointMotions, List.prod_append,
    List.prod_replicate, one_pow, mul_one]
  rfl

/-- The link pose at the reference configuration is `g_{sl_k}(0)` (MLS p. 168). -/
@[simp] theorem linkPose_zero (k : Fin n) : ch.linkPose k 0 = ch.linkRef k :=
  SerialChain.fk_zero _

/-- **MLS p. 168: the columns `ξⱼ†` of the link body Jacobian, `j ≤ k`.**
`ξⱼ† = Ad⁻¹_{(exp(ξ̂ⱼθⱼ) ⋯ exp(ξ̂_{k+1}θ_{k+1}) g_{sl_k}(0))} ξⱼ`, where the product runs over the
joint motions from Lean joint `j` to Lean joint `k`; the inverse adjoint is the adjoint of the
inverse transform (MLS p. 56). -/
theorem linkBodyJacobian_of_le (k : Fin n) (θ : Fin n → ℝ) {j : Fin n} (hj : j ≤ k) :
    ch.linkBodyJacobian k θ j =
      Twist.adjoint ((((ch.chain.jointMotions θ).take (k.val + 1)).drop j.val).prod *
        ch.linkRef k)⁻¹ (ch.chain.twist j) := by
  have hlen : j.val ≤ ((ch.chain.jointMotions θ).take (k.val + 1)).length := by
    simp only [SerialChain.jointMotions, List.length_take, List.length_ofFn]
    have := Fin.le_def.mp hj
    omega
  simp only [linkBodyJacobian, SerialChain.bodyJacobian, linkChain_jointMotions,
    List.drop_append_of_le_length hlen, List.prod_append, List.prod_replicate, one_pow,
    mul_one]
  simp only [linkChain, ite_eq_left hj]

/-- **MLS p. 168: the columns after `k` of the link body Jacobian vanish**,
`J^b_{sl_k} = [ξ₁† ⋯ ξ_{k+1}† 0 ⋯ 0]`. -/
theorem linkBodyJacobian_of_lt (k : Fin n) (θ : Fin n → ℝ) {j : Fin n} (hj : k < j) :
    ch.linkBodyJacobian k θ j = 0 := by
  simp only [linkBodyJacobian, SerialChain.bodyJacobian, linkChain, ite_eq_right (not_le.mpr hj),
    Twist.adjoint_zero]

/-- The link pose curve has an actual homogeneous derivative along every differentiable joint
trajectory (MLS eqs. (3.51)–(3.54), applied to `linkChain k`); this shows that the derivative
hypotheses below are satisfiable. -/
theorem hasDerivAt_linkPose_toHomogeneous (k : Fin n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) :
    HasDerivAt (fun s => (ch.linkPose k (θ s)).toHomogeneous)
      ((∑ i, θ' i • (ch.linkChain k).spatialJacobian (θ t) i).hat *
        (ch.linkPose k (θ t)).toHomogeneous) t :=
  (ch.linkChain k).hasDerivAt_fk_toHomogeneous hθ

/-- **MLS p. 168: `Vᵇ_{sl_k} = J^b_{sl_k}(θ) θ̇`.** Along a joint trajectory with actual
derivatives `θ̇`, the actual body velocity `g⁻¹ ġ` of the frame of link `k`, computed from any
derivative `D` of its homogeneous pose, is `∑ⱼ θ̇ⱼ ξⱼ†`. -/
theorem bodyVelocity_linkPose (k : Fin n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (ch.linkPose k (θ s)).toHomogeneous) D t) :
    RigidTransform.bodyVelocity (fun s => ch.linkPose k (θ s)) D t hD =
      ∑ j, θ' j • ch.linkBodyJacobian k (θ t) j :=
  (ch.linkChain k).bodyVelocity_fk hθ hD

/-- The link body Jacobian as the real `6 × n` matrix of MLS p. 168: column `j` holds
`Twist.coordinates` of `ξⱼ†`, rows linear first (`Sum.inl`) then angular (`Sum.inr`). -/
def linkJacobianMatrix (k : Fin n) (θ : Fin n → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin n) ℝ :=
  Matrix.of fun r j => (ch.linkBodyJacobian k θ j).coordinates r

/-- The matrix view acts on joint rates as the column form, `J_k θ̇` in six coordinates
(MLS p. 168, `Vᵇ_{sl_k} = J_k θ̇`). -/
theorem linkJacobianMatrix_mulVec (k : Fin n) (θ θ' : Fin n → ℝ) :
    ch.linkJacobianMatrix k θ *ᵥ θ' = (∑ j, θ' j • ch.linkBodyJacobian k θ j).coordinates := by
  rw [RigidBody.coordinates_sum]
  funext r
  simp only [linkJacobianMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply,
    RigidBody.coordinates_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-! ### The manipulator inertia matrix and the kinetic energy (MLS eqs. (4.17)–(4.19)) -/

/-- **MLS eq. (4.19), p. 168: the manipulator inertia matrix** `M(θ) = ∑ₖ J_kᵀ(θ) 𝓜_k J_k(θ)`,
an `n × n` real matrix, with `J_k = linkJacobianMatrix k θ`. -/
def massMatrix (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k, (ch.linkJacobianMatrix k θ)ᵀ * ch.linkInertia k * ch.linkJacobianMatrix k θ

/-- **MLS eq. (4.18), p. 168: the kinetic energy of the manipulator** `T(θ, θ̇) = ½ θ̇ᵀ M(θ) θ̇`. -/
def kineticEnergy (θ θ' : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (θ' ⬝ᵥ (ch.massMatrix θ *ᵥ θ'))

/-- The bilinear form of the manipulator inertia matrix (MLS eqs. (4.17)–(4.19)):
`x ⬝ M(θ) y = ∑ₖ (J_k x) ⬝ 𝓜_k (J_k y)`. -/
theorem dotProduct_massMatrix_mulVec (θ x y : Fin n → ℝ) :
    x ⬝ᵥ (ch.massMatrix θ *ᵥ y) =
      ∑ k, (ch.linkJacobianMatrix k θ *ᵥ x) ⬝ᵥ
        (ch.linkInertia k *ᵥ (ch.linkJacobianMatrix k θ *ᵥ y)) := by
  rw [massMatrix, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun k _ => dotProduct_transpose_mul_mul_mulVec _ _ x y

/-- **MLS eq. (4.19), entrywise.** `M(θ)ᵢⱼ = ∑ₖ ξᵢ†ᵀ 𝓜_k ξⱼ†`, the columns `ξ†` taken from the
body Jacobian of link `k` (zero after `k`). -/
theorem massMatrix_apply (θ : Fin n → ℝ) (i j : Fin n) :
    ch.massMatrix θ i j =
      ∑ k, (ch.linkBodyJacobian k θ i).coordinates ⬝ᵥ
        (ch.linkInertia k *ᵥ (ch.linkBodyJacobian k θ j).coordinates) := by
  rw [massMatrix, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, linkJacobianMatrix, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **MLS eqs. (4.17)–(4.18), p. 168.** The kinetic energy `½ θ̇ᵀ M(θ) θ̇` is the sum over the
links of `½ (J_k θ̇)ᵀ 𝓜_k (J_k θ̇)`, the rigid-body kinetic energy (eq. (4.9)) of the twist
`J_k θ̇ = ∑ⱼ θ̇ⱼ ξⱼ†`. -/
theorem kineticEnergy_eq_sum (θ θ' : Fin n → ℝ) :
    ch.kineticEnergy θ θ' =
      ∑ k, RigidBody.kineticEnergy (ch.linkInertia k) (∑ j, θ' j • ch.linkBodyJacobian k θ j) := by
  rw [kineticEnergy, dotProduct_massMatrix_mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RigidBody.kineticEnergy, linkJacobianMatrix_mulVec]

/-- **MLS eqs. (4.17)–(4.18), p. 168, along an actual motion.** For a joint trajectory with
actual derivatives `θ̇` at `t`, and any actual derivatives `D k` of the link-frame poses, the
manipulator kinetic energy `½ θ̇ᵀ M(θ) θ̇` equals the sum of the link kinetic energies
`½ (Vᵇ_{sl_k})ᵀ 𝓜_k Vᵇ_{sl_k}` computed from the actual link body velocities. The derivatives
`D k` exist by `hasDerivAt_linkPose_toHomogeneous`. -/
theorem kineticEnergy_eq_sum_bodyVelocity {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) (D : Fin n → HomogeneousMatrix)
    (hD : ∀ k, HasDerivAt (fun s => (ch.linkPose k (θ s)).toHomogeneous) (D k) t) :
    ch.kineticEnergy (θ t) θ' =
      ∑ k, RigidBody.kineticEnergy (ch.linkInertia k)
        (RigidTransform.bodyVelocity (fun s => ch.linkPose k (θ s)) (D k) t (hD k)) := by
  rw [kineticEnergy_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ch.bodyVelocity_linkPose k hθ (hD k)]

/-! ### Symmetry and positivity (MLS Lemma 4.2, part 1, p. 171) -/

/-- **MLS Lemma 4.2(1), symmetry.** `M(θ)` is symmetric when every link inertia is. -/
theorem massMatrix_isSymm (h : ∀ k, (ch.linkInertia k).IsSymm) (θ : Fin n → ℝ) :
    (ch.massMatrix θ).IsSymm := by
  unfold Matrix.IsSymm massMatrix
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, (h k).eq,
    Matrix.mul_assoc]

/-- **MLS Lemma 4.2(1), semidefinite form.** `M(θ)` is positive semidefinite at every
configuration when every link inertia is positive semidefinite. -/
theorem massMatrix_posSemidef (h : ∀ k, (ch.linkInertia k).PosSemidef) (θ : Fin n → ℝ) :
    (ch.massMatrix θ).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  simpa using (h k).conjTranspose_mul_mul_same (ch.linkJacobianMatrix k θ)

/-- The stacked link Jacobian `θ̇ ↦ (J_k(θ) θ̇)_k` is injective at `θ`: only the zero joint rate
gives zero body velocity to every link frame. This is the nondegeneracy hypothesis under which
positive definite link inertias give a positive definite `M(θ)` (the inference recorded in the
project's MLS assessment, not a hypothesis printed in MLS Lemma 4.2, p. 171). -/
def StackedJacobianInjective (θ : Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ k, ch.linkJacobianMatrix k θ *ᵥ x = 0) → x = 0

/-- **MLS Lemma 4.2(1), positive definiteness, under explicit hypotheses.** If every link
inertia is positive definite and the stacked Jacobian is injective at `θ`, then `M(θ)` is
positive definite. MLS asserts positive definiteness of `M(θ)` without listing these
hypotheses; its proof appeals to the kinetic energy vanishing only at rest. -/
theorem massMatrix_posDef (h : ∀ k, (ch.linkInertia k).PosDef) {θ : Fin n → ℝ}
    (hJ : ch.StackedJacobianInjective θ) : (ch.massMatrix θ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have hs : ∀ k, (ch.linkInertia k).IsSymm := fun k => by simpa using (h k).isHermitian
    simpa using ch.massMatrix_isSymm hs θ
  · intro x hx
    simp only [star_trivial]
    rw [dotProduct_massMatrix_mulVec]
    obtain ⟨k, hk⟩ : ∃ k, ch.linkJacobianMatrix k θ *ᵥ x ≠ 0 := by
      by_contra hne
      exact hx (hJ x fun k => not_not.mp fun hk => hne ⟨k, hk⟩)
    refine Finset.sum_pos' (fun k _ => ?_) ⟨k, Finset.mem_univ k, ?_⟩
    · simpa using (h k).posSemidef.dotProduct_mulVec_nonneg (ch.linkJacobianMatrix k θ *ᵥ x)
    · simpa using (h k).dotProduct_mulVec_pos hk

/-- With positive definite link inertias, `M(θ)` is positive definite exactly when the stacked
Jacobian is injective at `θ` (MLS Lemma 4.2(1), p. 171): the hypothesis of `massMatrix_posDef`
is also necessary. -/
theorem massMatrix_posDef_iff (h : ∀ k, (ch.linkInertia k).PosDef) (θ : Fin n → ℝ) :
    (ch.massMatrix θ).PosDef ↔ ch.StackedJacobianInjective θ := by
  refine ⟨fun hM x hx => ?_, ch.massMatrix_posDef h⟩
  by_contra hne
  have hpos := hM.dotProduct_mulVec_pos hne
  simp only [star_trivial] at hpos
  rw [dotProduct_massMatrix_mulVec] at hpos
  simp [hx] at hpos

/-- **The stacked Jacobian is injective when every joint twist is nonzero**, at every
configuration. Column `k` of `J_k` is a nonzero adjoint image of the twist of Lean joint `k`,
and the columns after `k` vanish (MLS p. 168), so `J_k θ̇ = 0` for all `k` forces
`θ̇₀ = θ̇₁ = ⋯ = 0` in turn. -/
theorem stackedJacobianInjective_of_twist_ne_zero (h : ∀ j, ch.chain.twist j ≠ 0)
    (θ : Fin n → ℝ) : ch.StackedJacobianInjective θ := by
  intro x hx
  suffices hm : ∀ m : ℕ, ∀ j : Fin n, j.val < m → x j = 0 by
    funext j
    exact hm (j.val + 1) j (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact ih j hlt
    · have hsum : (∑ i, x i • ch.linkBodyJacobian j θ i) = 0 := by
        rw [← RigidBody.coordinates_eq_zero_iff, ← linkJacobianMatrix_mulVec]
        exact hx j
      rw [Finset.sum_eq_single j] at hsum
      · have hcol : ch.linkBodyJacobian j θ j ≠ 0 := by
          rw [linkBodyJacobian_of_le _ _ _ le_rfl]
          intro h0
          apply h j
          simpa using congrArg (Twist.adjoint ((((ch.chain.jointMotions θ).take
            (j.val + 1)).drop j.val).prod * ch.linkRef j)) h0
        exact (smul_eq_zero.mp hsum).resolve_right hcol
      · intro i _ hij
        rcases lt_or_gt_of_ne hij with hi | hi
        · rw [ih i (by rw [← heq]; exact hi), zero_smul]
        · rw [linkBodyJacobian_of_lt _ _ _ hi, smul_zero]
      · intro hj'
        exact absurd (Finset.mem_univ j) hj'

/-- **MLS Lemma 4.2(1) with explicit hypotheses.** If every link inertia is positive definite
and every joint twist is nonzero, the manipulator inertia matrix `M(θ)` is positive definite at
every configuration. -/
theorem massMatrix_posDef_of_twist_ne_zero (h : ∀ k, (ch.linkInertia k).PosDef)
    (hξ : ∀ j, ch.chain.twist j ≠ 0) (θ : Fin n → ℝ) : (ch.massMatrix θ).PosDef :=
  ch.massMatrix_posDef h (ch.stackedJacobianInjective_of_twist_ne_zero hξ θ)

/-- A revolute joint twist with unit axis (MLS p. 87) is nonzero: its angular part is the unit
axis. -/
theorem twist_ne_zero_of_isRevoluteJoint {ξ : Twist} (hξ : ξ.IsRevoluteJoint) : ξ ≠ 0 := by
  obtain ⟨ω, q, hω, rfl⟩ := hξ
  intro h0
  have ha : (Twist.revolute ω q).angular = (0 : Twist).angular := by rw [h0]
  have hω0 : ω = 0 := ha
  rw [hω0, norm_zero] at hω
  exact zero_ne_one hω

/-- A prismatic joint twist with unit direction (MLS p. 87) is nonzero: its linear part is the
unit direction. -/
theorem twist_ne_zero_of_isPrismaticJoint {ξ : Twist} (hξ : ξ.IsPrismaticJoint) : ξ ≠ 0 := by
  obtain ⟨v, hv, rfl⟩ := hξ
  intro h0
  have hl : (Twist.prismatic v).linear = (0 : Twist).linear := by rw [h0]
  have hv0 : v = 0 := hl
  rw [hv0, norm_zero] at hv
  exact zero_ne_one hv

/-- **MLS Lemma 4.2(1), for chains of revolute and prismatic joints (p. 83, p. 87).** If every
joint is a unit-axis revolute or unit-direction prismatic joint and every link inertia is
positive definite, then `M(θ)` is symmetric positive definite at every configuration. -/
theorem massMatrix_posDef_of_joints (h : ∀ k, (ch.linkInertia k).PosDef)
    (hj : ∀ j, (ch.chain.twist j).IsRevoluteJoint ∨ (ch.chain.twist j).IsPrismaticJoint)
    (θ : Fin n → ℝ) : (ch.massMatrix θ).PosDef :=
  ch.massMatrix_posDef_of_twist_ne_zero h
    (fun j => (hj j).elim twist_ne_zero_of_isRevoluteJoint twist_ne_zero_of_isPrismaticJoint) θ

/-- **MLS p. 171, proof of Lemma 4.2(1): the kinetic energy vanishes only at rest.** If `M(θ)` is
positive definite (for example by `massMatrix_posDef_of_joints`), then `½ θ̇ᵀ M(θ) θ̇ = 0`
exactly when `θ̇ = 0`. -/
theorem kineticEnergy_eq_zero_iff {θ : Fin n → ℝ} (hM : (ch.massMatrix θ).PosDef)
    (θ' : Fin n → ℝ) : ch.kineticEnergy θ θ' = 0 ↔ θ' = 0 := by
  constructor
  · intro h0
    by_contra hne
    have hpos := hM.dotProduct_mulVec_pos hne
    simp only [star_trivial] at hpos
    rw [kineticEnergy] at h0
    linarith
  · rintro rfl
    simp [kineticEnergy]

end InertialChain
end RoboLean
