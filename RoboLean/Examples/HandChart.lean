import RoboLean.Dynamics.GraspChart
import RoboLean.Examples.HandGrasp

/-!
# The point-contact Cartesian hand as an instance of (6.18)–(6.22) through a chart

MLS Chapter 6, §2.1, printed pp. 277–278, eqs. (6.18)–(6.22), with the hand of ledger row G26: the
box of Example 5.2 (p. 221) held by two Cartesian fingers with point contacts with friction
(`Examples.pointHand`), and the object pose parameterized by the translational chart `x ↦ (I, x)`
(`Composite.translationalChart`, `Composite.isBodyJacobian_translationalChart`).

* The contact coefficients and the joints of the two fingers are relabeled by
  `pointHandIndex : (Σ _ : Fin 2, Fin 3) ≃ Fin 6` (finger `i`, coordinate `a` ↦ `3i + a`); the
  composite configuration is `q ∈ ℝ⁹`, object coordinates first (`finSumFinEquiv`).
* The hand Jacobian `J_h(θ, x)` of (6.18) obtained from (5.15) through the chart is invertible at
  every configuration (`isUnit_det_pointHand_chartHandJacobian`, MLS assumption 2 of p. 277), and
  `J_h⁻¹ Gᵀ = [I; I]` (`pointHand_inv_mul_transpose`): both fingertips move with the object.
* With constant symmetric finger inertias `M_{f₁}`, `M_{f₂}` and object inertia `M_o` (no
  potential), along every motion satisfying the grasp constraint near `t`, the Lagrange–d'Alembert
  equations of the hand–object system are `(M_o + M_{f₁} + M_{f₂}) ẍ = τ_{f₁} + τ_{f₂}`
  (`pointHand_lagrangeDAlembertAt_iff`), the effective dynamics (6.21) of this hand; the constraint
  is (5.15) by `Composite.pfaffianAt_handPfaffian_chart_iff`.

The inertias are arbitrary constant symmetric matrices chosen for the instance, not the inertia of a
physical Cartesian finger; nothing here models a physical hand.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Examples

open Composite Constrained

/-- **The relabeling of the two point-contact fingers' coordinates (MLS p. 276, stacked joints):**
finger `i`, coordinate `a` ↦ `3i + a`; used for the joints and for the contact coefficients. -/
def pointHandIndex : (Σ _ : Fin 2, Fin 3) ≃ Fin 6 :=
  (Equiv.sigmaEquivProd (Fin 2) (Fin 3)).trans finProdFinEquiv

/-- **The hand Jacobian of the point-contact Cartesian hand in local object coordinates (MLS eq.
(6.18), p. 277)**, from (5.15) through the translational chart. -/
def pointHandJacobian (μ r b : ℝ) (hμ : 0 < μ) (θ : Fin 6 → ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  chartHandJacobian (pointHand μ r b hμ) pointHandIndex pointHandIndex translationalChart θ x

/-- **The grasp map of the point-contact Cartesian hand in local object coordinates (MLS eq. (6.18),
p. 277):** `G(θ, x) = Jφᵀ G` for the translational chart. -/
def pointHandGrasp (μ r b : ℝ) (hμ : 0 < μ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 6) ℝ :=
  chartGrasp (pointHand μ r b hμ) pointHandIndex translationalChartJacobian x

/-- A rigid transform with identity rotation moves no free vector (MLS p. 37). -/
private theorem applyVector_of_rotation_eq_one {g : RigidTransform} (hg : g.rotation = 1)
    (w : Vec3) : g.applyVector w = w := by
  simp [RigidTransform.applyVector, hg]

/-- The inverse of a rigid transform with identity rotation moves no free vector (MLS p. 37). -/
private theorem inv_applyVector_of_rotation_eq_one {g : RigidTransform} (hg : g.rotation = 1)
    (w : Vec3) : g⁻¹.applyVector w = w := by
  have h := RigidTransform.mul_applyVector g⁻¹ g w
  rw [inv_mul_cancel, RigidTransform.one_applyVector, applyVector_of_rotation_eq_one hg] at h
  exact h.symm

/-- Block `i` of the point-contact hand at the translational chart pose reads the joint rates in
contact frame `i`: translations of the object and of the finger bases do not rotate (MLS eq. (5.13),
p. 236). -/
private theorem pointHand_fingerJacobian_chart (μ r b : ℝ) (hμ : 0 < μ) (x : Fin 3 → ℝ)
    (i : Fin 2) (θi v : Fin 3 → ℝ) :
    (pointHand μ r b hμ).fingerJacobian (translationalChart x) i θi v =
      (ContactModel.pointContact μ hμ).constraint
        (Twist.prismatic ((boxFrame r i)⁻¹.applyVector (WithLp.toLp 2 v))) := by
  rw [show pointHand μ r b hμ = boxHand (fun _ => ContactModel.pointContact μ hμ) r b from rfl,
    boxHand_fingerJacobian]
  have hv : (WithLp.toLp 2 ![v 0, v 1, v 2] : Vec3) = WithLp.toLp 2 v := by
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hv]
  simp only [HandGrasp.contactFrame, _root_.mul_inv_rev, inv_inv, RigidTransform.mul_applyVector]
  rw [applyVector_of_rotation_eq_one
      (g := (boxHand (fun _ => ContactModel.pointContact μ hμ) r b).base i)
      (by fin_cases i <;> rfl),
    inv_applyVector_of_rotation_eq_one (g := translationalChart x) rfl]
  rfl

/-- Row `(i, a)` of `J_h(θ, x) θ̇` for the point-contact hand (MLS eq. (6.18), p. 277). -/
private theorem pointHandJacobian_mulVec_apply (μ r b : ℝ) (hμ : 0 < μ) (θ : Fin 6 → ℝ)
    (x : Fin 3 → ℝ) (v : Fin 6 → ℝ) (i : Fin 2) (a : Fin 3) :
    (pointHandJacobian μ r b hμ θ x *ᵥ v) (pointHandIndex ⟨i, a⟩) =
      (ContactModel.pointContact μ hμ).constraint (Twist.prismatic ((boxFrame r i)⁻¹.applyVector
        (WithLp.toLp 2 fun l => v (pointHandIndex ⟨i, l⟩)))) a := by
  rw [pointHandJacobian, chartHandJacobian, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_apply, Equiv.symm_apply_apply]
  have hst : v ∘ pointHandIndex = ContactGrasp.stack (unstackJoints pointHandIndex v) := by
    funext c
    rfl
  rw [hst, HandGrasp.handJacobianMatrix_mulVec, ContactGrasp.stack_apply,
    HandGrasp.handJacobian_apply, pointHand_fingerJacobian_chart]
  rfl

/-- **MLS p. 277, assumption 2 ("The hand Jacobian is invertible"), for the point-contact Cartesian
hand:** `J_h(θ, x)` is invertible at every configuration. -/
theorem isUnit_det_pointHandJacobian (μ r b : ℝ) (hμ : 0 < μ) (θ : Fin 6 → ℝ) (x : Fin 3 → ℝ) :
    IsUnit (pointHandJacobian μ r b hμ θ x).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  intro y
  have hs : ∀ i : Fin 2, ∃ v : Fin 3 → ℝ,
      (ContactModel.pointContact μ hμ).constraint
        (Twist.prismatic ((boxFrame r i)⁻¹.applyVector (WithLp.toLp 2 v))) =
        fun a => y (pointHandIndex ⟨i, a⟩) := by
    intro i
    obtain ⟨v, hv⟩ := pointHand_fingerJacobian_surjective μ r b hμ (translationalChart x) i 0
      (fun a => y (pointHandIndex ⟨i, a⟩))
    exact ⟨v, by rw [← pointHand_fingerJacobian_chart μ r b hμ x i 0 v]; exact hv⟩
  choose v hv using hs
  refine ⟨fun j => v (pointHandIndex.symm j).1 (pointHandIndex.symm j).2, ?_⟩
  funext j
  obtain ⟨⟨i, a⟩, rfl⟩ := pointHandIndex.surjective j
  rw [pointHandJacobian_mulVec_apply]
  simp only [Equiv.symm_apply_apply]
  exact congrFun (hv i) a

/-- Row `(i, a)` of `Gᵀ(θ, x) ẋ` for the point-contact hand: the translation `(ẋ, 0)` read in
contact frame `i` (MLS eq. (6.18), p. 277, with `Twist.adjoint_prismatic`). -/
private theorem pointHandGrasp_transpose_mulVec_apply (μ r b : ℝ) (hμ : 0 < μ) (x w : Fin 3 → ℝ)
    (i : Fin 2) (a : Fin 3) :
    ((pointHandGrasp μ r b hμ x)ᵀ *ᵥ w) (pointHandIndex ⟨i, a⟩) =
      (ContactModel.pointContact μ hμ).constraint
        (Twist.prismatic ((boxFrame r i)⁻¹.applyVector (WithLp.toLp 2 w))) a := by
  have hJφ : translationalChartJacobian x *ᵥ w =
      (Twist.prismatic (WithLp.toLp 2 w)).coordinates := by
    funext s
    rcases s with k | k <;>
      simp [translationalChartJacobian, Matrix.mulVec, dotProduct, Twist.coordinates,
        Twist.prismatic]
  have key : ((pointHandGrasp μ r b hμ x)ᵀ *ᵥ w) (pointHandIndex ⟨i, a⟩) =
      ((localGrasp (pointHand μ r b hμ) (translationalChartJacobian x))ᵀ *ᵥ w) ⟨i, a⟩ := by
    simp [pointHandGrasp, chartGrasp, Matrix.mulVec, dotProduct]
  rw [key, localGrasp, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec,
    hJφ, ← SpatialGrasp.stack_graspTranspose, ContactGrasp.stack_apply,
    SpatialGrasp.graspTranspose_apply, Twist.adjoint_prismatic]
  rfl

/-- **`J_h⁻¹ Gᵀ = [I; I]` for the point-contact Cartesian hand (MLS p. 278, `θ̇ = J_h⁻¹ Gᵀ ẋ`):**
both fingertips move with the object, `θ̇_{fᵢ} = ẋ`. -/
theorem pointHand_inv_mul_transpose (μ r b : ℝ) (hμ : 0 < μ) (θ : Fin 6 → ℝ) (x : Fin 3 → ℝ) :
    (pointHandJacobian μ r b hμ θ x)⁻¹ * (pointHandGrasp μ r b hμ x)ᵀ =
      Matrix.of fun j a => if (pointHandIndex.symm j).2 = a then (1 : ℝ) else 0 := by
  have hJX : pointHandJacobian μ r b hμ θ x *
      Matrix.of (fun j a => if (pointHandIndex.symm j).2 = a then (1 : ℝ) else 0) =
      (pointHandGrasp μ r b hμ x)ᵀ := by
    apply Matrix.ext_of_mulVec_single
    intro k
    rw [← Matrix.mulVec_mulVec]
    funext j
    obtain ⟨⟨i, a⟩, rfl⟩ := pointHandIndex.surjective j
    rw [pointHandJacobian_mulVec_apply, pointHandGrasp_transpose_mulVec_apply]
    have e : (fun l => (Matrix.of (fun j a => if (pointHandIndex.symm j).2 = a then (1 : ℝ) else 0)
        *ᵥ Pi.single k 1) (pointHandIndex ⟨i, l⟩)) = Pi.single k 1 := by
      funext l
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e]
  rw [← hJX, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_pointHandJacobian μ r b hμ θ x), Matrix.one_mul]

/-- **Constant finger inertias of the point-contact Cartesian hand (MLS eq. (6.16), p. 276):**
`M_f = diag(M_{f₁}, M_{f₂})` on the relabeled joints. -/
def pointHandFingerInertia (Mf₁ Mf₂ : Matrix (Fin 3) (Fin 3) ℝ) (_θ : Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  (Matrix.blockDiagonal' fun i : Fin 2 => if i = 0 then Mf₁ else Mf₂).submatrix
    pointHandIndex.symm pointHandIndex.symm

/-- The gradient of the zero potential vanishes (MLS eq. (4.21)). -/
private theorem gradient_zero {k : ℕ} :
    Lagrangian.gradient (0 : (Fin k → ℝ) →L[ℝ] ℝ) = 0 :=
  rfl

/-- Constant inertia has zero Christoffel symbols and zero Coriolis matrix (MLS eq. (4.23)). -/
private theorem coriolisMatrix_partials_zero {k : ℕ} (v : Fin k → ℝ) :
    Christoffel.coriolisMatrix (Christoffel.partials 0) v = 0 := by
  ext i j
  simp [Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials]

/-- `[I; I]ᵀ w = w_{f₁} + w_{f₂}` (MLS p. 278, `G J_h⁻ᵀ = (J_h⁻¹ Gᵀ)ᵀ`). -/
private theorem pointHand_transpose_mulVec (w : Fin 6 → ℝ) :
    (Matrix.of fun j a => if (pointHandIndex.symm j).2 = a then (1 : ℝ) else 0)ᵀ *ᵥ w =
      fun a => w (pointHandIndex ⟨0, a⟩) + w (pointHandIndex ⟨1, a⟩) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
  rw [← pointHandIndex.sum_comp]
  simp [Fintype.sum_sigma, Fin.sum_univ_two]

/-- `[I; I]ᵀ M_f [I; I] = M_{f₁} + M_{f₂}` (MLS eq. (6.22), p. 278). -/
private theorem pointHand_congr_inertia (Mf₁ Mf₂ : Matrix (Fin 3) (Fin 3) ℝ) (θ : Fin 6 → ℝ) :
    (Matrix.of fun j a => if (pointHandIndex.symm j).2 = a then (1 : ℝ) else 0)ᵀ *
        pointHandFingerInertia Mf₁ Mf₂ θ *
        (Matrix.of fun j a => if (pointHandIndex.symm j).2 = a then (1 : ℝ) else 0) =
      Mf₁ + Mf₂ := by
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pointHand_transpose_mulVec]
  funext a
  simp only [Matrix.mulVec, dotProduct, pointHandFingerInertia, Matrix.submatrix_apply,
    Matrix.of_apply, Equiv.symm_apply_apply]
  rw [← pointHandIndex.sum_comp, ← pointHandIndex.sum_comp]
  simp [Fintype.sum_sigma, Matrix.blockDiagonal'_apply, Matrix.add_apply, Pi.single_apply]

/-- `M̃ = M_o + M_{f₁} + M_{f₂}` for the point-contact hand (MLS eq. (6.22), p. 278). -/
private theorem pointHand_effectiveMass (μ r b : ℝ) (hμ : 0 < μ)
    (Mo Mf₁ Mf₂ : Matrix (Fin 3) (Fin 3) ℝ) (θ : Fin 6 → ℝ) (x : Fin 3 → ℝ) :
    effectiveMass Mo (pointHandFingerInertia Mf₁ Mf₂ θ) (pointHandJacobian μ r b hμ θ x)
      (pointHandGrasp μ r b hμ x) = Mo + Mf₁ + Mf₂ := by
  rw [effectiveMass_eq, pointHand_inv_mul_transpose, pointHand_congr_inertia, add_assoc]

/-- **MLS eqs. (6.18)–(6.22), p. 278, for the point-contact Cartesian hand with the translational
chart:** for constant symmetric inertias `M_o`, `M_{f₁}`, `M_{f₂}` and no potential, along a motion
`q = (x, θ)` with velocity `q'` near `t` and acceleration `q''` at `t` satisfying the grasp
constraint (6.18) near `t` (equivalently (5.15), `pfaffianAt_handPfaffian_chart_iff`), the
Lagrange–d'Alembert equations with joint torques `τ` hold at `t` exactly when
`(M_o + M_{f₁} + M_{f₂}) ẍ = τ_{f₁} + τ_{f₂}`. -/
theorem pointHand_lagrangeDAlembertAt_iff (μ r b : ℝ) (hμ : 0 < μ)
    {Mo Mf₁ Mf₂ : Matrix (Fin 3) (Fin 3) ℝ} (hMo : Mo.IsSymm) (hMf₁ : Mf₁.IsSymm)
    (hMf₂ : Mf₂.IsSymm) {q q' : ℝ → Fin (3 + 6) → ℝ} {q'' : Fin (3 + 6) → ℝ} {t : ℝ}
    (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s) (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt
      (handPfaffian finSumFinEquiv
        (fun y => pointHandJacobian μ r b hμ (splitSnd finSumFinEquiv y)
          (splitFst finSumFinEquiv y))
        (fun y => pointHandGrasp μ r b hμ (splitFst finSumFinEquiv y))) (q s) (q' s))
    (τ : Fin 6 → ℝ) :
    LagrangeDAlembertAt
        (lagrangian finSumFinEquiv (Lagrangian.mechanical (fun _ => Mo) fun _ => 0)
          (Lagrangian.mechanical (pointHandFingerInertia Mf₁ Mf₂) fun _ => 0))
        (handPfaffian finSumFinEquiv
          (fun y => pointHandJacobian μ r b hμ (splitSnd finSumFinEquiv y)
            (splitFst finSumFinEquiv y))
          (fun y => pointHandGrasp μ r b hμ (splitFst finSumFinEquiv y)))
        q (handForce finSumFinEquiv τ) t ↔
      (Mo + Mf₁ + Mf₂) *ᵥ splitFst finSumFinEquiv q'' =
        fun a => τ (pointHandIndex ⟨0, a⟩) + τ (pointHandIndex ⟨1, a⟩) := by
  have hsymm : (Matrix.blockDiagonal' fun i : Fin 2 => if i = 0 then Mf₁ else Mf₂).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal'_transpose]
    congr 1
    funext i
    split_ifs
    · exact hMf₁
    · exact hMf₂
  have hJ : ∀ᶠ s in 𝓝 t, IsUnit (pointHandJacobian μ r b hμ (splitSnd finSumFinEquiv (q s))
      (splitFst finSumFinEquiv (q s))).det :=
    Filter.Eventually.of_forall fun s => isUnit_det_pointHandJacobian μ r b hμ _ _
  have hB : ∀ i j, HasDerivAt
      (fun s => ((pointHandJacobian μ r b hμ (splitSnd finSumFinEquiv (q s))
        (splitFst finSumFinEquiv (q s)))⁻¹ *
        (pointHandGrasp μ r b hμ (splitFst finSumFinEquiv (q s)))ᵀ) i j) (0 : ℝ) t := by
    intro i j
    simp only [pointHand_inv_mul_transpose]
    exact hasDerivAt_const t _
  rw [lagrangeDAlembertAt_handPfaffian_iff_effective finSumFinEquiv
    (Mo := fun _ => Mo) (Vo := fun _ => 0) (Mf := pointHandFingerInertia Mf₁ Mf₂)
    (Vf := fun _ => 0) (Mo' := 0) (Mf' := 0) (Vo' := 0) (Vf' := 0) (Bd := 0)
    (fun _ => hMo) (fun _ => hsymm.submatrix _)
    (fun i j => hasFDerivAt_const _ _) (hasFDerivAt_const _ _)
    (fun i j => hasFDerivAt_const _ _) (hasFDerivAt_const _ _) hq hq' hc hJ
    (fun i j => by simpa using hB i j) τ]
  rw [pointHand_effectiveMass, effectiveForce, ← transpose_inv_mul_transpose,
    pointHand_inv_mul_transpose, pointHand_transpose_mulVec]
  simp [coriolisMatrix_partials_zero, effectiveCoriolis, effectiveN, gradient_zero]

end Examples
end RoboLean
