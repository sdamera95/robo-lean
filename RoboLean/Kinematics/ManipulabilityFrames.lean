import RoboLean.Kinematics.Manipulability
import RoboLean.Kinematics.ReferenceConfiguration

/-!
# Frame dependence of the manipulability measures (MLS Exercise 18)

MLS Exercise 18, printed p. 151: "In general, the manipulator Jacobian depends on the choice of
base and tool frames. Determine which of the manipulability measures described in Section 4.4 is
independent of the choice of base and/or tool frames."

The library's measures (MLS pp. 127–129) are computed from the body Jacobian `Jᵇ(θ)`
(MLS eq. (3.55), p. 117): `μ₁ = σ_min`, `μ₂ = σ_min / σ_max` and `μ₃ = det Jᵇ` for six joints.
This module proves:

* a change of base frame (`SerialChain.changeBase`) leaves the body Jacobian, hence its singular
  values and all three measures, unchanged;
* a change of tool frame (`SerialChain.changeTool h`, the tool frame moving with the
  end-effector) moves the body Jacobian by the adjoint `Ad_{h⁻¹}` (MLS eq. (2.58), p. 55), and
  `μ₃` is unchanged because `det Ad = 1`.

The dependence of `μ₁` and `μ₂` on the tool frame is not formalized here. Conventions: twists
`(v, ω)`, Lean column `i` is the book's column `i + 1`, real joint lift.
-/

noncomputable section

open scoped Matrix

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

private theorem jointMotions_changeBase (c : SerialChain n) (g : RigidTransform)
    (θ : Fin n → ℝ) :
    (c.changeBase g).jointMotions θ = (c.jointMotions θ).map (MulAut.conj g) := by
  rw [jointMotions, jointMotions, List.map_ofFn]
  congr 1
  funext i
  simp [changeBase, Twist.exp_adjoint]

/-- **MLS Exercise 18, p. 151, base frame.** The body Jacobian (MLS eq. (3.55), p. 117) does not
depend on the base frame: changing the base frame by `g_{s's} = g` leaves every column
`ξᵢ† = Ad⁻¹_{exp(ξ̂ᵢθᵢ) ⋯ exp(ξ̂ₙθₙ) g_st(0)} ξᵢ` unchanged, for every real joint vector. -/
theorem bodyJacobian_changeBase (c : SerialChain n) (g : RigidTransform) (θ : Fin n → ℝ) :
    (c.changeBase g).bodyJacobian θ = c.bodyJacobian θ := by
  funext i
  have hd : (((c.changeBase g).jointMotions θ).drop i).prod =
      g * ((c.jointMotions θ).drop i).prod * g⁻¹ := by
    rw [jointMotions_changeBase, ← List.map_drop, ← map_list_prod, MulAut.conj_apply]
  simp only [bodyJacobian, hd]
  simp only [changeBase, ← Twist.adjoint_mul]
  congr 1
  group

/-- **MLS Exercise 18, p. 151, base frame, matrix form.** The `6 × n` body Jacobian matrix does
not depend on the base frame. -/
theorem bodyJacobianMatrix_changeBase (c : SerialChain n) (g : RigidTransform)
    (θ : Fin n → ℝ) : (c.changeBase g).bodyJacobianMatrix θ = c.bodyJacobianMatrix θ := by
  simp only [bodyJacobianMatrix, bodyJacobian_changeBase]

/-- **MLS Exercise 18, p. 151, with pp. 127–129: the singular values and the measures `μ₁`,
`μ₂`, `μ₃` do not depend on the base frame** (the library's measures use the body Jacobian;
`μ₃` is stated for six joints). -/
theorem manipulability_changeBase (c : SerialChain n) (g : RigidTransform) (θ : Fin n → ℝ) :
    (c.changeBase g).jacobianSingularValues θ = c.jacobianSingularValues θ ∧
      (c.changeBase g).minSingularValue θ = c.minSingularValue θ ∧
      (c.changeBase g).inverseConditionNumber θ = c.inverseConditionNumber θ := by
  have h : (c.changeBase g).jacobianSingularValues θ = c.jacobianSingularValues θ := by
    simp only [jacobianSingularValues, bodyJacobianMatrix_changeBase]
  refine ⟨h, ?_, ?_⟩
  · simp only [minSingularValue, h]
  · simp only [inverseConditionNumber, minSingularValue, maxSingularValue, h]

/-- **MLS Exercise 18, p. 151, and Example 3.16, p. 129: `μ₃ = det Jᵇ` does not depend on the
base frame**, for a six-joint chain. -/
theorem jacobianDet_changeBase (c : SerialChain 6) (g : RigidTransform) (θ : Fin 6 → ℝ) :
    (c.changeBase g).jacobianDet θ = c.jacobianDet θ := by
  simp only [jacobianDet, bodyJacobianMatrix_changeBase]

/-- **MLS Exercise 18, p. 151, tool frame.** With a new tool frame `g_{tt'} = h` moving with the
end-effector, every body Jacobian column is moved by `Ad_{h⁻¹}` (MLS eq. (2.58), p. 55):
`ξᵢ†' = Ad_{h⁻¹} ξᵢ†`, for every real joint vector. -/
theorem bodyJacobian_changeTool (c : SerialChain n) (h : RigidTransform) (θ : Fin n → ℝ)
    (i : Fin n) :
    (c.changeTool h).bodyJacobian θ i = Twist.adjoint h⁻¹ (c.bodyJacobian θ i) := by
  simp only [bodyJacobian, ← Twist.adjoint_mul]
  simp only [changeTool]
  congr 1
  simp only [jointMotions, mul_inv_rev, mul_assoc]

/-- **MLS Exercise 18, p. 151, tool frame, matrix form.** The new body Jacobian matrix is the
old one multiplied on the left by the `6 × 6` adjoint matrix of `h⁻¹`. -/
theorem bodyJacobianMatrix_changeTool (c : SerialChain n) (h : RigidTransform)
    (θ : Fin n → ℝ) :
    (c.changeTool h).bodyJacobianMatrix θ =
      Twist.adjointMatrix h⁻¹ * c.bodyJacobianMatrix θ := by
  ext r i
  change ((c.changeTool h).bodyJacobian θ i).coordinates r =
    (Twist.adjointMatrix h⁻¹ *ᵥ (c.bodyJacobian θ i).coordinates) r
  rw [Twist.adjointMatrix_mulVec, bodyJacobian_changeTool]

/-- **MLS Exercise 18, p. 151, and Example 3.16, p. 129: `μ₃ = det Jᵇ` does not depend on the
tool frame**, for a six-joint chain, because `det Ad_{h⁻¹} = 1`. -/
theorem jacobianDet_changeTool (c : SerialChain 6) (h : RigidTransform) (θ : Fin 6 → ℝ) :
    (c.changeTool h).jacobianDet θ = c.jacobianDet θ := by
  rw [jacobianDet_eq_det_square, jacobianDet_eq_det_square, bodyJacobianMatrix_changeTool,
    ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm, Matrix.det_mul,
    Matrix.det_submatrix_equiv_self, Twist.det_adjointMatrix, one_mul]

end SerialChain

end RoboLean
