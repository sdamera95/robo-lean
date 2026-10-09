import RoboLean.Geometry.Twist

/-!
# Adjoint transformations of twist coordinates

Twists are ordered `(v, ω)`. MLS printed p. 55, equation (2.58), defines
`Ad_(p,R) (v,ω) = (Rv + p × Rω, Rω)`. The coordinate definition below is
independent of homogeneous conjugation; `hat_adjoint` proves their agreement
(p. 56, Lemma 2.13). The inverse display on p. 56 and the derived composition
laws give ledger obligations X34–X37. These are algebraic statements for every
twist and proper rigid transform, without normalization or trajectory premises.

The adjoint is a real linear equivalence, not an asserted Euclidean isometry.
Frames, units, measured data, and differentiable velocity semantics are not
encoded by these statements.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Vec3

@[simp] theorem cross_add (u v w : Vec3) :
    cross u (v + w) = cross u v + cross u w := by
  apply WithLp.ofLp_injective
  exact (crossProduct (WithLp.ofLp u)).map_add _ _

@[simp] theorem add_cross (u v w : Vec3) :
    cross (u + v) w = cross u w + cross v w := by
  apply WithLp.ofLp_injective
  exact congrArg (fun f => f (WithLp.ofLp w)) (crossProduct.map_add _ _)

@[simp] theorem cross_smul (u v : Vec3) (c : ℝ) :
    cross u (c • v) = c • cross u v := by
  apply WithLp.ofLp_injective
  exact (crossProduct (WithLp.ofLp u)).map_smul c _

@[simp] theorem smul_cross (u v : Vec3) (c : ℝ) :
    cross (c • u) v = c • cross u v := by
  apply WithLp.ofLp_injective
  exact congrArg (fun f => f (WithLp.ofLp v)) (crossProduct.map_smul c _)

@[simp] theorem cross_zero (u : Vec3) : cross u 0 = 0 := by
  apply WithLp.ofLp_injective
  exact (crossProduct (WithLp.ofLp u)).map_zero

@[simp] theorem zero_cross (u : Vec3) : cross 0 u = 0 := by
  apply WithLp.ofLp_injective
  exact congrArg (fun f => f (WithLp.ofLp u)) crossProduct.map_zero

@[simp] theorem cross_neg (u v : Vec3) : cross u (-v) = -cross u v := by
  apply WithLp.ofLp_injective
  exact (crossProduct (WithLp.ofLp u)).map_neg _

@[simp] theorem neg_cross (u v : Vec3) : cross (-u) v = -cross u v := by
  simpa only [neg_one_smul] using smul_cross u v (-1)

theorem cross_anticomm (u v : Vec3) : cross u v = -cross v u := by
  apply WithLp.ofLp_injective
  exact (_root_.cross_anticomm (WithLp.ofLp v) (WithLp.ofLp u)).symm

end Vec3

namespace Twist

/-- MLS equation (2.58): the coordinate adjoint, with linear coordinates first. -/
def adjoint (g : RigidTransform) (ξ : Twist) : Twist :=
  (g.rotation.act ξ.linear + Vec3.cross g.translation (g.rotation.act ξ.angular),
    g.rotation.act ξ.angular)

@[simp] theorem adjoint_linear (g : RigidTransform) (ξ : Twist) :
    (adjoint g ξ).linear =
      g.rotation.act ξ.linear + Vec3.cross g.translation (g.rotation.act ξ.angular) := rfl

@[simp] theorem adjoint_angular (g : RigidTransform) (ξ : Twist) :
    (adjoint g ξ).angular = g.rotation.act ξ.angular := rfl

@[simp] theorem adjoint_add (g : RigidTransform) (ξ η : Twist) :
    adjoint g (ξ + η) = adjoint g ξ + adjoint g η := by
  apply Prod.ext
  · simp [adjoint, map_add, add_add_add_comm]
  · simp [adjoint, map_add]

@[simp] theorem adjoint_smul (g : RigidTransform) (c : ℝ) (ξ : Twist) :
    adjoint g (c • ξ) = c • adjoint g ξ := by
  apply Prod.ext <;> simp [adjoint, map_smul, smul_add]

@[simp] theorem adjoint_zero (g : RigidTransform) : adjoint g 0 = 0 := by
  apply Prod.ext <;> simp [adjoint]

/-- The adjoint packaged as a real linear map. -/
def adjointLinearMap (g : RigidTransform) : Twist →ₗ[ℝ] Twist where
  toFun := adjoint g
  map_add' := adjoint_add g
  map_smul' := adjoint_smul g

@[simp] theorem adjoint_one (ξ : Twist) : adjoint 1 ξ = ξ := by
  apply Prod.ext <;> simp [adjoint]

/-- Composition applies the right transform first, as for the rigid action. -/
@[simp] theorem adjoint_mul (g h : RigidTransform) (ξ : Twist) :
    adjoint (g * h) ξ = adjoint g (adjoint h ξ) := by
  apply Prod.ext
  · simp [adjoint, linear, angular, map_add, Rotation.act_cross, add_assoc]
  · simp [adjoint]

@[simp] theorem adjoint_inv_adjoint (g : RigidTransform) (ξ : Twist) :
    adjoint g⁻¹ (adjoint g ξ) = ξ := by
  rw [← adjoint_mul, inv_mul_cancel, adjoint_one]

@[simp] theorem adjoint_adjoint_inv (g : RigidTransform) (ξ : Twist) :
    adjoint g (adjoint g⁻¹ ξ) = ξ := by
  rw [← adjoint_mul, mul_inv_cancel, adjoint_one]

/-- Inversion of the adjoint is the adjoint of the inverse rigid transform. -/
def adjointEquiv (g : RigidTransform) : Twist ≃ₗ[ℝ] Twist where
  toFun := adjoint g
  invFun := adjoint g⁻¹
  left_inv := adjoint_inv_adjoint g
  right_inv := adjoint_adjoint_inv g
  map_add' := adjoint_add g
  map_smul' := adjoint_smul g

@[simp] theorem adjointEquiv_apply (g : RigidTransform) (ξ : Twist) :
    adjointEquiv g ξ = adjoint g ξ := rfl

@[simp] theorem adjointEquiv_symm_apply (g : RigidTransform) (ξ : Twist) :
    (adjointEquiv g).symm ξ = adjoint g⁻¹ ξ := rfl

/-- The explicit inverse coordinate formula from MLS printed p. 56. -/
theorem adjoint_inv (g : RigidTransform) (ξ : Twist) :
    adjoint g⁻¹ ξ =
      (g.rotation⁻¹.act (ξ.linear - Vec3.cross g.translation ξ.angular),
        g.rotation⁻¹.act ξ.angular) := by
  apply Prod.ext
  · simp [adjoint, Rotation.act_cross, sub_eq_add_neg]
  · rfl

private theorem hat_adjoint_intertwine (g : RigidTransform) (ξ : Twist) :
    (adjoint g ξ).hat * g.toHomogeneous = g.toHomogeneous * ξ.hat := by
  have hr : Vec3.hat (g.rotation.act ξ.angular) * g.rotation.val =
      g.rotation.val * Vec3.hat ξ.angular := by
    rw [Vec3.hat_act, mul_assoc, mul_assoc, Rotation.transpose_mul, mul_one]
  simp only [hat, adjoint, RigidTransform.toHomogeneous, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero]
  apply Matrix.ext_iff_blocks.mpr
  refine ⟨hr, ?_, rfl, rfl⟩
  ext i j
  change (Vec3.hat (g.rotation.act ξ.angular) *ᵥ WithLp.ofLp g.translation) i +
      (g.rotation.act ξ.linear + Vec3.cross g.translation (g.rotation.act ξ.angular)) i =
    (g.rotation.val *ᵥ WithLp.ofLp ξ.linear) i
  rw [Vec3.hat_mulVec]
  change (Vec3.cross (g.rotation.act ξ.angular) g.translation) i +
      ((g.rotation.act ξ.linear) i +
        (Vec3.cross g.translation (g.rotation.act ξ.angular)) i) =
    (g.rotation.act ξ.linear) i
  rw [Vec3.cross_anticomm (g.rotation.act ξ.angular) g.translation]
  simp only [PiLp.neg_apply]
  abel

/-- MLS Lemma 2.13: the independently defined coordinate adjoint agrees with
homogeneous conjugation. No twist normalization is required. -/
theorem hat_adjoint (g : RigidTransform) (ξ : Twist) :
    (adjoint g ξ).hat = g.toHomogeneous * ξ.hat * g.toHomogeneous⁻¹ := by
  have h := congrArg (fun A : HomogeneousMatrix => A * (g⁻¹).toHomogeneous)
    (hat_adjoint_intertwine g ξ)
  rw [mul_assoc, RigidTransform.toHomogeneous_mul_inv, mul_one] at h
  simpa only [RigidTransform.toHomogeneous_inv] using h

/-- Conjugation preserves the independent block-defined `se(3)` carrier. -/
theorem conjugation_mem_se3 (g : RigidTransform) (A : Se3) :
    g.toHomogeneous * A.val * g.toHomogeneous⁻¹ ∈ se3Submodule := by
  obtain ⟨ξ, rfl⟩ := hatLinearEquiv.surjective A
  change g.toHomogeneous * ξ.hat * g.toHomogeneous⁻¹ ∈ se3Submodule
  rw [← hat_adjoint]
  exact (hatLinearEquiv (adjoint g ξ)).property

/-- Conjugation as a linear equivalence of the independent twist-matrix space. -/
def se3AdjointEquiv (g : RigidTransform) : Se3 ≃ₗ[ℝ] Se3 :=
  hatLinearEquiv.symm.trans ((adjointEquiv g).trans hatLinearEquiv)

theorem se3AdjointEquiv_apply (g : RigidTransform) (A : Se3) :
    (se3AdjointEquiv g A).val =
      g.toHomogeneous * A.val * g.toHomogeneous⁻¹ := by
  obtain ⟨ξ, rfl⟩ := hatLinearEquiv.surjective A
  simp only [se3AdjointEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact hat_adjoint g ξ

/-- Six column coordinates, ordered linear then angular. -/
def coordinates (ξ : Twist) : Fin 3 ⊕ Fin 3 → ℝ :=
  Sum.elim (WithLp.ofLp ξ.linear) (WithLp.ofLp ξ.angular)

theorem coordinates_injective : Function.Injective coordinates := by
  intro ξ η h
  apply Prod.ext <;> ext i
  · exact congrFun h (Sum.inl i)
  · exact congrFun h (Sum.inr i)

/-- MLS equation (2.58), now as an explicit six-by-six block matrix. -/
def adjointMatrix (g : RigidTransform) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks g.rotation.val (Vec3.hat g.translation * g.rotation.val)
    0 g.rotation.val

/-- The block matrix acts by the separately defined twist-coordinate map. -/
theorem adjointMatrix_mulVec (g : RigidTransform) (ξ : Twist) :
    adjointMatrix g *ᵥ coordinates ξ = coordinates (adjoint g ξ) := by
  rw [adjointMatrix, coordinates, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    change (g.rotation.val *ᵥ WithLp.ofLp ξ.linear) i +
      ((Vec3.hat g.translation * g.rotation.val) *ᵥ WithLp.ofLp ξ.angular) i = _
    rw [← Matrix.mulVec_mulVec]
    change (g.rotation.act ξ.linear) i +
      (Vec3.hat g.translation *ᵥ WithLp.ofLp (g.rotation.act ξ.angular)) i = _
    rw [Vec3.hat_mulVec]
    rfl
  | inr i => simp [coordinates, adjoint, angular, Matrix.zero_mulVec, Rotation.act_apply]

private theorem coordinates_surjective : Function.Surjective coordinates := by
  intro x
  refine ⟨(WithLp.toLp 2 (fun i => x (Sum.inl i)),
    WithLp.toLp 2 (fun i => x (Sum.inr i))), ?_⟩
  funext i
  cases i <;> rfl

@[simp] theorem adjointMatrix_one : adjointMatrix 1 = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  obtain ⟨ξ, rfl⟩ := coordinates_surjective x
  rw [adjointMatrix_mulVec, adjoint_one, Matrix.one_mulVec]

/-- The adjoint matrices form a representation of the rigid-transform group. -/
@[simp] theorem adjointMatrix_mul (g h : RigidTransform) :
    adjointMatrix (g * h) = adjointMatrix g * adjointMatrix h := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  obtain ⟨ξ, rfl⟩ := coordinates_surjective x
  rw [← Matrix.mulVec_mulVec, adjointMatrix_mulVec, adjointMatrix_mulVec,
    adjointMatrix_mulVec, adjoint_mul]

/-- The inverse adjoint matrix is the adjoint matrix of the inverse transform. -/
@[simp] theorem adjointMatrix_inv (g : RigidTransform) :
    adjointMatrix g⁻¹ = (adjointMatrix g)⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  rw [← adjointMatrix_mul, inv_mul_cancel, adjointMatrix_one]

/-- Explicit inverse blocks from MLS p. 56; no six-dimensional orthogonality. -/
theorem adjointMatrix_inv_blocks (g : RigidTransform) :
    (adjointMatrix g)⁻¹ = Matrix.fromBlocks g.rotation.valᵀ
      (-(g.rotation.valᵀ * Vec3.hat g.translation)) 0 g.rotation.valᵀ := by
  rw [← adjointMatrix_inv, adjointMatrix]
  simp only [RigidTransform.inv_rotation, RigidTransform.inv_translation,
    Rotation.inv_val]
  have hn (v : Vec3) : Vec3.hat (-v) = -Vec3.hat v := by
    simpa only [neg_one_smul] using Vec3.hat_smul (-1) v
  rw [hn, Vec3.hat_act, Matrix.neg_mul, Rotation.inv_val,
    Matrix.transpose_transpose, mul_assoc, mul_assoc,
    Rotation.mul_transpose, mul_one]

/-- The six-coordinate representation, including identity and composition. -/
def adjointMatrixHom : RigidTransform →*
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ where
  toFun := adjointMatrix
  map_one' := adjointMatrix_one
  map_mul' := adjointMatrix_mul

end Twist

end RoboLean
