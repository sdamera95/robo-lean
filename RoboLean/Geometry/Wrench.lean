import RoboLean.Geometry.TwistAdjoint

/-!
# Wrenches and the twist–wrench pairing

MLS printed pp. 61–64, §2.5.1, uses wrench order `(f, τ)` and twist order
`(v, ω)`. A wrench's torque is about the origin of its stated frame. For
`g = g_AB`, `transform g` takes a wrench at B's origin to an equivalent wrench
at A's origin, expressed in A: `(Rf, p × Rf + Rτ)`.

The independently defined pairing is `f · v + τ · ω`. For compatible velocity
and force units this is instantaneous power. No trajectory integral, physical
contact model, or norm invariance for mixed force/torque coordinates is claimed.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- Force followed by moment about a stated frame origin, MLS printed p. 61.
Frame labels, origins, and units are conventions, not enforced by this type. -/
abbrev Wrench := Vec3 × Vec3

namespace Wrench

/-- The force component of a wrench. -/
abbrev force (F : Wrench) : Vec3 := F.1

/-- The moment component, about the origin of the wrench's stated frame. -/
abbrev torque (F : Wrench) : Vec3 := F.2

/-- The independent dual pairing; for velocity twists it is instantaneous power. -/
def pair (F : Wrench) (ξ : Twist) : ℝ :=
  inner ℝ F.force ξ.linear + inner ℝ F.torque ξ.angular

@[simp] theorem pair_zero_left (ξ : Twist) : pair 0 ξ = 0 := by
  simp [pair, force, torque]

@[simp] theorem pair_zero_right (F : Wrench) : pair F 0 = 0 := by
  simp [pair, Twist.linear, Twist.angular]

theorem pair_add_left (F G : Wrench) (ξ : Twist) :
    pair (F + G) ξ = pair F ξ + pair G ξ := by
  simp [pair, force, torque, inner_add_left]
  ring

theorem pair_add_right (F : Wrench) (ξ η : Twist) :
    pair F (ξ + η) = pair F ξ + pair F η := by
  simp [pair, Twist.linear, Twist.angular, inner_add_right]
  ring

theorem pair_smul_left (c : ℝ) (F : Wrench) (ξ : Twist) :
    pair (c • F) ξ = c * pair F ξ := by
  simp [pair, force, torque, inner_smul_left, mul_add]

theorem pair_smul_right (F : Wrench) (c : ℝ) (ξ : Twist) :
    pair F (c • ξ) = c * pair F ξ := by
  simp [pair, Twist.linear, Twist.angular, inner_smul_right, mul_add]

/-- The pairing as a real bilinear map into the algebraic dual of twists. -/
def pairing : Wrench →ₗ[ℝ] Twist →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := pair F
      map_add' := pair_add_right F
      map_smul' := fun c ξ => pair_smul_right F c ξ }
  map_add' F G := LinearMap.ext (pair_add_left F G)
  map_smul' c F := LinearMap.ext (pair_smul_left c F)

@[simp] theorem pairing_apply (F : Wrench) (ξ : Twist) : pairing F ξ = pair F ξ := rfl

/-- Pairing against every instantaneous twist distinguishes wrenches. -/
theorem ext_pair {F G : Wrench} (h : ∀ ξ : Twist, pair F ξ = pair G ξ) : F = G := by
  apply Prod.ext
  · apply ext_inner_right ℝ
    intro v
    simpa [pair, Twist.linear, Twist.angular] using h (v, 0)
  · apply ext_inner_right ℝ
    intro ω
    simpa [pair, Twist.linear, Twist.angular] using h (0, ω)

/-- Equality of pairing against all instantaneous motions in one frame.
This is pointwise equivalence, not a statement about time integrals. -/
def Equivalent (F G : Wrench) : Prop := ∀ ξ : Twist, pair F ξ = pair G ξ

theorem equivalent_iff_eq (F G : Wrench) : Equivalent F G ↔ F = G :=
  ⟨ext_pair, fun h => h ▸ fun _ => rfl⟩

/-- Transfer a wrench from B's origin to A's origin for `g = g_AB`.
The coordinate definition is independent of the adjoint matrix and pairing. -/
def transform (g : RigidTransform) (F : Wrench) : Wrench :=
  (g.rotation.act F.force,
    Vec3.cross g.translation (g.rotation.act F.force) + g.rotation.act F.torque)

@[simp] theorem transform_force (g : RigidTransform) (F : Wrench) :
    (transform g F).force = g.rotation.act F.force := rfl

@[simp] theorem transform_torque (g : RigidTransform) (F : Wrench) :
    (transform g F).torque =
      Vec3.cross g.translation (g.rotation.act F.force) + g.rotation.act F.torque := rfl

@[simp] theorem transform_add (g : RigidTransform) (F G : Wrench) :
    transform g (F + G) = transform g F + transform g G := by
  apply Prod.ext
  · simp [transform, force, map_add]
  · simp [transform, force, torque, map_add, add_add_add_comm]

@[simp] theorem transform_smul (g : RigidTransform) (c : ℝ) (F : Wrench) :
    transform g (c • F) = c • transform g F := by
  apply Prod.ext <;> simp [transform, force, torque, map_smul, smul_add]

@[simp] theorem transform_zero (g : RigidTransform) : transform g 0 = 0 := by
  apply Prod.ext <;> simp [transform, force, torque]

/-- Wrench transfer is linear for each fixed frame conversion. -/
def transformLinearMap (g : RigidTransform) : Wrench →ₗ[ℝ] Wrench where
  toFun := transform g
  map_add' := transform_add g
  map_smul' := transform_smul g

private theorem inner_cross_cancel (p f ω : Vec3) :
    inner ℝ f (Vec3.cross p ω) + inner ℝ (Vec3.cross p f) ω = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Vec3.cross, cross_apply,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- Compatible wrench and twist transformations preserve instantaneous power,
MLS printed p. 63 after equation (2.67). -/
theorem pair_transform_adjoint (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    pair (transform g F) (Twist.adjoint g ξ) = pair F ξ := by
  simp only [pair, transform_force, transform_torque, Twist.adjoint_linear,
    Twist.adjoint_angular, inner_add_left, inner_add_right, Rotation.inner_act]
  have h := inner_cross_cancel g.translation (g.rotation.act F.force)
    (g.rotation.act ξ.angular)
  linarith

/-- Wrench transfer is the dual of the inverse twist adjoint, characterized by
its action on every twist. The matrix-transpose identity is proved below. -/
theorem pair_transform (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    pair (transform g F) ξ = pair F (Twist.adjoint g⁻¹ ξ) := by
  simpa only [Twist.adjoint_adjoint_inv] using
    pair_transform_adjoint g F (Twist.adjoint g⁻¹ ξ)

/-- Pulling a spatial wrench back to body coordinates is dual to `Ad_g`. -/
theorem pair_transform_inv (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    pair (transform g⁻¹ F) ξ = pair F (Twist.adjoint g ξ) := by
  simpa only [inv_inv] using pair_transform g⁻¹ F ξ

@[simp] theorem transform_one (F : Wrench) : transform 1 F = F := by
  apply ext_pair
  intro ξ
  rw [pair_transform]
  simp

/-- Composition has the same frame-chain direction as rigid transforms. -/
@[simp] theorem transform_mul (g h : RigidTransform) (F : Wrench) :
    transform (g * h) F = transform g (transform h F) := by
  apply ext_pair
  intro ξ
  simp only [pair_transform, _root_.mul_inv_rev, Twist.adjoint_mul]

@[simp] theorem transform_inv_transform (g : RigidTransform) (F : Wrench) :
    transform g⁻¹ (transform g F) = F := by
  rw [← transform_mul, inv_mul_cancel, transform_one]

@[simp] theorem transform_transform_inv (g : RigidTransform) (F : Wrench) :
    transform g (transform g⁻¹ F) = F := by
  rw [← transform_mul, mul_inv_cancel, transform_one]

/-- Invertible wrench transfer; this is a linear equivalence, not a norm claim. -/
def transformEquiv (g : RigidTransform) : Wrench ≃ₗ[ℝ] Wrench where
  toFun := transform g
  invFun := transform g⁻¹
  left_inv := transform_inv_transform g
  right_inv := transform_transform_inv g
  map_add' := transform_add g
  map_smul' := transform_smul g

@[simp] theorem transformEquiv_apply (g : RigidTransform) (F : Wrench) :
    transformEquiv g F = transform g F := rfl

@[simp] theorem transformEquiv_symm_apply (g : RigidTransform) (F : Wrench) :
    (transformEquiv g).symm F = transform g⁻¹ F := rfl

/-- Six column coordinates, force before moment. -/
def coordinates (F : Wrench) : Fin 3 ⊕ Fin 3 → ℝ :=
  Sum.elim (WithLp.ofLp F.force) (WithLp.ofLp F.torque)

/-- The independently specified matrix of wrench transfer from B to A. -/
def transformMatrix (g : RigidTransform) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks g.rotation.val 0
    (Vec3.hat g.translation * g.rotation.val) g.rotation.val

/-- The block matrix agrees with the independent force/moment coordinate action. -/
theorem transformMatrix_mulVec (g : RigidTransform) (F : Wrench) :
    transformMatrix g *ᵥ coordinates F = coordinates (transform g F) := by
  rw [transformMatrix, coordinates, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    simp [coordinates, transform, force, Matrix.zero_mulVec, Rotation.act_apply]
  | inr i =>
    change ((Vec3.hat g.translation * g.rotation.val) *ᵥ WithLp.ofLp F.force) i +
      (g.rotation.val *ᵥ WithLp.ofLp F.torque) i = _
    rw [← Matrix.mulVec_mulVec]
    change (Vec3.hat g.translation *ᵥ WithLp.ofLp (g.rotation.act F.force)) i +
      (g.rotation.act F.torque) i = _
    rw [Vec3.hat_mulVec]
    rfl

/-- MLS equations (2.65)–(2.67), in the `g_AB` direction:
`F_A = Ad_(g_AB⁻¹)ᵀ F_B`, including the moment-origin shift. -/
theorem transformMatrix_eq_adjointMatrix_inv_transpose (g : RigidTransform) :
    transformMatrix g = (Twist.adjointMatrix g⁻¹)ᵀ := by
  rw [Twist.adjointMatrix_inv, Twist.adjointMatrix_inv_blocks,
    Matrix.fromBlocks_transpose]
  simp [transformMatrix, Matrix.transpose_mul, Vec3.hat_transpose]

theorem coordinates_transform (g : RigidTransform) (F : Wrench) :
    coordinates (transform g F) = (Twist.adjointMatrix g⁻¹)ᵀ *ᵥ coordinates F := by
  rw [← transformMatrix_eq_adjointMatrix_inv_transpose, transformMatrix_mulVec]

/-- Pairing is additive over a finite family already expressed in one frame. -/
theorem pair_sum_left {ι : Type*} (s : Finset ι) (F : ι → Wrench) (ξ : Twist) :
    pair (∑ i ∈ s, F i) ξ = ∑ i ∈ s, pair (F i) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, pair_add_left, ih]

/-- Sum equivalent wrenches after mapping every local frame to one common frame,
MLS printed pp. 63–64, Example 2.7. -/
def net {ι : Type*} (s : Finset ι) (g : ι → RigidTransform) (F : ι → Wrench) : Wrench :=
  ∑ i ∈ s, transform (g i) (F i)

/-- The net pairing is the sum of the local pairings with the corresponding
inverse-adjoint twists. The hypothesis that forces concern one physical body is
an interpretation of the common frame convention, not enforced by this type. -/
theorem pair_net {ι : Type*} (s : Finset ι) (g : ι → RigidTransform)
    (F : ι → Wrench) (ξ : Twist) :
    pair (net s g F) ξ = ∑ i ∈ s, pair (F i) (Twist.adjoint (g i)⁻¹ ξ) := by
  simp only [net, pair_sum_left, pair_transform]

/-- A common frame change commutes with the net-wrench sum. -/
theorem transform_net {ι : Type*} (s : Finset ι) (g : ι → RigidTransform)
    (F : ι → Wrench) (h : RigidTransform) :
    transform h (net s g F) = net s (fun i => h * g i) F := by
  change transformLinearMap h (∑ i ∈ s, transform (g i) (F i)) = _
  simp only [map_sum]
  simp only [net, transformLinearMap, LinearMap.coe_mk, AddHom.coe_mk, transform_mul]

end Wrench
end RoboLean
