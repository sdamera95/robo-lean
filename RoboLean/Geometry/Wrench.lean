import RoboLean.Geometry.TwistAdjoint

/-!
# Wrenches and the twist–wrench pairing

MLS printed pp. 61–64, §2.5.1, uses wrench order `(f, τ)` and twist order
`(v, ω)`. A wrench's torque is about the origin of its stated frame. For
`g = g_AB`, `transform g` takes a wrench at B's origin to an equivalent wrench
at A's origin, expressed in A: `(Rf, p × Rf + Rτ)`.

`Wrench` is a structure with fields `force` and `torque`, so it is a type
distinct from `Twist` (itself a two-field structure): a twist is rejected
where a wrench is expected, and conversely. Its additive group and real vector
space structures are componentwise, transported from `Vec3 × Vec3` along the
private component map. No coercion between twists and wrenches is declared;
the twist–wrench relations in the library are named maps: the pairing below,
`Wrench.toTwist`, and `Twist.swapWrench`. No norm or topology is put on
`Wrench`.

The independently defined pairing is `f · v + τ · ω`. For compatible velocity
and force units this is instantaneous power. No trajectory integral, physical
contact model, or norm invariance for mixed force/torque coordinates is claimed.
-/

noncomputable section

open Matrix

namespace RoboLean

/-- A wrench, MLS printed p. 61: force `f` followed by moment `τ` about the
origin of a stated frame, `F = (f, τ)`. This is a structure, hence a type
distinct from `Twist`; frame labels, origins, and units are conventions not
enforced by this type. -/
@[ext]
structure Wrench where
  /-- Build a wrench from its force and its moment, MLS printed p. 61. -/
  mk ::
  /-- The linear component `f`, MLS printed p. 61. -/
  force : Vec3
  /-- The rotational component `τ`, the moment about the origin of the wrench's
  stated frame, MLS printed p. 61. -/
  torque : Vec3

/-- Two wrenches are equal when their force and moment coordinates are equal
(MLS printed p. 61, wrench coordinates `(f, τ)`). -/
add_decl_doc Wrench.ext

/-- Wrenches are equal exactly when their force and moment coordinates are equal
(MLS printed p. 61, wrench coordinates `(f, τ)`). -/
add_decl_doc Wrench.ext_iff

namespace Wrench

/-- The zero wrench, with zero force and zero moment (MLS printed p. 61 coordinates). -/
instance instZero : Zero Wrench := ⟨⟨0, 0⟩⟩

/-- Componentwise sum of forces and moments. MLS printed p. 63 adds wrenches only
after expressing them in one frame about one origin; the type does not enforce that. -/
instance instAdd : Add Wrench := ⟨fun F G => ⟨F.force + G.force, F.torque + G.torque⟩⟩

/-- Componentwise negation of force and moment (MLS printed p. 61 coordinates). -/
instance instNeg : Neg Wrench := ⟨fun F => ⟨-F.force, -F.torque⟩⟩

/-- Componentwise difference of forces and moments (MLS printed p. 61 coordinates). -/
instance instSub : Sub Wrench := ⟨fun F G => ⟨F.force - G.force, F.torque - G.torque⟩⟩

/-- Componentwise scalar action on force and moment, for every scalar type acting
on `Vec3` (MLS printed p. 61 coordinates). -/
instance instSMul {R : Type*} [SMul R Vec3] : SMul R Wrench :=
  ⟨fun c F => ⟨c • F.force, c • F.torque⟩⟩

/-- The zero wrench has zero force (MLS printed p. 61 coordinates). -/
@[simp] theorem zero_force : (0 : Wrench).force = 0 := rfl

/-- The zero wrench has zero moment (MLS printed p. 61 coordinates). -/
@[simp] theorem zero_torque : (0 : Wrench).torque = 0 := rfl

/-- Forces add under the componentwise sum (MLS printed p. 63, wrenches in one frame). -/
@[simp] theorem add_force (F G : Wrench) : (F + G).force = F.force + G.force := rfl

/-- Moments add under the componentwise sum (MLS printed p. 63, wrenches in one frame). -/
@[simp] theorem add_torque (F G : Wrench) : (F + G).torque = F.torque + G.torque := rfl

/-- Negation negates the force (MLS printed p. 61 coordinates). -/
@[simp] theorem neg_force (F : Wrench) : (-F).force = -F.force := rfl

/-- Negation negates the moment (MLS printed p. 61 coordinates). -/
@[simp] theorem neg_torque (F : Wrench) : (-F).torque = -F.torque := rfl

/-- Forces subtract under the componentwise difference (MLS printed p. 61 coordinates). -/
@[simp] theorem sub_force (F G : Wrench) : (F - G).force = F.force - G.force := rfl

/-- Moments subtract under the componentwise difference (MLS printed p. 61 coordinates). -/
@[simp] theorem sub_torque (F G : Wrench) : (F - G).torque = F.torque - G.torque := rfl

/-- A scalar scales the force (MLS printed p. 61 coordinates). -/
@[simp] theorem smul_force {R : Type*} [SMul R Vec3] (c : R) (F : Wrench) :
    (c • F).force = c • F.force := rfl

/-- A scalar scales the moment (MLS printed p. 61 coordinates). -/
@[simp] theorem smul_torque {R : Type*} [SMul R Vec3] (c : R) (F : Wrench) :
    (c • F).torque = c • F.torque := rfl

/-- Component pair, used only to transport algebraic structure. It is not a
twist–wrench identification. -/
private def toProd (F : Wrench) : Vec3 × Vec3 := (F.force, F.torque)

private theorem toProd_injective : Function.Injective toProd := fun _ _ h =>
  Wrench.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The componentwise additive group of wrenches, transported from `Vec3 × Vec3`
(MLS printed p. 61, `F ∈ ℝ⁶`). -/
instance instAddCommGroup : AddCommGroup Wrench :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The componentwise real vector space of wrenches, transported from
`Vec3 × Vec3` (MLS printed p. 61, `F ∈ ℝ⁶`). -/
instance instModule : Module ℝ Wrench :=
  Function.Injective.module ℝ (AddMonoidHom.mk' toProd fun _ _ => rfl) toProd_injective
    fun _ _ => rfl

/-- Linear version of the component pair, used only for finite-dimensionality. -/
private def toProdLinearEquiv : Wrench ≃ₗ[ℝ] Vec3 × Vec3 where
  toFun := toProd
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Wrenches form a finite-dimensional real vector space (MLS printed p. 61, `F ∈ ℝ⁶`). -/
instance instFiniteDimensional : FiniteDimensional ℝ Wrench :=
  Module.Finite.equiv toProdLinearEquiv.symm

/-- The wrench space has real dimension six (MLS printed p. 61, `F ∈ ℝ⁶`). -/
theorem finrank_eq_six : Module.finrank ℝ Wrench = 6 := by
  rw [toProdLinearEquiv.finrank_eq]
  simp [Vec3, Module.finrank_prod]

/-- The independent dual pairing `f · v + τ · ω`, MLS printed p. 61 (`δW = V · F`);
for velocity twists it is instantaneous power. -/
def pair (F : Wrench) (ξ : Twist) : ℝ :=
  inner ℝ F.force ξ.linear + inner ℝ F.torque ξ.angular

/-- The zero wrench pairs to zero with every twist (MLS printed p. 61 pairing). -/
@[simp] theorem pair_zero_left (ξ : Twist) : pair 0 ξ = 0 := by
  simp [pair]

/-- Every wrench pairs to zero with the zero twist (MLS printed p. 61 pairing). -/
@[simp] theorem pair_zero_right (F : Wrench) : pair F 0 = 0 := by
  simp [pair]

/-- The pairing is additive in the wrench (MLS printed p. 61 pairing). -/
theorem pair_add_left (F G : Wrench) (ξ : Twist) :
    pair (F + G) ξ = pair F ξ + pair G ξ := by
  simp [pair, inner_add_left]
  ring

/-- The pairing is additive in the twist (MLS printed p. 61 pairing). -/
theorem pair_add_right (F : Wrench) (ξ η : Twist) :
    pair F (ξ + η) = pair F ξ + pair F η := by
  simp [pair, inner_add_right]
  ring

/-- The pairing is homogeneous in the wrench (MLS printed p. 61 pairing). -/
theorem pair_smul_left (c : ℝ) (F : Wrench) (ξ : Twist) :
    pair (c • F) ξ = c * pair F ξ := by
  simp [pair, inner_smul_left, mul_add]

/-- The pairing is homogeneous in the twist (MLS printed p. 61 pairing). -/
theorem pair_smul_right (F : Wrench) (c : ℝ) (ξ : Twist) :
    pair F (c • ξ) = c * pair F ξ := by
  simp [pair, inner_smul_right, mul_add]

/-- The pairing as a real bilinear map into the algebraic dual of twists
(MLS printed p. 61). -/
def pairing : Wrench →ₗ[ℝ] Twist →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := pair F
      map_add' := pair_add_right F
      map_smul' := fun c ξ => pair_smul_right F c ξ }
  map_add' F G := LinearMap.ext (pair_add_left F G)
  map_smul' c F := LinearMap.ext (pair_smul_left c F)

/-- The bilinear pairing evaluates to `pair` (MLS printed p. 61). -/
@[simp] theorem pairing_apply (F : Wrench) (ξ : Twist) : pairing F ξ = pair F ξ := rfl

/-- Pairing against every instantaneous twist distinguishes wrenches
(MLS printed p. 62, equivalent wrenches). -/
theorem ext_pair {F G : Wrench} (h : ∀ ξ : Twist, pair F ξ = pair G ξ) : F = G := by
  apply Wrench.ext
  · apply ext_inner_right ℝ
    intro v
    simpa [pair, Twist.linear, Twist.angular] using h ⟨v, 0⟩
  · apply ext_inner_right ℝ
    intro ω
    simpa [pair, Twist.linear, Twist.angular] using h ⟨0, ω⟩

/-- Equality of pairing against all instantaneous motions in one frame, MLS
printed p. 62 (equivalent wrenches). This is pointwise equivalence, not a
statement about time integrals. -/
def Equivalent (F G : Wrench) : Prop := ∀ ξ : Twist, pair F ξ = pair G ξ

/-- Pointwise equivalence of wrenches is equality of coordinates (MLS printed p. 62). -/
theorem equivalent_iff_eq (F G : Wrench) : Equivalent F G ↔ F = G :=
  ⟨ext_pair, fun h => h ▸ fun _ => rfl⟩

/-- Transfer a wrench from B's origin to A's origin for `g = g_AB`, MLS printed
p. 62, equations (2.65)–(2.66). The coordinate definition is independent of the
adjoint matrix and pairing. -/
def transform (g : RigidTransform) (F : Wrench) : Wrench :=
  ⟨g.rotation.act F.force,
    Vec3.cross g.translation (g.rotation.act F.force) + g.rotation.act F.torque⟩

/-- The transferred force is the rotated force, MLS printed p. 62, equation (2.66). -/
@[simp] theorem transform_force (g : RigidTransform) (F : Wrench) :
    (transform g F).force = g.rotation.act F.force := rfl

/-- The transferred moment includes the origin-shift term, MLS printed p. 62,
equation (2.66). -/
@[simp] theorem transform_torque (g : RigidTransform) (F : Wrench) :
    (transform g F).torque =
      Vec3.cross g.translation (g.rotation.act F.force) + g.rotation.act F.torque := rfl

/-- Wrench transfer is additive (MLS printed p. 62, equation (2.66)). -/
@[simp] theorem transform_add (g : RigidTransform) (F G : Wrench) :
    transform g (F + G) = transform g F + transform g G := by
  apply Wrench.ext
  · simp [transform, map_add]
  · simp [transform, map_add, add_add_add_comm]

/-- Wrench transfer is homogeneous (MLS printed p. 62, equation (2.66)). -/
@[simp] theorem transform_smul (g : RigidTransform) (c : ℝ) (F : Wrench) :
    transform g (c • F) = c • transform g F := by
  apply Wrench.ext <;> simp [transform, map_smul, smul_add]

/-- Wrench transfer fixes the zero wrench (MLS printed p. 62, equation (2.66)). -/
@[simp] theorem transform_zero (g : RigidTransform) : transform g 0 = 0 := by
  apply Wrench.ext <;> simp [transform]

/-- Wrench transfer is linear for each fixed frame conversion (MLS printed p. 62). -/
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
its action on every twist, MLS printed p. 62, equation (2.65). The
matrix-transpose identity is proved below. -/
theorem pair_transform (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    pair (transform g F) ξ = pair F (Twist.adjoint g⁻¹ ξ) := by
  simpa only [Twist.adjoint_adjoint_inv] using
    pair_transform_adjoint g F (Twist.adjoint g⁻¹ ξ)

/-- Pulling a spatial wrench back to body coordinates is dual to `Ad_g`,
MLS printed p. 63, equation (2.67). -/
theorem pair_transform_inv (g : RigidTransform) (F : Wrench) (ξ : Twist) :
    pair (transform g⁻¹ F) ξ = pair F (Twist.adjoint g ξ) := by
  simpa only [inv_inv] using pair_transform g⁻¹ F ξ

/-- The identity frame change fixes every wrench (MLS printed p. 62, equation (2.65)). -/
@[simp] theorem transform_one (F : Wrench) : transform 1 F = F := by
  apply ext_pair
  intro ξ
  rw [pair_transform]
  simp

/-- Composition has the same frame-chain direction as rigid transforms
(MLS printed p. 62, equation (2.65)). -/
@[simp] theorem transform_mul (g h : RigidTransform) (F : Wrench) :
    transform (g * h) F = transform g (transform h F) := by
  apply ext_pair
  intro ξ
  simp only [pair_transform, _root_.mul_inv_rev, Twist.adjoint_mul]

/-- Transfer by `g⁻¹` undoes transfer by `g` (MLS printed p. 62, equation (2.65)). -/
@[simp] theorem transform_inv_transform (g : RigidTransform) (F : Wrench) :
    transform g⁻¹ (transform g F) = F := by
  rw [← transform_mul, inv_mul_cancel, transform_one]

/-- Transfer by `g` undoes transfer by `g⁻¹` (MLS printed p. 62, equation (2.65)). -/
@[simp] theorem transform_transform_inv (g : RigidTransform) (F : Wrench) :
    transform g (transform g⁻¹ F) = F := by
  rw [← transform_mul, mul_inv_cancel, transform_one]

/-- Invertible wrench transfer (MLS printed p. 62); this is a linear equivalence,
not a norm claim. -/
def transformEquiv (g : RigidTransform) : Wrench ≃ₗ[ℝ] Wrench where
  toFun := transform g
  invFun := transform g⁻¹
  left_inv := transform_inv_transform g
  right_inv := transform_transform_inv g
  map_add' := transform_add g
  map_smul' := transform_smul g

/-- The forward map of `transformEquiv` is `transform` (MLS printed p. 62). -/
@[simp] theorem transformEquiv_apply (g : RigidTransform) (F : Wrench) :
    transformEquiv g F = transform g F := rfl

/-- The inverse of `transformEquiv g` is transfer by `g⁻¹` (MLS printed p. 62). -/
@[simp] theorem transformEquiv_symm_apply (g : RigidTransform) (F : Wrench) :
    (transformEquiv g).symm F = transform g⁻¹ F := rfl

/-- Six column coordinates, force before moment (MLS printed p. 61, `F ∈ ℝ⁶`). -/
def coordinates (F : Wrench) : Fin 3 ⊕ Fin 3 → ℝ :=
  Sum.elim (WithLp.ofLp F.force) (WithLp.ofLp F.torque)

/-- The independently specified matrix of wrench transfer from B to A,
MLS printed p. 62, equation (2.66). -/
def transformMatrix (g : RigidTransform) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks g.rotation.val 0
    (Vec3.hat g.translation * g.rotation.val) g.rotation.val

/-- The block matrix agrees with the independent force/moment coordinate action
(MLS printed p. 62, equation (2.66)). -/
theorem transformMatrix_mulVec (g : RigidTransform) (F : Wrench) :
    transformMatrix g *ᵥ coordinates F = coordinates (transform g F) := by
  rw [transformMatrix, coordinates, Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    simp [coordinates, transform, Matrix.zero_mulVec, Rotation.act_apply]
  | inr i =>
    change ((Vec3.hat g.translation * g.rotation.val) *ᵥ WithLp.ofLp F.force) i +
      (g.rotation.val *ᵥ WithLp.ofLp F.torque) i = _
    rw [← Matrix.mulVec_mulVec]
    change (Vec3.hat g.translation *ᵥ WithLp.ofLp (g.rotation.act F.force)) i +
      (g.rotation.act F.torque) i = _
    rw [Vec3.hat_mulVec]
    rfl

/-- MLS equations (2.65)–(2.67), printed pp. 62–63, in the `g_AB` direction:
`F_A = Ad_(g_AB⁻¹)ᵀ F_B`, including the moment-origin shift. -/
theorem transformMatrix_eq_adjointMatrix_inv_transpose (g : RigidTransform) :
    transformMatrix g = (Twist.adjointMatrix g⁻¹)ᵀ := by
  rw [Twist.adjointMatrix_inv, Twist.adjointMatrix_inv_blocks,
    Matrix.fromBlocks_transpose]
  simp [transformMatrix, Matrix.transpose_mul, Vec3.hat_transpose]

/-- Coordinates of the transferred wrench are the inverse-adjoint transpose applied
to the original coordinates, MLS printed pp. 62–63, equations (2.65)–(2.67). -/
theorem coordinates_transform (g : RigidTransform) (F : Wrench) :
    coordinates (transform g F) = (Twist.adjointMatrix g⁻¹)ᵀ *ᵥ coordinates F := by
  rw [← transformMatrix_eq_adjointMatrix_inv_transpose, transformMatrix_mulVec]

/-- Pairing is additive over a finite family already expressed in one frame
(MLS printed p. 63, net wrench). -/
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
inverse-adjoint twists, MLS printed pp. 63–64. The hypothesis that forces concern
one physical body is an interpretation of the common frame convention, not
enforced by this type. -/
theorem pair_net {ι : Type*} (s : Finset ι) (g : ι → RigidTransform)
    (F : ι → Wrench) (ξ : Twist) :
    pair (net s g F) ξ = ∑ i ∈ s, pair (F i) (Twist.adjoint (g i)⁻¹ ξ) := by
  simp only [net, pair_sum_left, pair_transform]

/-- A common frame change commutes with the net-wrench sum (MLS printed pp. 63–64). -/
theorem transform_net {ι : Type*} (s : Finset ι) (g : ι → RigidTransform)
    (F : ι → Wrench) (h : RigidTransform) :
    transform h (net s g F) = net s (fun i => h * g i) F := by
  change transformLinearMap h (∑ i ∈ s, transform (g i) (F i)) = _
  simp only [map_sum]
  simp only [net, transformLinearMap, LinearMap.coe_mk, AddHom.coe_mk, transform_mul]

end Wrench
end RoboLean
