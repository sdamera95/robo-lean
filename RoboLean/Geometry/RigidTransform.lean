import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Rigid transformations in three-dimensional Euclidean space

Rotations reuse Mathlib's special orthogonal group. Vectors carry the Euclidean
norm through `EuclideanSpace`, and matrices act on column coordinates.

The product `g * h` applies `h` first. Points transform as `R x + p`, while free
vectors transform as `R v`. Frame labels and physical units are not encoded here.

MLS references (printed pages): rotation matrices, `RᵀR = RRᵀ = I`, `det R = +1`
and the group `SO(3)` on pp. 23–24, equations (2.1)–(2.2); the coordinate action
`q_a = R_ab q_b` and the composition rule (2.3) on p. 25; Proposition 2.2
(rotations preserve distance) on p. 26; `SE(3)` and the point action
`q_a = p_ab + R_ab q_b` on p. 35, equations (2.21)–(2.22); the vector action
`g_*(v) = R v` on p. 36; composition (2.24), the identity and the inverse
`g⁻¹ = (-Rᵀp, Rᵀ)` on p. 37; Proposition 2.7 (rigid transformations preserve
distance) on p. 38.

Convention, as in `research/reports/geometry-conventions.md`: right-handed
orthonormal coordinates, column vectors, and `g_AB` converting coordinates of a
fixed point from frame B to frame A. MLS writes the pair as `(p, R)`; this
structure uses named `rotation` and `translation` fields, so no positional order
is implied.
-/

open Matrix

namespace RoboLean

/-- Three-dimensional real coordinate space `ℝ³` with its Euclidean metric: Cartesian
coordinates `(x, y, z)` relative to three orthonormal axes, MLS p. 20, with the magnitude of a
vector given by its Euclidean norm, MLS p. 21. Points and free vectors share this carrier, as
their 3-tuples do on MLS p. 21; `RigidTransform.applyPoint` and `RigidTransform.applyVector`
keep them apart. -/
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

/-- Proper rotations: the group `SO(3)` of real `3 × 3` matrices with `RRᵀ = RᵀR = I` and
`det R = +1`, MLS equations (2.1)–(2.2), pp. 23–24, the rotation matrices of right-handed
frames; reused from Mathlib's special orthogonal group. -/
abbrev Rotation : Type := Matrix.specialOrthogonalGroup (Fin 3) ℝ

namespace Rotation

/-- The linear action of a rotation on Euclidean coordinates, MLS p. 25: `R_ab` takes the
coordinates `q_b` of a point in frame B to `q_a = R_ab q_b` in frame A, and acts on vectors by
the same matrix product. Column-vector convention. -/
noncomputable def act (R : Rotation) : Vec3 →ₗ[ℝ] Vec3 :=
  Matrix.toEuclideanLin R.val

/-- The coordinate form of the rotation action, `q_a = R_ab q_b` (MLS p. 25). -/
theorem act_apply (R : Rotation) (x : Vec3) (i : Fin 3) :
    R.act x i = (R.val *ᵥ WithLp.ofLp x) i := rfl

/-- `RᵀR = I` for a rotation, MLS equation (2.1), p. 23. -/
theorem transpose_mul (R : Rotation) : R.valᵀ * R.val = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.property.1

/-- `RRᵀ = I` for a rotation, MLS equation (2.1), p. 23. -/
theorem mul_transpose (R : Rotation) : R.val * R.valᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp R.property.1

/-- For real orthogonal matrices, group inversion is transpose: the inverse of
`R ∈ SO(3)` is `Rᵀ`, MLS p. 24 (group axiom 3, from equation (2.1)). -/
@[simp] theorem inv_val (R : Rotation) : (R⁻¹).val = R.valᵀ := rfl

/-- A rotation has determinant `+1`, the condition defining `SO(3)` in MLS
equation (2.2), p. 24. -/
@[simp] theorem det_eq_one (R : Rotation) : Matrix.det R.val = 1 := R.property.2

/-- The identity matrix, the identity element of `SO(3)` (MLS p. 24), acts as the identity. -/
@[simp] theorem act_one (x : Vec3) : (1 : Rotation).act x = x := by
  apply WithLp.ofLp_injective
  change (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x = WithLp.ofLp x
  exact Matrix.one_mulVec _

/-- Composition rule for rotations, MLS equation (2.3), p. 25: the product acts by
applying the right factor first. -/
@[simp] theorem act_mul (R S : Rotation) (x : Vec3) :
    (R * S).act x = R.act (S.act x) := by
  apply WithLp.ofLp_injective
  change (R.val * S.val) *ᵥ WithLp.ofLp x = R.val *ᵥ (S.val *ᵥ WithLp.ofLp x)
  exact (Matrix.mulVec_mulVec _ _ _).symm

/-- Rotations preserve the Euclidean inner product; this is the `RᵀR = I` step in the
proof of MLS Proposition 2.2, p. 26. -/
theorem inner_act (R : Rotation) (x y : Vec3) :
    inner ℝ (R.act x) (R.act y) = inner ℝ x y := by
  simp only [act, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (R.val *ᵥ WithLp.ofLp y) ⬝ᵥ (R.val *ᵥ WithLp.ofLp x) =
    WithLp.ofLp y ⬝ᵥ WithLp.ofLp x
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    transpose_mul, Matrix.one_mulVec, dotProduct_comm]

/-- The matrix action packaged with its Euclidean norm-preservation proof; supports MLS
Proposition 2.2, part 1, p. 26 (rotations preserve distance). -/
noncomputable def toLinearIsometry (R : Rotation) : Vec3 →ₗᵢ[ℝ] Vec3 :=
  R.act.isometryOfInner R.inner_act

/-- Rotations preserve the Euclidean norm; supports MLS Proposition 2.2, p. 26. -/
@[simp] theorem norm_act (R : Rotation) (x : Vec3) : ‖R.act x‖ = ‖x‖ :=
  R.toLinearIsometry.norm_map x

/-- MLS Proposition 2.2, part 1, p. 26: `‖Rq - Rp‖ = ‖q - p‖`. -/
@[simp] theorem dist_act (R : Rotation) (x y : Vec3) :
    dist (R.act x) (R.act y) = dist x y :=
  R.toLinearIsometry.dist_map x y

/-- The inverse rotation `Rᵀ` (MLS p. 24) undoes the action of `R`. -/
@[simp] theorem inv_act_act (R : Rotation) (x : Vec3) :
    R⁻¹.act (R.act x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- The action of `R` undoes the inverse rotation `Rᵀ` (MLS p. 24). -/
@[simp] theorem act_inv_act (R : Rotation) (x : Vec3) :
    R.act (R⁻¹.act x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

end Rotation

/-- A proper rigid transformation, an element `(p, R)` of `SE(3) = ℝ³ × SO(3)`, MLS
equation (2.21), p. 35. Convention: named `rotation` and `translation` fields in place of
the book's positional pair `(p, R)`. -/
@[ext]
structure RigidTransform where
  /-- The orientation `R_ab ∈ SO(3)` of the pair in MLS equation (2.21), p. 35. -/
  rotation : Rotation
  /-- The position `p_ab ∈ ℝ³` of the pair in MLS equation (2.21), p. 35. -/
  translation : Vec3

/-- Build a rigid transformation from its rotation `R` and translation `p`, the pair
`(p, R) ∈ SE(3)` of MLS equation (2.21), p. 35, with named fields. -/
add_decl_doc RigidTransform.mk

/-- Two rigid transformations are equal when their rotations and translations are equal
(MLS p. 35, the pair `(p, R) ∈ SE(3)`). -/
add_decl_doc RigidTransform.ext

/-- Rigid transformations are equal exactly when their rotations and translations are equal
(MLS p. 35, the pair `(p, R) ∈ SE(3)`). -/
add_decl_doc RigidTransform.ext_iff

namespace RigidTransform

/-- The identity rigid transformation, the identity element of `SE(3)` (MLS p. 37). -/
noncomputable instance : One RigidTransform := ⟨⟨1, 0⟩⟩

/-- Supporting lemma; no direct MLS counterpart. Keeps `simp` confluent with
`Twist.mk_zero_zero`. -/
@[simp] theorem mk_one_zero : (⟨1, 0⟩ : RigidTransform) = 1 := rfl

/-- Composition of rigid transformations, MLS equation (2.24), p. 37:
`(R_ab R_bc, R_ab p_bc + p_ab)`. -/
noncomputable instance : Mul RigidTransform :=
  ⟨fun g h ↦ ⟨g.rotation * h.rotation, g.rotation.act h.translation + g.translation⟩⟩

/-- Inverse rigid transformation `g⁻¹ = (-Rᵀp, Rᵀ)`, MLS p. 37. -/
noncomputable instance : Inv RigidTransform :=
  ⟨fun g ↦ ⟨g.rotation⁻¹, -(g.rotation⁻¹).act g.translation⟩⟩

/-- The identity of `SE(3)` (MLS p. 37) has identity rotation. -/
@[simp] theorem one_rotation : (1 : RigidTransform).rotation = 1 := rfl
/-- The identity of `SE(3)` (MLS p. 37) has zero translation. -/
@[simp] theorem one_translation : (1 : RigidTransform).translation = 0 := rfl
/-- Rotation part of the composition rule, MLS equation (2.24), p. 37. -/
@[simp] theorem mul_rotation (g h : RigidTransform) :
    (g * h).rotation = g.rotation * h.rotation := rfl
/-- Translation part of the composition rule, MLS equation (2.24), p. 37. -/
@[simp] theorem mul_translation (g h : RigidTransform) :
    (g * h).translation = g.rotation.act h.translation + g.translation := rfl
/-- Rotation part of the inverse, `Rᵀ`, MLS p. 37. -/
@[simp] theorem inv_rotation (g : RigidTransform) :
    g⁻¹.rotation = g.rotation⁻¹ := rfl
/-- Translation part of the inverse, `-Rᵀp`, MLS p. 37. -/
@[simp] theorem inv_translation (g : RigidTransform) :
    g⁻¹.translation = -(g.rotation⁻¹).act g.translation := rfl

/-- The inverse translation in the textbook's explicit matrix coordinates, `-Rᵀp`, the
upper-right block of `ḡ⁻¹` printed on MLS p. 37 (item 3). -/
theorem inv_translation_coordinates (g : RigidTransform) :
    WithLp.ofLp g⁻¹.translation = -(g.rotation.valᵀ *ᵥ WithLp.ofLp g.translation) := rfl

/-- Rigid transformations form a group under composition, MLS p. 37 (items 1–4). -/
noncomputable instance : Group RigidTransform where
  mul_assoc g h k := by
    ext <;> simp [mul_assoc, map_add, add_assoc]
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp

/-- Action on a point, `g(q) = p + Rq`, MLS equation (2.22), p. 35, written here as
`R x + p`; translation affects point coordinates. -/
noncomputable def applyPoint (g : RigidTransform) (x : Vec3) : Vec3 :=
  g.rotation.act x + g.translation

/-- Action on a free vector, `g_*(v) = Rv`, MLS p. 36; translation does not affect it. -/
noncomputable def applyVector (g : RigidTransform) (v : Vec3) : Vec3 :=
  g.rotation.act v

/-- The identity transformation fixes every point; supports the identity of MLS p. 37. -/
@[simp] theorem one_applyPoint (x : Vec3) : (1 : RigidTransform).applyPoint x = x := by
  simp [applyPoint]

/-- A composite acts on points by applying the right factor first, MLS equation (2.24),
p. 37, with the point action (2.22), p. 35. -/
@[simp] theorem mul_applyPoint (g h : RigidTransform) (x : Vec3) :
    (g * h).applyPoint x = g.applyPoint (h.applyPoint x) := by
  simp [applyPoint, map_add, add_assoc]

/-- The identity transformation fixes every free vector; supports MLS pp. 36–37. -/
@[simp] theorem one_applyVector (v : Vec3) : (1 : RigidTransform).applyVector v = v := by
  simp [applyVector]

/-- A composite acts on free vectors by applying the right factor first; supports the
vector action of MLS p. 36 and composition (2.24), p. 37. -/
@[simp] theorem mul_applyVector (g h : RigidTransform) (v : Vec3) :
    (g * h).applyVector v = g.applyVector (h.applyVector v) := by
  simp [applyVector]

/-- The inverse of MLS p. 37 undoes the point action. -/
@[simp] theorem inv_applyPoint_applyPoint (g : RigidTransform) (x : Vec3) :
    g⁻¹.applyPoint (g.applyPoint x) = x := by
  rw [← mul_applyPoint, inv_mul_cancel, one_applyPoint]

/-- The point action undoes the inverse of MLS p. 37. -/
@[simp] theorem applyPoint_inv_applyPoint (g : RigidTransform) (x : Vec3) :
    g.applyPoint (g⁻¹.applyPoint x) = x := by
  rw [← mul_applyPoint, mul_inv_cancel, one_applyPoint]

/-- The vector action as a difference of point actions, `g(s) - g(r) = g_*(s - r)`,
MLS p. 36. -/
theorem applyPoint_sub_applyPoint (g : RigidTransform) (x y : Vec3) :
    g.applyPoint x - g.applyPoint y = g.applyVector (x - y) := by
  simp [applyPoint, applyVector, map_sub]

/-- A point plus a free vector maps to the image point plus the image vector; supports
the point and vector syntax rules of MLS p. 36. -/
theorem applyPoint_add (g : RigidTransform) (x v : Vec3) :
    g.applyPoint (x + v) = g.applyPoint x + g.applyVector v := by
  simp [applyPoint, applyVector, map_add, add_right_comm]

/-- The vector action preserves the Euclidean inner product, hence angles between
vectors; supports MLS Proposition 2.7, p. 38. -/
@[simp] theorem inner_applyVector (g : RigidTransform) (v w : Vec3) :
    inner ℝ (g.applyVector v) (g.applyVector w) = inner ℝ v w :=
  g.rotation.inner_act v w

/-- The vector action preserves the Euclidean norm; supports MLS Proposition 2.7, p. 38. -/
@[simp] theorem norm_applyVector (g : RigidTransform) (v : Vec3) :
    ‖g.applyVector v‖ = ‖v‖ := g.rotation.norm_act v

/-- MLS Proposition 2.7, part 1, p. 38: `‖gq - gp‖ = ‖q - p‖` for points. -/
@[simp] theorem dist_applyPoint (g : RigidTransform) (x y : Vec3) :
    dist (g.applyPoint x) (g.applyPoint y) = dist x y := by
  simpa only [applyPoint, dist_add_right] using g.rotation.dist_act x y

/-- Algebraic orientation convention: the linear part has determinant one, the condition
`det R = +1` of `SO(3)` in MLS equation (2.2), p. 24, for the rotation of `(p, R) ∈ SE(3)`,
equation (2.21), p. 35. -/
@[simp] theorem rotation_det (g : RigidTransform) : g.rotation.val.det = 1 :=
  g.rotation.det_eq_one

end RigidTransform
end RoboLean
