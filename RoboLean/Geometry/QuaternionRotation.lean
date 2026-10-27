import RoboLean.Geometry.UnitQuaternion
import RoboLean.Geometry.Rodrigues
import RoboLean.Geometry.RotationSurjectivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Unit quaternions as rotations: the half-angle map and the double cover

MLS printed p. 34. Given a rotation `R = exp(ω̂θ)` with a unit axis `ω`, the book associates the
unit quaternion `Q = (cos(θ/2), ω sin(θ/2))`, states that `Q_ac = Q_ab · Q_bc` for composed
rotations, and extracts the rotation from a unit quaternion by `θ = 2 cos⁻¹ q₀`,
`ω = q⃗ / sin(θ/2)` if `θ ≠ 0` and `ω = 0` otherwise, `R = exp(ω̂θ)`.

Convention (scalar-first, as in `UnitQuaternion`): a quaternion is `(q₀, q⃗)` with `q₀` the real
part and `q⃗ = (q₁, q₂, q₃)` its `i, j, k` parts. The rotation of a quaternion `q` is the map
`v ↦ q v q*` on pure quaternions `v = (0, v⃗)`; its matrix is
`(q₀² - ‖q⃗‖²) I + 2 q⃗ q⃗ᵀ + 2 q₀ q̂⃗` (`QuaternionCoordinates.rotationMatrix`). The book calls
this
correspondence "a detailed calculation" and does not print the map; it is the standard one.

Contents:

* `QuaternionCoordinates.rotationMatrix`: the matrix of `v ↦ q v q*`, for every real quaternion;
  `q v q*` is again a pure quaternion and its vector part is `rotationMatrix q` applied to `v`;
  the matrix is multiplicative, even in `q`, and in `SO(3)` for `‖q‖ = 1`;
* `QuaternionCoordinates.axisAngle ω θ = (cos(θ/2), ω sin(θ/2))`, a unit quaternion for a unit
  axis, whose rotation matrix is `exp(ω̂θ)` (ledger row R27);
* `UnitQuaternion.toRotation`, the group homomorphism from unit quaternions onto `SO(3)`
  (R28: `Q_ac = Q_ab · Q_bc` as `toRotation (q * p) = toRotation q * toRotation p`), with the
  double cover: `toRotation q = toRotation p` exactly when `p = ±q`, so the map is two-to-one
  and onto, never a bijection; for composed axis-angle rotations the axis-angle quaternion of the
  composite is `±(Q_ab · Q_bc)`;
* the reverse extraction: `angle q = 2 cos⁻¹ q₀ ∈ [0, 2π]`, `sin(angle q / 2) = ‖q⃗‖`, and for
  `q⃗ ≠ 0` the axis `q⃗ / sin(θ/2)` is a unit vector with `q = axisAngle ω θ` and
  `toRotation q = exp(ω̂θ)`; the endpoint cases `sin(θ/2) = 0` are exactly `q = 1` (`θ = 0`) and
  `q = -1` (`θ = 2π`), both the identity rotation, and every unit axis represents them.

Source observation: the printed extraction divides by `sin(θ/2)` whenever `θ ≠ 0`, which includes
`θ = 2π` (`q = -1`), where `sin(θ/2) = 0`; the guard that makes the formula total is
`sin(θ/2) ≠ 0`, equivalently `q⃗ ≠ 0`.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace QuaternionCoordinates

/-- The matrix of the quaternion rotation map `v ↦ q v q*` of MLS p. 34, in the scalar-first
convention `q = (q₀, q⃗)`: `(q₀² - ‖q⃗‖²) I + 2 q⃗ q⃗ᵀ + 2 q₀ q̂⃗`, where `q̂⃗` is the hat matrix of
MLS eq. (2.4). Defined for every real quaternion; it is a rotation when `‖q‖ = 1`. -/
def rotationMatrix (q : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (q.re ^ 2 - ‖vector q‖ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
    (2 : ℝ) • Vec3.outer (vector q) (vector q) + (2 * q.re) • Vec3.hat (vector q)

/-- The entries of `rotationMatrix q` as polynomials in the four coordinates of `q`. -/
private theorem rotationMatrix_eq (q : Quaternion ℝ) : rotationMatrix q =
    !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
        2 * (q.imI * q.imK + q.re * q.imJ);
      2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
        2 * (q.imJ * q.imK - q.re * q.imI);
      2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
        q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2] := by
  unfold rotationMatrix
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vector, Vec3.hat, Fin.sum_univ_succ] <;> ring

/-- The conjugate `q v q*` of a pure quaternion `v = (0, v⃗)` is pure, for every real
quaternion `q` (MLS p. 34, quaternion conjugation). -/
theorem re_mul_pure_mul_star (q : Quaternion ℝ) (v : Vec3) :
    (q * ofScalarVector 0 v * star q).re = 0 := by
  simp [ofScalarVector]
  ring

/-- The vector part of `q v q*` is `rotationMatrix q` applied to `v` (MLS p. 34, scalar-first
coordinates, column-vector action). -/
theorem vector_mul_pure_mul_star (q : Quaternion ℝ) (v : Vec3) :
    vector (q * ofScalarVector 0 v * star q) = Matrix.toEuclideanLin (rotationMatrix q) v := by
  ext i
  change _ = (rotationMatrix q *ᵥ WithLp.ofLp v) i
  rw [rotationMatrix_eq]
  fin_cases i <;> simp [vector, ofScalarVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The rotation matrix of a product is the product of the rotation matrices,
`(qp) v (qp)* = q (p v p*) q*` (MLS p. 34, `Q_ac = Q_ab · Q_bc`), for every real quaternions. -/
theorem rotationMatrix_mul (q p : Quaternion ℝ) :
    rotationMatrix (q * p) = rotationMatrix q * rotationMatrix p := by
  simp only [rotationMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- `q` and `-q` have the same rotation matrix (MLS p. 34; the double cover). -/
@[simp] theorem rotationMatrix_neg (q : Quaternion ℝ) : rotationMatrix (-q) = rotationMatrix q := by
  simp only [rotationMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The quaternion `1 = (1, 0)` gives the identity matrix (MLS p. 33, identity element). -/
@[simp] theorem rotationMatrix_one : rotationMatrix 1 = 1 := by
  rw [rotationMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `R Rᵀ = (normSq q)² I` for the rotation matrix of every real quaternion. -/
private theorem rotationMatrix_mul_transpose (q : Quaternion ℝ) :
    rotationMatrix q * (rotationMatrix q)ᵀ = (Quaternion.normSq q ^ 2) • 1 := by
  rw [rotationMatrix_eq, Quaternion.normSq_def']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- `det R = (normSq q)³` for the rotation matrix of every real quaternion. -/
private theorem det_rotationMatrix (q : Quaternion ℝ) :
    (rotationMatrix q).det = Quaternion.normSq q ^ 3 := by
  rw [Matrix.det_fin_three, rotationMatrix_eq, Quaternion.normSq_def']
  simp
  ring

/-- For a unit quaternion the rotation matrix is in `SO(3)`: `RᵀR = I` and `det R = 1` (MLS
eqs. (2.1)–(2.2), p. 24; MLS p. 34). -/
theorem rotationMatrix_mem_specialOrthogonalGroup {q : Quaternion ℝ} (hq : ‖q‖ = 1) :
    rotationMatrix q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hn : Quaternion.normSq q = 1 := by rw [Quaternion.normSq_eq_norm_mul_self, hq, one_mul]
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
    rotationMatrix_mul_transpose, det_rotationMatrix, hn]
  simp

/-- The axis-angle quaternion `Q = (cos(θ/2), ω sin(θ/2))` of MLS p. 34, scalar first. -/
def axisAngle (ω : Vec3) (θ : ℝ) : Quaternion ℝ :=
  ofScalarVector (Real.cos (θ / 2)) (Real.sin (θ / 2) • ω)

/-- For a unit axis the axis-angle quaternion has norm one (MLS p. 34). -/
theorem norm_axisAngle {ω : Vec3} (hω : ‖ω‖ = 1) (θ : ℝ) : ‖axisAngle ω θ‖ = 1 := by
  have hn : ‖axisAngle ω θ‖ * ‖axisAngle ω θ‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, axisAngle, normSq_ofScalarVector, norm_smul,
      hω, mul_one, Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]
  rcases mul_self_eq_one_iff.mp hn with h | h
  · exact h
  · linarith [norm_nonneg (axisAngle ω θ)]

/-- **MLS p. 34 (ledger R27): the axis-angle quaternion represents the axis rotation.** For a
unit axis `ω` and every angle `θ`, the rotation matrix of `(cos(θ/2), ω sin(θ/2))` is the matrix
exponential `exp(ω̂θ)` of MLS eq. (2.14). -/
theorem rotationMatrix_axisAngle {ω : Vec3} (hω : ‖ω‖ = 1) (θ : ℝ) :
    rotationMatrix (axisAngle ω θ) = (Rotation.exp ω θ).val := by
  rw [Rotation.exp_val, Vec3.exp_hat_of_norm_eq_one ω hω, Vec3.hat_sq_of_norm_eq_one ω hω]
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  have hx : 2 * x / 2 = x := by ring
  have hc : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := Real.cos_sq' x
  unfold rotationMatrix axisAngle
  rw [re_ofScalarVector, vector_ofScalarVector, norm_smul, hω, mul_one, Real.norm_eq_abs, sq_abs,
    hx, Real.sin_two_mul, Real.cos_two_mul, hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vec3.hat] <;> ring

/-- Adding a full turn negates the axis-angle quaternion, `Q(ω, θ + 2π) = -Q(ω, θ)`, while the
rotation is unchanged (MLS p. 34; the double cover in axis-angle form). -/
theorem axisAngle_add_two_pi (ω : Vec3) (θ : ℝ) :
    axisAngle ω (θ + 2 * Real.pi) = -axisAngle ω θ := by
  have h : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  ext <;> simp [axisAngle, ofScalarVector, h, Real.cos_add_pi, Real.sin_add_pi]

/-- The zero angle gives the identity quaternion `(1, 0)` for every axis (MLS p. 34). -/
@[simp] theorem axisAngle_zero (ω : Vec3) : axisAngle ω 0 = 1 := by
  ext <;> simp [axisAngle, ofScalarVector]

/-- Reversing the axis and the angle together leaves the quaternion unchanged (MLS p. 34). -/
theorem axisAngle_neg_neg (ω : Vec3) (θ : ℝ) : axisAngle (-ω) (-θ) = axisAngle ω θ := by
  simp [axisAngle, neg_div]

end QuaternionCoordinates

namespace UnitQuaternion

open QuaternionCoordinates

/-- **The rotation of a unit quaternion** (MLS p. 34): the rotation `v ↦ q v q*`, packaged as an
element of `SO(3)`. -/
def toRotation (q : UnitQuaternion) : Rotation :=
  ⟨rotationMatrix q.val, rotationMatrix_mem_specialOrthogonalGroup (norm_val q)⟩

/-- The matrix of the rotation of a unit quaternion is the quaternion rotation matrix of
MLS p. 34. -/
@[simp] theorem toRotation_val (q : UnitQuaternion) :
    (toRotation q).val = rotationMatrix q.val := rfl

/-- The rotation of a unit quaternion acts on vectors by `v ↦ q v q*` (MLS p. 34, scalar-first
coordinates; `v` is the pure quaternion `(0, v)`). -/
theorem toRotation_act (q : UnitQuaternion) (v : Vec3) :
    (toRotation q).act v =
      QuaternionCoordinates.vector (q.val * ofScalarVector 0 v * star q.val) := by
  rw [vector_mul_pure_mul_star]
  rfl

/-- **MLS p. 34 (ledger R28): `Q_ac = Q_ab · Q_bc`.** The rotation of a product of unit
quaternions is the product of their rotations, `R_ac = R_ab R_bc` (MLS eq. (2.3), p. 25). -/
theorem toRotation_mul (q p : UnitQuaternion) :
    toRotation (q * p) = toRotation q * toRotation p := by
  exact Subtype.ext (rotationMatrix_mul q.val p.val)

/-- The identity quaternion gives the identity rotation (MLS p. 33). -/
@[simp] theorem toRotation_one : toRotation 1 = 1 := by
  exact Subtype.ext rotationMatrix_one

/-- The inverse (conjugate) quaternion gives the inverse rotation (MLS pp. 33–34). -/
theorem toRotation_inv (q : UnitQuaternion) : toRotation q⁻¹ = (toRotation q)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← toRotation_mul, inv_mul_cancel, toRotation_one]

/-- The rotation map as a group homomorphism from unit quaternions to `SO(3)` (MLS p. 34: "the
group operation on unit quaternions directly corresponds to the group operation for
rotations"). -/
def toRotationHom : UnitQuaternion →* Rotation where
  toFun := toRotation
  map_one' := toRotation_one
  map_mul' := toRotation_mul

/-- The homomorphism of MLS p. 34 applied to a unit quaternion is its rotation. -/
@[simp] theorem toRotationHom_apply (q : UnitQuaternion) : toRotationHom q = toRotation q := rfl

/-- **The double cover (MLS p. 34).** `q` and `-q` give the same rotation. -/
@[simp] theorem toRotation_neg (q : UnitQuaternion) : toRotation (-q) = toRotation q := by
  exact Subtype.ext (rotationMatrix_neg q.val)

/-- A unit quaternion is determined by its scalar and vector coordinates. -/
private theorem ext_scalar_vector {q p : UnitQuaternion} (h₁ : scalar q = scalar p)
    (h₂ : vector q = vector p) : q = p := by
  apply Subtype.ext
  rw [← ofScalarVector_re_vector q.val, ← ofScalarVector_re_vector p.val]
  exact congrArg₂ ofScalarVector h₁ h₂

/-- The coordinates of `1`. -/
private theorem scalar_one : scalar 1 = 1 := rfl

/-- The coordinates of `1`. -/
private theorem vector_one : vector 1 = 0 := by
  ext i
  fin_cases i <;> rfl

/-- The coordinates of `-1`. -/
private theorem scalar_neg_one : scalar (-1) = -1 := rfl

/-- The coordinates of `-1`. -/
private theorem vector_neg_one : vector (-1) = 0 := by
  ext i
  fin_cases i <;> simp [vector, QuaternionCoordinates.vector]

/-- A unit quaternion with zero vector part is `1` or `-1`. -/
private theorem eq_one_or_eq_neg_one_of_vector_eq_zero {q : UnitQuaternion} (h : vector q = 0) :
    q = 1 ∨ q = -1 := by
  have hu := scalar_sq_add_norm_vector_sq q
  rw [h, norm_zero] at hu
  have hs : scalar q * scalar q = 1 := by nlinarith
  rcases mul_self_eq_one_iff.mp hs with hs | hs
  · exact Or.inl (ext_scalar_vector (hs.trans scalar_one.symm) (h.trans vector_one.symm))
  · exact Or.inr (ext_scalar_vector (hs.trans scalar_neg_one.symm) (h.trans vector_neg_one.symm))

/-- The unit quaternions with the identity rotation are exactly `1` and `-1` (MLS p. 34; the
kernel of the double cover). -/
theorem toRotation_eq_one_iff (q : UnitQuaternion) : toRotation q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have hm := congrArg Subtype.val h
    rw [toRotation_val, rotationMatrix_eq] at hm
    have h00 := congrFun (congrFun hm 0) 0
    have h11 := congrFun (congrFun hm 1) 1
    have h22 := congrFun (congrFun hm 2) 2
    simp at h00 h11 h22
    have hu := scalar_sq_add_norm_vector_sq q
    rw [scalar, vector, EuclideanSpace.real_norm_sq_eq] at hu
    simp [QuaternionCoordinates.vector, Fin.sum_univ_succ] at hu
    apply eq_one_or_eq_neg_one_of_vector_eq_zero
    have hi : q.val.imI = 0 := by nlinarith
    have hj : q.val.imJ = 0 := by nlinarith
    have hk : q.val.imK = 0 := by nlinarith
    ext i
    fin_cases i <;> simp [vector, QuaternionCoordinates.vector, hi, hj, hk]
  · rintro (rfl | rfl)
    · exact toRotation_one
    · rw [toRotation_neg, toRotation_one]

/-- **The double cover is exactly two-to-one (MLS p. 34).** Two unit quaternions give the same
rotation exactly when they are equal or opposite; the map is not injective, so unit quaternions
are not in bijection with `SO(3)`. -/
theorem toRotation_eq_toRotation_iff (q p : UnitQuaternion) :
    toRotation q = toRotation p ↔ p = q ∨ p = -q := by
  constructor
  · intro h
    have h1 : toRotation (q⁻¹ * p) = 1 := by
      rw [toRotation_mul, toRotation_inv, h, inv_mul_cancel]
    rcases (toRotation_eq_one_iff _).mp h1 with h2 | h2
    · exact Or.inl ((inv_mul_eq_one.mp h2).symm)
    · right
      rw [inv_mul_eq_iff_eq_mul.mp h2, mul_neg_one]
  · rintro (rfl | rfl)
    · rfl
    · exact (toRotation_neg q).symm

/-- The rotation map is onto `SO(3)` (MLS p. 34, "quaternions give a global parameterization of
`SO(3)`"; from MLS Theorem 2.6, p. 30, every rotation is `exp(ω̂θ)` with a unit axis). -/
theorem toRotation_surjective : Function.Surjective toRotation := by
  intro R
  obtain ⟨ω, hω, t, rfl⟩ := Rotation.exists_unit_exp R
  exact ⟨ofNormOne (axisAngle ω t) (norm_axisAngle hω t),
    Subtype.ext (rotationMatrix_axisAngle hω t)⟩

/-- The unit quaternion `(cos(θ/2), ω sin(θ/2))` of a unit axis `ω` and an angle `θ`
(MLS p. 34). -/
def ofAxisAngle (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) : UnitQuaternion :=
  ofNormOne (axisAngle ω θ) (norm_axisAngle hω θ)

/-- The underlying quaternion of the axis-angle unit quaternion is `(cos(θ/2), ω sin(θ/2))`
(MLS p. 34). -/
@[simp] theorem ofAxisAngle_val (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) :
    (ofAxisAngle ω hω θ).val = axisAngle ω θ := rfl

/-- **MLS p. 34 (ledger R27), as rotations.** The unit quaternion `(cos(θ/2), ω sin(θ/2))`
represents the rotation `exp(ω̂θ)` for every unit axis `ω` and angle `θ`. -/
theorem toRotation_ofAxisAngle (ω : Vec3) (hω : ‖ω‖ = 1) (θ : ℝ) :
    toRotation (ofAxisAngle ω hω θ) = Rotation.exp ω θ := by
  exact Subtype.ext (rotationMatrix_axisAngle hω θ)

/-- **MLS p. 34 (ledger R28), in the book's axis-angle form.** If `R_ab = exp(ω̂₁θ₁)`,
`R_bc = exp(ω̂₂θ₂)` and `R_ac = exp(ω̂₃θ₃)` with `R_ac = R_ab R_bc` (unit axes), then the
associated quaternions satisfy `Q_ac = Q_ab · Q_bc` up to the sign of the double cover:
`Q_ac = ±(Q_ab · Q_bc)`. Both signs occur, since `θ₃` and `θ₃ + 2π` describe the same
rotation. -/
theorem ofAxisAngle_eq_mul_or_eq_neg_mul {ω₁ ω₂ ω₃ : Vec3} (h₁ : ‖ω₁‖ = 1) (h₂ : ‖ω₂‖ = 1)
    (h₃ : ‖ω₃‖ = 1) {θ₁ θ₂ θ₃ : ℝ}
    (h : Rotation.exp ω₃ θ₃ = Rotation.exp ω₁ θ₁ * Rotation.exp ω₂ θ₂) :
    ofAxisAngle ω₃ h₃ θ₃ = ofAxisAngle ω₁ h₁ θ₁ * ofAxisAngle ω₂ h₂ θ₂ ∨
      ofAxisAngle ω₃ h₃ θ₃ = -(ofAxisAngle ω₁ h₁ θ₁ * ofAxisAngle ω₂ h₂ θ₂) := by
  apply (toRotation_eq_toRotation_iff _ _).mp
  rw [toRotation_mul, toRotation_ofAxisAngle, toRotation_ofAxisAngle, toRotation_ofAxisAngle, h]

/-- The rotation angle `θ = 2 cos⁻¹ q₀` extracted from a unit quaternion (MLS p. 34), with
Mathlib's `Real.arccos`, so `θ ∈ [0, 2π]`. -/
def angle (q : UnitQuaternion) : ℝ := 2 * Real.arccos (scalar q)

/-- The extracted angle lies in `[0, 2π]` (MLS p. 34). -/
theorem angle_mem_Icc (q : UnitQuaternion) : angle q ∈ Set.Icc 0 (2 * Real.pi) := by
  constructor
  · have := Real.arccos_nonneg (scalar q)
    unfold angle
    positivity
  · unfold angle
    linarith [Real.arccos_le_pi (scalar q)]

/-- The scalar part of a unit quaternion lies in `[-1, 1]`. -/
private theorem scalar_mem_Icc (q : UnitQuaternion) : -1 ≤ scalar q ∧ scalar q ≤ 1 := by
  have hu := scalar_sq_add_norm_vector_sq q
  have hv := sq_nonneg ‖vector q‖
  constructor <;> nlinarith

/-- Half the extracted angle is `cos⁻¹ q₀`. -/
private theorem angle_div_two (q : UnitQuaternion) : angle q / 2 = Real.arccos (scalar q) := by
  unfold angle
  ring

/-- `sin(θ/2) = ‖q⃗‖` for the extracted angle of a unit quaternion (MLS p. 34). -/
theorem sin_half_angle (q : UnitQuaternion) : Real.sin (angle q / 2) = ‖vector q‖ := by
  have hu := scalar_sq_add_norm_vector_sq q
  rw [angle_div_two, Real.sin_arccos, show 1 - scalar q ^ 2 = ‖vector q‖ ^ 2 by linarith,
    Real.sqrt_sq (norm_nonneg _)]

/-- `cos(θ/2) = q₀` for the extracted angle of a unit quaternion (MLS p. 34). -/
theorem cos_half_angle (q : UnitQuaternion) : Real.cos (angle q / 2) = scalar q := by
  rw [angle_div_two, Real.cos_arccos (scalar_mem_Icc q).1 (scalar_mem_Icc q).2]

/-- The rotation axis extracted from a unit quaternion (MLS p. 34): `ω = q⃗ / sin(θ/2)` with
`θ = angle q`. Lean's division gives `ω = 0` when `sin(θ/2) = 0`, the endpoint cases
`q = ±1`; the book prints `ω = 0` only for `θ = 0`. -/
def axis (q : UnitQuaternion) : Vec3 := (Real.sin (angle q / 2))⁻¹ • vector q

/-- **The endpoint cases (MLS p. 34).** `sin(θ/2) = 0` for the extracted angle exactly when the
vector part vanishes, exactly when `q = 1` or `q = -1`. -/
theorem sin_half_angle_eq_zero_iff (q : UnitQuaternion) :
    Real.sin (angle q / 2) = 0 ↔ q = 1 ∨ q = -1 := by
  rw [sin_half_angle, norm_eq_zero]
  constructor
  · exact eq_one_or_eq_neg_one_of_vector_eq_zero
  · rintro (rfl | rfl)
    · exact vector_one
    · exact vector_neg_one

/-- The extracted angle is `0` exactly for `q = 1` (MLS p. 34). -/
theorem angle_eq_zero_iff (q : UnitQuaternion) : angle q = 0 ↔ q = 1 := by
  have h : angle q = 0 ↔ Real.arccos (scalar q) = 0 := by
    unfold angle
    constructor <;> intro h <;> linarith
  rw [h, Real.arccos_eq_zero]
  constructor
  · intro h1
    have hs : scalar q = 1 := le_antisymm (scalar_mem_Icc q).2 h1
    have hu := scalar_sq_add_norm_vector_sq q
    rw [hs] at hu
    have hv : ‖vector q‖ = 0 := by nlinarith [norm_nonneg (vector q)]
    exact ext_scalar_vector (hs.trans scalar_one.symm)
      ((norm_eq_zero.mp hv).trans vector_one.symm)
  · rintro rfl
    exact scalar_one.ge

/-- The extracted angle is `2π` exactly for `q = -1`: the endpoint where the printed formula
`ω = q⃗ / sin(θ/2)` for `θ ≠ 0` divides by zero (MLS p. 34). -/
theorem angle_eq_two_pi_iff (q : UnitQuaternion) : angle q = 2 * Real.pi ↔ q = -1 := by
  have h : angle q = 2 * Real.pi ↔ Real.arccos (scalar q) = Real.pi := by
    unfold angle
    constructor <;> intro h <;> linarith
  rw [h, Real.arccos_eq_pi]
  constructor
  · intro h1
    have hs : scalar q = -1 := le_antisymm h1 (scalar_mem_Icc q).1
    have hu := scalar_sq_add_norm_vector_sq q
    rw [hs] at hu
    have hv : ‖vector q‖ = 0 := by nlinarith [norm_nonneg (vector q)]
    exact ext_scalar_vector (hs.trans scalar_neg_one.symm)
      ((norm_eq_zero.mp hv).trans vector_neg_one.symm)
  · rintro rfl
    exact scalar_neg_one.le

/-- **MLS p. 34, reverse extraction, generic case.** If `sin(θ/2) ≠ 0` (equivalently `q⃗ ≠ 0`,
`q ≠ ±1`), the extracted axis `ω = q⃗ / sin(θ/2)` is a unit vector. -/
theorem norm_axis {q : UnitQuaternion} (hq : Real.sin (angle q / 2) ≠ 0) : ‖axis q‖ = 1 := by
  rw [sin_half_angle] at hq
  rw [axis, sin_half_angle, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hq]

/-- **MLS p. 34, reverse extraction, generic case.** If `sin(θ/2) ≠ 0`, the unit quaternion is
the axis-angle quaternion of its extracted axis and angle, `q = (cos(θ/2), ω sin(θ/2))`. -/
theorem eq_ofAxisAngle {q : UnitQuaternion} (hq : Real.sin (angle q / 2) ≠ 0) :
    q = ofAxisAngle (axis q) (norm_axis hq) (angle q) := by
  apply Subtype.ext
  rw [ofAxisAngle_val, axisAngle, axis, smul_smul, mul_inv_cancel₀ hq, one_smul, cos_half_angle,
    scalar, vector, ofScalarVector_re_vector]

/-- **MLS p. 34, reverse extraction: `R = exp(ω̂θ)`.** For every unit quaternion, the rotation is
the exponential of the extracted axis and angle. In the endpoint cases `q = ±1` the axis is `0`
and the rotation is the identity. -/
theorem toRotation_eq_exp (q : UnitQuaternion) :
    toRotation q = Rotation.exp (axis q) (angle q) := by
  by_cases hs : Real.sin (angle q / 2) = 0
  · have ha : axis q = 0 := by rw [axis, hs, _root_.inv_zero, zero_smul]
    rw [ha, Rotation.exp_zero_axis, toRotation_eq_one_iff]
    exact (sin_half_angle_eq_zero_iff q).mp hs
  · have h := toRotation_ofAxisAngle (axis q) (norm_axis hs) (angle q)
    rw [← eq_ofAxisAngle hs] at h
    exact h

/-- **MLS p. 34, the endpoint cases with any axis.** If `sin(θ/2) = 0` for the extracted angle
(`q = ±1`), every unit axis `ω` represents `q`: `q = (cos(θ/2), ω sin(θ/2))`, and the rotation is
the identity. -/
theorem eq_ofAxisAngle_of_sin_half_angle_eq_zero {q : UnitQuaternion}
    (hq : Real.sin (angle q / 2) = 0) (ω : Vec3) (hω : ‖ω‖ = 1) :
    q = ofAxisAngle ω hω (angle q) ∧ toRotation q = 1 := by
  refine ⟨?_, (toRotation_eq_one_iff q).mpr ((sin_half_angle_eq_zero_iff q).mp hq)⟩
  have hv : vector q = 0 := by
    rw [sin_half_angle, norm_eq_zero] at hq
    exact hq
  apply Subtype.ext
  rw [ofAxisAngle_val, axisAngle, hq, zero_smul, cos_half_angle, ← hv, scalar, vector,
    ofScalarVector_re_vector]

end UnitQuaternion
end RoboLean
