import RoboLean.Geometry.RigidTransform
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Planar rotations `SO(2)` and planar rigid motions `SE(2)`

MLS equation (2.2), p. 24, defines `SO(n)` and leaves the planar case to the exercises:
Exercise 10 (planar rotational motion, pp. 75–76) and Exercise 11 (planar rigid body
transformations, p. 76). This file gives the planar group `SE(2)` as a carrier beside
`Rotation` and `RigidTransform`: a rotation in Mathlib's `specialOrthogonalGroup (Fin 2) ℝ` and a
translation in the Euclidean plane, with the homogeneous `3 × 3` representation printed in
Exercise 11, the matrix exponential of `so(2)` and `se(2)`, the pole of a planar motion, the planar
adjoint, and the embedding into `SE(3)` as rotations about the `z`-axis.

Conventions: planar points and vectors are `EuclideanSpace ℝ (Fin 2)`, ordered `(x, y)`, as
`Vec3` is for space; the product `g * h` applies `h` first, as for `RigidTransform`; a planar
twist is `(v, ω)` with `v ∈ ℝ²` and `ω ∈ ℝ`, with hat matrix `[[ω̂, v], [0, 0]]` and
`ω̂ = [[0, -ω], [ω, 0]]` (p. 76); the embedding into `SE(3)` sends `(p, R)` to
`(([p, 0]), [[R, 0], [0, 1]])`. Exponentials are Mathlib's `NormedSpace.exp` on real matrices.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

/-- The Euclidean plane `ℝ²` with coordinates `(x, y)`, the carrier of planar points and vectors
of MLS Exercise 11, p. 76 (`p ∈ ℝ²`, `v ∈ ℝ²`). Euclidean norm, as for `Vec3`. -/
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-- Planar rotations: the group `SO(2)` of real `2 × 2` orthogonal matrices with determinant
`+1`, MLS equation (2.2), p. 24, with `n = 2`, and Exercise 10, p. 75; reused from Mathlib's
special orthogonal group. -/
abbrev PlanarRotation : Type := Matrix.specialOrthogonalGroup (Fin 2) ℝ

/-- A matrix-valued solution of `Ṗ = A P` with `P(0) = I` is the matrix exponential `e^{tA}`
(uniqueness of solutions of a linear equation, used for the planar exponentials of MLS
Exercises 10(b) and 11(a), pp. 75–76). -/
private theorem exp_smul_eq_of_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (P : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ s, HasDerivAt P (A * P s) s) (h0 : P 0 = 1) (t : ℝ) :
    NormedSpace.exp (t • A) = P t := by
  have hF (s : ℝ) :
      HasDerivAt (fun r ↦ NormedSpace.exp (r • (-A)) * P r) 0 s := by
    have h := (hasDerivAt_exp_smul_const (-A) s).mul (hP s)
    convert! h using 1
    simp [mul_assoc]
  have hconst := is_const_of_deriv_eq_zero
    (fun s ↦ (hF s).differentiableAt) (fun s ↦ (hF s).deriv) t 0
  have hprod : NormedSpace.exp (t • (-A)) * P t = 1 := by
    simpa [h0] using hconst
  have hcancel : NormedSpace.exp (t • A) * NormedSpace.exp (t • (-A)) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • A)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have h := congrArg (fun M ↦ NormedSpace.exp (t • A) * M) hprod
  rw [← mul_assoc, hcancel, one_mul, mul_one] at h
  exact h.symm

namespace PlanarRotation

/-- The linear action of a planar rotation on the plane, the matrix product `R v` on column
coordinates (MLS Exercise 11, p. 76, with the action of p. 25 in the plane). -/
def act (R : PlanarRotation) : Vec2 →ₗ[ℝ] Vec2 :=
  Matrix.toEuclideanLin R.val

/-- The identity of `SO(2)` (MLS p. 24) acts as the identity. -/
@[simp] theorem act_one (x : Vec2) : (1 : PlanarRotation).act x = x := by
  apply WithLp.ofLp_injective
  change (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ WithLp.ofLp x = WithLp.ofLp x
  exact Matrix.one_mulVec _

/-- The product of planar rotations acts by applying the right factor first, MLS
equation (2.3), p. 25, in the plane. -/
@[simp] theorem act_mul (R S : PlanarRotation) (x : Vec2) :
    (R * S).act x = R.act (S.act x) := by
  apply WithLp.ofLp_injective
  change (R.val * S.val) *ᵥ WithLp.ofLp x = R.val *ᵥ (S.val *ᵥ WithLp.ofLp x)
  exact (Matrix.mulVec_mulVec _ _ _).symm

/-- The coordinates of the planar rotation action, `(R v)ᵢ = Rᵢ₀ v₀ + Rᵢ₁ v₁` (MLS
Exercise 11, p. 76). -/
theorem act_apply (R : PlanarRotation) (x : Vec2) (i : Fin 2) :
    R.act x i = R.val i 0 * x 0 + R.val i 1 * x 1 := by
  change (R.val *ᵥ WithLp.ofLp x) i = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The rotation of the plane by the angle `θ`, the matrix `[[cos θ, -sin θ], [sin θ, cos θ]]`
of MLS Exercise 10(b), p. 75. Counterclockwise for `θ > 0` in right-handed `(x, y)`
coordinates. -/
def ofAngle (θ : ℝ) : PlanarRotation :=
  ⟨!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ], by
    rw [of_mem_specialOrthogonalGroup_fin_two_iff]
    exact ⟨rfl, rfl, by rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ⟩⟩

/-- The skew-symmetric matrix `ω̂ = [[0, -ω], [ω, 0]] ∈ so(2)` of a real number `ω`, MLS
Exercise 10(b), p. 75. -/
def hat (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -ω; ω, 0]

/-- MLS Exercise 10(b), p. 75: `e^{ω̂ θ} = [[cos ωθ, -sin ωθ], [sin ωθ, cos ωθ]]`, as an equality
with the matrix exponential. -/
theorem exp_hat (ω θ : ℝ) : NormedSpace.exp (θ • hat ω) = (ofAngle (ω * θ)).val := by
  set J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
  have hA : hat ω = ω • J := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J, hat]
  have hJ : J * J = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]
  have h := exp_smul_eq_of_hasDerivAt (ω • J)
    (fun s ↦ Real.cos (ω * s) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin (ω * s) • J)
    (fun s ↦ by
      have hc := ((Real.hasDerivAt_cos (ω * s)).comp s
        ((hasDerivAt_id s).const_mul ω)).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)
      have hs := ((Real.hasDerivAt_sin (ω * s)).comp s
        ((hasDerivAt_id s).const_mul ω)).smul_const J
      refine (hc.add hs).congr_deriv ?_
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_one, hJ]
      module) (by simp) θ
  rw [hA, h]
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, ofAngle]

/-- MLS Exercise 10(b), p. 75, first question: the exponential map `exp : so(2) → SO(2)`,
`ω̂ ↦ e^{ω̂}`, is surjective. -/
theorem exists_exp_hat_eq (R : PlanarRotation) : ∃ ω : ℝ, NormedSpace.exp (hat ω) = R.val := by
  obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.2
  have hc : R.val 0 0 ^ 2 + R.val 1 0 ^ 2 = 1 := by rw [h2, neg_sq] at h3; exact h3
  obtain ⟨θ, hcos, hsin⟩ : ∃ θ : ℝ, Real.cos θ = R.val 0 0 ∧ Real.sin θ = R.val 1 0 := by
    set z : ℂ := ⟨R.val 0 0, R.val 1 0⟩
    have hz : ‖z‖ = 1 := by
      rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
      nlinarith [hc]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
    refine ⟨Complex.arg z, ?_, ?_⟩
    · rw [Complex.cos_arg hz0, hz, div_one]
    · rw [Complex.sin_arg, hz, div_one]
  refine ⟨θ, ?_⟩
  have h := exp_hat θ 1
  rw [one_smul, mul_one] at h
  rw [h]
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofAngle, hcos, hsin, h1, h2]

/-- MLS Exercise 10(b), p. 75, second question: the exponential map `exp : so(2) → SO(2)`,
`ω̂ ↦ e^{ω̂}`, is not injective (`ω = 0` and `ω = 2π` have the same image). -/
theorem not_injective_exp_hat : ¬ Function.Injective (fun ω : ℝ ↦ NormedSpace.exp (hat ω)) := by
  intro h
  have e : ∀ ω : ℝ, NormedSpace.exp (hat ω) = (ofAngle ω).val := fun ω ↦ by
    simpa using exp_hat ω 1
  have h2 : (fun ω : ℝ ↦ NormedSpace.exp (hat ω)) (2 * Real.pi) =
      (fun ω : ℝ ↦ NormedSpace.exp (hat ω)) 0 := by
    simp only [e]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ofAngle]
  have := h h2
  linarith [Real.pi_pos]

/-- MLS Exercise 10(c), p. 76: `R ω̂ Rᵀ = ω̂` for `R ∈ SO(2)` and `ω̂ ∈ so(2)`. -/
theorem mul_hat_mul_transpose (R : PlanarRotation) (ω : ℝ) : R.val * hat ω * R.valᵀ = hat ω := by
  obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.2
  have h3' : R.val 1 1 ^ 2 + R.val 1 0 ^ 2 = 1 := by rw [h1, h2, neg_sq] at h3; exact h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | ring1
      | linear_combination (ω * R.val 1 0) * h2 - (ω * R.val 1 1) * h1 - ω * h3'
      | linear_combination (ω * R.val 1 1) * h1 - (ω * R.val 1 0) * h2 + ω * h3'

end PlanarRotation

/-- A planar rigid body transformation `g = (p, R) ∈ SE(2)`, a translation `p ∈ ℝ²` and a
rotation `R ∈ SO(2)`, MLS Exercise 11, p. 76. Convention: named `rotation` and `translation`
fields, as for `RigidTransform`. -/
@[ext]
structure PlanarRigidTransform where
  /-- The rotation `R ∈ SO(2)` of `g = (p, R)`, MLS Exercise 11, p. 76. -/
  rotation : PlanarRotation
  /-- The translation `p ∈ ℝ²` of `g = (p, R)`, MLS Exercise 11, p. 76. -/
  translation : Vec2

namespace PlanarRigidTransform

/-- The identity of `SE(2)`, `(0, I)` (MLS Exercise 11, p. 76, with p. 37 in the plane). -/
instance : One PlanarRigidTransform := ⟨⟨1, 0⟩⟩

/-- Composition in `SE(2)`, `(R₁R₂, R₁p₂ + p₁)`, the product of the homogeneous matrices of MLS
Exercise 11, p. 76 (equation (2.24), p. 37, in the plane). -/
instance : Mul PlanarRigidTransform :=
  ⟨fun g h ↦ ⟨g.rotation * h.rotation, g.rotation.act h.translation + g.translation⟩⟩

/-- The inverse in `SE(2)`, `(-Rᵀp, Rᵀ)` (MLS p. 37 in the plane). -/
instance : Inv PlanarRigidTransform :=
  ⟨fun g ↦ ⟨g.rotation⁻¹, -(g.rotation⁻¹).act g.translation⟩⟩

/-- The identity of `SE(2)` has rotation `I` (MLS Exercise 11, p. 76). -/
@[simp] theorem one_rotation : (1 : PlanarRigidTransform).rotation = 1 := rfl

/-- The identity of `SE(2)` has translation `0` (MLS Exercise 11, p. 76). -/
@[simp] theorem one_translation : (1 : PlanarRigidTransform).translation = 0 := rfl

/-- The rotation of an inverse in `SE(2)` is `Rᵀ` (MLS Exercise 11, p. 76, with p. 37). -/
@[simp] theorem inv_rotation (g : PlanarRigidTransform) : g⁻¹.rotation = g.rotation⁻¹ := rfl

/-- The translation of an inverse in `SE(2)` is `-Rᵀp` (MLS Exercise 11, p. 76, with p. 37). -/
@[simp] theorem inv_translation (g : PlanarRigidTransform) :
    g⁻¹.translation = -(g.rotation⁻¹).act g.translation := rfl

/-- The rotation part of a composition in `SE(2)` (MLS Exercise 11, p. 76). -/
@[simp] theorem mul_rotation (g h : PlanarRigidTransform) :
    (g * h).rotation = g.rotation * h.rotation := rfl

/-- The translation part of a composition in `SE(2)` (MLS Exercise 11, p. 76). -/
@[simp] theorem mul_translation (g h : PlanarRigidTransform) :
    (g * h).translation = g.rotation.act h.translation + g.translation := rfl

/-- `SE(2)` is a group under composition (MLS Exercise 11, p. 76; the axioms of p. 24). -/
instance : Group PlanarRigidTransform where
  mul_assoc g h k := by
    ext1 <;> simp [mul_assoc, map_add, add_assoc]
  one_mul g := by ext1 <;> simp
  mul_one g := by ext1 <;> simp
  inv_mul_cancel g := by ext1 <;> simp

/-- The action of `g = (p, R) ∈ SE(2)` on a planar point, `x ↦ R x + p` (MLS Exercise 11,
p. 76, equation (2.22), p. 35, in the plane). -/
def applyPoint (g : PlanarRigidTransform) (x : Vec2) : Vec2 :=
  g.rotation.act x + g.translation

/-- A composite of planar motions acts on points by applying the right factor first (MLS
Exercise 11, p. 76). -/
@[simp] theorem mul_applyPoint (g h : PlanarRigidTransform) (x : Vec2) :
    (g * h).applyPoint x = g.applyPoint (h.applyPoint x) := by
  simp [applyPoint, map_add, add_assoc]

/-- The homogeneous representation `[[R, p], [0, 1]]` of `g = (p, R) ∈ SE(2)`, the `3 × 3` matrix
of MLS Exercise 11, p. 76, with coordinates ordered `x, y, homogeneous`. -/
def toHomogeneous (g : PlanarRigidTransform) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![g.rotation.val 0 0, g.rotation.val 0 1, g.translation 0;
     g.rotation.val 1 0, g.rotation.val 1 1, g.translation 1;
     0, 0, 1]

/-- The homogeneous representation of MLS Exercise 11, p. 76, turns composition in `SE(2)` into
matrix multiplication. -/
theorem toHomogeneous_mul (g h : PlanarRigidTransform) :
    (g * h).toHomogeneous = g.toHomogeneous * h.toHomogeneous := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toHomogeneous, Matrix.mul_apply, Fin.sum_univ_succ, PlanarRotation.act_apply] <;> ring

/-- The homogeneous representation of MLS Exercise 11, p. 76, is injective. -/
theorem toHomogeneous_injective : Function.Injective toHomogeneous := by
  intro g h hgh
  have e : ∀ i j, g.toHomogeneous i j = h.toHomogeneous i j := fun i j ↦ by rw [hgh]
  ext1
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [toHomogeneous] using e 0 0
    · simpa [toHomogeneous] using e 0 1
    · simpa [toHomogeneous] using e 1 0
    · simpa [toHomogeneous] using e 1 1
  · ext i
    fin_cases i
    · simpa [toHomogeneous] using e 0 2
    · simpa [toHomogeneous] using e 1 2

/-- The embedding of the plane into space as the plane `z = 0`, `(x, y) ↦ (x, y, 0)`, under which
the planar motions of MLS Exercise 11, p. 76, are rigid motions of space (equation (2.22), p. 35). -/
def embedPoint (x : Vec2) : Vec3 :=
  WithLp.toLp 2 ![x 0, x 1, 0]

/-- The embedding of `SE(2)` into `SE(3)`: `(p, R) ↦ ((p, 0), [[R, 0], [0, 1]])`, a rotation about
the `z`-axis followed by a translation in the plane `z = 0` (MLS Exercise 11, p. 76, with
equation (2.21), p. 35). A group homomorphism. -/
def toRigidTransform : PlanarRigidTransform →* RigidTransform where
  toFun g := ⟨⟨!![g.rotation.val 0 0, g.rotation.val 0 1, 0;
      g.rotation.val 1 0, g.rotation.val 1 1, 0; 0, 0, 1], by
    obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp g.rotation.2
    rw [h1, h2]
    rw [h1, h2] at h3
    refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | ring1 | linear_combination h3
    · rw [Matrix.det_fin_three]
      simp
      linear_combination h3⟩, embedPoint g.translation⟩
  map_one' := by
    ext1
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i
      fin_cases i <;> simp [embedPoint]
  map_mul' g h := by
    ext1
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i
      fin_cases i <;>
        simp [embedPoint, Rotation.act_apply, PlanarRotation.act_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_succ]

/-- The embedding of `SE(2)` into `SE(3)` (MLS Exercise 11, p. 76, with (2.21), p. 35) is
injective. -/
theorem toRigidTransform_injective : Function.Injective toRigidTransform := by
  intro g h hgh
  have hr := congrArg (fun T : RigidTransform ↦ T.rotation.val) hgh
  have ht := congrArg (fun T : RigidTransform ↦ T.translation) hgh
  have er : ∀ i j, (toRigidTransform g).rotation.val i j = (toRigidTransform h).rotation.val i j :=
    fun i j ↦ by rw [show (toRigidTransform g).rotation.val = _ from hr]
  have et : ∀ i, (toRigidTransform g).translation i = (toRigidTransform h).translation i :=
    fun i ↦ by rw [show (toRigidTransform g).translation = _ from ht]
  ext1
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [toRigidTransform] using er 0 0
    · simpa [toRigidTransform] using er 0 1
    · simpa [toRigidTransform] using er 1 0
    · simpa [toRigidTransform] using er 1 1
  · ext i
    fin_cases i
    · simpa [toRigidTransform, embedPoint] using et 0
    · simpa [toRigidTransform, embedPoint] using et 1

/-- The embedded planar motion moves embedded points as the planar motion does: the point action
of MLS equation (2.22), p. 35, restricted to the plane `z = 0` is the planar action of
Exercise 11, p. 76. -/
theorem toRigidTransform_applyPoint (g : PlanarRigidTransform) (x : Vec2) :
    (toRigidTransform g).applyPoint (embedPoint x) = embedPoint (g.applyPoint x) := by
  ext i
  fin_cases i <;>
    simp [toRigidTransform, embedPoint, applyPoint, RigidTransform.applyPoint, Rotation.act_apply,
      PlanarRotation.act_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The hat matrix `ξ̂ = [[ω̂, v], [0, 0]] ∈ se(2)` of the planar twist `ξ = (v, ω)`, `v ∈ ℝ²`,
`ω ∈ ℝ`, MLS Exercise 11, p. 76, with `ω̂ = [[0, -ω], [ω, 0]]`. -/
def twistHat (v : Vec2) (ω : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -ω, v 0; ω, 0, v 1; 0, 0, 0]

/-- MLS Exercise 11(a), p. 76, the pure translation case `ξ = (v, 0)`: `e^{ξ̂ θ}` is the planar
rigid motion `(θ v, I)`. Matrix exponential. -/
theorem exp_twistHat_zero (v : Vec2) (θ : ℝ) :
    NormedSpace.exp (θ • twistHat v 0) = (⟨1, θ • v⟩ : PlanarRigidTransform).toHomogeneous := by
  set N := twistHat v 0
  have hN : N * N = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, twistHat, Matrix.mul_apply, Fin.sum_univ_succ]
  have h := exp_smul_eq_of_hasDerivAt N (fun s ↦ 1 + s • N)
    (fun s ↦ by
      refine (((hasDerivAt_id s).smul_const N).const_add 1).congr_deriv ?_
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hN, smul_zero, add_zero, one_smul])
    (by simp) θ
  rw [h]
  ext i j; fin_cases i <;> fin_cases j <;> simp [N, twistHat, toHomogeneous]

/-- MLS Exercise 11(a), p. 76, the general case `ξ = (v, ω)`, `ω ≠ 0`: `e^{ξ̂ θ}` is the planar
rigid motion with rotation by `ωθ` and translation
`(1/ω) [[sin ωθ, -(1 - cos ωθ)], [1 - cos ωθ, sin ωθ]] v`. Matrix exponential. -/
theorem exp_twistHat (v : Vec2) (ω : ℝ) (hω : ω ≠ 0) (θ : ℝ) :
    NormedSpace.exp (θ • twistHat v ω) =
      (⟨PlanarRotation.ofAngle (ω * θ),
        WithLp.toLp 2 ![(Real.sin (ω * θ) * v 0 - (1 - Real.cos (ω * θ)) * v 1) / ω,
          ((1 - Real.cos (ω * θ)) * v 0 + Real.sin (ω * θ) * v 1) / ω]⟩ :
        PlanarRigidTransform).toHomogeneous := by
  set A := twistHat v ω
  set K : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, -(v 1 / ω); 0, 0, v 0 / ω; 0, 0, 1]
  set C : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, v 1 / ω; 0, 1, -(v 0 / ω); 0, 0, 0]
  set S : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, v 0 / ω; 1, 0, v 1 / ω; 0, 0, 0]
  have hK : A * K = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, K, twistHat, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring
  have hC : A * C = ω • S := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, C, S, twistHat, Matrix.mul_apply, Fin.sum_univ_succ]
  have hS : A * S = -(ω • C) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, C, S, twistHat, Matrix.mul_apply, Fin.sum_univ_succ]
  have h := exp_smul_eq_of_hasDerivAt A
    (fun s ↦ K + (Real.cos (ω * s) • C + Real.sin (ω * s) • S))
    (fun s ↦ by
      have hc := ((Real.hasDerivAt_cos (ω * s)).comp s
        ((hasDerivAt_id s).const_mul ω)).smul_const C
      have hs := ((Real.hasDerivAt_sin (ω * s)).comp s
        ((hasDerivAt_id s).const_mul ω)).smul_const S
      refine ((hc.add hs).const_add K).congr_deriv ?_
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hK, hC, hS]
      module)
    (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [K, C, S]) θ
  rw [h]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [K, C, S, toHomogeneous, PlanarRotation.ofAngle] <;> field_simp <;> ring

/-- MLS Exercise 11(a), p. 76: the exponential of every planar twist is a planar rigid body
transformation, `e^{ξ̂ θ} ∈ SE(2)` in the homogeneous representation. -/
theorem exists_exp_twistHat (v : Vec2) (ω θ : ℝ) :
    ∃ g : PlanarRigidTransform, NormedSpace.exp (θ • twistHat v ω) = g.toHomogeneous := by
  by_cases hω : ω = 0
  · subst hω
    exact ⟨_, exp_twistHat_zero v θ⟩
  · exact ⟨_, exp_twistHat v ω hω θ⟩

/-- MLS Exercise 11(b), p. 76, pure rotation: the planar twist `ξ = (q_y, -q_x, 1)` generates the
rotation by `θ` about the point `q`, `x ↦ R(θ)(x - q) + q`. -/
theorem exp_twistHat_rotation_about (q : Vec2) (θ : ℝ) :
    ∃ g : PlanarRigidTransform,
      NormedSpace.exp (θ • twistHat (WithLp.toLp 2 ![q 1, -q 0]) 1) = g.toHomogeneous ∧
        g.rotation = PlanarRotation.ofAngle θ ∧
        ∀ x, g.applyPoint x = (PlanarRotation.ofAngle θ).act (x - q) + q := by
  refine ⟨_, exp_twistHat _ 1 one_ne_zero θ, by simp, fun x ↦ ?_⟩
  ext i
  fin_cases i <;>
    simp [applyPoint, PlanarRotation.act_apply, PlanarRotation.ofAngle] <;> ring

/-- MLS Exercise 11(c), p. 76: every planar rigid body motion is a pure translation (rotation
`I`) or a pure rotation about a point `q`, the pole of the motion, `x ↦ R(x - q) + q`. -/
theorem rotation_eq_one_or_exists_pole (g : PlanarRigidTransform) :
    g.rotation = 1 ∨ ∃ q : Vec2, ∀ x, g.applyPoint x = g.rotation.act (x - q) + q := by
  obtain ⟨⟨M, hM⟩, p⟩ := g
  obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp hM
  by_cases ha : M 1 1 = 1
  · left
    have hc : M 1 0 = 0 := by
      rw [h1, h2, ha, neg_sq] at h3; nlinarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, ha, hc]
  · right
    have hd : (1 - M 1 1) ^ 2 + M 1 0 ^ 2 ≠ 0 := by
      have : 0 < (1 - M 1 1) ^ 2 := by
        have : 1 - M 1 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
        positivity
      positivity
    refine ⟨WithLp.toLp 2 ![((1 - M 1 1) * p 0 - M 1 0 * p 1) / ((1 - M 1 1) ^ 2 + M 1 0 ^ 2),
      (M 1 0 * p 0 + (1 - M 1 1) * p 1) / ((1 - M 1 1) ^ 2 + M 1 0 ^ 2)], fun x ↦ ?_⟩
    ext i
    fin_cases i <;>
      simp [applyPoint, PlanarRotation.act_apply, h1, h2] <;> field_simp <;> ring

/-- MLS Exercise 11(e), p. 76: the planar adjoint `Ad_g = [[R, (p_y, -p_x)ᵀ], [0, 1]]`, in the form
`g ξ̂ g⁻¹ = (Ad_g ξ)^`: conjugating the planar twist `(v, ω)` by `g = (p, R)` gives the twist
`(R v + ω (p_y, -p_x), ω)`. Homogeneous representation of p. 76. -/
theorem toHomogeneous_mul_twistHat_mul_inv (g : PlanarRigidTransform) (v : Vec2) (ω : ℝ) :
    g.toHomogeneous * twistHat v ω * g⁻¹.toHomogeneous =
      twistHat (g.rotation.act v + ω • WithLp.toLp 2 ![g.translation 1, -g.translation 0]) ω := by
  obtain ⟨⟨M, hM⟩, p⟩ := g
  obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp hM
  have h3' : M 1 1 ^ 2 + M 1 0 ^ 2 = 1 := by rw [h1, h2, neg_sq] at h3; exact h3
  have hinv : ((⟨M, hM⟩ : PlanarRotation)⁻¹).val = Mᵀ := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toHomogeneous, twistHat, Matrix.mul_apply, Fin.sum_univ_succ, PlanarRotation.act_apply,
      hinv, h1, h2] <;>
    first
      | ring1
      | linear_combination (-ω) * h3'
      | linear_combination ω * h3'
      | linear_combination (ω * p 1) * h3'
      | linear_combination (-(ω * p 0)) * h3'

end PlanarRigidTransform

end RoboLean
