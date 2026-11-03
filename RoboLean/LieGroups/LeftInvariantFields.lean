import Mathlib.Analysis.Calculus.VectorField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import RoboLean.Nonholonomic.VectorField

/-!
# Push-forward of vector fields and the Lie algebras of matrix groups

MLS Appendix A, §1.4–§2.2, printed pp. 407–411, without a manifold structure on the groups.

* Proposition A.1 (p. 407), `F_*[X, Y] = [F_* X, F_* Y]`, for a diffeomorphism `F` between real
  normed spaces, with the push-forward `(F_* X)_q = DF(F⁻¹ q) X(F⁻¹ q)` defined on the same page.
  Corrected printing: the proposition is printed for "`F : M → N` a smooth map", but the
  push-forward `F_* X` is defined on p. 407 only when `F` is a diffeomorphism; the statement here
  takes `F` a bijection with `F` differentiable and `F⁻¹` twice continuously differentiable, the
  fields differentiable. The bracket is Mathlib's `VectorField.lieBracket`,
  `[X, Y](x) = DY(x) X(x) - DX(x) Y(x)`, which is the coordinate formula printed on p. 407.
* The Lie algebra of `GL(n, ℝ)`, Example A.6 (p. 410): the left invariant vector fields on the
  open set `GL(n, ℝ) ⊂ ℝⁿˣⁿ` are `X_A(g) = g A = T_e L_g A` (p. 410); a left invariant field is
  determined by its value at the identity; and `[X_A, X_B] = X_{AB - BA}`, so the bracket (A.1)
  `[A, B] = [X_A, X_B](e)` is the commutator `AB - BA`. The fields are written on the whole matrix
  space, whose norm is the entrywise norm (`Matrix.Norms.Elementwise`).
* Example A.5 (`ℝⁿ`, constant fields, trivial bracket), Example A.7 (`so(3)` with
  `[ω̂₁, ω̂₂] = (ω₁ × ω₂)^`) and Example A.8 (`se(3)` with the twist bracket) as brackets of the
  left invariant fields `g ↦ g ω̂` and `g ↦ g ξ̂` at the identity.
-/

noncomputable section

open VectorField Matrix

namespace RoboLean

namespace LieGroup

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- The push-forward of a vector field `X` on `E` by a bijection `F : E ≃ E'`,
`(F_* X)_q = DF(F⁻¹ q) X(F⁻¹ q)`, MLS printed p. 407 (defined there for a diffeomorphism). -/
def pushforward (F : E ≃ E') (X : E → E) (q : E') : E' :=
  fderiv ℝ F (F.symm q) (X (F.symm q))

/-- MLS Proposition A.1, printed p. 407: the push-forward of a Lie bracket is the bracket of the
push-forwards, `F_*[X, Y] = [F_* X, F_* Y]`, for `F` a diffeomorphism (a bijection, differentiable,
with twice continuously differentiable inverse; corrected printing, see the module docstring) and
differentiable fields `X, Y`. Mathlib's bracket, the coordinate formula of p. 407. -/
theorem pushforward_lieBracket [CompleteSpace E'] (F : E ≃ E') (hF : Differentiable ℝ F)
    (hF' : ContDiff ℝ 2 F.symm) {X Y : E → E} (hX : Differentiable ℝ X)
    (hY : Differentiable ℝ Y) (q : E') :
    pushforward F (lieBracket ℝ X Y) q = lieBracket ℝ (pushforward F X) (pushforward F Y) q := by
  have hFs : Differentiable ℝ F.symm := hF'.differentiable (by norm_num)
  -- the derivative of `F⁻¹` at `q'` is invertible with inverse `DF(F⁻¹ q')`
  have hinv (q' : E') : (fderiv ℝ F.symm q').inverse = fderiv ℝ F (F.symm q') := by
    have h1 : (fderiv ℝ F (F.symm q')).comp (fderiv ℝ F.symm q') = ContinuousLinearMap.id ℝ E' := by
      rw [← fderiv_comp q' (hF _) (hFs q')]
      have : (⇑F ∘ ⇑F.symm) = id := funext F.apply_symm_apply
      rw [this, fderiv_id]
    have h2 : (fderiv ℝ F.symm q').comp (fderiv ℝ F (F.symm q')) = ContinuousLinearMap.id ℝ E := by
      have e := fderiv_comp (F.symm q') (hFs (F (F.symm q'))) (hF (F.symm q'))
      rw [F.apply_symm_apply] at e
      rw [← e]
      have : (⇑F.symm ∘ ⇑F) = id := funext F.symm_apply_apply
      rw [this, fderiv_id]
    let e := ContinuousLinearEquiv.equivOfInverse (fderiv ℝ F.symm q') (fderiv ℝ F (F.symm q'))
      (fun v => by simpa using congrArg (fun L => L v) h1)
      (fun v => by simpa using congrArg (fun L => L v) h2)
    change (e : E' →L[ℝ] E).inverse = _
    rw [ContinuousLinearMap.inverse_equiv]
    rfl
  have hpush (Z : E → E) : pushforward F Z = pullback ℝ F.symm Z := by
    funext q'
    rw [pushforward, pullback, hinv]
  rw [hpush, hpush, hpush]
  exact pullback_lieBracket (n := 2) (by simp) (hF'.contDiffAt) (hX _) (hY _)

/-- MLS Example A.5, printed p. 410: the left invariant vector fields of `(ℝⁿ, +)` are the constant
fields, and their bracket is zero, so the Lie algebra of `ℝⁿ` is `ℝⁿ` with the trivial bracket.
Stated on a real normed space `E`. -/
theorem lieBracket_const (v w x : E) : lieBracket ℝ (fun _ => v) (fun _ => w) x = 0 := by
  simp [lieBracket]

section GeneralLinear

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

/-- The left invariant vector field of `A ∈ gl(n, ℝ)`, `X_A(g) = T_e L_g A = g A`, MLS printed
p. 410 (`X_ξ(g) = T_e L_g ξ`) with left matrix multiplication (Example A.6); written on the whole
matrix space `ℝⁿˣⁿ`, which contains `GL(n, ℝ)` as an open set. -/
def leftInvariantField (A : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  g * A

/-- `X_A` is left invariant, `T_h L_g X_A(h) = X_A(g h)`, MLS printed p. 410 (the tangent map of
left multiplication by `g` is `X ↦ g X`). -/
theorem leftInvariantField_mul (A g h : Matrix (Fin n) (Fin n) ℝ) :
    leftInvariantField A (g * h) = g * leftInvariantField A h := by
  simp only [leftInvariantField, Matrix.mul_assoc]

/-- `ρ₁ ∘ ρ₂ = id` of MLS printed p. 410: the left invariant field of `A` takes the value `A` at the
identity. -/
theorem leftInvariantField_one (A : Matrix (Fin n) (Fin n) ℝ) : leftInvariantField A 1 = A := by
  simp only [leftInvariantField, Matrix.one_mul]

/-- `ρ₂ ∘ ρ₁ = id` of MLS printed p. 410 for `GL(n, ℝ)`: a vector field on `GL(n, ℝ)` that is left
invariant, `X(g h) = g X(h)` for all `g, h ∈ GL(n, ℝ)`, is the left invariant field of its value at
the identity, `X(g) = g X(e)`. -/
theorem eq_leftInvariantField_one (X : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ g h : GL (Fin n) ℝ, X (g * h) = g * X h) (g : GL (Fin n) ℝ) :
    X g = leftInvariantField (X 1) g := by
  have := hX g 1
  simpa [leftInvariantField] using this

/-- MLS Example A.6, printed p. 410: the bracket of two left invariant fields of `GL(n, ℝ)` is the
left invariant field of the commutator, `[X_A, X_B] = X_{AB - BA}`; in particular the left invariant
fields form a Lie subalgebra (p. 410). Mathlib's bracket (the book's sign, p. 407), entrywise norm. -/
theorem lieBracket_leftInvariantField (A B g : Matrix (Fin n) (Fin n) ℝ) :
    lieBracket ℝ (leftInvariantField A) (leftInvariantField B) g =
      leftInvariantField (A * B - B * A) g := by
  let L : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    fun M =>
    { toFun := fun x => x * M
      map_add' := fun x y => Matrix.add_mul x y M
      map_smul' := fun c x => Matrix.smul_mul c x M
      cont := by fun_prop }
  refine (Nonholonomic.lieBracket_continuousLinearMap (L A) (L B) g).trans ?_
  show g * A * B - g * B * A = g * (A * B - B * A)
  noncomm_ring

/-- MLS Example A.6 with equation (A.1), printed p. 410: the Lie algebra bracket of `gl(n, ℝ)`,
`[A, B] = [X_A, X_B](e)`, is the commutator `AB - BA`. -/
theorem lieBracket_leftInvariantField_one (A B : Matrix (Fin n) (Fin n) ℝ) :
    lieBracket ℝ (leftInvariantField A) (leftInvariantField B) 1 = A * B - B * A := by
  rw [lieBracket_leftInvariantField, leftInvariantField_one]

end GeneralLinear

section MatrixSubgroups

open scoped Matrix.Norms.Elementwise

/-- MLS Example A.7, printed p. 411: on `3 × 3` matrices (entrywise norm), the left invariant
fields `g ↦ g ω̂₁` and `g ↦ g ω̂₂` of `so(3)` have the bracket `g ↦ g (ω₁ × ω₂)^`, so the
bracket (A.1) on `so(3)` is `[ω̂₁, ω̂₂] = (ω₁ × ω₂)^`, the cross product on `ℝ³`. Hat map of (A.2).
-/
theorem lieBracket_mul_hat_vec (ω₁ ω₂ : Vec3) (g : Matrix (Fin 3) (Fin 3) ℝ) :
    lieBracket ℝ (fun x => x * Vec3.hat ω₁) (fun x => x * Vec3.hat ω₂) g =
      g * Vec3.hat (Vec3.cross ω₁ ω₂) := by
  let L : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
    fun M =>
    { toFun := fun x => x * M
      map_add' := fun x y => Matrix.add_mul x y M
      map_smul' := fun c x => Matrix.smul_mul c x M
      cont := by fun_prop }
  refine (Nonholonomic.lieBracket_continuousLinearMap (L (Vec3.hat ω₁)) (L (Vec3.hat ω₂)) g).trans ?_
  show g * Vec3.hat ω₁ * Vec3.hat ω₂ - g * Vec3.hat ω₂ * Vec3.hat ω₁ = _
  rw [Vec3.hat_cross]
  noncomm_ring

/-- MLS Example A.8 with equation (A.1), printed p. 411: on `4 × 4` homogeneous matrices
(entrywise norm), the bracket of the left invariant fields `g ↦ g ξ̂` and `g ↦ g η̂` at the identity
is the hat of the twist bracket `(ω₁ × v₂ - ω₂ × v₁, ω₁ × ω₂)`; coordinates `(v, ω)`. -/
theorem lieBracket_mul_twistHat_one (ξ η : Twist) :
    lieBracket ℝ (fun x : HomogeneousMatrix => x * ξ.hat) (fun x => x * η.hat) 1 =
      (Twist.bracket ξ η).hat := by
  rw [Nonholonomic.lieBracket_mul_hat, Matrix.one_mul]

end MatrixSubgroups

end LieGroup

end RoboLean
