import RoboLean.LieGroups.LeftInvariantForms
import Mathlib.LinearAlgebra.Determinant

/-!
# Volume forms on `SE(3)` extended by left translation, and Theorem A.8

MLS Appendix A, §3.3, printed pp. 430–431. A volume form on an `n`-dimensional manifold is a
nonvanishing skew-symmetric `n`-linear map on each tangent space; its pull back by `F` is
`F^*Ω = (det J) Ω` in local coordinates (A.16). Theorem A.8: a left invariant volume form on
`SE(3)` is also right invariant, hence bi-invariant; the sketch of proof is `I_h^*Ω = Ω` because
the Jacobian of the conjugation `I_h` at the identity is `Ad_h` and `det Ad_h = 1`. The corollary
after it: `SE(3)` supports a bi-invariant volume form, defined on `se(3) ≅ ℝ⁶` and moved to every
tangent space by left translation.

Reading, as for the quadratic forms of the same appendix (`Twist.leftTranslatedForm`): without a
manifold structure on `SE(3)`, a tangent vector at `g` is a `4 × 4` matrix `X` with `g⁻¹ X ∈ se(3)`
(`Twist.IsTangentAt`), a volume form at the identity is an alternating `6`-linear map `Ω` on twists,
and its left translate is `Ω_g(X₁, …, X₆) = Ω((g⁻¹X₁)^∨, …, (g⁻¹X₆)^∨)`. The tangent maps of left
translation, right translation and conjugation by `h` are `X ↦ hX`, `X ↦ Xh` and `X ↦ hXh⁻¹`.
Smoothness in `g` is not stated: the extension is an explicit formula and the statements are
algebraic. The index type of the six arguments is `Fin 6`; twist coordinates are `(v, ω)`.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Twist

/-- A basis of the twists indexed by `Fin 6`: the six coordinate twists of `(v, ω)` (MLS
eq. (2.30), p. 41), linear coordinates first. Used to compare alternating `6`-forms with the
determinant. -/
def twistBasis : Module.Basis (Fin 6) ℝ Twist :=
  ((Pi.basisFun ℝ (Fin 3 ⊕ Fin 3)).map coordinatesEquiv.symm).reindex finSumFinEquiv

/-- **MLS eq. (A.16), p. 431, at a single tangent space: `F^*Ω = (det J) Ω`.** For every alternating
`6`-linear map `Ω` on twists and every linear map `f` of the twists,
`Ω(f ξ₁, …, f ξ₆) = det f · Ω(ξ₁, …, ξ₆)`. -/
theorem alternatingMap_comp_eq_det_mul (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (f : Twist →ₗ[ℝ] Twist)
    (ξ : Fin 6 → Twist) : Ω (f ∘ ξ) = LinearMap.det f * Ω ξ := by
  have h := Ω.eq_smul_basis_det twistBasis
  rw [h, AlternatingMap.smul_apply, AlternatingMap.smul_apply, Module.Basis.det_comp, smul_eq_mul,
    smul_eq_mul]
  ring

/-- **MLS p. 431, sketch of proof of Theorem A.8: `det Ad_h = 1`** for the adjoint as a linear map
of the twists (the block matrix `[R, p̂R; 0, R]` of eq. (2.58), p. 55). -/
theorem det_adjointLinearMap (h : RigidTransform) : LinearMap.det (adjointLinearMap h) = 1 := by
  have e : adjointLinearMap h = (coordinatesEquiv.symm : (Fin 3 ⊕ Fin 3 → ℝ) →ₗ[ℝ] Twist) ∘ₗ
      Matrix.toLin' (adjointMatrix h) ∘ₗ (coordinatesEquiv.symm.symm : Twist →ₗ[ℝ] _) := by
    apply LinearMap.ext
    intro ξ
    apply coordinatesEquiv.injective
    simp [adjointLinearMap, adjointMatrix_mulVec]
  rw [e, LinearMap.det_conj, LinearMap.det_toLin', det_adjointMatrix]

/-- **MLS p. 431: every volume form at the identity is `Ad`-invariant**,
`Ω(Ad_h ξ₁, …, Ad_h ξ₆) = det(Ad_h) Ω(ξ₁, …, ξ₆) = Ω(ξ₁, …, ξ₆)`, for every `h ∈ SE(3)`. -/
theorem alternatingMap_adjoint (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (h : RigidTransform)
    (ξ : Fin 6 → Twist) : Ω (fun i => adjoint h (ξ i)) = Ω ξ := by
  have := alternatingMap_comp_eq_det_mul Ω (adjointLinearMap h) ξ
  rw [det_adjointLinearMap, one_mul] at this
  exact this

/-- The volume form on `SE(3)` obtained from the alternating `6`-form `Ω` on `se(3)` by left
translation, `Ω_g(X₁, …, X₆) = Ω((g⁻¹X₁)^∨, …, (g⁻¹X₆)^∨)` for tangent vectors `Xᵢ` at `g` (MLS
p. 431: "define the volume element on `se(3) ≅ ℝ⁶` and then use left (or right) translation to
define a volume form on all of `T SE(3)`"). Coordinates `(v, ω)`. -/
def leftTranslatedVolume (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (g : RigidTransform)
    (X : Fin 6 → HomogeneousMatrix) : ℝ :=
  Ω (fun i => vee ((g⁻¹).toHomogeneous * X i))

/-- The left translated volume form at `g` on the tangent vectors `g ξ̂ᵢ` is `Ω(ξ₁, …, ξ₆)`
(MLS p. 431). -/
theorem leftTranslatedVolume_mul_hat (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (g : RigidTransform)
    (ξ : Fin 6 → Twist) :
    leftTranslatedVolume Ω g (fun i => g.toHomogeneous * (ξ i).hat) = Ω ξ := by
  simp only [leftTranslatedVolume, ← Matrix.mul_assoc, RigidTransform.toHomogeneous_inv_mul,
    Matrix.one_mul, vee_hat]

/-- **MLS p. 431: the left translated volume form is left invariant**, `L_h^*Ω = Ω`:
`Ω_{hg}(hX₁, …, hX₆) = Ω_g(X₁, …, X₆)`. -/
theorem leftTranslatedVolume_left (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (h g : RigidTransform)
    (X : Fin 6 → HomogeneousMatrix) :
    leftTranslatedVolume Ω (h * g) (fun i => h.toHomogeneous * X i) =
      leftTranslatedVolume Ω g X := by
  have e (Z : HomogeneousMatrix) :
      ((h * g)⁻¹).toHomogeneous * (h.toHomogeneous * Z) = (g⁻¹).toHomogeneous * Z := by
    rw [_root_.mul_inv_rev, RigidTransform.toHomogeneous_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (h⁻¹).toHomogeneous, RigidTransform.toHomogeneous_inv_mul,
      Matrix.one_mul]
  simp only [leftTranslatedVolume, e]

/-- **MLS Theorem A.8, p. 431: a left invariant volume form on `SE(3)` is right invariant.** For
every alternating `6`-form `Ω` on `se(3)`, its left translate satisfies `R_h^*Ω = Ω`:
`Ω_{gh}(X₁h, …, X₆h) = Ω_g(X₁, …, X₆)` for tangent vectors `Xᵢ` at `g` and every `h ∈ SE(3)`. -/
theorem leftTranslatedVolume_right (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (g h : RigidTransform)
    (X : Fin 6 → HomogeneousMatrix) (hX : ∀ i, IsTangentAt g (X i)) :
    leftTranslatedVolume Ω (g * h) (fun i => X i * h.toHomogeneous) =
      leftTranslatedVolume Ω g X := by
  choose ξ hξ using fun i => (isTangentAt_iff g (X i)).mp (hX i)
  have e (i : Fin 6) : vee (((g * h)⁻¹).toHomogeneous * (X i * h.toHomogeneous)) =
      adjoint h⁻¹ (vee ((g⁻¹).toHomogeneous * X i)) := by
    rw [hξ i, ← Matrix.mul_assoc (g⁻¹).toHomogeneous, RigidTransform.toHomogeneous_inv_mul,
      Matrix.one_mul, vee_hat, ← vee_hat (adjoint h⁻¹ (ξ i)), hat_adjoint,
      ← RigidTransform.toHomogeneous_inv, inv_inv, _root_.mul_inv_rev,
      RigidTransform.toHomogeneous_mul]
    congr 1
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (g⁻¹).toHomogeneous,
      RigidTransform.toHomogeneous_inv_mul, Matrix.one_mul]
  simp only [leftTranslatedVolume, e]
  exact alternatingMap_adjoint Ω h⁻¹ _

/-- **MLS p. 431, sketch of proof of Theorem A.8: `I_h^*Ω = Ω`.** The left translate of every
alternating `6`-form on `se(3)` is invariant under every conjugation `I_h(g) = hgh⁻¹`:
`Ω_{hgh⁻¹}(hX₁h⁻¹, …, hX₆h⁻¹) = Ω_g(X₁, …, X₆)` for tangent vectors `Xᵢ` at `g`. -/
theorem leftTranslatedVolume_conj (Ω : Twist [⋀^Fin 6]→ₗ[ℝ] ℝ) (h g : RigidTransform)
    (X : Fin 6 → HomogeneousMatrix) (hX : ∀ i, IsTangentAt g (X i)) :
    leftTranslatedVolume Ω (h * g * h⁻¹)
        (fun i => h.toHomogeneous * X i * (h⁻¹).toHomogeneous) =
      leftTranslatedVolume Ω g X := by
  have hY : ∀ i, IsTangentAt (h * g) (h.toHomogeneous * X i) := by
    intro i
    obtain ⟨ξ, hξ⟩ := (isTangentAt_iff g (X i)).mp (hX i)
    exact (isTangentAt_iff _ _).mpr ⟨ξ, by rw [hξ, RigidTransform.toHomogeneous_mul,
      Matrix.mul_assoc]⟩
  have := leftTranslatedVolume_right Ω (h * g) h⁻¹ (fun i => h.toHomogeneous * X i) hY
  rw [leftTranslatedVolume_left] at this
  exact this

/-- **MLS p. 431, the corollary of Theorem A.8: `SE(3)` supports a bi-invariant volume form.** The
determinant form `Ω = det` in the twist basis is a nonzero alternating `6`-form on `se(3)`; its
left translate is nonzero at every `g` (on the tangent vectors `g ξ̂ᵢ` with `ξ` the twist basis), and
it is left invariant, right invariant and conjugation invariant by the theorems above. -/
theorem leftTranslatedVolume_det_ne_zero (g : RigidTransform) :
    leftTranslatedVolume twistBasis.det g (fun i => g.toHomogeneous * (twistBasis i).hat) ≠ 0 := by
  rw [leftTranslatedVolume_mul_hat, Module.Basis.det_self]
  exact one_ne_zero

end Twist
end RoboLean
