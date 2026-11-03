import RoboLean.LieGroups.TwistForms

/-!
# Quadratic forms on `SE(3)` extended from the identity by left translation

MLS Appendix A, §3.2, printed pp. 424–425: "to define a metric on a Lie group, we may first define
it at the identity and then translate it to the whole group by either left or right translation";
a quadratic form is bi-invariant when it is also right invariant, equivalently invariant under
every conjugation `I_h(g) = h g h⁻¹`. Lemma A.4: a left invariant quadratic form is
`I_h`-invariant exactly when it is `I_h`-invariant at the identity,
`Ψ_e(ξ̂, η̂) = Ψ_e(Ad_h ξ̂, Ad_h η̂)`.

The reading here, without a manifold structure on `SE(3)`: group elements are the library's rigid
transforms with their homogeneous matrices, and a tangent vector at `g` is a `4 × 4` matrix `X`
with `g⁻¹ X ∈ se(3)`, so `X = g ξ̂` (the left translation `T_g L_h X = h X` of p. 417). A form
`Ψ_e` on `se(3)`, written through its matrix on twist coordinates `(v, ω)`, is extended by left
translation: `Ψ_g(X, Y) = Ψ_e(g⁻¹ X, g⁻¹ Y)`. The tangent maps of right translation and of
conjugation are `X ↦ X h` and `X ↦ h X h⁻¹`. Smooth dependence on `g`, part of the book's
definition of a quadratic form on a manifold (p. 424), is not stated: the extension is given by an
explicit formula and the statements are algebraic.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Twist

/-- A `4 × 4` matrix `X` is a tangent vector to `SE(3)` at `g` when `g⁻¹ X ∈ se(3)`, so that
`X = g ξ̂` for a twist `ξ` (MLS printed p. 417, tangent vectors moved to the identity by left
translation, `T_g L_h X_g = h X_g`; `se(3)` as in equation (2.29), p. 40). -/
def IsTangentAt (g : RigidTransform) (X : HomogeneousMatrix) : Prop :=
  (g⁻¹).toHomogeneous * X ∈ se3Submodule

/-- The quadratic form on `SE(3)` obtained from the form `Ψ_e` on `se(3)` by left translation,
`Ψ_g(X, Y) = Ψ_e(g⁻¹ X, g⁻¹ Y)` for tangent vectors `X, Y` at `g` (MLS printed p. 424, "define it
at the identity and then translate it to the whole group by … left … translation"); `Ψ_e` is the
matrix of the form on twist coordinates `(v, ω)`. -/
def leftTranslatedForm (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (g : RigidTransform)
    (X Y : HomogeneousMatrix) : ℝ :=
  form Ψ (vee ((g⁻¹).toHomogeneous * X)) (vee ((g⁻¹).toHomogeneous * Y))

/-- Conjugating an element of `se(3)` by `h` is the adjoint action on its twist coordinates,
`(h M h⁻¹)^∨ = Ad_h M^∨` (MLS Lemma 2.13, printed p. 56). Supporting lemma. -/
private theorem vee_conj (h : RigidTransform) (M : HomogeneousMatrix) (hM : M ∈ se3Submodule) :
    vee (h.toHomogeneous * M * (h⁻¹).toHomogeneous) = adjoint h (vee M) := by
  conv_lhs => rw [← hat_vee M hM]
  rw [RigidTransform.toHomogeneous_inv, ← hat_adjoint, vee_hat]

private theorem toHomogeneous_inv_mul_cancel_left (g : RigidTransform) (X : HomogeneousMatrix) :
    (g⁻¹).toHomogeneous * (g.toHomogeneous * X) = X := by
  rw [← Matrix.mul_assoc, RigidTransform.toHomogeneous_inv_mul, Matrix.one_mul]

/-- The tangent vectors at `g` are exactly the matrices `g ξ̂`, `ξ` a twist (MLS printed p. 417,
`T_g L_h X = h X`, with `ξ̂` as in equation (2.31), p. 41). -/
theorem isTangentAt_iff (g : RigidTransform) (X : HomogeneousMatrix) :
    IsTangentAt g X ↔ ∃ ξ : Twist, X = g.toHomogeneous * ξ.hat := by
  constructor
  · intro hX
    refine ⟨vee ((g⁻¹).toHomogeneous * X), ?_⟩
    rw [hat_vee _ hX, ← Matrix.mul_assoc, RigidTransform.toHomogeneous_mul_inv, Matrix.one_mul]
  · rintro ⟨ξ, rfl⟩
    rw [IsTangentAt, toHomogeneous_inv_mul_cancel_left]
    exact hat_mem_se3Submodule ξ

/-- The left translated form at `g` on the tangent vectors `g ξ̂, g η̂` is `Ψ_e(ξ, η)`; at the
identity it is `Ψ_e` (MLS printed p. 424). Coordinates `(v, ω)`. -/
theorem leftTranslatedForm_mul_hat (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (g : RigidTransform) (ξ η : Twist) :
    leftTranslatedForm Ψ g (g.toHomogeneous * ξ.hat) (g.toHomogeneous * η.hat) = form Ψ ξ η := by
  rw [leftTranslatedForm, toHomogeneous_inv_mul_cancel_left, toHomogeneous_inv_mul_cancel_left,
    vee_hat, vee_hat]

/-- A form extended by left translation is left invariant, `L_h^* Ψ = Ψ`:
`Ψ_{h g}(h X, h Y) = Ψ_g(X, Y)` (MLS printed p. 424, "the resulting metric is automatically left
… invariant"; the pullback `F^* Ψ` and `F`-invariance as defined there). -/
theorem leftTranslatedForm_left (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (h g : RigidTransform) (X Y : HomogeneousMatrix) :
    leftTranslatedForm Ψ (h * g) (h.toHomogeneous * X) (h.toHomogeneous * Y) =
      leftTranslatedForm Ψ g X Y := by
  have e (Z : HomogeneousMatrix) :
      ((h * g)⁻¹).toHomogeneous * (h.toHomogeneous * Z) = (g⁻¹).toHomogeneous * Z := by
    rw [_root_.mul_inv_rev, RigidTransform.toHomogeneous_mul, Matrix.mul_assoc,
      toHomogeneous_inv_mul_cancel_left]
  rw [leftTranslatedForm, leftTranslatedForm, e, e]

/-- Right invariance of the left translated form, `R_h^* Ψ = Ψ` for every `h`:
`Ψ_{g h}(X h, Y h) = Ψ_g(X, Y)` for tangent vectors `X, Y` at `g` (MLS printed p. 424, right
invariance; the tangent map of `R_h` on matrices is `X ↦ X h`). -/
def IsRightInvariant (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) : Prop :=
  ∀ (g h : RigidTransform) (X Y : HomogeneousMatrix), IsTangentAt g X → IsTangentAt g Y →
    leftTranslatedForm Ψ (g * h) (X * h.toHomogeneous) (Y * h.toHomogeneous) =
      leftTranslatedForm Ψ g X Y

/-- Invariance of the left translated form under every conjugation `I_h(g) = h g h⁻¹`,
`I_h^* Ψ = Ψ` for all `h ∈ SE(3)` (MLS printed p. 424): `Ψ_{h g h⁻¹}(h X h⁻¹, h Y h⁻¹) = Ψ_g(X, Y)`
for tangent vectors `X, Y` at `g`; the tangent map of `I_h` on matrices is `X ↦ h X h⁻¹`. -/
def IsConjugationInvariant (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) : Prop :=
  ∀ (h g : RigidTransform) (X Y : HomogeneousMatrix), IsTangentAt g X → IsTangentAt g Y →
    leftTranslatedForm Ψ (h * g * h⁻¹) (h.toHomogeneous * X * (h⁻¹).toHomogeneous)
        (h.toHomogeneous * Y * (h⁻¹).toHomogeneous) =
      leftTranslatedForm Ψ g X Y

/-- MLS Lemma A.4, printed p. 425: the left translated form of `Ψ_e` is `I_h`-invariant for every
`h ∈ SE(3)` exactly when it is `I_h`-invariant at the identity, `Ψ_e(Ad_h ξ, Ad_h η) = Ψ_e(ξ, η)`
for all `h` and all twists, which is equation (A.11). Coordinates `(v, ω)`. -/
theorem isConjugationInvariant_iff_isAdInvariant
    (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    IsConjugationInvariant Ψ ↔ IsAdInvariant Ψ := by
  have e (h g : RigidTransform) (X : HomogeneousMatrix) (hX : IsTangentAt g X) :
      vee (((h * g * h⁻¹)⁻¹).toHomogeneous * (h.toHomogeneous * X * (h⁻¹).toHomogeneous)) =
        adjoint h (vee ((g⁻¹).toHomogeneous * X)) := by
    rw [← vee_conj h _ hX]
    congr 1
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, RigidTransform.toHomogeneous_mul,
      RigidTransform.toHomogeneous_mul]
    simp only [Matrix.mul_assoc, toHomogeneous_inv_mul_cancel_left]
  rw [isAdInvariant_iff_form]
  constructor
  · intro hc h ξ η
    have hξ : IsTangentAt 1 ξ.hat := by
      rw [isTangentAt_iff]; exact ⟨ξ, by rw [RigidTransform.toHomogeneous_one, Matrix.one_mul]⟩
    have hη : IsTangentAt 1 η.hat := by
      rw [isTangentAt_iff]; exact ⟨η, by rw [RigidTransform.toHomogeneous_one, Matrix.one_mul]⟩
    have := hc h 1 ξ.hat η.hat hξ hη
    rw [leftTranslatedForm, leftTranslatedForm, e h 1 _ hξ, e h 1 _ hη] at this
    simpa [RigidTransform.toHomogeneous_one] using this
  · intro hf h g X Y hX hY
    rw [leftTranslatedForm, leftTranslatedForm, e h g X hX, e h g Y hY, hf]

/-- The step of the proof of Lemma A.4, MLS printed p. 425: the left translated form of `Ψ_e` is
right invariant exactly when `Ψ_e` is `Ad`-invariant (A.11). Coordinates `(v, ω)`. -/
theorem isRightInvariant_iff_isAdInvariant (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    IsRightInvariant Ψ ↔ IsAdInvariant Ψ := by
  have e (g h : RigidTransform) (X : HomogeneousMatrix) (hX : IsTangentAt g X) :
      vee (((g * h)⁻¹).toHomogeneous * (X * h.toHomogeneous)) =
        adjoint h⁻¹ (vee ((g⁻¹).toHomogeneous * X)) := by
    rw [← vee_conj h⁻¹ _ hX, inv_inv]
    congr 1
    rw [_root_.mul_inv_rev, RigidTransform.toHomogeneous_mul]
    simp only [Matrix.mul_assoc]
  rw [isAdInvariant_iff_form]
  constructor
  · intro hr h ξ η
    have hξ : IsTangentAt 1 ξ.hat := by
      rw [isTangentAt_iff]; exact ⟨ξ, by rw [RigidTransform.toHomogeneous_one, Matrix.one_mul]⟩
    have hη : IsTangentAt 1 η.hat := by
      rw [isTangentAt_iff]; exact ⟨η, by rw [RigidTransform.toHomogeneous_one, Matrix.one_mul]⟩
    have := hr 1 h⁻¹ ξ.hat η.hat hξ hη
    rw [leftTranslatedForm, leftTranslatedForm, e 1 h⁻¹ _ hξ, e 1 h⁻¹ _ hη, inv_inv] at this
    simpa [RigidTransform.toHomogeneous_one] using this
  · intro hf g h X Y hX hY
    rw [leftTranslatedForm, leftTranslatedForm, e g h X hX, e g h Y hY, hf]

/-- MLS Proposition A.5, printed p. 425, for left invariant quadratic forms on `SE(3)` read as
forms on `se(3)` extended by left translation: the left translated form of a symmetric `Ψ_e` is
bi-invariant (right invariant, equivalently `I_h`-invariant for every `h`) exactly when
`Ψ_e = [[0, β I], [β I, γ I]]`. Coordinates `(v, ω)`. -/
theorem isRightInvariant_iff_eq_biInvariantMatrix
    (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (hΨ : Ψᵀ = Ψ) :
    IsRightInvariant Ψ ↔ ∃ β γ : ℝ, Ψ = biInvariantMatrix β γ := by
  rw [isRightInvariant_iff_isAdInvariant, isAdInvariant_iff_eq_biInvariantMatrix Ψ hΨ]

/-- MLS Corollary A.5.1, printed p. 427, in the left translated reading: no positive definite
form at the identity (Mathlib's `PosDef`) has a bi-invariant left translation. -/
theorem not_exists_posDef_isRightInvariant :
    ¬ ∃ Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ, Ψ.PosDef ∧ IsRightInvariant Ψ := by
  rintro ⟨Ψ, hpos, hr⟩
  exact not_exists_posDef_isAdInvariant ⟨Ψ, hpos, (isRightInvariant_iff_isAdInvariant Ψ).mp hr⟩

end Twist

end RoboLean
