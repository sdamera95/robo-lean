import RoboLean.Geometry.TwistAdjoint
import RoboLean.LieGroups.InvariantMetrics

/-!
# Bilinear forms on twist coordinates and their invariance under the adjoint action

MLS Appendix A, §3.2, printed pp. 422 and 424–427. The Lie algebra `se(3)` is identified with
`ℝ⁶` through the twist coordinates `ξ = (v, ω)`, linear part first (MLS equation (2.30), p. 41,
and the block form of `Ad_h` on p. 426). A bilinear form on `se(3)` is written through its
`6 × 6` matrix `Ψ` as `Ψ(ξ, η) = ξᵀ Ψ η` (p. 423 for `ℝⁿ`, p. 425 for `se(3)`).

A change of coordinate frame by `g ∈ SE(3)` acts on twists by `Ad_g` (p. 422), so a form is
invariant under every change of frame exactly when `Ad_hᵀ Ψ Ad_h = Ψ` for every `h`, equation
(A.11), equivalently `Ψ(Ad_h ξ, Ad_h η) = Ψ(ξ, η)`, equation (A.10). In this file that condition
is the statement about forms on `ℝ⁶`; the reading of a left invariant quadratic form on `SE(3)`
as a form on `se(3)` extended by left translation, and Lemma A.4 in that reading, are in
`RoboLean.LieGroups.LeftInvariantForms`.

Contents: the display on p. 422 for `Ad_gᵀ Ad_g` and the failure of frame invariance of the
Euclidean inner product of twist coordinates (also MLS Exercise 2.17(b), p. 78); the block
equations (A.12); Proposition A.5 (the `Ad`-invariant symmetric forms are exactly
`[[0, β I], [β I, γ I]]`); Corollary A.5.1 (no `Ad`-invariant positive definite form).
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Twist

/-- The bilinear form with matrix `Ψ` on twist coordinates, `Ψ(ξ, η) = ξᵀ Ψ η`, with `se(3)`
identified with `ℝ⁶` through the coordinates `(v, ω)` (MLS printed p. 423, `Ψ(v, w) = vᵀ Ψ w`,
and p. 425, "identifying `se(3)` with `ℝ⁶`"). -/
def form (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (ξ η : Twist) : ℝ :=
  ξ.coordinates ⬝ᵥ (Ψ *ᵥ η.coordinates)

/-- Invariance of a form on `se(3)` under every change of coordinate frame, MLS equation (A.11),
printed p. 425: `Ad_hᵀ Ψ Ad_h = Ψ` for all `h ∈ SE(3)`, with `Ad_h` the block matrix
`[[R, p̂ R], [0, R]]` of equation (2.58), p. 55, on coordinates `(v, ω)`. -/
def IsAdInvariant (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) : Prop :=
  ∀ h : RigidTransform, (adjointMatrix h)ᵀ * Ψ * adjointMatrix h = Ψ

/-- `Vec3.hat 0 = 0`: the cross product with the zero vector vanishes (MLS equation (2.4),
printed p. 26). Supporting lemma. -/
private theorem hat_zero_vec : Vec3.hat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vec3.hat]

/-- The form of a matrix product: `(M x) · Ψ (M y) = x · (Mᵀ Ψ M) y`. Supporting lemma for (A.10)
and (A.11), MLS printed p. 425. -/
private theorem dotProduct_mulVec_conj (M Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (x y : Fin 3 ⊕ Fin 3 → ℝ) :
    (M *ᵥ x) ⬝ᵥ (Ψ *ᵥ (M *ᵥ y)) = x ⬝ᵥ ((Mᵀ * Ψ * M) *ᵥ y) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Two matrices with the same form on all twists are equal (supporting lemma: the coordinates of
MLS equation (2.30), p. 41, are onto `ℝ⁶`). -/
private theorem form_ext {A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ}
    (h : ∀ ξ η : Twist, form A ξ η = form B ξ η) : A = B := by
  ext i j
  have := h (coordinatesEquiv.symm (Pi.single i 1)) (coordinatesEquiv.symm (Pi.single j 1))
  simp only [form, ← coordinatesEquiv_apply, LinearEquiv.apply_symm_apply] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- The form of `Ψ` evaluated on transformed twists is the form of `Ad_hᵀ Ψ Ad_h`: MLS printed
p. 422 (the display for the Euclidean inner product) and p. 425 (from (A.10) to (A.11));
coordinates `(v, ω)`. -/
theorem form_adjoint (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (h : RigidTransform)
    (ξ η : Twist) :
    form Ψ (adjoint h ξ) (adjoint h η) = form ((adjointMatrix h)ᵀ * Ψ * adjointMatrix h) ξ η := by
  rw [form, form, ← adjointMatrix_mulVec, ← adjointMatrix_mulVec, dotProduct_mulVec_conj]

/-- Equations (A.10) and (A.11) are equivalent, MLS printed p. 425: `Ψ(Ad_h ξ, Ad_h η) = Ψ(ξ, η)`
for all `h` and all twists exactly when `Ad_hᵀ Ψ Ad_h = Ψ` for all `h`. Coordinates `(v, ω)`. -/
theorem isAdInvariant_iff_form (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    IsAdInvariant Ψ ↔
      ∀ (h : RigidTransform) (ξ η : Twist), form Ψ (adjoint h ξ) (adjoint h η) = form Ψ ξ η := by
  constructor
  · intro hinv h ξ η
    rw [form_adjoint, hinv h]
  · intro hform h
    exact form_ext fun ξ η => by rw [← form_adjoint, hform]

/-- The Euclidean inner product of twist coordinates is the form of the identity matrix
(MLS printed p. 422, "the usual inner product on `ℝ⁶`"); coordinates `(v, ω)`. -/
theorem form_one (ξ η : Twist) : form 1 ξ η = ξ.coordinates ⬝ᵥ η.coordinates := by
  rw [form, Matrix.one_mulVec]

/-- MLS equations (A.12), printed p. 426: with `Ψ = [[A, B], [B′, C]]` and `h = (p, R)`,
`Ad_hᵀ Ψ Ad_h` has the blocks `Rᵀ A R`, `Rᵀ A p̂ R + Rᵀ B R`, `-Rᵀ p̂ A R + Rᵀ B′ R` and
`-Rᵀ p̂ A p̂ R - Rᵀ p̂ B R + Rᵀ B′ p̂ R + Rᵀ C R`. The book takes `B′ = Bᵀ` and prints the three
blocks other than the lower-left; here `B′` is arbitrary. Coordinates `(v, ω)`. -/
theorem adjointMatrix_transpose_mul_fromBlocks_mul (h : RigidTransform)
    (A B B' C : Matrix (Fin 3) (Fin 3) ℝ) :
    (adjointMatrix h)ᵀ * fromBlocks A B B' C * adjointMatrix h =
      fromBlocks (h.rotation.valᵀ * A * h.rotation.val)
        (h.rotation.valᵀ * A * Vec3.hat h.translation * h.rotation.val +
          h.rotation.valᵀ * B * h.rotation.val)
        (-(h.rotation.valᵀ * Vec3.hat h.translation * A * h.rotation.val) +
          h.rotation.valᵀ * B' * h.rotation.val)
        (-(h.rotation.valᵀ * Vec3.hat h.translation * A * Vec3.hat h.translation *
            h.rotation.val) -
          h.rotation.valᵀ * Vec3.hat h.translation * B * h.rotation.val +
          h.rotation.valᵀ * B' * Vec3.hat h.translation * h.rotation.val +
          h.rotation.valᵀ * C * h.rotation.val) := by
  rw [adjointMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_mul, Vec3.hat_transpose, Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero]
  congr 1 <;> noncomm_ring

/-- The display of MLS printed p. 422: `Ad_gᵀ Ad_g = [[I, Rᵀ p̂ R], [-Rᵀ p̂ R, I - Rᵀ p̂² R]]` for
`g = (p, R)`, so that `ξ₁′ · ξ₂′ = ξ₁ᵀ (Ad_gᵀ Ad_g) ξ₂` for `ξᵢ′ = Ad_g ξᵢ`. Coordinates `(v, ω)`. -/
theorem adjointMatrix_transpose_mul_self (g : RigidTransform) :
    (adjointMatrix g)ᵀ * adjointMatrix g =
      fromBlocks 1 (g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val)
        (-(g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val))
        (1 - g.rotation.valᵀ * Vec3.hat g.translation * Vec3.hat g.translation *
          g.rotation.val) := by
  have h := adjointMatrix_transpose_mul_fromBlocks_mul g 1 0 0 1
  rw [Matrix.fromBlocks_one, Matrix.mul_one] at h
  rw [h]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, sub_zero,
    Rotation.transpose_mul]
  congr 1
  abel

/-- The Euclidean inner product of twists in the new frame, MLS printed p. 422:
`Ad_g ξ₁ · Ad_g ξ₂ = ξ₁ᵀ (Ad_gᵀ Ad_g) ξ₂`. Coordinates `(v, ω)`. -/
theorem coordinates_adjoint_dotProduct (g : RigidTransform) (ξ η : Twist) :
    (adjoint g ξ).coordinates ⬝ᵥ (adjoint g η).coordinates =
      form ((adjointMatrix g)ᵀ * adjointMatrix g) ξ η := by
  rw [← form_one, form_adjoint, Matrix.mul_one]

/-- MLS printed p. 422, "if `p ≠ 0`, then the dot product is not preserved": the change of frame
by `g = (p, R)` preserves the Euclidean inner product of twist coordinates, `Ad_gᵀ Ad_g = I`,
exactly when `p = 0`. Coordinates `(v, ω)`. -/
theorem adjointMatrix_transpose_mul_self_eq_one_iff (g : RigidTransform) :
    (adjointMatrix g)ᵀ * adjointMatrix g = 1 ↔ g.translation = 0 := by
  rw [adjointMatrix_transpose_mul_self, ← Matrix.fromBlocks_one]
  constructor
  · intro h
    have h12 := (Matrix.fromBlocks_inj.mp h).2.1
    have hp : Vec3.hat g.translation = 0 := by
      calc Vec3.hat g.translation
          = g.rotation.val * (g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val) *
              g.rotation.valᵀ := by
            simp only [← Matrix.mul_assoc, Rotation.mul_transpose, Matrix.one_mul]
            rw [Matrix.mul_assoc, Rotation.mul_transpose, Matrix.mul_one]
        _ = 0 := by rw [h12, Matrix.mul_zero, Matrix.zero_mul]
    rw [← Vec3.vee_hat g.translation, hp]
    ext i
    fin_cases i <;> simp [Vec3.vee]
  · intro hp
    rw [hp, hat_zero_vec]
    simp

/-- Two twists orthogonal in one frame need not be orthogonal in another, MLS printed p. 422, and
MLS Exercise 2.17(b), printed p. 78 (the inner product between two twists is not frame
invariant): for `g = (e₁, I)`, the twists `(0, e₃)` and `(e₂, 0)` have zero Euclidean inner
product while their transforms by `Ad_g` have inner product `-1`. Coordinates `(v, ω)`, indices
`0, 1, 2` for the book's `1, 2, 3`. -/
theorem exists_dotProduct_eq_zero_adjoint_ne_zero :
    ∃ (g : RigidTransform) (ξ η : Twist), ξ.coordinates ⬝ᵥ η.coordinates = 0 ∧
      (adjoint g ξ).coordinates ⬝ᵥ (adjoint g η).coordinates ≠ 0 := by
  refine ⟨⟨1, WithLp.toLp 2 ![1, 0, 0]⟩, ⟨0, WithLp.toLp 2 ![0, 0, 1]⟩,
    ⟨WithLp.toLp 2 ![0, 1, 0], 0⟩, ?_, ?_⟩
  · simp [coordinates, dotProduct, Fintype.sum_sum_type]
  · simp [coordinates, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three, adjoint,
      Vec3.cross, cross_apply]

/-- The Euclidean form on `se(3) ≅ ℝ⁶` is not invariant under change of coordinate frame,
MLS printed p. 422 (and p. 423, "there is no inner product structure on `se(3)` which is invariant
under change of coordinate frame", made precise by Corollary A.5.1). Coordinates `(v, ω)`. -/
theorem not_isAdInvariant_one : ¬ IsAdInvariant 1 := by
  intro h
  have h1 := h ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩
  rw [Matrix.mul_one, adjointMatrix_transpose_mul_self_eq_one_iff] at h1
  have := congrArg (fun v : Vec3 => v 0) h1
  simp at this

/-- The matrix `[[0, β I], [β I, γ I]]` of MLS Proposition A.5, printed p. 425, on coordinates
`(v, ω)`: the bi-invariant quadratic forms on `SE(3)` at the identity. -/
def biInvariantMatrix (β γ : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks 0 (β • 1) (β • 1) (γ • 1)

/-- The matrix of Proposition A.5 is symmetric (MLS printed p. 425; a quadratic form is
symmetric, p. 424). -/
theorem biInvariantMatrix_transpose (β γ : ℝ) : (biInvariantMatrix β γ)ᵀ = biInvariantMatrix β γ := by
  simp [biInvariantMatrix, Matrix.fromBlocks_transpose]

/-- The form of `[[0, β I], [β I, γ I]]` in coordinates, MLS printed pp. 425–427:
`β (v₁ · ω₂ + ω₁ · v₂) + γ (ω₁ · ω₂)` for `ξ = (v₁, ω₁)` and `η = (v₂, ω₂)`. -/
theorem form_biInvariantMatrix (β γ : ℝ) (ξ η : Twist) :
    form (biInvariantMatrix β γ) ξ η =
      β * (inner ℝ ξ.linear η.angular + inner ℝ ξ.angular η.linear) +
        γ * inner ℝ ξ.angular η.angular := by
  simp only [form, biInvariantMatrix, coordinates, Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, zero_add]
  simp [dotProduct, Fintype.sum_sum_type, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- MLS Proposition A.5, printed p. 425, at the identity: a symmetric form `Ψ` on `se(3) ≅ ℝ⁶`
satisfies (A.11), `Ad_hᵀ Ψ Ad_h = Ψ` for all `h ∈ SE(3)`, exactly when
`Ψ = [[0, β I], [β I, γ I]]` for some `β, γ ∈ ℝ`. Coordinates `(v, ω)`. With Lemma A.4
(`RoboLean.LieGroups.LeftInvariantForms`) this is the book's statement for left invariant
quadratic forms on `SE(3)`. -/
theorem isAdInvariant_iff_eq_biInvariantMatrix (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (hΨ : Ψᵀ = Ψ) : IsAdInvariant Ψ ↔ ∃ β γ : ℝ, Ψ = biInvariantMatrix β γ := by
  constructor
  · intro hinv
    set A := Ψ.toBlocks₁₁
    set B := Ψ.toBlocks₁₂
    set B' := Ψ.toBlocks₂₁
    set C := Ψ.toBlocks₂₂
    have hΨb : Ψ = fromBlocks A B B' C := (Matrix.fromBlocks_toBlocks Ψ).symm
    have hblocks (h : RigidTransform) := by
      have e := hinv h
      rw [hΨb, adjointMatrix_transpose_mul_fromBlocks_mul] at e
      exact Matrix.fromBlocks_inj.mp e
    -- rotations about the origin: every block commutes with every rotation
    have hcomm (M : Matrix (Fin 3) (Fin 3) ℝ)
        (hM : ∀ R : Rotation, R.valᵀ * M * R.val = M) :
        ∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, M * R = R * M := by
      intro R hR
      have e := hM ⟨R, hR⟩
      calc M * R = (R * Rᵀ) * (M * R) := by
            rw [show R * Rᵀ = 1 from Rotation.mul_transpose ⟨R, hR⟩, Matrix.one_mul]
        _ = R * (Rᵀ * M * R) := by simp only [Matrix.mul_assoc]
        _ = R * M := by rw [e]
    have hrot (R : Rotation) := hblocks ⟨R, 0⟩
    simp only [hat_zero_vec, Matrix.mul_zero, Matrix.zero_mul, add_zero, neg_zero, zero_add,
      sub_zero] at hrot
    obtain ⟨α, hα⟩ := InvariantMetric.eq_smul_one_of_commute_of_three_le le_rfl A
      (hcomm A fun R => (hrot R).1)
    obtain ⟨β, hβ⟩ := InvariantMetric.eq_smul_one_of_commute_of_three_le le_rfl B
      (hcomm B fun R => (hrot R).2.1)
    obtain ⟨γ, hγ⟩ := InvariantMetric.eq_smul_one_of_commute_of_three_le le_rfl C
      (hcomm C fun R => (hrot R).2.2.2)
    have hB' : B' = Bᵀ := by
      ext i j
      have := congrFun (congrFun hΨ (Sum.inr i)) (Sum.inl j)
      simpa [B', B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using this.symm
    -- a pure translation forces `α = 0`
    have htr := (hblocks ⟨1, WithLp.toLp 2 ![1, 0, 0]⟩).2.1
    simp only [OneMemClass.coe_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at htr
    have hα0 : α = 0 := by
      have e := congrFun (congrFun htr 1) 2
      rw [hα] at e
      simpa [Vec3.hat, Matrix.smul_mul] using e
    refine ⟨β, γ, ?_⟩
    rw [hΨb, biInvariantMatrix, hα, hα0, zero_smul, hB', hβ, hγ]
    simp
  · rintro ⟨β, γ, rfl⟩ h
    rw [biInvariantMatrix, adjointMatrix_transpose_mul_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, zero_add, zero_sub, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Rotation.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    abel

/-- MLS printed p. 427, before Corollary A.5.1: every bi-invariant quadratic form vanishes on pure
translations, `Ψ((v, 0), (v, 0)) = 0`. Stated for a symmetric `Ad`-invariant `Ψ`;
coordinates `(v, ω)`. -/
theorem form_linear_self_eq_zero (Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ)
    (hΨ : Ψᵀ = Ψ) (hinv : IsAdInvariant Ψ) (v : Vec3) : form Ψ ⟨v, 0⟩ ⟨v, 0⟩ = 0 := by
  obtain ⟨β, γ, rfl⟩ := (isAdInvariant_iff_eq_biInvariantMatrix Ψ hΨ).mp hinv
  simp [form_biInvariantMatrix]

/-- MLS Corollary A.5.1, printed p. 427: there is no bi-invariant positive definite metric on
`SE(3)`. Stated at the identity: no positive definite `6 × 6` matrix (Mathlib's `PosDef`,
symmetric with `xᵀ Ψ x > 0` for `x ≠ 0`) satisfies (A.11). Coordinates `(v, ω)`. -/
theorem not_exists_posDef_isAdInvariant :
    ¬ ∃ Ψ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ, Ψ.PosDef ∧ IsAdInvariant Ψ := by
  rintro ⟨Ψ, hpos, hinv⟩
  have hsymm : Ψᵀ = Ψ := by
    have := hpos.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set ξ : Twist := ⟨WithLp.toLp 2 ![1, 0, 0], 0⟩
  have hne : ξ.coordinates ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp [ξ, coordinates] at this
  have hlt := (Matrix.posDef_iff_dotProduct_mulVec.mp hpos).2 hne
  have h0 := form_linear_self_eq_zero Ψ hsymm hinv (WithLp.toLp 2 ![1, 0, 0])
  rw [form] at h0
  simp only [star_trivial] at hlt
  linarith

end Twist

end RoboLean
