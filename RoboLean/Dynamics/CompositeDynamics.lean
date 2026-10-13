import RoboLean.Dynamics.ConstrainedLagrangian
import RoboLean.Control.WorkspaceControl

/-!
# Robot hand dynamics: the composite system, eqs. (6.18)–(6.26) and Lemma 6.1

MLS Chapter 6, §2, printed pp. 276–284 (renders inspected this session).

**Setting (MLS pp. 276–278).** Fingers with joint angles `θ ∈ ℝⁿ` and dynamics
`M_f(θ) θ̈ + C_f θ̇ + N_f = τ` (6.16); an object with local coordinates `x ∈ ℝᵖ` and dynamics
`M_o(x) ẍ + C_o ẋ + N_o = 0` (p. 277); the grasp constraint (6.18) `J_h(θ, x) θ̇ = Gᵀ(θ, x) ẋ` with
`J_h` invertible (assumption 2, p. 277, so `m = n`). The composite configuration is `q = (θ, x)`;
here it is `q ∈ ℝᴺ` with a relabeling `e : Fin p ⊕ Fin n ≃ Fin N`, `x = q ∘ e ∘ inl`,
`θ = q ∘ e ∘ inr` (`Constrained.splitFst`, `splitSnd`), so that MLS's ordering `q = (θ, x)` is one
choice of `e` (`mlsSplit`).

**The object chart is abstract** (E034 ruling): `J_h` and `Gᵀ` are matrix-valued functions of the
composite configuration, or matrix curves along a motion with actual entrywise derivatives as
hypotheses, as MLS treats every system of §2.3. The library's twist-level grasping constraint
`HandGrasp.GraspingConstraint` (`J_h θ̇ = Gᵀ V^b_po`, MLS (5.15), E028) is the origin of (6.18); its
link to a local chart `x ↦ x_o ∈ SE(3)` with Jacobian `J_φ(x)` is not formalized here.

**Sign convention.** The constraint matrix is `A = [J_h −Gᵀ]` (MLS p. 267, `handPfaffian`), so that
the multiplier `λ` of (6.4) satisfies `J_hᵀ λ = τ − (M_f θ̈ + C_f θ̇ + N_f)` and
`G λ = M_o ẍ + C_o ẋ + N_o`: `λ` is the contact force in the sense of MLS (5.16), `τ = J_hᵀ f_c` (p.
238), at rest without finger gravity. MLS p. 280 prints `A = [−J_h Gᵀ]` together with
`λ = J_h⁻ᵀ (τ − M_f θ̈ − C_f θ̇ − N_f)`; that `λ` is the one of `A = [J_h −Gᵀ]` (E034 source
observation, one-input evaluation in the gate's `Observation.lean`).

**Formalized.**

* The congruence identity behind Lemma 4.11(2) and Lemma 6.1(2), for rectangular `S`:
  `S'ᵀ M S + Sᵀ Ṁ S + Sᵀ M S' − 2 Sᵀ (C S + M S') = Sᵀ (Ṁ − 2C) S + S'ᵀ M S − Sᵀ M S'`, skew when
  `M` is symmetric and `Ṁ − 2C` is skew (`skew_reduced`). It covers `S = J⁻¹` (Lemma 4.11),
  `S = J_h⁻¹ Gᵀ` (Lemma 6.1) and the augmented Jacobians of §3.
* The effective parameters (6.22) `effectiveMass`, `effectiveCoriolis`, `effectiveN`,
  `effectiveForce`, with the book's `(d/dt)(J_h⁻¹ Gᵀ)` an explicit argument, and the algebra of
  (6.20) ⇒ (6.21) (`effective_dynamics_eq`).
* Lemma 6.1(1): `M̃` symmetric; positive definite for `M_o` positive definite and `M_f`
  semidefinite, or for `M_f` positive definite, `M_o` semidefinite (possibly `0`), `J_h` invertible
  and `G` onto (the book's route through force-closure, which makes `G` onto). Lemma 6.1(2):
  `M̃˙ − 2C̃` skew for every actual derivative `M̃˙` along a motion, given the skew symmetry of
  `Ṁ_o − 2C_o` and `Ṁ_f − 2C_f` (the "usual structural properties", p. 283) and an actual derivative
  of `J_h⁻¹ Gᵀ`.
* The workspace form (6.26) with `G = I` and its overlap with E029's Lemma 4.11 (`M_o = 0`).
* The composite Lagrangian (6.19), (6.18) as a Pfaffian constraint with independent rows, (6.20) as
  the instance of (6.9) with `q₁ = x`, `q₂ = θ`, `A₁ = −Gᵀ`, `A₂ = J_h`, (6.21) along a motion, the
  multiplier equations (6.24) and the displayed contact-force formula of p. 280.

**Hypotheses the book does not print, all explicit:** symmetric `M_f`, `M_o`; `J_h` invertible along
the motion near `t` (assumption 2, p. 277, at the configurations used); the constraint (6.18) on a
neighborhood of `t`; an actual derivative of `s ↦ J_h⁻¹ Gᵀ` at `t`; the skew symmetry of the finger
and object pieces as hypotheses (for Christoffel matrices it is E013's Lemma 4.2(2)). Existence or
uniqueness of motions of the composite system is not claimed; force-closure and friction-cone
conditions (assumptions 1 and 3, p. 277) are not used by the algebra and are not formalized here.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Composite

/-! ### The congruence identity (MLS Lemmas 4.11(2) and 6.1(2), pp. 197, 279) -/

section Congruence

variable {ι κ : Type*} [Fintype ι]

/-- **The identity in the proof of MLS Lemma 6.1(2), p. 279, for a rectangular reduction `S`.** With
`M̃ = Sᵀ M S`, `M̃˙ = S'ᵀ M S + Sᵀ Ṁ S + Sᵀ M S'` and `C̃ = Sᵀ (C S + M S')`,
`M̃˙ − 2C̃ = Sᵀ (Ṁ − 2C) S + S'ᵀ M S − Sᵀ M S'`. For `S = J_h⁻¹ Gᵀ` this is the printed identity of
p. 279 (finger part); for `S = J⁻¹` it is Lemma 4.11's (p. 197). -/
theorem reduced_sub_two_eq (M Md C : Matrix ι ι ℝ) (S S' : Matrix ι κ ℝ) :
    S'ᵀ * M * S + Sᵀ * Md * S + Sᵀ * M * S' - (2 : ℝ) • (Sᵀ * (C * S + M * S')) =
      Sᵀ * (Md - (2 : ℝ) • C) * S + S'ᵀ * M * S - Sᵀ * M * S' := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]
  module

/-- **The congruence step of MLS Lemma 6.1(2), p. 279, for a rectangular reduction `S`:** "Taking
transposes and using symmetry of `M_f` inverts the sign of the last line". If `M` is symmetric and
`Ṁ − 2C` is skew-symmetric, then `S'ᵀ M S + Sᵀ Ṁ S + Sᵀ M S' − 2 Sᵀ (C S + M S')` is skew-symmetric
for all `S`, `S'`. -/
theorem skew_reduced {M Md C : Matrix ι ι ℝ} {S S' : Matrix ι κ ℝ} (hM : Mᵀ = M)
    (hs : (Md - (2 : ℝ) • C)ᵀ = -(Md - (2 : ℝ) • C)) :
    (S'ᵀ * M * S + Sᵀ * Md * S + Sᵀ * M * S' - (2 : ℝ) • (Sᵀ * (C * S + M * S')))ᵀ =
      -(S'ᵀ * M * S + Sᵀ * Md * S + Sᵀ * M * S' - (2 : ℝ) • (Sᵀ * (C * S + M * S'))) := by
  rw [reduced_sub_two_eq, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, hs, hM, Matrix.transpose_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  module

end Congruence

/-! ### The effective parameters (MLS eqs. (6.21)–(6.22), p. 278) -/

variable {n p : ℕ}

/-- **MLS eq. (6.22), p. 278: the effective mass** `M̃ = M_o + G J_h⁻ᵀ M_f J_h⁻¹ Gᵀ`, with
`J_h⁻ᵀ = (J_h⁻¹)ᵀ` (`Matrix.inv`; meaningful where `J_h` is invertible). -/
def effectiveMass (Mo : Matrix (Fin p) (Fin p) ℝ) (Mf J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Mo + G * (J⁻¹)ᵀ * Mf * J⁻¹ * Gᵀ

/-- **MLS eq. (6.22), p. 278: the effective Coriolis matrix**
`C̃ = C_o + G J_h⁻ᵀ (C_f J_h⁻¹ Gᵀ + M_f (d/dt)(J_h⁻¹ Gᵀ))`; the book's `(d/dt)(J_h⁻¹ Gᵀ)` is the
argument `Bd`, an actual derivative along a motion in the theorems that use it. -/
def effectiveCoriolis (Co : Matrix (Fin p) (Fin p) ℝ) (Cf Mf J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) (Bd : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Co + G * (J⁻¹)ᵀ * (Cf * J⁻¹ * Gᵀ + Mf * Bd)

/-- **MLS eq. (6.22), p. 278: the effective gravitational and nonconservative forces**
`Ñ = N_o + G J_h⁻ᵀ N_f`. -/
def effectiveN (No : Fin p → ℝ) (Nf : Fin n → ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) : Fin p → ℝ :=
  No + (G * (J⁻¹)ᵀ) *ᵥ Nf

/-- **MLS eq. (6.22), p. 278: the object force produced by the joint torques,** `F = G J_h⁻ᵀ τ`. -/
def effectiveForce (J : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin p) (Fin n) ℝ)
    (τ : Fin n → ℝ) : Fin p → ℝ :=
  (G * (J⁻¹)ᵀ) *ᵥ τ

/-- **`(J_h⁻¹ Gᵀ)ᵀ = G J_h⁻ᵀ` (MLS p. 278).** -/
theorem transpose_inv_mul_transpose (J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) : (J⁻¹ * Gᵀ)ᵀ = G * (J⁻¹)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **MLS eq. (6.22) as a congruence:** `M̃ = M_o + Xᵀ M_f X` with `X = J_h⁻¹ Gᵀ` (p. 279). -/
theorem effectiveMass_eq (Mo : Matrix (Fin p) (Fin p) ℝ) (Mf J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) :
    effectiveMass Mo Mf J G = Mo + (J⁻¹ * Gᵀ)ᵀ * Mf * (J⁻¹ * Gᵀ) := by
  rw [transpose_inv_mul_transpose, effectiveMass]
  simp only [Matrix.mul_assoc]

/-- **MLS eq. (6.22) as a congruence:** `C̃ = C_o + Xᵀ (C_f X + M_f Ẋ)` with `X = J_h⁻¹ Gᵀ` and
`Ẋ = Bd` (p. 279). -/
theorem effectiveCoriolis_eq (Co : Matrix (Fin p) (Fin p) ℝ) (Cf Mf J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) (Bd : Matrix (Fin n) (Fin p) ℝ) :
    effectiveCoriolis Co Cf Mf J G Bd = Co + (J⁻¹ * Gᵀ)ᵀ * (Cf * (J⁻¹ * Gᵀ) + Mf * Bd) := by
  rw [transpose_inv_mul_transpose, effectiveCoriolis]
  simp only [Matrix.mul_assoc]

/-- **The algebra of MLS eqs. (6.20)–(6.21), p. 278: "eliminating `θ̇` and `θ̈` via the
constraints".** If `θ̇ = J_h⁻¹ Gᵀ ẋ` and `θ̈ = J_h⁻¹ Gᵀ ẍ + Ẋ ẋ` (with `Ẋ = Bd`), then the left side
of (6.20), `(M_o ẍ + C_o ẋ + N_o) + G J_h⁻ᵀ (M_f θ̈ + C_f θ̇ + N_f)`, is `M̃ ẍ + C̃ ẋ + Ñ`. -/
theorem effective_dynamics_eq (Mo Co : Matrix (Fin p) (Fin p) ℝ) (No : Fin p → ℝ)
    (Mf Cf J : Matrix (Fin n) (Fin n) ℝ) (Nf : Fin n → ℝ) (G : Matrix (Fin p) (Fin n) ℝ)
    (Bd : Matrix (Fin n) (Fin p) ℝ) {x' x'' : Fin p → ℝ} {θ' θ'' : Fin n → ℝ}
    (hv : θ' = (J⁻¹ * Gᵀ) *ᵥ x') (ha : θ'' = (J⁻¹ * Gᵀ) *ᵥ x'' + Bd *ᵥ x') :
    (Mo *ᵥ x'' + Co *ᵥ x' + No) + (G * (J⁻¹)ᵀ) *ᵥ (Mf *ᵥ θ'' + Cf *ᵥ θ' + Nf) =
      effectiveMass Mo Mf J G *ᵥ x'' + effectiveCoriolis Co Cf Mf J G Bd *ᵥ x' +
        effectiveN No Nf J G := by
  subst hv ha
  simp only [effectiveMass, effectiveCoriolis, effectiveN, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- **The book's `(d/dt)(J_h⁻¹ Gᵀ)` from the rates of `J_h` and `G` (MLS p. 278).** If the entries
of `s ↦ J_h(s)` and `s ↦ G(s)` have the derivatives `J'`, `G'` at `t` and `J_h(t)` is invertible,
the entries of `s ↦ J_h(s)⁻¹ G(s)ᵀ` have the derivative `−J_h⁻¹ J' J_h⁻¹ Gᵀ + J_h⁻¹ G'ᵀ` at `t`. -/
theorem hasDerivAt_inv_mul_transpose {J : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G : ℝ → Matrix (Fin p) (Fin n) ℝ} {J' : Matrix (Fin n) (Fin n) ℝ}
    {G' : Matrix (Fin p) (Fin n) ℝ} {t : ℝ} (hJ : ∀ i j, HasDerivAt (fun s => J s i j) (J' i j) t)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) (hu : IsUnit (J t).det) (i : Fin n)
    (a : Fin p) :
    HasDerivAt (fun s => ((J s)⁻¹ * (G s)ᵀ) i a)
      ((-((J t)⁻¹ * J' * (J t)⁻¹) * (G t)ᵀ + (J t)⁻¹ * G'ᵀ) i a) t :=
  Control.hasDerivAt_matrix_mul (Control.hasDerivAt_matrix_inv hJ hu)
    (Control.hasDerivAt_matrix_transpose hG) i a

/-! ### Lemma 6.1(1): the effective mass is symmetric and positive definite (MLS p. 279) -/

/-- **MLS Lemma 6.1(1), p. 279, symmetry:** for symmetric `M_o` and `M_f`, `M̃` is symmetric (no
invertibility is needed). -/
theorem effectiveMass_isSymm {Mo : Matrix (Fin p) (Fin p) ℝ} {Mf : Matrix (Fin n) (Fin n) ℝ}
    (hMo : Mo.IsSymm) (hMf : Mf.IsSymm) (J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) : (effectiveMass Mo Mf J G).IsSymm := by
  rw [effectiveMass_eq]
  generalize J⁻¹ * Gᵀ = X
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add, hMo.eq, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hMf.eq, Matrix.mul_assoc]

/-- **MLS Lemma 6.1(1), p. 279, positive definiteness from the object (p. 277, `M_o(x) > 0`):** for
`M_o` positive definite and `M_f` positive semidefinite, `M̃` is positive definite for every `J_h`
and `G` (Mathlib's `Matrix.PosDef`, which includes symmetry). -/
theorem effectiveMass_posDef {Mo : Matrix (Fin p) (Fin p) ℝ} {Mf : Matrix (Fin n) (Fin n) ℝ}
    (hMo : Mo.PosDef) (hMf : Mf.PosSemidef) (J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) : (effectiveMass Mo Mf J G).PosDef := by
  rw [effectiveMass_eq]
  have h := hMf.conjTranspose_mul_mul_same (J⁻¹ * Gᵀ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact hMo.add_posSemidef h

/-- **`G` onto makes `Gᵀ` injective (MLS p. 279 with p. 214).** Force-closure gives `G(FC) = ℝᵖ`, so
`G` is onto, and then `λ ↦ Gᵀ λ` is injective. -/
theorem transpose_mulVec_injective_of_surjective {G : Matrix (Fin p) (Fin n) ℝ}
    (hG : Function.Surjective G.mulVec) : Function.Injective Gᵀ.mulVec := by
  intro a b hab
  have h0 : Gᵀ *ᵥ (a - b) = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hab
  obtain ⟨z, hz⟩ := hG (a - b)
  have h1 : (a - b) ⬝ᵥ (G *ᵥ z) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h0, zero_dotProduct]
  rw [hz] at h1
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h1)

/-- **MLS Lemma 6.1(1), p. 279, the book's route:** "Since the grasp is assumed to be force-closure
and manipulable and `J_h` is assumed injective, property 1 follows". For `M_f` positive definite
(Lemma 4.2(1)), `M_o` positive semidefinite (possibly `0`, as on p. 284), `J_h` invertible and `G`
onto (a consequence of force-closure, `G(FC) = ℝᵖ`, p. 214), `M̃` is positive definite. -/
theorem effectiveMass_posDef_of_surjective {Mo : Matrix (Fin p) (Fin p) ℝ}
    {Mf J : Matrix (Fin n) (Fin n) ℝ} {G : Matrix (Fin p) (Fin n) ℝ} (hMo : Mo.PosSemidef)
    (hMf : Mf.PosDef) (hJ : IsUnit J.det) (hG : Function.Surjective G.mulVec) :
    (effectiveMass Mo Mf J G).PosDef := by
  rw [effectiveMass_eq, add_comm]
  have hJi : Function.Injective (J⁻¹).mulVec :=
    Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det J hJ))
  have hX : Function.Injective (J⁻¹ * Gᵀ).mulVec := by
    intro a b hab
    simp only [← Matrix.mulVec_mulVec] at hab
    exact transpose_mulVec_injective_of_surjective hG (hJi hab)
  have h := hMf.conjTranspose_mul_mul_same hX
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.add_posSemidef hMo

/-! ### Lemma 6.1(2): `M̃˙ − 2C̃` is skew-symmetric (MLS p. 279) -/

/-- **MLS Lemma 6.1(2), p. 279, at one instant.** With `X = J_h⁻¹ Gᵀ`, `Ẋ = Bd`, `M_f` symmetric and
`Ṁ_o − 2C_o`, `Ṁ_f − 2C_f` skew-symmetric, the matrix `(Ṁ_o + Ẋᵀ M_f X + Xᵀ Ṁ_f X + Xᵀ M_f Ẋ) − 2C̃`
is skew-symmetric; the first summand is the rate of `M̃` along a motion
(`hasDerivAt_effectiveMass`). The proof is the printed one: the object and finger pieces are skew,
and the transpose of the last line changes its sign. -/
theorem skew_effectiveMassRate_sub_two_effectiveCoriolis {Mod Co : Matrix (Fin p) (Fin p) ℝ}
    {Mf Mfd Cf : Matrix (Fin n) (Fin n) ℝ} (hMf : Mfᵀ = Mf)
    (hso : (Mod - (2 : ℝ) • Co)ᵀ = -(Mod - (2 : ℝ) • Co))
    (hsf : (Mfd - (2 : ℝ) • Cf)ᵀ = -(Mfd - (2 : ℝ) • Cf)) (J : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ) (Bd : Matrix (Fin n) (Fin p) ℝ) :
    (Mod + Bdᵀ * Mf * (J⁻¹ * Gᵀ) + (J⁻¹ * Gᵀ)ᵀ * Mfd * (J⁻¹ * Gᵀ) + (J⁻¹ * Gᵀ)ᵀ * Mf * Bd -
        (2 : ℝ) • effectiveCoriolis Co Cf Mf J G Bd)ᵀ =
      -(Mod + Bdᵀ * Mf * (J⁻¹ * Gᵀ) + (J⁻¹ * Gᵀ)ᵀ * Mfd * (J⁻¹ * Gᵀ) +
        (J⁻¹ * Gᵀ)ᵀ * Mf * Bd - (2 : ℝ) • effectiveCoriolis Co Cf Mf J G Bd) := by
  rw [effectiveCoriolis_eq]
  generalize J⁻¹ * Gᵀ = X
  have e : Mod + Bdᵀ * Mf * X + Xᵀ * Mfd * X + Xᵀ * Mf * Bd -
      (2 : ℝ) • (Co + Xᵀ * (Cf * X + Mf * Bd)) =
      (Mod - (2 : ℝ) • Co) + (Bdᵀ * Mf * X + Xᵀ * Mfd * X + Xᵀ * Mf * Bd -
        (2 : ℝ) • (Xᵀ * (Cf * X + Mf * Bd))) := by
    rw [smul_add]
    abel
  rw [e, Matrix.transpose_add, hso, skew_reduced hMf hsf, neg_add]

/-- **The rate of the effective mass along a motion (MLS p. 279, `M̃˙`).** If the entries of
`s ↦ M_o(s)`, `s ↦ M_f(s)` and `s ↦ J_h(s)⁻¹ G(s)ᵀ` have the derivatives `Ṁ_o`, `Ṁ_f`, `Ẋ` at `t`,
then the entries of `s ↦ M̃(s)` have the derivative `Ṁ_o + Ẋᵀ M_f X + Xᵀ Ṁ_f X + Xᵀ M_f Ẋ` at `t`,
`X = J_h(t)⁻¹ G(t)ᵀ`. -/
theorem hasDerivAt_effectiveMass {Mo : ℝ → Matrix (Fin p) (Fin p) ℝ}
    {Mf J : ℝ → Matrix (Fin n) (Fin n) ℝ} {G : ℝ → Matrix (Fin p) (Fin n) ℝ}
    {Mod : Matrix (Fin p) (Fin p) ℝ} {Mfd : Matrix (Fin n) (Fin n) ℝ}
    {Bd : Matrix (Fin n) (Fin p) ℝ} {t : ℝ} (hMo : ∀ i j, HasDerivAt (fun s => Mo s i j) (Mod i j)
    t)
    (hMf : ∀ i j, HasDerivAt (fun s => Mf s i j) (Mfd i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => ((J s)⁻¹ * (G s)ᵀ) i j) (Bd i j) t) (i j : Fin p) :
    HasDerivAt (fun s => effectiveMass (Mo s) (Mf s) (J s) (G s) i j)
      ((Mod + Bdᵀ * Mf t * ((J t)⁻¹ * (G t)ᵀ) + ((J t)⁻¹ * (G t)ᵀ)ᵀ * Mfd * ((J t)⁻¹ * (G t)ᵀ) +
        ((J t)⁻¹ * (G t)ᵀ)ᵀ * Mf t * Bd) i j) t := by
  have h := (hMo i j).add (Control.hasDerivAt_matrix_mul
    (Control.hasDerivAt_matrix_mul (Control.hasDerivAt_matrix_transpose hB) hMf) hB i j)
  convert h using 1
  · funext s
    rw [effectiveMass_eq]
    rfl
  · simp only [Matrix.add_apply, Matrix.add_mul]
    ring

/-- **MLS Lemma 6.1(2), p. 279: "`M̃˙(q) − 2C̃` is a skew-symmetric matrix", along a motion.** Let
the entries of `s ↦ M_o(s)`, `s ↦ M_f(s)` and `s ↦ J_h(s)⁻¹ G(s)ᵀ` have the derivatives `Ṁ_o`,
`Ṁ_f`, `Bd` at `t` (the book's `(d/dt)(J_h⁻¹ Gᵀ)`), let `M_f(t)` be symmetric and let `Ṁ_o − 2C_o`
and `Ṁ_f − 2C_f` be skew-symmetric (the structural properties of object and fingers). Then every
actual derivative `M̃˙` of `s ↦ M̃(s)` at `t` makes `M̃˙ − 2C̃` skew-symmetric, with `C̃` of (6.22).
-/
theorem skew_deriv_effectiveMass_sub_two_effectiveCoriolis {Mo : ℝ → Matrix (Fin p) (Fin p) ℝ}
    {Mf J : ℝ → Matrix (Fin n) (Fin n) ℝ} {G : ℝ → Matrix (Fin p) (Fin n) ℝ}
    {Mod Co : Matrix (Fin p) (Fin p) ℝ} {Mfd Cf : Matrix (Fin n) (Fin n) ℝ}
    {Bd : Matrix (Fin n) (Fin p) ℝ} {t : ℝ} (hMo : ∀ i j, HasDerivAt (fun s => Mo s i j) (Mod i j)
    t)
    (hMf : ∀ i j, HasDerivAt (fun s => Mf s i j) (Mfd i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => ((J s)⁻¹ * (G s)ᵀ) i j) (Bd i j) t)
    (hsymm : (Mf t)ᵀ = Mf t) (hso : (Mod - (2 : ℝ) • Co)ᵀ = -(Mod - (2 : ℝ) • Co))
    (hsf : (Mfd - (2 : ℝ) • Cf)ᵀ = -(Mfd - (2 : ℝ) • Cf)) {Mtd : Matrix (Fin p) (Fin p) ℝ}
    (hMt : ∀ i j, HasDerivAt (fun s => effectiveMass (Mo s) (Mf s) (J s) (G s) i j) (Mtd i j) t) :
    (Mtd - (2 : ℝ) • effectiveCoriolis Co Cf (Mf t) (J t) (G t) Bd)ᵀ =
      -(Mtd - (2 : ℝ) • effectiveCoriolis Co Cf (Mf t) (J t) (G t) Bd) := by
  have h : Mtd = Mod + Bdᵀ * Mf t * ((J t)⁻¹ * (G t)ᵀ) +
      ((J t)⁻¹ * (G t)ᵀ)ᵀ * Mfd * ((J t)⁻¹ * (G t)ᵀ) + ((J t)⁻¹ * (G t)ᵀ)ᵀ * Mf t * Bd := by
    ext i j
    exact (hMt i j).unique (hasDerivAt_effectiveMass hMo hMf hB i j)
  rw [h]
  exact skew_effectiveMassRate_sub_two_effectiveCoriolis hsymm hso hsf (J t) (G t) Bd

/-- **MLS Lemma 6.1(2), p. 279, with Christoffel Coriolis matrices.** If the inertia fields `M_o(x)`
and `M_f(θ)` are symmetric at every configuration, with Fréchet derivative data at `x(t)` and
`θ(t)`, and `C_o`, `C_f` are their Christoffel Coriolis matrices (MLS eq. (4.23)) at the velocities
`x'`, `θ'` of the motion, then the structural hypotheses of
`skew_deriv_effectiveMass_sub_two_effectiveCoriolis` hold by MLS Lemma 4.2(2) (E013), and
`M̃˙ − 2C̃` is skew-symmetric for every actual derivative `M̃˙` along the motion. -/
theorem skew_deriv_effectiveMass_sub_two_effectiveCoriolis_christoffel
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {J : ℝ → Matrix (Fin n) (Fin n) ℝ} {G : ℝ → Matrix (Fin p) (Fin n) ℝ}
    {x : ℝ → Fin p → ℝ} {θ : ℝ → Fin n → ℝ} {x' : Fin p → ℝ} {θ' : Fin n → ℝ}
    {Bd : Matrix (Fin n) (Fin p) ℝ} {t : ℝ} (hMo_symm : ∀ y, (Mo y).IsSymm)
    (hMf_symm : ∀ y, (Mf y).IsSymm) (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (x t))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (θ t)) (hx : HasDerivAt x x' t)
    (hθ : HasDerivAt θ θ' t)
    (hB : ∀ i j, HasDerivAt (fun s => ((J s)⁻¹ * (G s)ᵀ) i j) (Bd i j) t)
    {Mtd : Matrix (Fin p) (Fin p) ℝ}
    (hMt : ∀ i j, HasDerivAt (fun s => effectiveMass (Mo (x s)) (Mf (θ s)) (J s) (G s) i j)
      (Mtd i j) t) :
    (Mtd - (2 : ℝ) • effectiveCoriolis (Christoffel.coriolisMatrix (Christoffel.partials Mo') x')
        (Christoffel.coriolisMatrix (Christoffel.partials Mf') θ') (Mf (θ t)) (J t) (G t) Bd)ᵀ =
      -(Mtd - (2 : ℝ) • effectiveCoriolis (Christoffel.coriolisMatrix (Christoffel.partials Mo') x')
        (Christoffel.coriolisMatrix (Christoffel.partials Mf') θ') (Mf (θ t)) (J t) (G t) Bd) := by
  have hxk : ∀ k, HasDerivAt (fun s => x s k) (x' k) t := hasDerivAt_pi.mp hx
  have hθk : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t := hasDerivAt_pi.mp hθ
  exact skew_deriv_effectiveMass_sub_two_effectiveCoriolis
    (Christoffel.hasDerivAt_comp hMo hxk) (Christoffel.hasDerivAt_comp hMf hθk) hB
    (hMf_symm (θ t)).eq
    (Christoffel.skew_deriv_sub_two_coriolisMatrix hMo_symm hMo hxk
      (Christoffel.hasDerivAt_comp hMo hxk))
    (Christoffel.skew_deriv_sub_two_coriolisMatrix hMf_symm hMf hθk
      (Christoffel.hasDerivAt_comp hMf hθk)) hMt

/-! ### Workspace dynamics, eq. (6.26) (MLS pp. 282–283) -/

/-- **MLS eq. (6.26), p. 283: with `G = I`, `M̃ = M_o + J⁻ᵀ M_f J⁻¹`.** -/
theorem effectiveMass_one (Mo Mf J : Matrix (Fin n) (Fin n) ℝ) :
    effectiveMass Mo Mf J 1 = Mo + (J⁻¹)ᵀ * Mf * J⁻¹ := by
  simp [effectiveMass]

/-- **MLS eq. (6.26), p. 283: with `G = I`, `C̃ = C_o + J⁻ᵀ (C_f J⁻¹ + M_f (d/dt)(J⁻¹))`.** -/
theorem effectiveCoriolis_one (Co Cf Mf J Bd : Matrix (Fin n) (Fin n) ℝ) :
    effectiveCoriolis Co Cf Mf J 1 Bd = Co + (J⁻¹)ᵀ * (Cf * J⁻¹ + Mf * Bd) := by
  simp [effectiveCoriolis]

/-- **MLS eq. (6.26), p. 283: with `G = I`, `Ñ = N_o + J⁻ᵀ N_f` and `F = J⁻ᵀ τ`.** -/
theorem effectiveN_one_and_effectiveForce_one (No Nf τ : Fin n → ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) :
    effectiveN No Nf J 1 = No + (J⁻¹)ᵀ *ᵥ Nf ∧ effectiveForce J 1 τ = (J⁻¹)ᵀ *ᵥ τ := by
  simp [effectiveN, effectiveForce]

/-- **MLS p. 283, (6.26): "It follows immediately that `M̃ > 0`"**, for `M_f` positive definite,
`M_o` positive semidefinite (possibly `0`: "no object is present") and `J` invertible. -/
theorem effectiveMass_one_posDef {Mo Mf J : Matrix (Fin n) (Fin n) ℝ} (hMo : Mo.PosSemidef)
    (hMf : Mf.PosDef) (hJ : IsUnit J.det) : (effectiveMass Mo Mf J 1).PosDef :=
  effectiveMass_posDef_of_surjective hMo hMf hJ fun v => ⟨v, Matrix.one_mulVec v⟩

/-- **MLS p. 283 with E029 (N42): without an object (`M_o = 0`, `G = I`), `M̃` is the workspace
inertia `J⁻ᵀ M J⁻¹` of MLS eq. (4.55), p. 197**, for a manipulator model `P` and a coordinate map
`f` with Jacobian `J = ∂f/∂θ`. -/
theorem effectiveMass_zero_one_eq_workspaceM {n : ℕ} (P : ManipulatorModel n)
    (f : (Fin n → ℝ) → Fin n → ℝ) (q : Fin n → ℝ) :
    effectiveMass 0 (P.M q) (MapJacobian.jac f q) 1 = P.workspaceM f q := by
  rw [effectiveMass_one, zero_add]
  rfl

/-- **MLS p. 283 with E029 (N42): without an object, `C̃` is the workspace Coriolis matrix of MLS
eq. (4.55), p. 197**, along a motion `θ` with velocity `θ'` at `t`, `f` of class `C²`, `J(θ(t))`
invertible and `X'` the actual derivative of `s ↦ J(θ(s))⁻¹` at `t` (the book's `(d/dt)(J⁻¹)`). -/
theorem effectiveCoriolis_zero_one_eq_workspaceC {n : ℕ} (P : ManipulatorModel n)
    (f : (Fin n → ℝ) → Fin n → ℝ) (hf : ContDiff ℝ 2 f) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : HasDerivAt θ θ' t) (hJ : IsUnit (MapJacobian.jac f (θ t)).det)
    {X' : Matrix (Fin n) (Fin n) ℝ}
    (hX' : ∀ i j, HasDerivAt (fun s => (MapJacobian.jac f (θ s))⁻¹ i j) (X' i j) t) :
    effectiveCoriolis 0 (P.C (θ t) θ') (P.M (θ t)) (MapJacobian.jac f (θ t)) 1 X' =
      P.workspaceC f (θ t) θ' := by
  rw [effectiveCoriolis_one, zero_add, P.workspaceC_eq_printed f hf hθ hJ hX']

/-! ### The composite system: eqs. (6.18)–(6.20) as an instance of (6.9) (MLS pp. 277–278) -/

section CompositeSystem

variable {N : ℕ}

open Constrained

/-- **MLS eq. (6.19), p. 278: the Lagrangian of the composite system,** `L = L_f(θ, θ̇) + L_o(x, ẋ)`
on `q ∈ ℝᴺ` with object coordinates `x = q ∘ e ∘ inl` and finger coordinates `θ = q ∘ e ∘ inr`; with
`L_f = ½ θ̇ᵀ M_f θ̇ − V_f` and `L_o = ½ ẋᵀ M_o ẋ − V_o` it is (6.19)
(`lagrangian_mechanical_apply`). -/
def lagrangian (e : Fin p ⊕ Fin n ≃ Fin N) (Lo : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (Lf : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
  fun q v => Lf (splitSnd e q) (splitSnd e v) + Lo (splitFst e q) (splitFst e v)

/-- **MLS eq. (6.19), p. 278:** `L = ½ θ̇ᵀ M_f θ̇ + ½ ẋᵀ M_o ẋ − V_f(θ) − V_o(x)` for mechanical
finger and object Lagrangians. -/
theorem lagrangian_mechanical_apply (e : Fin p ⊕ Fin n ≃ Fin N)
    (Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ) (Vo : (Fin p → ℝ) → ℝ)
    (Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (Vf : (Fin n → ℝ) → ℝ) (q v : Fin N → ℝ) :
    lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf) q v =
      1 / 2 * (splitSnd e v ⬝ᵥ (Mf (splitSnd e q) *ᵥ splitSnd e v)) +
        1 / 2 * (splitFst e v ⬝ᵥ (Mo (splitFst e q) *ᵥ splitFst e v)) - Vf (splitSnd e q) -
          Vo (splitFst e q) := by
  simp only [lagrangian, Lagrangian.mechanical]
  ring

/-- **MLS eq. (6.18), p. 277, as a Pfaffian constraint (MLS p. 267): `A(q) = [J_h(q) −Gᵀ(q)]`,**
with the columns of `q` relabeled by `e` (the `θ` columns carry `J_h`, the `x` columns `−Gᵀ`). -/
def handPfaffian (e : Fin p ⊕ Fin n ≃ Fin N) (Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ) : (Fin N → ℝ) → Matrix (Fin n) (Fin N) ℝ :=
  fun q => Matrix.of fun i j => Sum.elim (fun a => -(G q)ᵀ i a) (fun b => Jh q i b) (e.symm j)

/-- **MLS p. 267: the `x` block of `A = [J_h −Gᵀ]` is `−Gᵀ`.** -/
@[simp] theorem colsFst_handPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ)
    (q : Fin N → ℝ) : colsFst (handPfaffian e Jh G q) e = -(G q)ᵀ := by
  ext i a
  simp [colsFst, handPfaffian]

/-- **MLS p. 267: the `θ` block of `A = [J_h −Gᵀ]` is `J_h`.** -/
@[simp] theorem colsSnd_handPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ)
    (q : Fin N → ℝ) : colsSnd (handPfaffian e Jh G q) e = Jh q := by
  ext i b
  simp [colsSnd, handPfaffian]

/-- **MLS eq. (6.18), p. 277: the Pfaffian constraint `[J_h −Gᵀ] q̇ = 0` is the grasp constraint
`J_h θ̇ = Gᵀ ẋ`.** -/
theorem pfaffianAt_handPfaffian_iff (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ)
    (q v : Fin N → ℝ) :
    PfaffianAt (handPfaffian e Jh G) q v ↔ Jh q *ᵥ splitSnd e v = (G q)ᵀ *ᵥ splitFst e v := by
  unfold PfaffianAt
  rw [mulVec_split _ e, colsFst_handPfaffian, colsSnd_handPfaffian, Matrix.neg_mulVec,
    neg_add_eq_sub, sub_eq_zero]

/-- **MLS pp. 267, 277: with `J_h` invertible the constraint `[J_h −Gᵀ]` has independent rows** ("we
assume that the constraints are pointwise linearly independent"; here it follows from assumption 2
of p. 277). -/
theorem linearIndependent_row_handPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    (Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ) (G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ)
    {q : Fin N → ℝ} (hJ : IsUnit (Jh q).det) : LinearIndependent ℝ (handPfaffian e Jh G q).row := by
  refine linearIndependent_row_of_isUnit_det (e ∘ Sum.inr) ?_
  have h := colsSnd_handPfaffian e Jh G q
  unfold colsSnd at h
  rwa [h]

/-- **MLS's ordering `q = (θ, x)` (p. 267):** the relabeling `Fin p ⊕ Fin n ≃ Fin (n + p)` that puts
the `n` finger coordinates first and the `p` object coordinates last. -/
def mlsSplit (p n : ℕ) : Fin p ⊕ Fin n ≃ Fin (n + p) :=
  (Equiv.sumComm (Fin p) (Fin n)).trans finSumFinEquiv

/-- **MLS p. 267, `A(q) = [J_h(q) −Gᵀ(q)]` in the ordering `q = (θ, x)`:** the first `n` columns are
`J_h`, the last `p` columns are `−Gᵀ`. -/
theorem handPfaffian_mlsSplit_apply (Jh : (Fin (n + p) → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (G : (Fin (n + p) → ℝ) → Matrix (Fin p) (Fin n) ℝ) (q : Fin (n + p) → ℝ) (i b : Fin n)
    (a : Fin p) :
    handPfaffian (mlsSplit p n) Jh G q i (Fin.castAdd p b) = Jh q i b ∧
      handPfaffian (mlsSplit p n) Jh G q i (Fin.natAdd n a) = -(G q)ᵀ i a := by
  have h1 : (mlsSplit p n).symm (Fin.castAdd p b) = Sum.inr b := by
    rw [Equiv.symm_apply_eq]
    rfl
  have h2 : (mlsSplit p n).symm (Fin.natAdd n a) = Sum.inl a := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp [handPfaffian, h1, h2]

/-- **MLS p. 278: the generalized force `(τ, 0)` of the composite system:** joint torques `τ` on the
finger coordinates, no applied force on the object coordinates. -/
def handForce (e : Fin p ⊕ Fin n ≃ Fin N) (τ : Fin n → ℝ) : Fin N → ℝ :=
  splitJoin e 0 τ

private theorem splitFst_sub (e : Fin p ⊕ Fin n ≃ Fin N) (a b : Fin N → ℝ) :
    splitFst e (a - b) = splitFst e a - splitFst e b := rfl

private theorem splitSnd_sub (e : Fin p ⊕ Fin n ≃ Fin N) (a b : Fin N → ℝ) :
    splitSnd e (a - b) = splitSnd e a - splitSnd e b := rfl

private theorem splitFst_transpose_mulVec (e : Fin p ⊕ Fin n ≃ Fin N)
    (A : Matrix (Fin n) (Fin N) ℝ) (μ : Fin n → ℝ) :
    splitFst e (Aᵀ *ᵥ μ) = (colsFst A e)ᵀ *ᵥ μ := rfl

private theorem splitSnd_transpose_mulVec (e : Fin p ⊕ Fin n ≃ Fin N)
    (A : Matrix (Fin n) (Fin N) ℝ) (μ : Fin n → ℝ) :
    splitSnd e (Aᵀ *ᵥ μ) = (colsSnd A e)ᵀ *ᵥ μ := rfl

private theorem splitFst_add_smul_single_inl (e : Fin p ⊕ Fin n ≃ Fin N) (v : Fin N → ℝ)
    (s : ℝ) (a : Fin p) :
    splitFst e (v + s • Pi.single (e (Sum.inl a)) 1) = splitFst e v + s • Pi.single a 1 := by
  funext a'
  by_cases h : a' = a
  · subst h
    simp [splitFst]
  · simp [splitFst, h]

private theorem splitSnd_add_smul_single_inl (e : Fin p ⊕ Fin n ≃ Fin N) (v : Fin N → ℝ)
    (s : ℝ) (a : Fin p) : splitSnd e (v + s • Pi.single (e (Sum.inl a)) 1) = splitSnd e v := by
  funext b
  simp [splitSnd]

private theorem splitFst_add_smul_single_inr (e : Fin p ⊕ Fin n ≃ Fin N) (v : Fin N → ℝ)
    (s : ℝ) (b : Fin n) : splitFst e (v + s • Pi.single (e (Sum.inr b)) 1) = splitFst e v := by
  funext a
  simp [splitFst]

private theorem splitSnd_add_smul_single_inr (e : Fin p ⊕ Fin n ≃ Fin N) (v : Fin N → ℝ)
    (s : ℝ) (b : Fin n) :
    splitSnd e (v + s • Pi.single (e (Sum.inr b)) 1) = splitSnd e v + s • Pi.single b 1 := by
  funext b'
  by_cases h : b' = b
  · subst h
    simp [splitSnd]
  · simp [splitSnd, h]

/-- **MLS p. 278: "the Lagrangian for the system splits into two separate parts".** The partial
derivative `∂L/∂ẋₐ` of the composite Lagrangian is the object's. -/
theorem velocityPartial_lagrangian_inl (e : Fin p ⊕ Fin n ≃ Fin N)
    (Lo : (Fin p → ℝ) → (Fin p → ℝ) → ℝ) (Lf : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (q v : Fin N → ℝ) (a : Fin p) :
    Lagrangian.velocityPartial (lagrangian e Lo Lf) q v (e (Sum.inl a)) =
      Lagrangian.velocityPartial Lo (splitFst e q) (splitFst e v) a := by
  unfold Lagrangian.velocityPartial lagrangian
  simp only [splitFst_add_smul_single_inl, splitSnd_add_smul_single_inl]
  exact deriv_const_add _

/-- **MLS p. 278:** the partial derivative `∂L/∂xₐ` of the composite Lagrangian is the object's. -/
theorem positionPartial_lagrangian_inl (e : Fin p ⊕ Fin n ≃ Fin N)
    (Lo : (Fin p → ℝ) → (Fin p → ℝ) → ℝ) (Lf : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (q v : Fin N → ℝ) (a : Fin p) :
    Lagrangian.positionPartial (lagrangian e Lo Lf) q v (e (Sum.inl a)) =
      Lagrangian.positionPartial Lo (splitFst e q) (splitFst e v) a := by
  unfold Lagrangian.positionPartial lagrangian
  simp only [splitFst_add_smul_single_inl, splitSnd_add_smul_single_inl]
  exact deriv_const_add _

/-- **MLS p. 278:** the partial derivative `∂L/∂θ̇_b` of the composite Lagrangian is the fingers'.
-/
theorem velocityPartial_lagrangian_inr (e : Fin p ⊕ Fin n ≃ Fin N)
    (Lo : (Fin p → ℝ) → (Fin p → ℝ) → ℝ) (Lf : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (q v : Fin N → ℝ) (b : Fin n) :
    Lagrangian.velocityPartial (lagrangian e Lo Lf) q v (e (Sum.inr b)) =
      Lagrangian.velocityPartial Lf (splitSnd e q) (splitSnd e v) b := by
  unfold Lagrangian.velocityPartial lagrangian
  simp only [splitFst_add_smul_single_inr, splitSnd_add_smul_single_inr]
  exact deriv_add_const _

/-- **MLS p. 278:** the partial derivative `∂L/∂θ_b` of the composite Lagrangian is the fingers'. -/
theorem positionPartial_lagrangian_inr (e : Fin p ⊕ Fin n ≃ Fin N)
    (Lo : (Fin p → ℝ) → (Fin p → ℝ) → ℝ) (Lf : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (q v : Fin N → ℝ) (b : Fin n) :
    Lagrangian.positionPartial (lagrangian e Lo Lf) q v (e (Sum.inr b)) =
      Lagrangian.positionPartial Lf (splitSnd e q) (splitSnd e v) b := by
  unfold Lagrangian.positionPartial lagrangian
  simp only [splitFst_add_smul_single_inr, splitSnd_add_smul_single_inr]
  exact deriv_add_const _

private theorem hasDerivAt_splitFst (e : Fin p ⊕ Fin n ≃ Fin N) {q : ℝ → Fin N → ℝ}
    {q' : Fin N → ℝ} {s : ℝ} (h : HasDerivAt q q' s) :
    HasDerivAt (fun s => splitFst e (q s)) (splitFst e q') s :=
  hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mp h (e (Sum.inl a))

private theorem hasDerivAt_splitSnd (e : Fin p ⊕ Fin n ≃ Fin N) {q : ℝ → Fin N → ℝ}
    {q' : Fin N → ℝ} {s : ℝ} (h : HasDerivAt q q' s) :
    HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e q') s :=
  hasDerivAt_pi.mpr fun b => hasDerivAt_pi.mp h (e (Sum.inr b))

/-- **MLS p. 278, "the two terms ... simplify into the object dynamics and the finger dynamics":**
along a motion `q` with velocity `q'` near `t`, the composite Lagrangian (6.19) satisfies Lagrange's
equations with a generalized force `R` exactly when the object Lagrangian does along
`x = q ∘ e ∘ inl` with the force `R ∘ e ∘ inl` and the finger Lagrangian does along
`θ = q ∘ e ∘ inr` with the force `R ∘ e ∘ inr`. -/
theorem lagrangeEquationsAt_lagrangian_iff (e : Fin p ⊕ Fin n ≃ Fin N)
    (Lo : (Fin p → ℝ) → (Fin p → ℝ) → ℝ) (Lf : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    {q q' : ℝ → Fin N → ℝ} {t : ℝ} (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s) (R : Fin N → ℝ) :
    Lagrangian.LagrangeEquationsAt (lagrangian e Lo Lf) q R t ↔
      Lagrangian.LagrangeEquationsAt Lo (fun s => splitFst e (q s)) (splitFst e R) t ∧
        Lagrangian.LagrangeEquationsAt Lf (fun s => splitSnd e (q s)) (splitSnd e R) t := by
  have hFst : ∀ᶠ s in 𝓝 t, deriv (fun s => splitFst e (q s)) s = splitFst e (deriv q s) := by
    filter_upwards [hq] with s hs
    rw [hs.deriv]
    exact (hasDerivAt_splitFst e hs).deriv
  have hSnd : ∀ᶠ s in 𝓝 t, deriv (fun s => splitSnd e (q s)) s = splitSnd e (deriv q s) := by
    filter_upwards [hq] with s hs
    rw [hs.deriv]
    exact (hasDerivAt_splitSnd e hs).deriv
  unfold Lagrangian.LagrangeEquationsAt
  rw [← e.forall_congr_right, Sum.forall]
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun b => ?_)
  · simp only [velocityPartial_lagrangian_inl, positionPartial_lagrangian_inl]
    rw [hFst.self_of_nhds]
    refine Filter.EventuallyEq.hasDerivAt_iff ?_
    filter_upwards [hFst] with s hs
    rw [hs]
  · simp only [velocityPartial_lagrangian_inr, positionPartial_lagrangian_inr]
    rw [hSnd.self_of_nhds]
    refine Filter.EventuallyEq.hasDerivAt_iff ?_
    filter_upwards [hSnd] with s hs
    rw [hs]

/-- **MLS eq. (6.20), p. 278, as the instance of (6.9) with `q₁ = x`, `q₂ = θ`, `A₁ = −Gᵀ`,
`A₂ = J_h`.** For mechanical finger and object Lagrangians (6.19) with symmetric inertia fields and
Fréchet derivative data at `θ(t)`, `x(t)`, along a motion `q` with velocity `q'` near `t` and
acceleration `q''` at `t`, and with `J_h(q(t))` invertible, the Lagrange–d'Alembert equations with
the constraint `[J_h −Gᵀ]` and the force `(τ, 0)` hold at `t` exactly when
`(M_o ẍ + C_o ẋ + ∂V_o/∂x) + G J_h⁻ᵀ (M_f θ̈ + C_f θ̇ + ∂V_f/∂θ) = G J_h⁻ᵀ τ`, i.e.
`(d/dt ∂L/∂ẋ − ∂L/∂x) + G J_h⁻ᵀ (d/dt ∂L/∂θ̇ − ∂L/∂θ) = G J_h⁻ᵀ τ`, with `C_o`, `C_f` the
Christoffel Coriolis matrices (MLS eq. (4.23)). Equation (6.20) has `p` rows (MLS p. 278 says
`n − m`). -/
theorem lagrangeDAlembertAt_handPfaffian_iff (e : Fin p ⊕ Fin n ≃ Fin N)
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Vo : (Fin p → ℝ) → ℝ} {Vo' : (Fin p → ℝ) →L[ℝ] ℝ}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {Vf : (Fin n → ℝ) → ℝ} {Vf' : (Fin n → ℝ) →L[ℝ] ℝ}
    {Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ} {G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ}
    {q q' : ℝ → Fin N → ℝ} {q'' : Fin N → ℝ} {t : ℝ} (hMo_symm : ∀ y, (Mo y).IsSymm)
    (hMf_symm : ∀ y, (Mf y).IsSymm)
    (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (splitFst e (q t)))
    (hVo : HasFDerivAt Vo Vo' (splitFst e (q t)))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (splitSnd e (q t)))
    (hVf : HasFDerivAt Vf Vf' (splitSnd e (q t))) (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t) (hJ : IsUnit (Jh (q t)).det) (τ : Fin n → ℝ) :
    LagrangeDAlembertAt (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf))
        (handPfaffian e Jh G) q (handForce e τ) t ↔
      (Mo (splitFst e (q t)) *ᵥ splitFst e q'' +
          Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)) *ᵥ
            splitFst e (q' t) + Lagrangian.gradient Vo') +
        (G (q t) * ((Jh (q t))⁻¹)ᵀ) *ᵥ
          (Mf (splitSnd e (q t)) *ᵥ splitSnd e q'' +
            Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)) *ᵥ
              splitSnd e (q' t) + Lagrangian.gradient Vf') =
        (G (q t) * ((Jh (q t))⁻¹)ᵀ) *ᵥ τ := by
  set Ro := Mo (splitFst e (q t)) *ᵥ splitFst e q'' +
    Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)) *ᵥ
      splitFst e (q' t) + Lagrangian.gradient Vo'
  set Rf := Mf (splitSnd e (q t)) *ᵥ splitSnd e q'' +
    Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)) *ᵥ
      splitSnd e (q' t) + Lagrangian.gradient Vf'
  have hxq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitFst e (q s)) (splitFst e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitFst e hs
  have hθq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitSnd e hs
  have hRo := lagrangeEquationsAt_mechanical_inertial hMo_symm hMo hVo hxq
    (hasDerivAt_splitFst e hq')
  have hRf := lagrangeEquationsAt_mechanical_inertial hMf_symm hMf hVf hθq
    (hasDerivAt_splitSnd e hq')
  have hR : Lagrangian.LagrangeEquationsAt
      (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf)) q
      (splitJoin e Ro Rf) t :=
    (lagrangeEquationsAt_lagrangian_iff e _ _ hq _).mpr
      ⟨by rwa [splitFst_splitJoin], by rwa [splitSnd_splitJoin]⟩
  have hJ' : IsUnit (colsSnd (handPfaffian e Jh G (q t)) e).det := by
    rwa [colsSnd_handPfaffian]
  rw [lagrangeDAlembertAt_iff_of_lagrangeEquationsAt hR, doesNoVirtualWork_iff_split hJ',
    splitFst_sub, splitSnd_sub, splitFst_splitJoin, splitSnd_splitJoin, handForce,
    splitFst_splitJoin, splitSnd_splitJoin, colsFst_handPfaffian, colsSnd_handPfaffian,
    Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.neg_mul, Matrix.neg_mulVec, sub_zero,
    sub_neg_eq_add, Matrix.mulVec_sub, ← add_sub_assoc, sub_eq_zero]

/-- **MLS p. 278: "eliminating `θ̇` and `θ̈` via the constraints".** Along a motion on which the
grasp constraint `J_h(s) θ'(s) = G(s)ᵀ x'(s)` holds and `J_h(s)` is invertible for `s` near `t`, and
the entries of `s ↦ J_h(s)⁻¹ G(s)ᵀ` have the derivatives `Bd` at `t`: if `θ'`, `x'` have the
derivatives `θ''`, `x''` at `t`, then `θ'(t) = J_h⁻¹ Gᵀ x'(t)` and `θ'' = J_h⁻¹ Gᵀ x'' + Bd x'(t)`
(the book's `(d/dt)(J_h⁻¹ Gᵀ)` is `Bd`). -/
theorem velocity_acceleration_eq {J : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G : ℝ → Matrix (Fin p) (Fin n) ℝ} {θ' : ℝ → Fin n → ℝ} {x' : ℝ → Fin p → ℝ}
    {θ'' : Fin n → ℝ} {x'' : Fin p → ℝ} {Bd : Matrix (Fin n) (Fin p) ℝ} {t : ℝ}
    (hc : ∀ᶠ s in 𝓝 t, J s *ᵥ θ' s = (G s)ᵀ *ᵥ x' s) (hJ : ∀ᶠ s in 𝓝 t, IsUnit (J s).det)
    (hB : ∀ i j, HasDerivAt (fun s => ((J s)⁻¹ * (G s)ᵀ) i j) (Bd i j) t)
    (hθ' : HasDerivAt θ' θ'' t) (hx' : HasDerivAt x' x'' t) :
    θ' t = ((J t)⁻¹ * (G t)ᵀ) *ᵥ x' t ∧ θ'' = ((J t)⁻¹ * (G t)ᵀ) *ᵥ x'' + Bd *ᵥ x' t := by
  have hev : ∀ᶠ s in 𝓝 t, θ' s = ((J s)⁻¹ * (G s)ᵀ) *ᵥ x' s := by
    filter_upwards [hc, hJ] with s h1 h2
    rw [← Matrix.mulVec_mulVec, ← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h2,
      Matrix.one_mulVec]
  refine ⟨hev.self_of_nhds, ?_⟩
  have h1 := (hasDerivAt_matrix_mulVec_rect hB hx').congr_of_eventuallyEq hev
  rw [hθ'.unique h1, add_comm]

/-- **MLS eqs. (6.21)–(6.22), p. 278: the equations of motion of the hand–object system,**
`M̃ ẍ + C̃ ẋ + Ñ = F`. Under the hypotheses of `lagrangeDAlembertAt_handPfaffian_iff`, with the
grasp constraint (6.18) on a neighborhood of `t`, `J_h(q(s))` invertible near `t` and `Bd` the
derivative of `s ↦ J_h(q(s))⁻¹ G(q(s))ᵀ` at `t`, the Lagrange–d'Alembert equations hold at `t`
exactly when (6.21) holds with `M̃`, `C̃`, `Ñ`, `F` of (6.22) (`C_o`, `C_f` the Christoffel Coriolis
matrices, `N_o = ∂V_o/∂x`, `N_f = ∂V_f/∂θ`). -/
theorem lagrangeDAlembertAt_handPfaffian_iff_effective (e : Fin p ⊕ Fin n ≃ Fin N)
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Vo : (Fin p → ℝ) → ℝ} {Vo' : (Fin p → ℝ) →L[ℝ] ℝ}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {Vf : (Fin n → ℝ) → ℝ} {Vf' : (Fin n → ℝ) →L[ℝ] ℝ}
    {Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ} {G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ}
    {q q' : ℝ → Fin N → ℝ} {q'' : Fin N → ℝ} {Bd : Matrix (Fin n) (Fin p) ℝ} {t : ℝ}
    (hMo_symm : ∀ y, (Mo y).IsSymm) (hMf_symm : ∀ y, (Mf y).IsSymm)
    (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (splitFst e (q t)))
    (hVo : HasFDerivAt Vo Vo' (splitFst e (q t)))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (splitSnd e (q t)))
    (hVf : HasFDerivAt Vf Vf' (splitSnd e (q t))) (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t)
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt (handPfaffian e Jh G) (q s) (q' s))
    (hJ : ∀ᶠ s in 𝓝 t, IsUnit (Jh (q s)).det)
    (hB : ∀ i j, HasDerivAt (fun s => ((Jh (q s))⁻¹ * (G (q s))ᵀ) i j) (Bd i j) t)
    (τ : Fin n → ℝ) :
    LagrangeDAlembertAt (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf))
        (handPfaffian e Jh G) q (handForce e τ) t ↔
      effectiveMass (Mo (splitFst e (q t))) (Mf (splitSnd e (q t))) (Jh (q t)) (G (q t)) *ᵥ
            splitFst e q'' +
          effectiveCoriolis
              (Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)))
              (Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)))
              (Mf (splitSnd e (q t))) (Jh (q t)) (G (q t)) Bd *ᵥ splitFst e (q' t) +
          effectiveN (Lagrangian.gradient Vo') (Lagrangian.gradient Vf') (Jh (q t)) (G (q t)) =
        effectiveForce (Jh (q t)) (G (q t)) τ := by
  have hc' : ∀ᶠ s in 𝓝 t, Jh (q s) *ᵥ splitSnd e (q' s) = (G (q s))ᵀ *ᵥ splitFst e (q' s) := by
    filter_upwards [hc] with s hs
    exact (pfaffianAt_handPfaffian_iff e Jh G _ _).mp hs
  obtain ⟨hv, ha⟩ := velocity_acceleration_eq hc' hJ hB (hasDerivAt_splitSnd e hq')
    (hasDerivAt_splitFst e hq')
  rw [lagrangeDAlembertAt_handPfaffian_iff e hMo_symm hMf_symm hMo hVo hMf hVf hq hq'
    hJ.self_of_nhds, effective_dynamics_eq _ _ _ _ _ _ _ _ _ hv ha, effectiveForce]

/-- **MLS eq. (6.24), p. 280: the full equations of motion of the hand with multipliers,** in the
sign convention `A = [J_h −Gᵀ]` of p. 267: (6.4) holds at `t` with multipliers `λ ∈ ℝⁿ` exactly when
`M_f θ̈ + C_f θ̇ + N_f + J_hᵀ λ = τ` and `M_o ẍ + C_o ẋ + N_o − G λ = 0`. MLS p. 280 prints
`A = [−J_h Gᵀ]` and `+ [−J_hᵀ ; G] λ`, the same equations with `−λ` (E034 source observation).
Hypotheses as in `lagrangeDAlembertAt_handPfaffian_iff`, without invertibility of `J_h`. -/
theorem multiplierEquationsAt_handPfaffian_iff (e : Fin p ⊕ Fin n ≃ Fin N)
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Vo : (Fin p → ℝ) → ℝ} {Vo' : (Fin p → ℝ) →L[ℝ] ℝ}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {Vf : (Fin n → ℝ) → ℝ} {Vf' : (Fin n → ℝ) →L[ℝ] ℝ}
    {Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ} {G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ}
    {q q' : ℝ → Fin N → ℝ} {q'' : Fin N → ℝ} {t : ℝ} (hMo_symm : ∀ y, (Mo y).IsSymm)
    (hMf_symm : ∀ y, (Mf y).IsSymm)
    (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (splitFst e (q t)))
    (hVo : HasFDerivAt Vo Vo' (splitFst e (q t)))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (splitSnd e (q t)))
    (hVf : HasFDerivAt Vf Vf' (splitSnd e (q t))) (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t) (τ μ : Fin n → ℝ) :
    MultiplierEquationsAt (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf))
        (handPfaffian e Jh G) q (handForce e τ) μ t ↔
      Mf (splitSnd e (q t)) *ᵥ splitSnd e q'' +
          Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t)) *ᵥ
            splitSnd e (q' t) + Lagrangian.gradient Vf' + (Jh (q t))ᵀ *ᵥ μ = τ ∧
        Mo (splitFst e (q t)) *ᵥ splitFst e q'' +
          Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)) *ᵥ
            splitFst e (q' t) + Lagrangian.gradient Vo' - G (q t) *ᵥ μ = 0 := by
  have hxq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitFst e (q s)) (splitFst e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitFst e hs
  have hθq : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => splitSnd e (q s)) (splitSnd e (q' s)) s := by
    filter_upwards [hq] with s hs
    exact hasDerivAt_splitSnd e hs
  unfold MultiplierEquationsAt
  rw [lagrangeEquationsAt_lagrangian_iff e _ _ hq,
    Lagrangian.lagrangeEquationsAt_mechanical_iff hMo_symm hMo hVo hxq (hasDerivAt_splitFst e hq'),
    Lagrangian.lagrangeEquationsAt_mechanical_iff hMf_symm hMf hVf hθq (hasDerivAt_splitSnd e hq'),
    splitFst_sub, splitSnd_sub, splitFst_transpose_mulVec, splitSnd_transpose_mulVec,
    colsFst_handPfaffian, colsSnd_handPfaffian, handForce, splitFst_splitJoin, splitSnd_splitJoin,
    Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.neg_mulVec, zero_sub, neg_neg,
    and_comm, sub_eq_zero, eq_sub_iff_add_eq]

end CompositeSystem

/-! ### Hybrid position/force dynamics, eqs. (6.27)–(6.28) (MLS p. 284) -/

/-- **MLS eq. (6.28), p. 284: "Equation (6.27) can be converted into the standard problem by
differentiating with respect to time",** `(∂h/∂θ) θ̇ = −(∂h/∂x) ẋ`. For a holonomic constraint
`h(θ, x) = 0` on `q ∈ ℝᴺ` (relabeled by `e`, `h` with `n` components) that holds near `t`, with `h`
differentiable at `q(t)` and the motion with velocity `q'` at `t`. The blocks `∂h/∂θ`, `∂h/∂x` are
the columns of `MapJacobian.jac h` for `θ` and `x`. -/
theorem hybrid_constraint {N : ℕ} (e : Fin p ⊕ Fin n ≃ Fin N) {h : (Fin N → ℝ) → Fin n → ℝ}
    {q : ℝ → Fin N → ℝ} {q' : Fin N → ℝ} {t : ℝ} (hh : DifferentiableAt ℝ h (q t))
    (hq : HasDerivAt q q' t) (hc : ∀ᶠ s in 𝓝 t, h (q s) = 0) :
    Constrained.colsSnd (MapJacobian.jac h (q t)) e *ᵥ Constrained.splitSnd e q' =
      -Constrained.colsFst (MapJacobian.jac h (q t)) e *ᵥ Constrained.splitFst e q' := by
  have h0 := Constrained.jac_mulVec_eq_zero_of_eventually hh hq hc
  rw [Constrained.mulVec_split _ e] at h0
  rw [Matrix.neg_mulVec]
  exact eq_neg_of_add_eq_zero_right h0

/-- **MLS eq. (6.28), p. 284: with `J = ∂h/∂θ` and `Gᵀ = −∂h/∂x` the hybrid constraint has the form
of the grasp constraint (6.18),** `[J −Gᵀ] q̇ = 0`; the dynamics of p. 284 are then (6.21)–(6.22)
with `M_o = 0` (`effectiveMass 0`), positive definite when `G` is onto
(`effectiveMass_posDef_of_surjective`), and the internal forces are the torques with `G J⁻ᵀ τ = 0`
(`effectiveForce_eq_zero_iff`). -/
theorem pfaffianAt_jac_iff_handPfaffian {N : ℕ} (e : Fin p ⊕ Fin n ≃ Fin N)
    (h : (Fin N → ℝ) → Fin n → ℝ) (q v : Fin N → ℝ) :
    Constrained.PfaffianAt (MapJacobian.jac h) q v ↔
      Constrained.PfaffianAt (handPfaffian e (fun y => Constrained.colsSnd (MapJacobian.jac h y) e)
        (fun y => -(Constrained.colsFst (MapJacobian.jac h y) e)ᵀ)) q v := by
  rw [pfaffianAt_handPfaffian_iff]
  unfold Constrained.PfaffianAt
  rw [Constrained.mulVec_split _ e, Matrix.transpose_neg, Matrix.transpose_transpose,
    Matrix.neg_mulVec, add_comm, add_eq_zero_iff_eq_neg]

/-! ### The contact forces (MLS §2.2, p. 280) -/

/-- **MLS p. 280: "If `J_h` is invertible, the contact forces satisfy
`λ = J_h⁻ᵀ (τ − M_f θ̈ − C_f θ̇ − N_f)`"**, from the finger rows of (6.24) in the sign convention
`A = [J_h −Gᵀ]` (`multiplierEquationsAt_handPfaffian_iff`). -/
theorem contactForce_eq {J Mf Cf : Matrix (Fin n) (Fin n) ℝ} (hJ : IsUnit J.det)
    {θ' θ'' Nf τ μ : Fin n → ℝ} (h : Mf *ᵥ θ'' + Cf *ᵥ θ' + Nf + Jᵀ *ᵥ μ = τ) :
    μ = (J⁻¹)ᵀ *ᵥ (τ - Mf *ᵥ θ'' - Cf *ᵥ θ' - Nf) := by
  have h' : Jᵀ *ᵥ μ = τ - Mf *ᵥ θ'' - Cf *ᵥ θ' - Nf := by
    rw [← h]
    abel
  rw [← h', Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ,
    Matrix.transpose_one, Matrix.one_mulVec]

/-- **MLS p. 280: "`λ = f_c := J_h⁻ᵀ τ` only when the system is at rest"**, in the precise form that
holds: given the finger rows of (6.24) with `J_h` invertible, `λ = J_h⁻ᵀ τ` exactly when
`M_f θ̈ + C_f θ̇ + N_f = 0` (at rest, `θ̇ = θ̈ = 0`, this is `N_f(θ, 0) = 0`, for example without
finger gravity). -/
theorem contactForce_eq_iff {J Mf Cf : Matrix (Fin n) (Fin n) ℝ} (hJ : IsUnit J.det)
    {θ' θ'' Nf τ μ : Fin n → ℝ} (h : Mf *ᵥ θ'' + Cf *ᵥ θ' + Nf + Jᵀ *ᵥ μ = τ) :
    μ = (J⁻¹)ᵀ *ᵥ τ ↔ Mf *ᵥ θ'' + Cf *ᵥ θ' + Nf = 0 := by
  rw [contactForce_eq hJ h]
  have hinj : Function.Injective ((J⁻¹)ᵀ *ᵥ ·) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_transpose _).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det J hJ)))
  rw [hinj.eq_iff]
  constructor
  · intro h2
    rwa [sub_sub, sub_sub, sub_eq_self, ← add_assoc] at h2
  · intro h2
    rw [sub_sub, sub_sub, ← add_assoc, h2, sub_zero]

/-- **MLS p. 280: "If `J_h⁻ᵀ τ ∈ N(G)`, then no net wrench is generated":** the object force
`F = G J_h⁻ᵀ τ` of (6.22) vanishes exactly when `J_h⁻ᵀ τ` is in the null space of `G`. -/
theorem effectiveForce_eq_zero_iff (J : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin p) (Fin n) ℝ)
    (τ : Fin n → ℝ) : effectiveForce J G τ = 0 ↔ G *ᵥ ((J⁻¹)ᵀ *ᵥ τ) = 0 := by
  rw [effectiveForce, Matrix.mulVec_mulVec]

/-! ### The multipliers from (6.6): eq. (6.25) (MLS p. 280) -/

section Multipliers

variable {N : ℕ}

open Constrained

/-- **MLS p. 272: `q = (q₁, q₂)`**, every vector is assembled from its two relabeled parts. -/
theorem splitJoin_splitFst_splitSnd (e : Fin p ⊕ Fin n ≃ Fin N) (v : Fin N → ℝ) :
    splitJoin e (splitFst e v) (splitSnd e v) = v := by
  funext j
  obtain ⟨s, rfl⟩ := e.surjective j
  rcases s with a | b <;> simp [splitJoin, splitFst, splitSnd]

private theorem splitFst_add (e : Fin p ⊕ Fin n ≃ Fin N) (a b : Fin N → ℝ) :
    splitFst e (a + b) = splitFst e a + splitFst e b := rfl

private theorem splitSnd_add (e : Fin p ⊕ Fin n ≃ Fin N) (a b : Fin N → ℝ) :
    splitSnd e (a + b) = splitSnd e a + splitSnd e b := rfl

/-- **MLS eq. (6.24), p. 280: the block matrices `M̄ = diag(M_f, M_o)` and `C̄ = diag(C_f, C_o)`**
in the relabeled coordinates `q = (x, θ)` of `e` (object block `Mo`, finger block `Mf`). -/
def blockMatrix (e : Fin p ⊕ Fin n ≃ Fin N) (Mo : Matrix (Fin p) (Fin p) ℝ)
    (Mf : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (Matrix.fromBlocks Mo 0 0 Mf).submatrix e.symm e.symm

/-- **MLS eq. (6.24), p. 280: `M̄ q̈ = (M_f θ̈, M_o ẍ)`** in the relabeled coordinates. -/
theorem blockMatrix_mulVec (e : Fin p ⊕ Fin n ≃ Fin N) (Mo : Matrix (Fin p) (Fin p) ℝ)
    (Mf : Matrix (Fin n) (Fin n) ℝ) (v : Fin N → ℝ) :
    blockMatrix e Mo Mf *ᵥ v = splitJoin e (Mo *ᵥ splitFst e v) (Mf *ᵥ splitSnd e v) := by
  rw [blockMatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, Matrix.fromBlocks_mulVec]
  funext j
  simp [splitJoin, Function.comp_def]
  rfl

/-- **MLS p. 280: the block inertia `M̄ = diag(M_f, M_o)` is positive definite** when `M_f` and
`M_o` are (MLS Lemma 4.2(1) and p. 277). -/
theorem blockMatrix_posDef (e : Fin p ⊕ Fin n ≃ Fin N) {Mo : Matrix (Fin p) (Fin p) ℝ}
    {Mf : Matrix (Fin n) (Fin n) ℝ} (hMo : Mo.PosDef) (hMf : Mf.PosDef) :
    (blockMatrix e Mo Mf).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(Matrix.IsHermitian.fromBlocks hMo.isHermitian (by simp) hMf.isHermitian).submatrix _,
    fun x hx => ?_⟩
  have hsplit : x = splitJoin e (splitFst e x) (splitSnd e x) :=
    (splitJoin_splitFst_splitSnd e x).symm
  have q1 := hMo.posSemidef.dotProduct_mulVec_nonneg (splitFst e x)
  have q2 := hMf.posSemidef.dotProduct_mulVec_nonneg (splitSnd e x)
  simp only [star_trivial] at q1 q2 ⊢
  rw [blockMatrix_mulVec, dotProduct_split e, splitFst_splitJoin, splitSnd_splitJoin]
  by_cases h1 : splitFst e x = 0
  · have h2 : splitSnd e x ≠ 0 := by
      intro h2
      apply hx
      rw [hsplit, h1, h2]
      funext j
      simp only [splitJoin, Pi.zero_apply]
      rcases e.symm j with a | b <;> rfl
    have := hMf.dotProduct_mulVec_pos h2
    simp only [star_trivial] at this
    linarith
  · have := hMo.dotProduct_mulVec_pos h1
    simp only [star_trivial] at this
    linarith

/-- **MLS eq. (6.25), p. 280: the hand multipliers from (6.6).** Under the hypotheses of
`multiplierEquationsAt_handPfaffian_iff`, with `M_o(x(t))` and `M_f(θ(t))` positive definite,
`J_h(q(t))` invertible, the grasp constraint on a neighborhood of `t` and `Ad` the derivative of
`s ↦ [J_h −Gᵀ](q(s))` at `t` (the book's `Ȧ`), every multiplier vector `λ` of (6.24) at `t` is
`λ = (A M̄⁻¹ Aᵀ)⁻¹ (A M̄⁻¹ ((τ, 0) − C̄ q̇ − N̄) + Ȧ q̇)`, with `M̄ = diag(M_f, M_o)`,
`C̄ = diag(C_f, C_o)` (Christoffel matrices) and `N̄ = (∂V_f/∂θ, ∂V_o/∂x)`. -/
theorem eq_multiplier_of_multiplierEquationsAt_handPfaffian (e : Fin p ⊕ Fin n ≃ Fin N)
    {Mo : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ} {Mo' : Fin p → Fin p → ((Fin p → ℝ) →L[ℝ] ℝ)}
    {Vo : (Fin p → ℝ) → ℝ} {Vo' : (Fin p → ℝ) →L[ℝ] ℝ}
    {Mf : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Mf' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {Vf : (Fin n → ℝ) → ℝ} {Vf' : (Fin n → ℝ) →L[ℝ] ℝ}
    {Jh : (Fin N → ℝ) → Matrix (Fin n) (Fin n) ℝ} {G : (Fin N → ℝ) → Matrix (Fin p) (Fin n) ℝ}
    {q q' : ℝ → Fin N → ℝ} {q'' : Fin N → ℝ} {Ad : Matrix (Fin n) (Fin N) ℝ} {t : ℝ}
    (hMo_symm : ∀ y, (Mo y).IsSymm) (hMf_symm : ∀ y, (Mf y).IsSymm)
    (hMo : ∀ i j, HasFDerivAt (fun y => Mo y i j) (Mo' i j) (splitFst e (q t)))
    (hVo : HasFDerivAt Vo Vo' (splitFst e (q t)))
    (hMf : ∀ i j, HasFDerivAt (fun y => Mf y i j) (Mf' i j) (splitSnd e (q t)))
    (hVf : HasFDerivAt Vf Vf' (splitSnd e (q t))) (hq : ∀ᶠ s in 𝓝 t, HasDerivAt q (q' s) s)
    (hq' : HasDerivAt q' q'' t) (hMo_pd : (Mo (splitFst e (q t))).PosDef)
    (hMf_pd : (Mf (splitSnd e (q t))).PosDef) (hJ : IsUnit (Jh (q t)).det)
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt (handPfaffian e Jh G) (q s) (q' s))
    (hAd : ∀ i j, HasDerivAt (fun s => handPfaffian e Jh G (q s) i j) (Ad i j) t)
    {τ μ : Fin n → ℝ}
    (h : MultiplierEquationsAt
      (lagrangian e (Lagrangian.mechanical Mo Vo) (Lagrangian.mechanical Mf Vf))
      (handPfaffian e Jh G) q (handForce e τ) μ t) :
    μ = multiplier (handPfaffian e Jh G (q t))
      (blockMatrix e (Mo (splitFst e (q t))) (Mf (splitSnd e (q t))))
      (handForce e τ -
        blockMatrix e (Christoffel.coriolisMatrix (Christoffel.partials Mo') (splitFst e (q' t)))
          (Christoffel.coriolisMatrix (Christoffel.partials Mf') (splitSnd e (q' t))) *ᵥ q' t -
        splitJoin e (Lagrangian.gradient Vo') (Lagrangian.gradient Vf'))
      (Ad *ᵥ q' t) := by
  obtain ⟨hf, ho⟩ :=
    (multiplierEquationsAt_handPfaffian_iff e hMo_symm hMf_symm hMo hVo hMf hVf hq hq' τ μ).mp h
  have hA := linearIndependent_row_handPfaffian e Jh G hJ
  have hM := blockMatrix_posDef e hMo_pd hMf_pd
  refine (add_eq_zero_iff_eq_multiplier hM hA ?_).mp (mulVec_add_mulVec_eq_zero hc hAd hq')
  have key : ∀ v w : Fin N → ℝ, splitFst e v = splitFst e w → splitSnd e v = splitSnd e w →
      v = w := by
    intro v w h1 h2
    rw [← splitJoin_splitFst_splitSnd e v, ← splitJoin_splitFst_splitSnd e w, h1, h2]
  apply key
  · simp only [splitFst_add, splitFst_sub, blockMatrix_mulVec, splitFst_splitJoin, handForce,
      splitFst_transpose_mulVec, colsFst_handPfaffian, Matrix.transpose_neg,
      Matrix.transpose_transpose, Matrix.neg_mulVec]
    linear_combination ho
  · simp only [splitSnd_add, splitSnd_sub, blockMatrix_mulVec, splitSnd_splitJoin, handForce,
      splitSnd_transpose_mulVec, colsSnd_handPfaffian]
    linear_combination hf

end Multipliers

end Composite
end RoboLean
