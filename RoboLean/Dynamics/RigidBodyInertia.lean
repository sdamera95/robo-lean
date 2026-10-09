import RoboLean.Geometry.TwistAdjoint
import RoboLean.Geometry.RigidVelocityComposition
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The generalized inertia matrix of a rigid body

MLS Chapter 4, §2.2, printed pp. 161–163, eq. (4.9): with the body frame placed at the mass
center, the kinetic energy of a rigid body of mass `m` and inertia tensor `𝓘` (expressed in
the body frame) is

`T = ½ m ‖ṗ‖² + ½ ωᵀ 𝓘 ω = ½ (Vᵇ)ᵀ 𝓜 Vᵇ`,  `𝓜 = [[m I, 0], [0, 𝓘]]`,

where `V̂ᵇ = g⁻¹ ġ` is the body velocity and `ω` the body angular velocity. The book's block
order is linear first, which is the library's twist order `(v, ω)`; no transposition is
needed. Six-by-six matrices are indexed by `Fin 3 ⊕ Fin 3` exactly as
`Twist.coordinates` and `Twist.adjointMatrix` are: `Sum.inl` rows and columns are the linear
coordinates, `Sum.inr` the angular ones.

Contents:

* `RigidBody.generalizedInertia m 𝓘` and `RigidBody.kineticEnergy 𝓜 V`;
* the block expansion of the kinetic energy, and the same expansion for the actual body
  velocity of a differentiable pose trajectory, where `‖vᵇ‖ = ‖ṗ‖` (first line of (4.9));
* symmetry, positive semidefiniteness and positive definiteness, each under explicit
  hypotheses on `m` and `𝓘` (MLS asserts "symmetric and positive definite" with no
  hypothesis printed);
* the change of body frame `𝓜' = Ad_gᵀ 𝓜 Ad_g` (the form of eq. (4.28), p. 176), which
  preserves kinetic energy along actual trajectories, composes, and preserves symmetry and
  positivity; and its exact block form for a pure translation (compare Example 4.4, p. 177).

The inertia tensor is an arbitrary real `3 × 3` matrix here, not the mass integral
`-∫ ρ r̂² dV` of p. 162; positivity of `m` and `𝓘` is a hypothesis, not derived from a mass
density. Masses, lengths and times carry units only by convention. Nothing here asserts that
given parameters are physically realizable (for example the triangle inequalities between
principal moments), or anything about a physical body.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

/-- Congruence of a bilinear form, used for `Aᵀ 𝓜 A` with `A` an adjoint or a Jacobian
matrix (MLS eqs. (4.17), (4.28)): `x ⬝ (Aᵀ M A y) = (A x) ⬝ (M (A y))`. Pure matrix
algebra over `ℝ`, for any finite index types. -/
theorem dotProduct_transpose_mul_mul_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (M : Matrix m m ℝ) (x y : n → ℝ) :
    x ⬝ᵥ ((Aᵀ * M * A) *ᵥ y) = (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

namespace RigidBody

/-! ### Six coordinates of a twist as a linear map -/

/-- The six coordinates `Twist.coordinates` (linear first, MLS eq. (2.30), p. 41) as a real
linear map; used to read sums of Jacobian columns as six-vectors. -/
def coordinatesLinearMap : Twist →ₗ[ℝ] (Fin 3 ⊕ Fin 3 → ℝ) where
  toFun := Twist.coordinates
  map_add' ξ η := by
    funext r
    rcases r with i | i <;> rfl
  map_smul' c ξ := by
    funext r
    rcases r with i | i <;> rfl

/-- The linear map `coordinatesLinearMap` is `Twist.coordinates` (MLS eq. (2.30), p. 41). -/
@[simp] theorem coordinatesLinearMap_apply (ξ : Twist) :
    coordinatesLinearMap ξ = ξ.coordinates := rfl

/-- Six coordinates of a sum of twists (MLS eq. (2.30), p. 41, twist coordinates). -/
theorem coordinates_add (ξ η : Twist) :
    (ξ + η).coordinates = ξ.coordinates + η.coordinates :=
  coordinatesLinearMap.map_add ξ η

/-- Six coordinates of a scaled twist (MLS eq. (2.30), p. 41, twist coordinates). -/
theorem coordinates_smul (c : ℝ) (ξ : Twist) :
    (c • ξ).coordinates = c • ξ.coordinates :=
  coordinatesLinearMap.map_smul c ξ

/-- The zero twist has zero coordinates (MLS eq. (2.30), p. 41, twist coordinates). -/
@[simp] theorem coordinates_zero : (0 : Twist).coordinates = 0 :=
  coordinatesLinearMap.map_zero

/-- Six coordinates of a finite sum of twists, for example `J θ̇ = ∑ᵢ θ̇ᵢ Jᵢ`
(MLS p. 168, `Vᵇ = J θ̇`). -/
theorem coordinates_sum {ι : Type*} (s : Finset ι) (f : ι → Twist) :
    (∑ i ∈ s, f i).coordinates = ∑ i ∈ s, (f i).coordinates :=
  map_sum coordinatesLinearMap f s

/-- A twist vanishes exactly when its six coordinates do (MLS eq. (2.30), p. 41). -/
theorem coordinates_eq_zero_iff (ξ : Twist) : ξ.coordinates = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    exact Twist.coordinates_injective (h.trans coordinates_zero.symm)
  · rintro rfl
    exact coordinates_zero

/-! ### Generalized inertia and kinetic energy -/

/-- **MLS eq. (4.9), p. 162.** The generalized inertia matrix `𝓜 = [[m I, 0], [0, 𝓘]]` of a
rigid body of mass `m` and inertia tensor `𝓘`, both expressed in a body frame at the mass
center. Rows and columns are indexed like `Twist.coordinates`: the linear block (`Sum.inl`)
first, as printed and as in the library twist order `(v, ω)`. No hypothesis on `m` or `𝓘` is
built in. -/
def generalizedInertia (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (m • (1 : Matrix (Fin 3) (Fin 3) ℝ)) 0 0 𝓘

/-- **MLS eq. (4.9), p. 162.** The kinetic energy `½ (Vᵇ)ᵀ 𝓜 Vᵇ` of a rigid body with
generalized inertia `𝓜` and body velocity `Vᵇ`, through the six coordinates
`Twist.coordinates` (order `(v, ω)`). `𝓜` and `Vᵇ` must refer to the same body frame; the
types do not enforce it. -/
def kineticEnergy (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (V : Twist) : ℝ :=
  (1 / 2 : ℝ) * (V.coordinates ⬝ᵥ (𝓜 *ᵥ V.coordinates))

/-- The bilinear form of the generalized inertia of MLS eq. (4.9), p. 162, on six-vectors:
`x ⬝ 𝓜 y = m (xᵥ ⬝ yᵥ) + x_ω ⬝ 𝓘 y_ω`, with `x ∘ Sum.inl` the linear coordinates. -/
theorem dotProduct_generalizedInertia_mulVec (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    (x y : Fin 3 ⊕ Fin 3 → ℝ) :
    x ⬝ᵥ (generalizedInertia m 𝓘 *ᵥ y) =
      m * ((x ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inl)) + (x ∘ Sum.inr) ⬝ᵥ (𝓘 *ᵥ (y ∘ Sum.inr)) := by
  simp [generalizedInertia, dotProduct, Matrix.fromBlocks_mulVec, Fintype.sum_sum_type,
    Matrix.smul_mulVec, Finset.mul_sum, mul_left_comm]

/-- The bilinear form of MLS eq. (4.9), p. 162, on two twists:
`V ⬝ 𝓜 W = m (v_V ⬝ v_W) + ω_V ⬝ 𝓘 ω_W`, in the twist order `(v, ω)`. -/
theorem coordinates_dotProduct_generalizedInertia_mulVec (m : ℝ)
    (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V W : Twist) :
    V.coordinates ⬝ᵥ (generalizedInertia m 𝓘 *ᵥ W.coordinates) =
      m * (WithLp.ofLp V.linear ⬝ᵥ WithLp.ofLp W.linear) +
        WithLp.ofLp V.angular ⬝ᵥ (𝓘 *ᵥ WithLp.ofLp W.angular) :=
  dotProduct_generalizedInertia_mulVec m 𝓘 _ _

private theorem dotProduct_self_ofLp (v : Vec3) :
    WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

/-- **MLS eq. (4.9), p. 162, block form.** For the generalized inertia of a body frame at the
mass center, `½ Vᵀ 𝓜 V = ½ m ‖v‖² + ½ ωᵀ 𝓘 ω`, where `V = (v, ω)`. -/
theorem kineticEnergy_generalizedInertia (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) (V : Twist) :
    kineticEnergy (generalizedInertia m 𝓘) V =
      (1 / 2 : ℝ) * m * ‖V.linear‖ ^ 2 +
        (1 / 2 : ℝ) * (WithLp.ofLp V.angular ⬝ᵥ (𝓘 *ᵥ WithLp.ofLp V.angular)) := by
  rw [kineticEnergy, coordinates_dotProduct_generalizedInertia_mulVec, dotProduct_self_ofLp]
  ring

/-- **MLS eq. (4.9), p. 162, along an actual motion.** For a pose trajectory `g` of a body
frame at the mass center, with actual derivative `D` of the homogeneous pose at `t`, the
kinetic energy of the actual body velocity is `½ m ‖ṗ‖² + ½ ωᵀ 𝓘 ω`: `ṗ` is the actual
derivative of the frame origin (`RigidTransform.hasDerivAt_translation`) and `ω` the body
angular velocity. The step `‖vᵇ‖ = ‖Rᵀ ṗ‖ = ‖ṗ‖` uses that rotations preserve the norm. -/
theorem kineticEnergy_generalizedInertia_bodyVelocity (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    kineticEnergy (generalizedInertia m 𝓘) (RigidTransform.bodyVelocity g D t h) =
      (1 / 2 : ℝ) * m * ‖RigidTransform.translationDerivative D‖ ^ 2 +
        (1 / 2 : ℝ) * (WithLp.ofLp (RigidTransform.bodyVelocity g D t h).angular ⬝ᵥ
          (𝓘 *ᵥ WithLp.ofLp (RigidTransform.bodyVelocity g D t h).angular)) := by
  rw [kineticEnergy_generalizedInertia, RigidTransform.bodyVelocity_linear, Rotation.norm_act]

/-! ### Symmetry and positivity (MLS p. 162: "symmetric and positive definite") -/

/-- The generalized inertia of MLS eq. (4.9), p. 162, is symmetric when the inertia tensor
is. MLS defines `𝓘` as a symmetric integral; here symmetry is a hypothesis. -/
theorem generalizedInertia_isSymm (m : ℝ) {𝓘 : Matrix (Fin 3) (Fin 3) ℝ} (h𝓘 : 𝓘.IsSymm) :
    (generalizedInertia m 𝓘).IsSymm := by
  refine Matrix.IsSymm.fromBlocks ?_ (by simp) h𝓘
  simp [Matrix.IsSymm]

/-- **MLS p. 162, positivity, semidefinite form.** The generalized inertia
`[[m I, 0], [0, 𝓘]]` of eq. (4.9) is positive semidefinite when `0 ≤ m` and `𝓘` is positive
semidefinite. MLS states positive definiteness without hypotheses; these are the explicit
ones for the semidefinite conclusion. -/
theorem generalizedInertia_posSemidef {m : ℝ} {𝓘 : Matrix (Fin 3) (Fin 3) ℝ} (hm : 0 ≤ m)
    (h𝓘 : 𝓘.PosSemidef) : (generalizedInertia m 𝓘).PosSemidef := by
  have hs : 𝓘.IsSymm := by simpa using h𝓘.isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa using generalizedInertia_isSymm m hs
  · intro x
    simp only [star_trivial]
    rw [dotProduct_generalizedInertia_mulVec]
    have h1 : 0 ≤ (x ∘ Sum.inl) ⬝ᵥ (x ∘ Sum.inl) := by
      simpa using dotProduct_star_self_nonneg (x ∘ Sum.inl)
    have h2 : 0 ≤ (x ∘ Sum.inr) ⬝ᵥ (𝓘 *ᵥ (x ∘ Sum.inr)) := by
      simpa using h𝓘.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    positivity

/-- **MLS p. 162, positivity.** The generalized inertia `[[m I, 0], [0, 𝓘]]` of eq. (4.9) is
positive definite when `0 < m` and `𝓘` is positive definite. MLS asserts positive
definiteness without printing these hypotheses. -/
theorem generalizedInertia_posDef {m : ℝ} {𝓘 : Matrix (Fin 3) (Fin 3) ℝ} (hm : 0 < m)
    (h𝓘 : 𝓘.PosDef) : (generalizedInertia m 𝓘).PosDef := by
  have hs : 𝓘.IsSymm := by simpa using h𝓘.isHermitian
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa using generalizedInertia_isSymm m hs
  · intro x hx
    simp only [star_trivial]
    rw [dotProduct_generalizedInertia_mulVec]
    have h1 : 0 ≤ (x ∘ Sum.inl) ⬝ᵥ (x ∘ Sum.inl) := by
      simpa using dotProduct_star_self_nonneg (x ∘ Sum.inl)
    have h2 : 0 ≤ (x ∘ Sum.inr) ⬝ᵥ (𝓘 *ᵥ (x ∘ Sum.inr)) := by
      simpa using h𝓘.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    by_cases hl : x ∘ Sum.inl = 0
    · have hr : x ∘ Sum.inr ≠ 0 := by
        intro hr
        apply hx
        funext r
        rcases r with i | i
        · exact congrFun hl i
        · exact congrFun hr i
      have h2' : 0 < (x ∘ Sum.inr) ⬝ᵥ (𝓘 *ᵥ (x ∘ Sum.inr)) := by
        simpa using h𝓘.dotProduct_mulVec_pos hr
      positivity
    · have h1' : 0 < (x ∘ Sum.inl) ⬝ᵥ (x ∘ Sum.inl) := by
        simpa using (dotProduct_star_self_pos_iff (v := x ∘ Sum.inl)).mpr hl
      positivity

/-- The kinetic energy `½ Vᵀ 𝓜 V` of MLS eq. (4.9), p. 162, is nonnegative for a positive
semidefinite generalized inertia. -/
theorem kineticEnergy_nonneg {𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ}
    (h𝓜 : 𝓜.PosSemidef) (V : Twist) : 0 ≤ kineticEnergy 𝓜 V := by
  have h := h𝓜.dotProduct_mulVec_nonneg V.coordinates
  simp only [star_trivial] at h
  rw [kineticEnergy]
  positivity

/-- **MLS p. 171 (proof of Lemma 4.2), for one body.** With a positive definite generalized
inertia the kinetic energy `½ Vᵀ 𝓜 V` of eq. (4.9) vanishes only at rest, `V = 0`. -/
theorem kineticEnergy_eq_zero_iff {𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ}
    (h𝓜 : 𝓜.PosDef) (V : Twist) : kineticEnergy 𝓜 V = 0 ↔ V = 0 := by
  constructor
  · intro h0
    by_contra hV
    have hc : V.coordinates ≠ 0 := fun hc => hV ((coordinates_eq_zero_iff V).mp hc)
    have h := h𝓜.dotProduct_mulVec_pos hc
    simp only [star_trivial] at h
    rw [kineticEnergy] at h0
    linarith
  · rintro rfl
    simp [kineticEnergy]

/-- With a positive definite generalized inertia, a nonzero body velocity has positive kinetic
energy (MLS eq. (4.9), p. 162; p. 171). -/
theorem kineticEnergy_pos {𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ} (h𝓜 : 𝓜.PosDef)
    {V : Twist} (hV : V ≠ 0) : 0 < kineticEnergy 𝓜 V :=
  lt_of_le_of_ne (kineticEnergy_nonneg h𝓜.posSemidef V)
    (fun h => hV ((kineticEnergy_eq_zero_iff h𝓜 V).mp h.symm))

/-! ### Change of body frame (MLS eq. (4.28), p. 176) -/

/-- **The change-of-frame law of the generalized inertia, in the form of MLS eq. (4.28),
p. 176.** If `𝓜` is the generalized inertia of a body in frame `B`, and a second body-fixed
frame `C` has constant pose `g = g_BC` relative to `B`, then the generalized inertia of the
same body expressed in `C` is `Ad_gᵀ 𝓜 Ad_g` (`Twist.adjointMatrix`, order `(v, ω)`).
MLS eq. (4.28) is the case `g = g_{sl_i}(0)⁻¹`, "the inertia of the ith link reflected into
the base frame". -/
def transformInertia (g : RigidTransform) (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  (Twist.adjointMatrix g)ᵀ * 𝓜 * Twist.adjointMatrix g

/-- The bilinear form of the transformed inertia (MLS eq. (4.28), p. 176):
`V ⬝ (Ad_gᵀ 𝓜 Ad_g) W = (Ad_g V) ⬝ 𝓜 (Ad_g W)`. -/
theorem coordinates_dotProduct_transformInertia_mulVec (g : RigidTransform)
    (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (V W : Twist) :
    V.coordinates ⬝ᵥ (transformInertia g 𝓜 *ᵥ W.coordinates) =
      (Twist.adjoint g V).coordinates ⬝ᵥ (𝓜 *ᵥ (Twist.adjoint g W).coordinates) := by
  rw [transformInertia, dotProduct_transpose_mul_mul_mulVec, Twist.adjointMatrix_mulVec,
    Twist.adjointMatrix_mulVec]

/-- **Kinetic energy is unchanged by the change of body frame (MLS eq. (4.28), p. 176).**
`½ Vᵀ (Ad_gᵀ 𝓜 Ad_g) V = ½ (Ad_g V)ᵀ 𝓜 (Ad_g V)`, for every twist `V` and rigid transform
`g`. -/
theorem kineticEnergy_transformInertia (g : RigidTransform)
    (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (V : Twist) :
    kineticEnergy (transformInertia g 𝓜) V = kineticEnergy 𝓜 (Twist.adjoint g V) := by
  rw [kineticEnergy, kineticEnergy, coordinates_dotProduct_transformInertia_mulVec]

private theorem bodyVelocity_const (h : RigidTransform) (t : ℝ)
    (hh : HasDerivAt (fun _ : ℝ => h.toHomogeneous) 0 t) :
    RigidTransform.bodyVelocity (fun _ => h) 0 t hh = 0 := by
  apply Twist.hat_injective
  rw [RigidTransform.hat_bodyVelocity, Matrix.mul_zero, Twist.hat_zero]

/-- **Change of body frame along an actual motion (MLS Proposition 2.15, p. 59, with a
constant `g_BC`; eq. (4.28), p. 176).**
Let `g(t)` be the pose of a body frame `B` with actual homogeneous derivative `D`, let a second
body-fixed frame `C` have constant pose `h = g_BC` relative to `B`, and let `E` be any actual
derivative of the pose `g(t) h` of `C`. Then the kinetic energy computed in `C`, with the
transformed inertia `Ad_hᵀ 𝓜 Ad_h` and the body velocity of `C`, equals the kinetic energy
computed in `B`. The derivative `E` exists (`RigidTransform.hasDerivAt_toHomogeneous_mul`). -/
theorem kineticEnergy_bodyVelocity_mul_const {g : ℝ → RigidTransform} {D : HomogeneousMatrix}
    {t : ℝ} (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) (h : RigidTransform)
    (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) {E : HomogeneousMatrix}
    (hE : HasDerivAt (fun s => (g s * h).toHomogeneous) E t) :
    kineticEnergy (transformInertia h 𝓜) (RigidTransform.bodyVelocity (fun s => g s * h) E t hE) =
      kineticEnergy 𝓜 (RigidTransform.bodyVelocity g D t hg) := by
  have hh : HasDerivAt (fun _ : ℝ => h.toHomogeneous) 0 t := hasDerivAt_const t _
  have hmul := RigidTransform.hasDerivAt_toHomogeneous_mul (h := fun _ => h) hg hh
  obtain rfl : E = D * h.toHomogeneous + (g t).toHomogeneous * 0 := hE.unique hmul
  have hv := RigidTransform.bodyVelocity_mul (h := fun _ => h) hg hh
  rw [bodyVelocity_const, add_zero] at hv
  rw [hv, kineticEnergy_transformInertia, Twist.adjoint_adjoint_inv]

/-- The transformed inertia for the identity transform is the original (MLS eq. (4.28)). -/
@[simp] theorem transformInertia_one (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    transformInertia 1 𝓜 = 𝓜 := by
  simp [transformInertia]

/-- Two successive changes of body frame compose (MLS eq. (4.28), p. 176, with the adjoint
representation law, p. 56): first `g = g_BC`, then `h = g_CD`, gives `g h = g_BD`. -/
theorem transformInertia_mul (g h : RigidTransform)
    (𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :
    transformInertia (g * h) 𝓜 = transformInertia h (transformInertia g 𝓜) := by
  simp only [transformInertia, Twist.adjointMatrix_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The transformed inertia of MLS eq. (4.28), p. 176, is symmetric when `𝓜` is. -/
theorem transformInertia_isSymm (g : RigidTransform)
    {𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ} (h𝓜 : 𝓜.IsSymm) :
    (transformInertia g 𝓜).IsSymm := by
  unfold Matrix.IsSymm transformInertia
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h𝓜,
    Matrix.mul_assoc]

/-- The transformed inertia of MLS eq. (4.28), p. 176, is positive semidefinite when `𝓜` is. -/
theorem transformInertia_posSemidef (g : RigidTransform)
    {𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ} (h𝓜 : 𝓜.PosSemidef) :
    (transformInertia g 𝓜).PosSemidef := by
  simpa [transformInertia] using h𝓜.conjTranspose_mul_mul_same (Twist.adjointMatrix g)

/-- The adjoint matrix acts injectively on six-vectors, since `Ad_{g⁻¹} Ad_g = I`
(MLS p. 56). -/
theorem adjointMatrix_mulVec_injective (g : RigidTransform) :
    Function.Injective (Twist.adjointMatrix g).mulVec := by
  intro x y hxy
  have h := congrArg (Twist.adjointMatrix g⁻¹ *ᵥ ·) hxy
  simpa only [Matrix.mulVec_mulVec, ← Twist.adjointMatrix_mul, inv_mul_cancel,
    Twist.adjointMatrix_one, Matrix.one_mulVec] using h

/-- The transformed inertia of MLS eq. (4.28), p. 176, is positive definite when `𝓜` is: the
adjoint matrix is invertible. -/
theorem transformInertia_posDef (g : RigidTransform)
    {𝓜 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ} (h𝓜 : 𝓜.PosDef) :
    (transformInertia g 𝓜).PosDef := by
  simpa [transformInertia] using
    h𝓜.conjTranspose_mul_mul_same (adjointMatrix_mulVec_injective g)

/-- **Pure translation of the body frame (compare MLS Example 4.4, p. 177).** For `g = (I, p)`,
the generalized inertia `[[m I, 0], [0, 𝓘]]` of eq. (4.9) transforms to
`[[m I, m p̂], [-m p̂, 𝓘 - m p̂²]]`, the six-dimensional parallel-axis form. The display on
MLS p. 177 prints the factors `Ad_{(I,p)}ᵀ`, `𝓜`, `Ad_{(I,p)}` but the right-hand side
`[[m I, m p̂], [-m p̂, 𝓘]]` without the term `-m p̂²`; with (4.28)'s `g = g_{sl_i}(0)⁻¹ = (I, -p)`
the off-diagonal signs flip. This theorem is the exact product. -/
theorem transformInertia_translation (p : Vec3) (m : ℝ) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ) :
    transformInertia ⟨1, p⟩ (generalizedInertia m 𝓘) =
      Matrix.fromBlocks (m • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (m • Vec3.hat p)
        (-(m • Vec3.hat p)) (𝓘 - m • (Vec3.hat p * Vec3.hat p)) := by
  have h1 : ((1 : Rotation) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := rfl
  simp only [transformInertia, generalizedInertia, Twist.adjointMatrix, h1,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Vec3.hat_transpose,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul]
  congr 1
  · exact smul_neg m _
  · rw [smul_neg, sub_eq_add_neg, add_comm]

end RigidBody
end RoboLean
