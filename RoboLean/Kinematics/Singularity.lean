import RoboLean.Kinematics.Jacobian
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Singular configurations of a serial chain

MLS Chapter 3, §4.3, printed pp. 123–127. "A singular configuration of a robot manipulator
is a configuration at which the manipulator Jacobian drops rank" (p. 123). For a six-joint
manipulator this is the failure of the `6 × 6` Jacobian to be invertible; for fewer than six
joints it is that "two or more of the columns of `Jˢ(θ) ∈ ℝ^{6×n}` become linearly
dependent" (p. 123).

`SerialChain.IsSingular c θ` says that the rank of the `6 × n` spatial Jacobian matrix
`SerialChain.spatialJacobianMatrix` is less than `min 6 n`. For `n ≤ 6` this is exactly the
printed column condition (`isSingular_iff_not_linearIndependent`). For `n > 6` it says that
the Jacobian does not have rank six; the book's p. 123 text does not treat that case, so for
redundant chains the definition is this library's extension.

Proved here:

* the rank of the matrix is the dimension of the span of the twist columns, and for
  `n ≤ 6` the configuration is singular exactly when the columns are linearly dependent
  (p. 123);
* the body Jacobian gives the same singular configurations (pp. 125 and 128: a change of
  frame multiplies the Jacobian by an invertible adjoint);
* Example 3.11, p. 124: two collinear revolute axes give a singular configuration;
* Example 3.12, pp. 125–126: three parallel coplanar revolute axes give a singular
  configuration;
* Example 3.13, p. 126: four revolute axes through one point give a singular configuration.

The supporting lemmas about revolute twists (`Twist.revoluteLinear`,
`Twist.revolute_eq_of_cross_sub_eq_zero`, `Twist.revolute_eq_smul_of_collinear`) live next to
`Twist.revolute` in `RoboLean.Kinematics.SerialChain`, and `Twist.coordinatesEquiv` next to
`Twist.coordinates` in `RoboLean.Geometry.TwistAdjoint`. The statements hold for `n ≤ 6`
joints, which contains the book's six-joint case; they concern the coordinate model only, not
the behaviour of a physical arm near a singularity.
-/

noncomputable section

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-- **MLS p. 123: singular configuration.** A configuration `θ` of the chain is singular when
the `6 × n` spatial manipulator Jacobian `Jˢ(θ)` (`spatialJacobianMatrix`, eq. (3.54),
p. 116) "drops rank", i.e. has rank less than `min 6 n`. For `n = 6` this is the failure of
invertibility, and for `n ≤ 6` it is linear dependence of the columns
(`isSingular_iff_not_linearIndependent`), the two readings printed on p. 123. For `n > 6`
the book's p. 123 text gives no reading; rank less than six is this library's choice. Joint
coordinates are the real lift `Fin n → ℝ`; admissibility is not part of the definition. -/
def IsSingular (c : SerialChain n) (θ : Fin n → ℝ) : Prop :=
  (c.spatialJacobianMatrix θ).rank < min 6 n

/-- The columns of the matrix view are the coordinates of the twist columns
(MLS p. 116, eq. (3.54); `Twist.coordinates`, linear first). -/
theorem col_spatialJacobianMatrix (c : SerialChain n) (θ : Fin n → ℝ) :
    (c.spatialJacobianMatrix θ).col =
      (Twist.coordinatesEquiv : Twist →ₗ[ℝ] (Fin 3 ⊕ Fin 3 → ℝ)) ∘ c.spatialJacobian θ := rfl

/-- The rank of the spatial Jacobian matrix (MLS p. 116) is the dimension of the real span
of its twist columns. -/
theorem rank_spatialJacobianMatrix (c : SerialChain n) (θ : Fin n → ℝ) :
    (c.spatialJacobianMatrix θ).rank =
      Module.finrank ℝ (Submodule.span ℝ (Set.range (c.spatialJacobian θ))) := by
  rw [Matrix.rank_eq_finrank_span_cols, col_spatialJacobianMatrix, Set.range_comp,
    Submodule.span_image, LinearEquiv.finrank_map_eq]

/-- The spatial Jacobian matrix (MLS p. 116) has rank at most `n`, the number of columns. -/
theorem rank_spatialJacobianMatrix_le (c : SerialChain n) (θ : Fin n → ℝ) :
    (c.spatialJacobianMatrix θ).rank ≤ n := by
  simpa using Matrix.rank_le_card_width (c.spatialJacobianMatrix θ)

/-- The twist columns of the spatial Jacobian (MLS eq. (3.54), p. 116) are linearly
independent exactly when the `6 × n` matrix has rank `n`. -/
theorem linearIndependent_spatialJacobian_iff (c : SerialChain n) (θ : Fin n → ℝ) :
    LinearIndependent ℝ (c.spatialJacobian θ) ↔ (c.spatialJacobianMatrix θ).rank = n := by
  rw [← LinearMap.linearIndependent_iff _ (LinearEquiv.ker Twist.coordinatesEquiv),
    ← col_spatialJacobianMatrix, linearIndependent_iff_card_eq_finrank_span,
    Matrix.rank_eq_finrank_span_cols, Fintype.card_fin, eq_comm]
  rfl

/-- **MLS p. 123, chains with at most six joints.** For `n ≤ 6`, a configuration is singular
exactly when the columns of `Jˢ(θ) ∈ ℝ^{6×n}` are linearly dependent ("two or more of the
columns of `Jˢ(θ)` become linearly dependent"). -/
theorem isSingular_iff_not_linearIndependent (c : SerialChain n) (θ : Fin n → ℝ)
    (hn : n ≤ 6) :
    c.IsSingular θ ↔ ¬ LinearIndependent ℝ (c.spatialJacobian θ) := by
  rw [IsSingular, linearIndependent_spatialJacobian_iff, min_eq_right hn]
  have := c.rank_spatialJacobianMatrix_le θ
  omega

/-- **MLS pp. 125 and 128: singularity does not depend on the frame of the Jacobian.** The
spatial Jacobian columns are the body Jacobian columns moved by the invertible adjoint
`Ad_{g_st(θ)}` (eq. (3.56), p. 117), so for `n ≤ 6` the configuration is singular exactly when
the columns of the body Jacobian `Jᵇ(θ)` (eq. (3.55)) are linearly dependent. -/
theorem isSingular_iff_not_linearIndependent_bodyJacobian (c : SerialChain n)
    (θ : Fin n → ℝ) (hn : n ≤ 6) :
    c.IsSingular θ ↔ ¬ LinearIndependent ℝ (c.bodyJacobian θ) := by
  have hJ : c.spatialJacobian θ =
      (Twist.adjointEquiv (c.fk θ)).toLinearMap ∘ c.bodyJacobian θ := by
    funext i
    exact c.spatialJacobian_eq_adjoint_bodyJacobian θ i
  rw [c.isSingular_iff_not_linearIndependent θ hn, hJ,
    LinearMap.linearIndependent_iff _ (LinearEquiv.ker _)]

/-- A family of twists with two distinct members `ξ_j = s ξ_i` is linearly dependent.
Supporting lemma for MLS Example 3.11, p. 124. -/
theorem not_linearIndependent_of_eq_smul {J : Fin n → Twist} {i j : Fin n} (hij : i ≠ j)
    (s : ℝ) (h : J j = s • J i) : ¬ LinearIndependent ℝ J := by
  intro hJ
  have hpair : LinearIndependent ℝ ![J i, J j] := by
    have := hJ.comp ![i, j] (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [eq_comm])
    convert this using 1
    funext k
    fin_cases k <;> rfl
  have := (LinearIndependent.pair_iff.mp hpair) s (-1) (by rw [h]; simp)
  norm_num at this

/-- **MLS Example 3.11, p. 124: two collinear revolute joints.** If at the configuration `θ`
two distinct columns `i ≠ j` of the spatial Jacobian are revolute twists
`ξᵢ' = (-ω₁ × q₁, ω₁)` and `ξⱼ' = (-ω₂ × q₂, ω₂)` whose axes are parallel (`ω₂ = ω₁` or
`ω₂ = -ω₁`, condition 1) and collinear (`ω₁ × (q₁ - q₂) = 0`, condition 2 for `i = 1`; the
case `i = 2` follows from it and condition 1), then the configuration is singular, for every
chain with `n ≤ 6` joints. The columns are the joint axes in the current configuration
(p. 116); by `Twist.adjoint_revolute` every column of a revolute joint has this form. The
book's unit-magnitude premise is not needed. -/
theorem isSingular_of_collinear_revolute (c : SerialChain n) (θ : Fin n → ℝ) (hn : n ≤ 6)
    {i j : Fin n} (hij : i ≠ j) (ω₁ ω₂ q₁ q₂ : Vec3)
    (hi : c.spatialJacobian θ i = Twist.revolute ω₁ q₁)
    (hj : c.spatialJacobian θ j = Twist.revolute ω₂ q₂)
    (hpar : ω₂ = ω₁ ∨ ω₂ = -ω₁) (hcol : Vec3.cross ω₁ (q₁ - q₂) = 0) :
    c.IsSingular θ := by
  rw [c.isSingular_iff_not_linearIndependent θ hn]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, ω₂ = s • ω₁ := by
    rcases hpar with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  refine not_linearIndependent_of_eq_smul hij s ?_
  rw [hi, hj]
  exact Twist.revolute_eq_smul_of_collinear ω₁ ω₂ q₁ q₂ s hs hcol

/-- **MLS Example 3.13, p. 126: four intersecting revolute joint axes.** If at the
configuration `θ` four distinct columns `f 0, …, f 3` of the spatial Jacobian are revolute
twists `(-ωₖ × qₖ, ωₖ)` whose axes all pass through one point `q` (`ωₖ × (qₖ - q) = 0`), the
configuration is singular, for every chain with `n ≤ 6` joints. The proof is the dimension
count: the four columns lie in the three-dimensional space of revolute twists through `q`.
The book argues with the three-dimensional reciprocal system of pure forces through `q`; the
dimension count is a different route to the same conclusion. -/
theorem isSingular_of_four_concurrent_revolute (c : SerialChain n) (θ : Fin n → ℝ)
    (hn : n ≤ 6) (f : Fin 4 → Fin n) (hf : Function.Injective f) (ω qs : Fin 4 → Vec3)
    (q : Vec3) (hcol : ∀ k, c.spatialJacobian θ (f k) = Twist.revolute (ω k) (qs k))
    (hq : ∀ k, Vec3.cross (ω k) (qs k - q) = 0) :
    c.IsSingular θ := by
  rw [c.isSingular_iff_not_linearIndependent θ hn]
  intro hJ
  have hcomp : c.spatialJacobian θ ∘ f = Twist.revoluteLinear q ∘ ω := by
    funext k
    simp [hcol k, Twist.revolute_eq_of_cross_sub_eq_zero (ω k) (qs k) q (hq k)]
  have hω : LinearIndependent ℝ ω :=
    LinearIndependent.of_comp (Twist.revoluteLinear q) (hcomp ▸ hJ.comp f hf)
  have hcard := hω.fintype_card_le_finrank
  simp [Vec3] at hcard

/-! ### Example 3.12: three parallel coplanar revolute axes -/

private theorem inner_eq_dot (x y : Vec3) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

private theorem cross_cross_right (a b c : Vec3) :
    Vec3.cross a (Vec3.cross b c) = inner ℝ a c • b - inner ℝ a b • c := by
  apply WithLp.ofLp_injective
  simp only [Vec3.cross_coordinates, WithLp.ofLp_sub, WithLp.ofLp_smul, inner_eq_dot]
  rw [cross_cross_eq_smul_sub_smul', dotProduct_comm (WithLp.ofLp b)]

/-- Two vectors perpendicular to a unit vector `ν` have their cross product along `ν`. -/
private theorem cross_eq_inner_smul_of_perp {ν a b : Vec3} (hν : ‖ν‖ = 1)
    (ha : inner ℝ ν a = 0) (hb : inner ℝ ν b = 0) :
    Vec3.cross a b = inner ℝ ν (Vec3.cross a b) • ν := by
  have h0 : Vec3.cross ν (Vec3.cross a b) = 0 := by
    rw [cross_cross_right, ha, hb, zero_smul, zero_smul, sub_zero]
  have h2 := cross_cross_right ν ν (Vec3.cross a b)
  rw [h0, Vec3.cross_zero, real_inner_self_eq_norm_sq, hν] at h2
  simp only [one_pow, one_smul] at h2
  exact (sub_eq_zero.mp h2.symm).symm

/-- **MLS Example 3.12, pp. 125–126: three parallel coplanar revolute joint axes.** If at the
configuration `θ` three distinct columns `f 0, f 1, f 2` of the spatial Jacobian are revolute
twists `(-ωₖ × qₖ, ωₖ)` whose axes are parallel (`ωᵢ = ±ωⱼ` for all `i, j`, condition 1) and
coplanar (a plane with unit normal `ν`, the book's `n`, with `νᵀωᵢ = 0` and `νᵀ(qᵢ - qⱼ) = 0`
for all `i, j`, condition 2), the configuration is singular, for every chain with `n ≤ 6`
joints. The columns are the joint axes in the current configuration (p. 116). The proof is a
dimension count: with `ω = ω₀`, each column is `±((-ω × q₀, ω) - c (ν, 0))` for a real `c`,
because `ω × (qₖ - q₀)` is perpendicular to the plane, so the three columns lie in a
two-dimensional space. The book changes coordinates by an adjoint and reads off three dependent
columns; the dimension count is a different route to the same conclusion. -/
theorem isSingular_of_three_parallel_coplanar_revolute (c : SerialChain n) (θ : Fin n → ℝ)
    (hn : n ≤ 6) (f : Fin 3 → Fin n) (hf : Function.Injective f) (ω qs : Fin 3 → Vec3)
    (hcol : ∀ k, c.spatialJacobian θ (f k) = Twist.revolute (ω k) (qs k))
    (hpar : ∀ i j, ω i = ω j ∨ ω i = -ω j) (ν : Vec3) (hν : ‖ν‖ = 1)
    (hνω : ∀ i, inner ℝ ν (ω i) = 0) (hνq : ∀ i j, inner ℝ ν (qs i - qs j) = 0) :
    c.IsSingular θ := by
  rw [c.isSingular_iff_not_linearIndependent θ hn]
  intro hJ
  have hs : ∀ k, ∃ s : ℝ, ω k = s • ω 0 := by
    intro k
    rcases hpar k 0 with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose s hs using hs
  set A : Twist := Twist.revolute (ω 0) (qs 0)
  set N : Twist := ⟨ν, 0⟩
  set coef : Fin 3 → ℝ := fun k => inner ℝ ν (Vec3.cross (ω 0) (qs k - qs 0))
  have hcross : ∀ k, Vec3.cross (ω 0) (qs k - qs 0) = coef k • ν := fun k =>
    cross_eq_inner_smul_of_perp hν (hνω 0) (hνq k 0)
  let L : (Fin 2 → ℝ) →ₗ[ℝ] Twist :=
    { toFun := fun x => x 0 • A + x 1 • N
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul]
        abel
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hcomp : c.spatialJacobian θ ∘ f = L ∘ fun k => ![s k, -(s k * coef k)] := by
    funext k
    have hrev : Twist.revolute (ω 0) (qs k) = A + (-coef k) • N := by
      apply Twist.ext
      · have hq : Vec3.cross (ω 0) (qs k) =
            Vec3.cross (ω 0) (qs 0) + Vec3.cross (ω 0) (qs k - qs 0) := by
          rw [← Vec3.cross_add]
          congr 1
          abel
        simp only [A, N, Twist.revolute, Twist.add_linear, Twist.smul_linear, hq, hcross k]
        simp only [neg_add, neg_smul]
      · simp [A, N, Twist.revolute]
    simp only [Function.comp_apply, hcol k, hs k, L, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [← Twist.revoluteLinear_apply, map_smul, Twist.revoluteLinear_apply, hrev, smul_add,
      smul_smul, neg_mul_eq_mul_neg]
  have hg : LinearIndependent ℝ fun k : Fin 3 => ![s k, -(s k * coef k)] :=
    LinearIndependent.of_comp L (hcomp ▸ hJ.comp f hf)
  have hcard := hg.fintype_card_le_finrank
  simp at hcard

end SerialChain

end RoboLean
