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
* Example 3.13, p. 126: four revolute axes through one point give a singular configuration.

Example 3.12 (three parallel coplanar revolute axes) is not formalized. The statements hold
for `n ≤ 6` joints, which contains the book's six-joint case; they concern the coordinate
model only, not the behaviour of a physical arm near a singularity.
-/

noncomputable section

namespace RoboLean

namespace Twist

/-! ### Supporting lemmas -/

/-- The six coordinates `Twist.coordinates` (linear first, MLS eq. (2.30), p. 41) as a real
linear equivalence. Supporting lemma for reading Jacobian columns as columns of a real
matrix. -/
def coordinatesEquiv : Twist ≃ₗ[ℝ] (Fin 3 ⊕ Fin 3 → ℝ) where
  toFun := coordinates
  invFun x := ⟨WithLp.toLp 2 (fun i => x (Sum.inl i)), WithLp.toLp 2 (fun i => x (Sum.inr i))⟩
  map_add' ξ η := by
    funext r
    rcases r with i | i <;> rfl
  map_smul' c ξ := by
    funext r
    rcases r with i | i <;> rfl
  left_inv ξ := rfl
  right_inv x := by
    funext r
    rcases r with i | i <;> rfl

/-- `coordinatesEquiv` applies `Twist.coordinates` (MLS eq. (2.30), p. 41). -/
@[simp] theorem coordinatesEquiv_apply (ξ : Twist) : coordinatesEquiv ξ = ξ.coordinates := rfl

/-- The revolute joint twist `(-ω × q, ω)` of MLS p. 87 is linear in the axis direction `ω`
for a fixed axis point `q`. Supporting lemma for Example 3.13, p. 126. -/
def revoluteLinear (q : Vec3) : Vec3 →ₗ[ℝ] Twist where
  toFun ω := revolute ω q
  map_add' ω η := by
    apply Twist.ext
    · simp [revolute, add_comm]
    · rfl
  map_smul' c ω := by
    apply Twist.ext
    · simp [revolute]
    · rfl

/-- `revoluteLinear q ω` is the revolute twist `Twist.revolute ω q` of MLS p. 87. -/
@[simp] theorem revoluteLinear_apply (q ω : Vec3) : revoluteLinear q ω = revolute ω q := rfl

/-- The revolute twist depends on the axis point only through `ω × q`: if
`ω × (q₁ - q₂) = 0`, both points give the same twist. This is condition 2 of MLS
Example 3.11, p. 124, and the condition of Example 3.13, p. 126. -/
theorem revolute_eq_of_cross_sub_eq_zero (ω q₁ q₂ : Vec3)
    (h : Vec3.cross ω (q₁ - q₂) = 0) : revolute ω q₁ = revolute ω q₂ := by
  have h' : Vec3.cross ω q₁ = Vec3.cross ω q₂ := by
    have hs : Vec3.cross ω (q₁ - q₂) = Vec3.cross ω q₁ - Vec3.cross ω q₂ := by
      rw [sub_eq_add_neg, Vec3.cross_add, Vec3.cross_neg, ← sub_eq_add_neg]
    rw [hs] at h
    exact sub_eq_zero.mp h
  apply Twist.ext
  · simp [revolute, h']
  · rfl

/-- Two revolute twists with parallel axes `ω₂ = ±ω₁` and collinear axis lines
(`ω₁ × (q₁ - q₂) = 0`) are proportional, `ξ₂ = ±ξ₁`: the column computation in the proof of
MLS Example 3.11, p. 124–125. The unit-magnitude premise of the book is not needed. -/
theorem revolute_eq_smul_of_collinear (ω₁ ω₂ q₁ q₂ : Vec3) (s : ℝ) (hω : ω₂ = s • ω₁)
    (hcol : Vec3.cross ω₁ (q₁ - q₂) = 0) : revolute ω₂ q₂ = s • revolute ω₁ q₁ := by
  rw [revolute_eq_of_cross_sub_eq_zero ω₁ q₁ q₂ hcol, hω]
  apply Twist.ext
  · simp [revolute]
  · rfl

end Twist

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

end SerialChain

end RoboLean
