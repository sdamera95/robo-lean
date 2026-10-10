import RoboLean.Kinematics.Singularity
import RoboLean.Kinematics.Workspace
import RoboLean.Kinematics.ForcePullback
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Manipulability measures and the alternative dextrous workspace

MLS Chapter 3, §4.4, printed pp. 127–129. Local manipulability is read off the manipulator
Jacobian `J`: "Either the spatial or body Jacobian can be used, but the body Jacobian is preferred
since the body velocity of the end-effector is independent of the choice of base frame" (p. 128).
The singular values of `A ∈ ℝ^{p×n}` are "the square roots of the eigenvalues of `AᵀA`" (p. 128).
The page defines three measures,

* `μ₁(θ) = σ_min(J(θ))`, the minimum singular value (Example 3.14, p. 128);
* `μ₂(θ) = σ_min(J(θ)) / σ_max(J(θ))`, the inverse condition number (Example 3.15, p. 128);
* `μ₃(θ) = det J(θ)`, the determinant (Example 3.16, p. 129), for a square Jacobian;

and the alternative dextrous workspace `W′_D = {g_st(θ) : θ ∈ Q, μᵢ(θ) ≠ 0} ⊂ SE(3)`
(eq. (3.61), p. 129), "the set of end-effector configurations for which the manipulator can move
infinitesimally in any direction".

Carrier and conventions (choices of this library):

* `J` is the body Jacobian matrix `SerialChain.bodyJacobianMatrix` (`6 × n`, rows `v` then `ω`,
  columns the joints), the book's preferred choice. Its singular values are Mathlib's
  `LinearMap.singularValues` of `Matrix.toEuclideanLin J : ℝⁿ → ℝ⁶`, with the standard inner
  products on joint rates and on the six twist coordinates; Mathlib's definition is the square
  roots of the eigenvalues of `T† T`, in decreasing order, indexed from `0`, and `T† T` is the
  map of `JᵀJ` (`hasEigenvalue_transpose_mul_bodyJacobianMatrix`). So `σ_max = σ₀` and
  `σ_min = σ_{n-1}`. The values of `μ₁` and `μ₂` depend on that inner product and on the frame of
  the Jacobian (the spatial Jacobian `Ad_g Jᵇ` has other singular values in general); their zero
  sets do not.
* `μ₃` is defined for six-joint chains, as the determinant of the `6 × 6` body Jacobian with rows
  `(v, ω)` and columns joints `1 … 6` in order (`jacobianDet_eq_det_square`); it equals the
  determinant of the spatial Jacobian, since `det Ad_g = 1` (`jacobianDet_eq_det_spatial`).
* `W′_D` takes the measure as an argument, `alternativeDextrousWorkspace c Q μ`, with the joint
  space `Q` explicit as in `RoboLean.Kinematics.Workspace`; `admissibleAlternativeDextrousWorkspace`
  fixes `Q := c.admissible`.

Proved here: each measure vanishes exactly at the singular configurations of
`SerialChain.IsSingular` (MLS p. 123) when `0 < n ≤ 6` (for `μ₃`, `n = 6`), which contains the
book's claims "at a singular configuration, the minimum singular value of `J` is zero" (p. 128)
and "at a singular configuration, the inverse condition number is zero" (p. 128); `|μ₃|` is the
product of the six singular values (the book says `det J(θ)` "is the product of the singular
values"; the determinant may be negative, so the product is its absolute value); `0 ≤ μ₂ ≤ 1`;
consequently `W′_D` is the same set for the three measures, the image of the nonsingular
admissible configurations, and for six joints it is the set of poses reached at a configuration
where every twist is `J θ̇` for some joint rate (`mem_alternativeDextrousWorkspace_iff_forall`).

Not formalized: `σ_max(A) = ‖A‖₂` (p. 128), the interpretations of `μ₁` as the minimum
workspace velocity for unit joint velocity and of `μ₃` as an ellipsoid volume, and the measures of
the exercises. For `n > 6`, `σ_min = σ_{n-1}` is always zero while `IsSingular` (rank below six)
is not; the book's measures are stated for the square case. These are statements about the
coordinate model, not about a physical robot's dexterity.
-/

noncomputable section

open Module
open scoped Matrix

namespace RoboLean

namespace SerialChain

variable {n : ℕ}

/-! ### The body and spatial Jacobian matrices -/

/-- The matrix form of MLS eq. (3.56), p. 117: `Jˢ(θ) = Ad_{g_st(θ)} Jᵇ(θ)` as `6 × n` matrices,
with the `6 × 6` adjoint matrix of eq. (2.58), p. 55 (`Twist.adjointMatrix`). -/
theorem spatialJacobianMatrix_eq_adjointMatrix_mul (c : SerialChain n) (θ : Fin n → ℝ) :
    c.spatialJacobianMatrix θ = Twist.adjointMatrix (c.fk θ) * c.bodyJacobianMatrix θ := by
  ext r i
  change (c.spatialJacobian θ i).coordinates r =
    (Twist.adjointMatrix (c.fk θ) *ᵥ (c.bodyJacobian θ i).coordinates) r
  rw [Twist.adjointMatrix_mulVec, ← spatialJacobian_eq_adjoint_bodyJacobian]

/-- The body and spatial Jacobian matrices (MLS eqs. (3.54)–(3.55), pp. 116–117) have the same
rank: they differ by the invertible adjoint matrix (MLS pp. 125 and 128). -/
theorem rank_bodyJacobianMatrix (c : SerialChain n) (θ : Fin n → ℝ) :
    (c.bodyJacobianMatrix θ).rank = (c.spatialJacobianMatrix θ).rank := by
  rw [spatialJacobianMatrix_eq_adjointMatrix_mul, Matrix.rank_mul_eq_right_of_det_ne_zero _ _
    (by rw [Twist.det_adjointMatrix]; exact one_ne_zero)]

/-- The rank of a real matrix is the dimension of the range of its Euclidean linear map. -/
private theorem rank_eq_finrank_range_toEuclideanLin {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k] (A : Matrix m k ℝ) :
    A.rank = finrank ℝ (LinearMap.range (Matrix.toEuclideanLin A)) :=
  A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℝ).toBasis
    (EuclideanSpace.basisFun k ℝ).toBasis

/-! ### Singular values of the Jacobian (MLS p. 128) -/

/-- The singular values of the body Jacobian `J = Jᵇ(θ)` (MLS p. 128: "the square roots of the
eigenvalues of `AᵀA`"), as Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin J`:
the sequence `σ₀ ≥ σ₁ ≥ ⋯ ≥ σ_{n-1} ≥ 0` followed by zeros. The inner products are the standard
ones on joint rates and on the six twist coordinates `(v, ω)`. -/
def jacobianSingularValues (c : SerialChain n) (θ : Fin n → ℝ) : ℕ →₀ ℝ :=
  (Matrix.toEuclideanLin (c.bodyJacobianMatrix θ)).singularValues

/-- **MLS p. 128: singular values are square roots of eigenvalues of `JᵀJ`.** For `i < n`, the
square of the `i`-th singular value of the body Jacobian is an eigenvalue of `JᵀJ` (as a linear
map on joint rates). -/
theorem hasEigenvalue_transpose_mul_bodyJacobianMatrix (c : SerialChain n) (θ : Fin n → ℝ)
    {i : ℕ} (hi : i < n) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin ((c.bodyJacobianMatrix θ)ᵀ * c.bodyJacobianMatrix θ))
      (c.jacobianSingularValues θ i ^ 2) := by
  have h := LinearMap.hasEigenvalue_adjoint_comp_self_sq_singularValues
    (Matrix.toEuclideanLin (c.bodyJacobianMatrix θ)) (n := i)
    (by rw [finrank_euclideanSpace_fin]; exact hi)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.toLpLin_mul_same] at h
  exact h

/-- The largest singular value `σ_max(J(θ))` of the body Jacobian (MLS p. 128), Mathlib's index
`0`. -/
def maxSingularValue (c : SerialChain n) (θ : Fin n → ℝ) : ℝ :=
  c.jacobianSingularValues θ 0

/-- **MLS Example 3.14, p. 128: `μ₁(θ) = σ_min(J(θ))`.** The smallest of the `n` singular values
of the body Jacobian, Mathlib's index `n - 1`. For `n = 0` it is the junk value `0`. -/
def minSingularValue (c : SerialChain n) (θ : Fin n → ℝ) : ℝ :=
  c.jacobianSingularValues θ (n - 1)

/-- **MLS Example 3.15, p. 128: `μ₂(θ) = σ_min(J(θ)) / σ_max(J(θ))`**, the inverse condition
number of the body Jacobian. Lean's division gives `0` when `σ_max = 0`. -/
def inverseConditionNumber (c : SerialChain n) (θ : Fin n → ℝ) : ℝ :=
  c.minSingularValue θ / c.maxSingularValue θ

/-- Singular values are nonnegative (MLS p. 128, square roots). -/
theorem minSingularValue_nonneg (c : SerialChain n) (θ : Fin n → ℝ) :
    0 ≤ c.minSingularValue θ :=
  LinearMap.singularValues_nonneg _ _

/-- `σ_min ≤ σ_max` (MLS p. 128): Mathlib orders the singular values decreasingly. -/
theorem minSingularValue_le_maxSingularValue (c : SerialChain n) (θ : Fin n → ℝ) :
    c.minSingularValue θ ≤ c.maxSingularValue θ :=
  LinearMap.singularValues_antitone _ (Nat.zero_le _)

/-- The inverse condition number (MLS Example 3.15, p. 128) is nonnegative. -/
theorem inverseConditionNumber_nonneg (c : SerialChain n) (θ : Fin n → ℝ) :
    0 ≤ c.inverseConditionNumber θ :=
  div_nonneg (c.minSingularValue_nonneg θ) (LinearMap.singularValues_nonneg _ _)

/-- The inverse condition number (MLS Example 3.15, p. 128) is at most `1`. -/
theorem inverseConditionNumber_le_one (c : SerialChain n) (θ : Fin n → ℝ) :
    c.inverseConditionNumber θ ≤ 1 :=
  div_le_one_of_le₀ (c.minSingularValue_le_maxSingularValue θ)
    (LinearMap.singularValues_nonneg _ _)

/-- The minimum singular value of the body Jacobian vanishes exactly when the Jacobian has rank
below `n` (for `0 < n`; MLS p. 128, "if a matrix is singular, then at least one of its singular
values is zero"). -/
theorem minSingularValue_eq_zero_iff_rank_lt (c : SerialChain n) (θ : Fin n → ℝ) (hn₀ : 0 < n) :
    c.minSingularValue θ = 0 ↔ (c.bodyJacobianMatrix θ).rank < n := by
  rw [minSingularValue, jacobianSingularValues,
    LinearMap.singularValues_eq_zero_iff_le_finrank_range,
    ← rank_eq_finrank_range_toEuclideanLin]
  omega

/-- **MLS Example 3.14, p. 128: "At a singular configuration, the minimum singular value of `J`
is zero"**, with the converse: for `0 < n ≤ 6`, `μ₁(θ) = 0` exactly when `θ` is singular in the
sense of p. 123 (`SerialChain.IsSingular`). -/
theorem minSingularValue_eq_zero_iff_isSingular (c : SerialChain n) (θ : Fin n → ℝ)
    (hn₀ : 0 < n) (hn : n ≤ 6) :
    c.minSingularValue θ = 0 ↔ c.IsSingular θ := by
  rw [c.minSingularValue_eq_zero_iff_rank_lt θ hn₀, rank_bodyJacobianMatrix, IsSingular,
    min_eq_right hn]

/-- **MLS Example 3.15, p. 128: "At a singular configuration, the inverse condition number is
zero"**, with the converse: for `0 < n ≤ 6`, `μ₂(θ) = 0` exactly when `θ` is singular
(`SerialChain.IsSingular`, p. 123). -/
theorem inverseConditionNumber_eq_zero_iff_isSingular (c : SerialChain n) (θ : Fin n → ℝ)
    (hn₀ : 0 < n) (hn : n ≤ 6) :
    c.inverseConditionNumber θ = 0 ↔ c.IsSingular θ := by
  rw [← c.minSingularValue_eq_zero_iff_isSingular θ hn₀ hn, inverseConditionNumber,
    div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact le_antisymm (h ▸ c.minSingularValue_le_maxSingularValue θ)
        (c.minSingularValue_nonneg θ)
  · exact Or.inl

/-! ### The determinant (MLS Example 3.16, p. 129) -/

/-- The order-preserving identification of `Fin 3 ⊕ Fin 3` (the twist rows `v`, then `ω`) with
the six joints `Fin 6`, `finSumFinEquiv`, used to square the `6 × 6` Jacobian. -/
private def jointIndex : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

/-- **MLS Example 3.16, p. 129: `μ₃(θ) = det J(θ)`** for a six-joint chain, with `J` the body
Jacobian. The `6 × 6` matrix has rows `(v, ω)` (indexed by `Fin 3 ⊕ Fin 3`) and columns the joints;
the columns are indexed through the order-preserving `finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6`, so
the value is the determinant of the book's matrix (`jacobianDet_eq_det_square`). -/
def jacobianDet (c : SerialChain 6) (θ : Fin 6 → ℝ) : ℝ :=
  ((c.bodyJacobianMatrix θ).submatrix id jointIndex).det

/-- `μ₃` (MLS Example 3.16, p. 129) is the determinant of the `6 × 6` body Jacobian with rows
`v_x, v_y, v_z, ω_x, ω_y, ω_z` and columns joints `1 … 6`, both in the printed order. -/
theorem jacobianDet_eq_det_square (c : SerialChain 6) (θ : Fin 6 → ℝ) :
    c.jacobianDet θ = ((c.bodyJacobianMatrix θ).submatrix finSumFinEquiv.symm id).det := by
  rw [jacobianDet, ← Matrix.det_submatrix_equiv_self jointIndex]
  congr 1
  ext r s
  simp [jointIndex]

/-- **MLS p. 128: the choice of spatial or body Jacobian does not change `μ₃`.** The determinant
of the spatial Jacobian (eq. (3.54)) equals that of the body Jacobian, because
`Jˢ = Ad_{g_st(θ)} Jᵇ` (eq. (3.56)) and `det Ad_g = 1`. -/
theorem jacobianDet_eq_det_spatial (c : SerialChain 6) (θ : Fin 6 → ℝ) :
    c.jacobianDet θ = ((c.spatialJacobianMatrix θ).submatrix id finSumFinEquiv).det := by
  have h : (c.spatialJacobianMatrix θ).submatrix id finSumFinEquiv =
      Twist.adjointMatrix (c.fk θ) * (c.bodyJacobianMatrix θ).submatrix id jointIndex := by
    rw [spatialJacobianMatrix_eq_adjointMatrix_mul]
    ext r s
    simp [Matrix.mul_apply, jointIndex]
  rw [h, Matrix.det_mul, Twist.det_adjointMatrix, one_mul, jacobianDet]

/-- **MLS Example 3.16, p. 129: the determinant vanishes exactly at the singular
configurations** of a six-joint chain (p. 123: "the failure of the `6 × 6` Jacobian to be
invertible"). -/
theorem jacobianDet_eq_zero_iff_isSingular (c : SerialChain 6) (θ : Fin 6 → ℝ) :
    c.jacobianDet θ = 0 ↔ c.IsSingular θ := by
  rw [c.isSingular_iff_not_linearIndependent_bodyJacobian θ le_rfl, jacobianDet,
    ← not_iff_not, not_not, ← ne_eq, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : ((c.bodyJacobianMatrix θ).submatrix id jointIndex).col =
      (Twist.coordinatesEquiv : Twist →ₗ[ℝ] (Fin 3 ⊕ Fin 3 → ℝ)) ∘
        (c.bodyJacobian θ ∘ jointIndex) := by
    funext s
    rfl
  rw [hcol, LinearMap.linearIndependent_iff _ (LinearEquiv.ker Twist.coordinatesEquiv),
    linearIndependent_equiv]

/-- **MLS p. 129: `|det J(θ)|` is the product of the singular values.** For a six-joint chain the
absolute value of `μ₃` (Example 3.16) is `σ₀ σ₁ ⋯ σ₅`, the product of the six singular values of
the body Jacobian. The book writes "`det J(θ)` is the product of the singular values"; the
determinant can be negative, so the product is its absolute value. -/
theorem abs_jacobianDet_eq_prod_singularValues (c : SerialChain 6) (θ : Fin 6 → ℝ) :
    |c.jacobianDet θ| = ∏ i ∈ Finset.range 6, c.jacobianSingularValues θ i := by
  set J := c.bodyJacobianMatrix θ
  set T := Matrix.toEuclideanLin J
  have hprod : T.normDet = ∏ i ∈ Finset.range 6, c.jacobianSingularValues θ i := by
    rw [LinearMap.normDet_eq_prod_singularValues, finrank_euclideanSpace_fin]
    rfl
  have hsq : T.normDet ^ 2 = (Jᵀ * J).det := by
    have h := T.normDet_sq
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.toLpLin_mul_same] at h
    have hdet : LinearMap.det (Matrix.toLpLin 2 2 (Jᵀ * J)) = (Jᵀ * J).det :=
      LinearMap.det_toLin (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis (Jᵀ * J)
    rw [hdet] at h
    simpa using h
  have hJ : (Jᵀ * J).det = (c.jacobianDet θ) ^ 2 := by
    have hm : (J.submatrix id jointIndex)ᵀ * J.submatrix id jointIndex =
        (Jᵀ * J).submatrix jointIndex jointIndex := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at h
    rw [jacobianDet, sq, h]
  rw [← hprod, ← Real.sqrt_sq (abs_nonneg (c.jacobianDet θ)), sq_abs, ← hJ, ← hsq,
    Real.sqrt_sq (LinearMap.normDet_nonneg T)]

/-! ### Moving in every direction -/

private instance : FiniteDimensional ℝ Twist :=
  LinearEquiv.finiteDimensional Twist.coordinatesEquiv.symm

private theorem finrank_twist : finrank ℝ Twist = 6 := by
  rw [Twist.coordinatesEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

/-- **MLS p. 129: a nonsingular configuration of a six-joint chain allows every end-effector
velocity.** For `n = 6`, `θ` is not singular (p. 123) exactly when every twist `V` is
`Jˢ(θ) θ̇ = ∑ᵢ θ̇ᵢ ξᵢ'` for some joint rate `θ̇` (eq. (3.54)): the manipulator "can move
infinitesimally in any direction". The same holds for the body Jacobian, by eq. (3.56). -/
theorem not_isSingular_iff_forall_exists_rate (c : SerialChain 6) (θ : Fin 6 → ℝ) :
    ¬ c.IsSingular θ ↔ ∀ V : Twist, ∃ θ' : Fin 6 → ℝ, ∑ i, θ' i • c.spatialJacobian θ i = V := by
  rw [c.isSingular_iff_not_linearIndependent θ le_rfl, not_not]
  have hcard : Fintype.card (Fin 6) = finrank ℝ Twist := by rw [finrank_twist, Fintype.card_fin]
  constructor
  · intro h V
    have hV : V ∈ Submodule.span ℝ (Set.range (c.spatialJacobian θ)) := by
      rw [h.span_eq_top_of_card_eq_finrank' hcard]
      exact Submodule.mem_top
    exact Submodule.mem_span_range_iff_exists_fun ℝ |>.mp hV
  · intro h
    apply linearIndependent_of_top_le_span_of_card_eq_finrank _ hcard
    intro V _
    exact Submodule.mem_span_range_iff_exists_fun ℝ |>.mpr (h V)

/-! ### The alternative dextrous workspace (MLS eq. (3.61), p. 129) -/

/-- **MLS eq. (3.61), p. 129: the alternative dextrous workspace**
`W′_D = {g_st(θ) : θ ∈ Q, μ(θ) ≠ 0} ⊂ SE(3)` for a manipulability measure `μ` (one of
`minSingularValue`, `inverseConditionNumber`, or `jacobianDet` for six joints). The joint space
`Q` is explicit, as for the workspaces of eqs. (3.11)–(3.13). Unlike the dextrous workspace of
eq. (3.13), it is a set of poses, not of positions. -/
def alternativeDextrousWorkspace (c : SerialChain n) (Q : Set (Fin n → ℝ))
    (μ : (Fin n → ℝ) → ℝ) : Set RigidTransform :=
  c.fk '' {θ | θ ∈ Q ∧ μ θ ≠ 0}

/-- The alternative dextrous workspace (MLS eq. (3.61), p. 129) with `Q` the chain's own
admissible joint set `c.admissible` (MLS p. 84). -/
def admissibleAlternativeDextrousWorkspace (c : SerialChain n) (μ : (Fin n → ℝ) → ℝ) :
    Set RigidTransform :=
  c.alternativeDextrousWorkspace c.admissible μ

/-- The alternative dextrous workspace (MLS eq. (3.61), p. 129) lies in the complete workspace
(eq. (3.11), p. 95) over the same joint space. -/
theorem alternativeDextrousWorkspace_subset_completeWorkspace (c : SerialChain n)
    (Q : Set (Fin n → ℝ)) (μ : (Fin n → ℝ) → ℝ) :
    c.alternativeDextrousWorkspace Q μ ⊆ c.completeWorkspace Q :=
  Set.image_mono fun _ h => h.1

/-- For a measure that vanishes exactly at the singular configurations (MLS p. 123), the
alternative dextrous workspace of eq. (3.61), p. 129, is the image of the nonsingular
configurations in `Q`. -/
theorem alternativeDextrousWorkspace_eq_of_iff (c : SerialChain n) (Q : Set (Fin n → ℝ))
    {μ : (Fin n → ℝ) → ℝ} (hμ : ∀ θ, μ θ = 0 ↔ c.IsSingular θ) :
    c.alternativeDextrousWorkspace Q μ = c.fk '' {θ | θ ∈ Q ∧ ¬ c.IsSingular θ} := by
  simp only [alternativeDextrousWorkspace, ne_eq, hμ]

/-- **MLS eq. (3.61), p. 129, with `μ₁ = σ_min`.** For `0 < n ≤ 6`, `W′_D` defined by the minimum
singular value (Example 3.14) is the image of the nonsingular configurations in `Q`. -/
theorem alternativeDextrousWorkspace_minSingularValue (c : SerialChain n) (Q : Set (Fin n → ℝ))
    (hn₀ : 0 < n) (hn : n ≤ 6) :
    c.alternativeDextrousWorkspace Q c.minSingularValue =
      c.fk '' {θ | θ ∈ Q ∧ ¬ c.IsSingular θ} :=
  c.alternativeDextrousWorkspace_eq_of_iff Q fun θ =>
    c.minSingularValue_eq_zero_iff_isSingular θ hn₀ hn

/-- **MLS eq. (3.61), p. 129, with `μ₂ = σ_min / σ_max`.** For `0 < n ≤ 6`, `W′_D` defined by the
inverse condition number (Example 3.15) is the image of the nonsingular configurations in `Q`. -/
theorem alternativeDextrousWorkspace_inverseConditionNumber (c : SerialChain n)
    (Q : Set (Fin n → ℝ)) (hn₀ : 0 < n) (hn : n ≤ 6) :
    c.alternativeDextrousWorkspace Q c.inverseConditionNumber =
      c.fk '' {θ | θ ∈ Q ∧ ¬ c.IsSingular θ} :=
  c.alternativeDextrousWorkspace_eq_of_iff Q fun θ =>
    c.inverseConditionNumber_eq_zero_iff_isSingular θ hn₀ hn

/-- **MLS eq. (3.61), p. 129, with `μ₃ = det J`.** For a six-joint chain, `W′_D` defined by the
determinant (Example 3.16) is the image of the nonsingular configurations in `Q`; so the three
measures of the page give the same `W′_D` ("for any of the measures given above"). -/
theorem alternativeDextrousWorkspace_jacobianDet (c : SerialChain 6) (Q : Set (Fin 6 → ℝ)) :
    c.alternativeDextrousWorkspace Q c.jacobianDet = c.fk '' {θ | θ ∈ Q ∧ ¬ c.IsSingular θ} :=
  c.alternativeDextrousWorkspace_eq_of_iff Q fun θ => c.jacobianDet_eq_zero_iff_isSingular θ

/-- **MLS p. 129: "`W′_D` is the set of end-effector configurations for which the manipulator can
move infinitesimally in any direction."** For a six-joint chain and any of the three measures (here
`μ₃`; the others give the same set), a pose lies in `W′_D` exactly when it is reached at a
configuration `θ ∈ Q` at which every twist is `Jˢ(θ) θ̇` for some joint rate `θ̇`. -/
theorem mem_alternativeDextrousWorkspace_iff_forall (c : SerialChain 6) (Q : Set (Fin 6 → ℝ))
    (g : RigidTransform) :
    g ∈ c.alternativeDextrousWorkspace Q c.jacobianDet ↔
      ∃ θ ∈ Q, c.fk θ = g ∧
        ∀ V : Twist, ∃ θ' : Fin 6 → ℝ, ∑ i, θ' i • c.spatialJacobian θ i = V := by
  rw [alternativeDextrousWorkspace_jacobianDet]
  constructor
  · rintro ⟨θ, ⟨hQ, hs⟩, rfl⟩
    exact ⟨θ, hQ, rfl, (c.not_isSingular_iff_forall_exists_rate θ).mp hs⟩
  · rintro ⟨θ, hQ, rfl, hV⟩
    exact ⟨θ, ⟨hQ, (c.not_isSingular_iff_forall_exists_rate θ).mpr hV⟩, rfl⟩

end SerialChain

end RoboLean
