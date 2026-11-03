import RoboLean.Geometry.RigidTransform

/-!
# No global three-parameter representation of `SO(3)` (MLS p. 33)

MLS Chapter 2, printed p. 33, after the ZYX Euler angles: "It is a fundamental topological fact
that singularities can never be eliminated in any 3-dimensional representation of `SO(3)`. This
situation is similar to that of attempting to find a global coordinate chart on a sphere, which
also fails."

Reading (stated here): a 3-dimensional representation without singularities would be a global
chart, a homeomorphism from `SO(3)` onto an open subset of `ℝ³`. Proved: `SO(3)` (the library's
`Rotation`, with the subspace topology of `3 × 3` matrices) is compact, and no continuous map from
`SO(3)` to `ℝ³` has an open range, so no global chart exists. The proof is the compactness
argument: the range would be a nonempty compact open subset of the connected, noncompact `ℝ³`.
The statement concerns homeomorphisms; the differential claim that every smooth three-parameter
map onto `SO(3)` has a singular point is not formalized here.
-/

noncomputable section

open Matrix Set

namespace RoboLean.Rotation

/-- MLS p. 24 with p. 33: `SO(3)`, as a set of `3 × 3` real matrices (eq. (2.2), `RᵀR = I`,
`det R = 1`), is compact: it is closed and its entries lie in `[-1, 1]`. -/
theorem isCompact_specialOrthogonalGroup :
    IsCompact (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have hset : (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
      {M | Mᵀ * M = 1} ∩ {M | M.det = 1} := by
    ext M
    simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  have hc1 : Continuous fun M : Matrix (Fin 3) (Fin 3) ℝ => Mᵀ * M :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_transpose.matrix_mul
      (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ))
  have hc2 : Continuous fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det :=
    (continuous_id (X := Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  have hclosed : IsClosed ({M : Matrix (Fin 3) (Fin 3) ℝ | Mᵀ * M = 1} ∩ {M | M.det = 1}) :=
    (isClosed_eq hc1 continuous_const).inter (isClosed_eq hc2 continuous_const)
  have hbox : IsCompact ((Set.univ.pi fun _ : Fin 3 => Set.univ.pi fun _ : Fin 3 =>
      Set.Icc (-1 : ℝ) 1) : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  rw [hset]
  refine hbox.of_isClosed_subset hclosed ?_
  rintro (M : Matrix (Fin 3) (Fin 3) ℝ) ⟨hM, -⟩ i - j -
  have h := congrFun (congrFun (show Mᵀ * M = 1 from hM) j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have hle : M i j * M i j ≤ 1 :=
    h ▸ Finset.single_le_sum (fun k _ => mul_self_nonneg (M k j)) (Finset.mem_univ i)
  constructor <;> nlinarith

/-- MLS p. 33: `SO(3)` (the library's `Rotation`) is a compact topological space. -/
theorem compactSpace_rotation : CompactSpace Rotation := by
  exact isCompact_iff_compactSpace.mp isCompact_specialOrthogonalGroup

/-- **MLS p. 33, no global representation**: no continuous map from `SO(3)` to `ℝ³` has an open
range. -/
theorem not_isOpen_range_of_continuous {f : Rotation → EuclideanSpace ℝ (Fin 3)}
    (hf : Continuous f) : ¬ IsOpen (Set.range f) := by
  intro hopen
  have := compactSpace_rotation
  have hc : IsCompact (Set.range f) := isCompact_range hf
  have hclopen : IsClopen (Set.range f) := ⟨hc.isClosed, hopen⟩
  have huniv : Set.range f = Set.univ := hclopen.eq_univ (Set.range_nonempty f)
  rw [huniv] at hc
  exact noncompact_univ (EuclideanSpace ℝ (Fin 3)) hc

/-- **MLS p. 33, "singularities can never be eliminated in any 3-dimensional representation of
`SO(3)`"**, read as the nonexistence of a global chart: there is no homeomorphism from `SO(3)`
onto an open subset of `ℝ³`. -/
theorem not_exists_homeomorph_isOpen :
    ¬ ∃ (U : Set (EuclideanSpace ℝ (Fin 3))) (_ : Rotation ≃ₜ U), IsOpen U := by
  rintro ⟨U, e, hU⟩
  refine not_isOpen_range_of_continuous (f := fun R => (e R : EuclideanSpace ℝ (Fin 3)))
    (continuous_subtype_val.comp e.continuous) ?_
  have : Set.range (fun R => (e R : EuclideanSpace ℝ (Fin 3))) = U := by
    ext x
    constructor
    · rintro ⟨R, rfl⟩
      exact (e R).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  rw [this]
  exact hU

end RoboLean.Rotation
