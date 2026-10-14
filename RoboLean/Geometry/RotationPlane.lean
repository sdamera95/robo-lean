import RoboLean.Geometry.HatPowers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A right-handed orthonormal basis adapted to a unit axis

These Euclidean linear-algebra helpers support the planar reduction in the
axis-angle proof. They do not assume a rotation representation theorem. The
basis is ordered `![ω, u, ω × u]`, with both initial vectors unit and orthogonal.

MLS context (printed pages): these lemmas support the library's proof of
Proposition 2.5 (the exponential map is onto `SO(3)`, pp. 29–30) and Theorem 2.6
(Euler's equivalent-axis theorem, p. 31) in `RoboLean.Geometry.RotationSurjectivity`.
MLS proves Proposition 2.5 by equating matrix entries, not through an adapted
basis, so none of these lemmas has a direct MLS counterpart. The cross product is
the right-handed one of MLS p. 26, equations (2.4)–(2.5), and the third basis
vector `ω × u` makes the frame right-handed in the sense of MLS pp. 23–24
(`r₂ × r₃ = r₁`, equivalently `r₁ × r₂ = r₃`). Coordinates follow
`research/reports/geometry-conventions.md`.

The file also holds `perp`, the projection onto the plane perpendicular to an axis
(MLS pp. 100 and 102), moved here from `RoboLean.Kinematics.PadenKahan` on 2026-10-11, and its
four lemmas `inner_perp`, `norm_perp_sq`, `inner_perp_perp` and `cross_perp`, moved from there on
2026-10-13 (the old `PadenKahan` names are deprecated aliases). The section "Planar rotations"
holds three `SO(2)` lemmas of the planar grasp modules (`Grasp.so2_entries`,
`Grasp.so2_mulVec_transpose_mulVec`, `Grasp.so2_transpose_mulVec_mulVec`), moved from
`RoboLean.Grasp.PlanarWrench` on 2026-10-14.
-/

noncomputable section

open Matrix

namespace RoboLean.Vec3

/-- Supporting lemma; no direct MLS counterpart. Every unit axis has a perpendicular unit vector in
Euclidean three-space; supplies the second adapted basis vector for the library's proof of MLS
Proposition 2.5, pp. 29–30. -/
theorem exists_unit_orthogonal (ω : Vec3) (hω : ‖ω‖ = 1) :
    ∃ u : Vec3, ‖u‖ = 1 ∧ inner ℝ ω u = 0 := by
  have hω0 : ω ≠ 0 := by
    intro h
    simp [h] at hω
  let : Fact (Module.finrank ℝ Vec3 = 2 + 1) := ⟨by simp [Vec3]⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := Vec3) 2 hω0
  refine ⟨(b 0 : Vec3), b.orthonormal.norm_eq_one 0, ?_⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property

/-- Supporting lemma; no direct MLS counterpart. The cross product of MLS p. 26, equations
(2.4)–(2.5), is orthogonal to its first argument, in the Euclidean inner product; supports the
orthonormality of the adapted frame. -/
@[simp] theorem inner_cross_left (v w : Vec3) : inner ℝ v (cross v w) = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, cross_coordinates, star_trivial]
  rw [dotProduct_comm, dot_self_cross]

/-- Supporting lemma; no direct MLS counterpart. The cross product of MLS p. 26, equations
(2.4)–(2.5), is orthogonal to its second argument; supports the orthonormality of the adapted
frame. -/
@[simp] theorem inner_cross_right (v w : Vec3) : inner ℝ w (cross v w) = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, cross_coordinates, star_trivial]
  rw [dotProduct_comm, dot_cross_self]

/-- Supporting lemma; no direct MLS counterpart. The Euclidean squared-norm identity
`‖v × w‖² = ‖v‖² ‖w‖² - (v · w)²` for the right-handed cross product of MLS p. 26; supports
the unit norm of the third adapted basis vector. -/
theorem norm_cross_sq (v w : Vec3) :
    ‖cross v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2 := by
  have h : inner ℝ (cross v w) (cross v w) =
      inner ℝ v v * inner ℝ w w - inner ℝ v w * inner ℝ w v := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, cross_coordinates, star_trivial]
    rw [cross_dot_cross]
    ring
  simpa only [real_inner_self_eq_norm_sq, real_inner_comm w v, pow_two] using h

/-- Supporting lemma; no direct MLS counterpart. The third vector of the adapted frame has unit
Euclidean norm; supports its orthonormality. -/
theorem norm_cross_of_unit_orthogonal (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    ‖cross ω u‖ = 1 := by
  have h := norm_cross_sq ω u
  rw [hω, hu, hperp] at h
  nlinarith [norm_nonneg (cross ω u)]

/-- Supporting lemma; no direct MLS counterpart. The ordered frame is orthonormal, and its third
vector fixes the handedness; supports the construction of `adaptedBasis`. -/
theorem orthonormal_adapted (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    Orthonormal ℝ ![ω, u, cross ω u] := by
  simp [orthonormal_vecCons_iff, Fin.forall_fin_succ, hω, hu, hperp,
    norm_cross_of_unit_orthogonal ω u hω hu hperp]

/-- Supporting lemma; no direct MLS counterpart. The full orthonormal basis associated with a unit
axis and perpendicular unit vector; supports the planar reduction in the library's proof of MLS
Proposition 2.5, pp. 29–30. -/
def adaptedBasis (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    OrthonormalBasis (Fin 3) ℝ Vec3 :=
  (basisOfOrthonormalOfCardEqFinrank (orthonormal_adapted ω u hω hu hperp)
    (by simp [Vec3])).toOrthonormalBasis (by
      simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using
        orthonormal_adapted ω u hω hu hperp)

/-- Supporting lemma; no direct MLS counterpart. The adapted basis is `![ω, u, ω × u]`. -/
@[simp] theorem coe_adaptedBasis (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    (adaptedBasis ω u hω hu hperp : Fin 3 → Vec3) = ![ω, u, cross ω u] := by
  simp [adaptedBasis]

/-- Supporting lemma; no direct MLS counterpart. The first adapted basis vector is `ω`. -/
@[simp] theorem adaptedBasis_zero (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    adaptedBasis ω u hω hu hperp 0 = ω := by
  rw [coe_adaptedBasis]
  rfl

/-- Supporting lemma; no direct MLS counterpart. The second adapted basis vector is `u`. -/
@[simp] theorem adaptedBasis_one (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    adaptedBasis ω u hω hu hperp 1 = u := by
  rw [coe_adaptedBasis]
  rfl

/-- Supporting lemma; no direct MLS counterpart. The third adapted basis vector is
`ω × u`. -/
@[simp] theorem adaptedBasis_two (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    adaptedBasis ω u hω hu hperp 2 = cross ω u := by
  rw [coe_adaptedBasis]
  rfl

/-- Supporting lemma; no direct MLS counterpart. Exact coordinates in the adapted basis, for every
Euclidean vector; supports the planar reduction in the library's proof of MLS Proposition 2.5,
pp. 29–30. -/
theorem adapted_decomposition (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) (v : Vec3) :
    v = inner ℝ ω v • ω + inner ℝ u v • u +
      inner ℝ (cross ω u) v • cross ω u := by
  have h := (adaptedBasis ω u hω hu hperp).sum_repr' v
  simpa [OrthonormalBasis.repr_apply_apply, Fin.sum_univ_succ, add_assoc] using h.symm

/-- The projection `u′ = u - ω ωᵀ u` of a vector onto the plane perpendicular to the axis
direction `ω`, MLS p. 100 (Subproblem 1) and p. 102 (Subproblem 3). It is the orthogonal
projection when `ω` is a unit vector. -/
def perp (ω u : Vec3) : Vec3 := u - inner ℝ ω u • ω

/-- The projected vector `u′` of MLS p. 100 is perpendicular to the unit axis `ω`. -/
theorem inner_perp {ω : Vec3} (hω : ‖ω‖ = 1) (u : Vec3) : inner ℝ ω (Vec3.perp ω u) = 0 := by
  simp [Vec3.perp, inner_sub_right, inner_smul_right, hω]

/-- Pythagoras for the projection of MLS p. 100: `‖u′‖² = ‖u‖² - (ωᵀu)²` for a unit axis. -/
theorem norm_perp_sq {ω : Vec3} (hω : ‖ω‖ = 1) (u : Vec3) :
    ‖Vec3.perp ω u‖ ^ 2 = ‖u‖ ^ 2 - inner ℝ ω u ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [Vec3.perp, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hω, real_inner_comm u ω, RCLike.conj_to_real]
  ring

/-- The inner product of two projections (MLS p. 100): `u′ᵀv′ = uᵀv - (ωᵀu)(ωᵀv)` for a unit
axis. -/
theorem inner_perp_perp {ω : Vec3} (hω : ‖ω‖ = 1) (u v : Vec3) :
    inner ℝ (Vec3.perp ω u) (Vec3.perp ω v) = inner ℝ u v - inner ℝ ω u * inner ℝ ω v := by
  simp only [Vec3.perp, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hω, real_inner_comm u ω, real_inner_comm v ω,
    RCLike.conj_to_real]
  ring

/-- Supporting lemma: the cross product with the axis does not see the axial component,
`ω × u′ = ω × u`. -/
theorem cross_perp (ω u : Vec3) : Vec3.cross ω (Vec3.perp ω u) = Vec3.cross ω u := by
  apply WithLp.ofLp_injective
  simp [Vec3.perp, cross_coordinates, map_sub, map_smul, cross_self]

end RoboLean.Vec3

/-! ### Planar rotations

Supporting lemmas on `SO(2)` (Mathlib's `specialOrthogonalGroup (Fin 2) ℝ`) for the planar
contact frames of MLS printed pp. 222 and 232, moved from `RoboLean.Grasp.PlanarWrench` on
2026-10-14 with their full names `RoboLean.Grasp.*` unchanged. -/

namespace RoboLean.Grasp

/-- Entries of a planar rotation (supporting lemma for MLS printed pp. 222 and 232):
`R = [[a, -c], [c, a]]` with `a² + c² = 1` (Mathlib
`Matrix.mem_specialOrthogonalGroup_fin_two_iff`). -/
theorem so2_entries (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    (R : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
      (R : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ∧
      (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp R.2
  refine ⟨h1.symm, h2, ?_⟩
  rw [h2] at h3
  linarith

/-- `R Rᵀ d = d` for a planar rotation (supporting lemma for MLS printed pp. 222, 232). -/
theorem so2_mulVec_transpose_mulVec (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (d : Fin 2 → ℝ) :
    (R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ((R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ d) = d := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- `Rᵀ R f = f` for a planar rotation (supporting lemma for MLS printed pp. 222, 232). -/
theorem so2_transpose_mulVec_mulVec (R : Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (f : Fin 2 → ℝ) :
    (R : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ ((R : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ f) = f := by
  have h := (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp R.2).1
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

end RoboLean.Grasp
