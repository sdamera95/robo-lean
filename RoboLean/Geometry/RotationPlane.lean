import RoboLean.Geometry.HatPowers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A right-handed orthonormal basis adapted to a unit axis

These Euclidean linear-algebra helpers support the planar reduction in the
axis-angle proof. They do not assume a rotation representation theorem. The
basis is ordered `![ω, u, ω × u]`, with both initial vectors unit and orthogonal.
-/

noncomputable section

open Matrix

namespace RoboLean.Vec3

/-- Every unit axis has a perpendicular unit vector in Euclidean three-space. -/
theorem exists_unit_orthogonal (ω : Vec3) (hω : ‖ω‖ = 1) :
    ∃ u : Vec3, ‖u‖ = 1 ∧ inner ℝ ω u = 0 := by
  have hω0 : ω ≠ 0 := by
    intro h
    simp [h] at hω
  letI : Fact (Module.finrank ℝ Vec3 = 2 + 1) := ⟨by simp [Vec3]⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := Vec3) 2 hω0
  refine ⟨(b 0 : Vec3), b.orthonormal.norm_eq_one 0, ?_⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property

/-- Cross product is orthogonal to its first argument, in the Euclidean inner product. -/
@[simp] theorem inner_cross_left (v w : Vec3) : inner ℝ v (cross v w) = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, cross_coordinates, star_trivial]
  rw [dotProduct_comm, dot_self_cross]

/-- Cross product is orthogonal to its second argument. -/
@[simp] theorem inner_cross_right (v w : Vec3) : inner ℝ w (cross v w) = 0 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, cross_coordinates, star_trivial]
  rw [dotProduct_comm, dot_cross_self]

/-- The Euclidean squared-norm identity for the right-handed cross product. -/
theorem norm_cross_sq (v w : Vec3) :
    ‖cross v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 - (inner ℝ v w) ^ 2 := by
  have h : inner ℝ (cross v w) (cross v w) =
      inner ℝ v v * inner ℝ w w - inner ℝ v w * inner ℝ w v := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, cross_coordinates, star_trivial]
    rw [cross_dot_cross]
    ring
  simpa only [real_inner_self_eq_norm_sq, real_inner_comm w v, pow_two] using h

/-- The third vector of the adapted frame has unit Euclidean norm. -/
theorem norm_cross_of_unit_orthogonal (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    ‖cross ω u‖ = 1 := by
  have h := norm_cross_sq ω u
  rw [hω, hu, hperp] at h
  nlinarith [norm_nonneg (cross ω u)]

/-- The ordered frame is orthonormal; its third vector fixes the handedness. -/
theorem orthonormal_adapted (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    Orthonormal ℝ ![ω, u, cross ω u] := by
  simp [orthonormal_vecCons_iff, Fin.forall_fin_succ, hω, hu, hperp,
    norm_cross_of_unit_orthogonal ω u hω hu hperp]

/-- The full orthonormal basis associated with a unit axis and perpendicular unit vector. -/
def adaptedBasis (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    OrthonormalBasis (Fin 3) ℝ Vec3 :=
  (basisOfOrthonormalOfCardEqFinrank (orthonormal_adapted ω u hω hu hperp)
    (by simp [Vec3])).toOrthonormalBasis (by
      simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using
        orthonormal_adapted ω u hω hu hperp)

@[simp] theorem coe_adaptedBasis (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    (adaptedBasis ω u hω hu hperp : Fin 3 → Vec3) = ![ω, u, cross ω u] := by
  simp [adaptedBasis]

@[simp] theorem adaptedBasis_zero (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    adaptedBasis ω u hω hu hperp 0 = ω := by
  rw [coe_adaptedBasis]
  rfl

@[simp] theorem adaptedBasis_one (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    adaptedBasis ω u hω hu hperp 1 = u := by
  rw [coe_adaptedBasis]
  rfl

@[simp] theorem adaptedBasis_two (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) :
    adaptedBasis ω u hω hu hperp 2 = cross ω u := by
  rw [coe_adaptedBasis]
  rfl

/-- Exact coordinates in the adapted basis, for every Euclidean vector. -/
theorem adapted_decomposition (ω u : Vec3)
    (hω : ‖ω‖ = 1) (hu : ‖u‖ = 1) (hperp : inner ℝ ω u = 0) (v : Vec3) :
    v = inner ℝ ω v • ω + inner ℝ u v • u +
      inner ℝ (cross ω u) v • cross ω u := by
  have h := (adaptedBasis ω u hω hu hperp).sum_repr' v
  simpa [OrthonormalBasis.repr_apply_apply, Fin.sum_univ_succ, add_assoc] using h.symm

end RoboLean.Vec3
