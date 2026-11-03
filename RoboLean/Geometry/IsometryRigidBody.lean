import RoboLean.Geometry.CrossProduct
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Rigid body transformations as maps of `ℝ³` (Definition 2.1) and their converse

MLS Definition 2.1, p. 21, calls a map `g : ℝ³ → ℝ³` a rigid body transformation when it
preserves lengths, `‖g(p) - g(q)‖ = ‖p - q‖`, and cross products, `g_*(v × w) = g_*(v) × g_*(w)`,
where the action on vectors is defined by differences of points, `g_*(v) = g(q) - g(p)` for
`v = q - p` (p. 21). The chapter then represents every rigid motion by a pair
`(p, R) ∈ SE(3)` (p. 35) without stating the converse of Definition 2.1 as a theorem. This file
states Definition 2.1 for maps `Vec3 → Vec3` with `g_*` by differences, as printed, and proves that
the maps it describes are exactly the point actions of `RigidTransform`.

Convention: the difference `g(p + v) - g(p)` is the vector action at the base point `p`;
Definition 2.1 requires the cross-product clause at every base point. The converse direction
uses the clause at the origin only, so it is stated with that weaker hypothesis. The length
clause is read with the Euclidean norm of `Vec3`; an isometry of a strictly convex normed space
is affine (Mathlib's `Isometry.affineIsometryOfStrictConvexSpace`, which needs no surjectivity),
and the cross-product clause forces the determinant of its linear part to be `+1`.
-/

open Matrix

namespace RoboLean

/-- MLS Definition 2.1, p. 21: a map `g : ℝ³ → ℝ³` is a rigid body transformation when lengths are
preserved, `‖g(p) - g(q)‖ = ‖p - q‖`, and the cross product is preserved,
`g_*(v × w) = g_*(v) × g_*(w)`. Convention: `g_*` is defined by differences of points as on
p. 21, `g_*(v) = g(p + v) - g(p)`, and the cross-product clause is required at every base
point `p`. -/
structure IsRigidBodyTransformation (g : Vec3 → Vec3) : Prop where
  /-- Length is preserved, MLS Definition 2.1, property 1, p. 21. -/
  norm_sub : ∀ p q, ‖g p - g q‖ = ‖p - q‖
  /-- The cross product is preserved, MLS Definition 2.1, property 2, p. 21, with
  `g_*(v) = g(p + v) - g(p)` at the base point `p`. -/
  cross : ∀ p v w, g (p + Vec3.cross v w) - g p = Vec3.cross (g (p + v) - g p) (g (p + w) - g p)

/-- The converse of MLS Definition 2.1, p. 21, in the representation of p. 35: a map of `ℝ³`
that preserves lengths and preserves cross products at the origin, with `g_*` by differences
(`g_*(v) = g(v) - g(0)`, p. 21), is the point action `x ↦ R x + p` of some `(p, R) ∈ SE(3)`,
equation (2.22), p. 35. Euclidean norm of `Vec3`; the rotation has determinant `+1`. -/
theorem exists_rigidTransform_of_norm_sub_of_cross (g : Vec3 → Vec3)
    (hn : ∀ p q, ‖g p - g q‖ = ‖p - q‖)
    (hc : ∀ v w, g (Vec3.cross v w) - g 0 = Vec3.cross (g v - g 0) (g w - g 0)) :
    ∃ T : RigidTransform, ∀ x, g x = T.applyPoint x := by
  have hi : Isometry g := Isometry.of_dist_eq (fun p q => by rw [dist_eq_norm, dist_eq_norm, hn])
  set A := hi.affineIsometryOfStrictConvexSpace
  set L : Vec3 →ₗ[ℝ] Vec3 := A.linearIsometry.toLinearMap
  have hL : ∀ x, g x - g 0 = L x := by
    intro x
    have := A.map_vsub x 0
    simpa [A, L] using this.symm
  have hinner : ∀ x y, inner ℝ (L x) (L y) = inner ℝ x y := fun x y =>
    A.linearIsometry.inner_map_map x y
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.toEuclideanLin.symm L
  have hM : ∀ x, Matrix.toEuclideanLin M x = L x := by
    intro x; simp [M]
  have hcol : ∀ i k, M k i = L (EuclideanSpace.single i 1) k := by
    intro i k
    rw [← hM]
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have horth : Mᵀ * M = 1 := by
    ext i j
    have := hinner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol]
    rw [dotProduct_comm] at this
    simp only [dotProduct] at this
    rw [this]
    simp [Matrix.one_apply, eq_comm]
  have hcross : ∀ v w, L (Vec3.cross v w) = Vec3.cross (L v) (L w) := by
    intro v w; rw [← hL, ← hL, ← hL, hc]
  have e01 : Vec3.cross (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) =
      EuclideanSpace.single 2 1 := by
    apply WithLp.ofLp_injective
    ext i; fin_cases i <;> simp [Vec3.cross_coordinates, crossProduct]
  have hdet : M.det = 1 := by
    set c : Fin 3 → (Fin 3 → ℝ) := fun i => WithLp.ofLp (L (EuclideanSpace.single i 1))
    have hT : Mᵀ = ![c 0, c 1, c 2] := by
      ext i k; fin_cases i <;> simp [c, hcol]
    have h2 : c 2 = crossProduct (c 0) (c 1) := by
      simp only [c]; rw [← e01, hcross]; rfl
    have hn2 : c 2 ⬝ᵥ c 2 = 1 := by
      have := hinner (EuclideanSpace.single 2 1) (EuclideanSpace.single 2 1)
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
      simpa [c] using this
    rw [← Matrix.det_transpose, hT]
    have := triple_product_eq_det (c 0) (c 1) (c 2)
    rw [← this, triple_product_permutation, triple_product_permutation, ← h2, hn2]
  refine ⟨⟨⟨M, ?_⟩, g 0⟩, fun x => ?_⟩
  · rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
    exact ⟨horth, hdet⟩
  · simp only [RigidTransform.applyPoint, Rotation.act]
    change g x = Matrix.toEuclideanLin M x + g 0
    rw [hM, ← hL]; abel

/-- MLS Definition 2.1, p. 21, characterized by the representation of p. 35: a map
`g : ℝ³ → ℝ³` is a rigid body transformation exactly when it is the point action
`x ↦ R x + p` of some `(p, R) ∈ SE(3)`, equations (2.21)–(2.22). The direction from `SE(3)` uses
Proposition 2.7, p. 38; the converse is `exists_rigidTransform_of_norm_sub_of_cross`. -/
theorem isRigidBodyTransformation_iff (g : Vec3 → Vec3) :
    IsRigidBodyTransformation g ↔ ∃ T : RigidTransform, g = T.applyPoint := by
  constructor
  · intro hg
    obtain ⟨T, hT⟩ := exists_rigidTransform_of_norm_sub_of_cross g hg.norm_sub
      (fun v w => by simpa using hg.cross 0 v w)
    exact ⟨T, funext hT⟩
  · rintro ⟨T, rfl⟩
    refine ⟨fun p q => ?_, fun p v w => ?_⟩
    · rw [T.applyPoint_sub_applyPoint, T.norm_applyVector]
    · simp only [T.applyPoint_sub_applyPoint, add_sub_cancel_left, T.applyVector_cross]

/-- The vector action of MLS p. 21 is well defined for a rigid body transformation: the
difference `g(q) - g(p)` depends only on `v = q - p`, and equals `R v` for the rotation of the
representing pair, MLS p. 36. Definition 2.1, p. 21. -/
theorem IsRigidBodyTransformation.sub_eq_sub {g : Vec3 → Vec3} (hg : IsRigidBodyTransformation g)
    (p q r s : Vec3) (h : q - p = s - r) : g q - g p = g s - g r := by
  obtain ⟨T, rfl⟩ := (isRigidBodyTransformation_iff g).mp hg
  rw [T.applyPoint_sub_applyPoint, T.applyPoint_sub_applyPoint, h]

/-- The first consequence of MLS Definition 2.1 drawn on pp. 21–22: a rigid body transformation
preserves inner products of vectors, `v₁ᵀ v₂ = g_*(v₁)ᵀ g_*(v₂)` (the book argues by the
polarization identity). Convention: `g_*(v) = g(p + v) - g(p)` at any base point `p`. -/
theorem IsRigidBodyTransformation.inner_sub {g : Vec3 → Vec3} (hg : IsRigidBodyTransformation g)
    (p v w : Vec3) : inner ℝ (g (p + v) - g p) (g (p + w) - g p) = inner ℝ v w := by
  obtain ⟨T, rfl⟩ := (isRigidBodyTransformation_iff g).mp hg
  simp only [T.applyPoint_sub_applyPoint, add_sub_cancel_left, T.inner_applyVector]

end RoboLean
