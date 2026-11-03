import RoboLean.Grasp.SpatialGrasp

/-!
# Exercise 2(c): three point contacts with friction on a sphere

MLS Chapter 5, Exercise 2(c), printed p. 259: "Construct the grasp map for the grasps shown below
and write the friction cone conditions with respect to the contact basis you choose. Determine if
the grasp is force-closure. Assume that all contacts are point contacts with friction", grasp (c)
with `µ > 0`.

Figure reading (p. 259, rendered at 220 dpi): a sphere with one contact pushing down at the top
of its meridian and two horizontal contacts pushing inward at opposite ends of its equator. Here
the sphere is the unit sphere centred at the object origin, with contacts at `(1, 0, 0)`,
`(−1, 0, 0)` and `(0, 0, 1)` (`sphereFrame`); the figure gives no dimensions, and the radius and
the exact placement are this reading.

**Formalized.** With the contact `z`-axes the inward normals (MLS p. 214) and the tangent axes of
`sphereFrame`:

* the grasp map (`sphereGrasp_graspMap`): force
  `(−f₁₃ + f₂₃ + f₃₁, f₁₁ + f₂₁ − f₃₂, −f₁₂ + f₂₂ − f₃₃)` and moment
  `(f₃₂, f₁₂ + f₂₂ + f₃₁, f₁₁ − f₂₁)` (contact `i`, coefficient `j` as `fᵢⱼ`, normal last), with
  the friction cones `√(fᵢ₁² + fᵢ₂²) ≤ µ fᵢ₃` of eq. (5.3);
* the grasp map is surjective (`sphereGrasp_surjective`), the squeeze of the equatorial contacts
  with friction holding up the top contact is a strictly internal force
  (`sphereGrasp_isStrictlyInternalForce`), so the grasp is force-closure for every `µ > 0`
  (`sphereGrasp_isForceClosure`, Proposition 5.2).

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214); nothing here concerns a physical object.
-/

noncomputable section

open Matrix

namespace RoboLean

namespace Grasp

/-- The contact rotation at `(1, 0, 0)` on the unit sphere (MLS Exercise 2(c), p. 259): columns
`x = (0, 1, 0)`, `y = (0, 0, −1)`, `z = (−1, 0, 0)` (the inward normal). -/
def sphereRotationEast : Rotation :=
  ⟨!![0, 0, -1; 1, 0, 0; 0, -1, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- The contact rotation at `(−1, 0, 0)` on the unit sphere (MLS Exercise 2(c), p. 259): columns
`x = (0, 1, 0)`, `y = (0, 0, 1)`, `z = (1, 0, 0)` (the inward normal). -/
def sphereRotationWest : Rotation :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- The contact rotation at `(0, 0, 1)` on the unit sphere (MLS Exercise 2(c), p. 259): columns
`x = (1, 0, 0)`, `y = (0, −1, 0)`, `z = (0, 0, −1)` (the inward normal). -/
def sphereRotationTop : Rotation :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [Matrix.det_fin_three]⟩

/-- The contact frames of MLS Exercise 2(c), printed p. 259, under the figure reading: the unit
sphere with contacts at `(1, 0, 0)`, `(−1, 0, 0)` and `(0, 0, 1)`. -/
def sphereFrame : Fin 3 → RigidTransform :=
  ![⟨sphereRotationEast, WithLp.toLp 2 ![1, 0, 0]⟩, ⟨sphereRotationWest, WithLp.toLp 2 ![-1, 0, 0]⟩,
    ⟨sphereRotationTop, WithLp.toLp 2 ![0, 0, 1]⟩]

/-- The grasp of MLS Exercise 2(c), printed p. 259: three point contacts with friction
(eq. (5.3), `µ > 0`) at the frames `sphereFrame`. -/
def sphereGrasp (μ : ℝ) (hμ : 0 < μ) : SpatialGrasp (Fin 3) fun _ => 3 :=
  ⟨fun _ => ContactModel.pointContact μ hμ, sphereFrame⟩

/-- **The grasp map of MLS Exercise 2(c)**, printed p. 259, computed by the wrench transfer
(2.66): force `(−f₁₃ + f₂₃ + f₃₁, f₁₁ + f₂₁ − f₃₂, −f₁₂ + f₂₂ − f₃₃)` and moment
`(f₃₂, f₁₂ + f₂₂ + f₃₁, f₁₁ − f₂₁)` (book indices from `1`; Lean `f i j` from `0`). -/
theorem sphereGrasp_graspMap (μ : ℝ) (hμ : 0 < μ) (f : Fin 3 → Fin 3 → ℝ) :
    (sphereGrasp μ hμ).graspMap f =
      ⟨WithLp.toLp 2 ![-f 0 2 + f 1 2 + f 2 0, f 0 0 + f 1 0 - f 2 1, -f 0 1 + f 1 1 - f 2 2],
        WithLp.toLp 2 ![f 2 1, f 0 1 + f 1 1 + f 2 0, f 0 0 - f 1 0]⟩ := by
  rw [SpatialGrasp.graspMap_apply, Fin.sum_univ_three]
  simp only [sphereGrasp, ContactModel.pointContact_wrench]
  apply Wrench.ext
  · ext i
    fin_cases i <;>
      simp [Wrench.transform, Rotation.act_apply, sphereFrame, sphereRotationEast,
        sphereRotationWest, sphereRotationTop, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring
  · ext i
    fin_cases i
    all_goals simp [Wrench.transform, Rotation.act_apply, Vec3.cross_coordinates, crossProduct,
      sphereFrame, sphereRotationEast, sphereRotationWest, sphereRotationTop, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring

/-- The grasp map of MLS Exercise 2(c), printed p. 259, is surjective onto the wrenches. -/
theorem sphereGrasp_surjective (μ : ℝ) (hμ : 0 < μ) :
    Function.Surjective (sphereGrasp μ hμ).graspMap := by
  intro F
  refine ⟨![![(F.force 1 + F.torque 0 + F.torque 2) / 2, (F.torque 1 - F.force 2) / 2, 0],
    ![(F.force 1 + F.torque 0 - F.torque 2) / 2, (F.torque 1 + F.force 2) / 2, F.force 0],
    ![0, F.torque 0, 0]], ?_⟩
  rw [sphereGrasp_graspMap]
  apply Wrench.ext
  · ext i
    fin_cases i <;> simp <;> ring
  · ext i
    fin_cases i <;> simp <;> ring

/-- The internal force of MLS Exercise 2(c), printed p. 259: normal forces `2` at the equatorial
contacts with tangential forces `µ` holding up the top contact, which pushes with normal force
`2µ`. -/
def sphereInternalForce (μ : ℝ) : Fin 3 → Fin 3 → ℝ := ![![0, -μ, 2], ![0, μ, 2], ![0, 0, 2 * μ]]

/-- `sphereInternalForce μ` is a strictly internal force (MLS Definition 5.3, printed p. 223) of
the grasp of Exercise 2(c), printed p. 259, for every `µ > 0`. -/
theorem sphereGrasp_isStrictlyInternalForce (μ : ℝ) (hμ : 0 < μ) :
    Grasp.IsStrictlyInternalForce (sphereGrasp μ hμ).graspMap
      ((sphereGrasp μ hμ).cone : Set (Fin 3 → Fin 3 → ℝ)) (sphereInternalForce μ) := by
  refine ⟨?_, ?_⟩
  · rw [sphereGrasp_graspMap]
    apply Wrench.ext
    · ext i
      fin_cases i
      all_goals simp [sphereInternalForce]
      ring
    · ext i
      fin_cases i <;> simp [sphereInternalForce]
  · rw [SpatialGrasp.cone, ContactGrasp.mem_interior_cone]
    intro i
    have hs : √(μ ^ 2) = μ := Real.sqrt_sq hμ.le
    fin_cases i <;> refine Grasp.mem_interior_pointContactCone ?_ ?_ <;>
      simp [sphereInternalForce, hs] <;> nlinarith

/-- **MLS Exercise 2(c)**, printed p. 259, under the figure reading: the three point contacts
with friction on the sphere form a force-closure grasp for every `µ > 0` (Proposition 5.2,
p. 224). Finite-force caveat (MLS p. 214). -/
theorem sphereGrasp_isForceClosure (μ : ℝ) (hμ : 0 < μ) :
    (sphereGrasp μ hμ).toGrasp.IsForceClosure :=
  (Grasp.isForceClosure_iff _).mpr
    ⟨sphereGrasp_surjective μ hμ, _, sphereGrasp_isStrictlyInternalForce μ hμ⟩

end Grasp

end RoboLean
