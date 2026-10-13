import RoboLean.Grasp.GraspMap

/-!
# Spatial antipodal grasps: the "if" direction of Theorem 5.7

MLS Chapter 5, §4.2, printed p. 233: "**Theorem 5.7. Spatial antipodal grasps** [82]. A spatial
grasp with two soft-finger contacts is force-closure if and only if the line connecting the
contact point lies inside both friction cones." No proof is printed.

Here only the "if" direction, for the library's spatial grasp of two soft-finger contacts
(`ContactModel.softFinger`, eq. (5.4), p. 217, `μ > 0`, `γ > 0`) with contact frames
`g_{ocᵢ} = (pᵢ, Rᵢ)` (`ContactGrasp.spatial`, contact `z`-axis the inward normal, pp. 214–215).
"The line lies inside the friction cone at contact `i`" is read, as for Theorem 5.6 (Q6), as the
open cone: the direction `x = Rᵢᵀ (pⱼ - pᵢ)` to the other contact, in contact coordinates,
satisfies `√(x₁² + x₂²) < μ x₃` (the strict form of the Coulomb cone (5.3), which gives interior
points, `mem_interior_pointContactCone`). The "only if" direction is false in the library's
soft-finger model: `Examples.softAntipodal_onlyIf_counterexample` is force-closure with the line
outside the closed cone at one contact (torsion balances the moment of non-collinear forces).

Finite-force caveat: force-closure assumes unbounded contact forces at maintained rigid contacts
(MLS p. 214).
-/

noncomputable section

open Matrix

namespace RoboLean.Grasp

/-- A vector of Euclidean three-space is rebuilt from its three coordinates. -/
private theorem toLp_vec3_eta (v : Vec3) : WithLp.toLp 2 ![v 0, v 1, v 2] = v := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> rfl

/-- The coefficients of a soft-finger contact (MLS eq. (5.4), p. 217) applying the object-frame
force `F` with torsion `t`: the contact-frame coordinates `Rᵀ F`, then `t`. -/
private def softCoef (g : RigidTransform) (F : Vec3) (t : ℝ) : Fin 4 → ℝ :=
  ![(g.rotation⁻¹.act F) 0, (g.rotation⁻¹.act F) 1, (g.rotation⁻¹.act F) 2, t]

/-- The soft-finger contact at frame `g = (p, R)` with coefficients `softCoef g F t` applies, in
object coordinates, the force `F` and the moment `p × F + t R e_z` (MLS eq. (5.4), p. 217, and
the wrench transfer of p. 218). -/
private theorem transform_softCoef {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (g : RigidTransform)
    (F : Vec3) (t : ℝ) :
    Wrench.transform g ((ContactModel.softFinger μ γ hμ hγ).wrench (softCoef g F t)) =
      ⟨F, Vec3.cross g.translation F + t • g.rotation.act Rotation.zAxis⟩ := by
  rw [ContactModel.softFinger_wrench]
  have hz : WithLp.toLp 2 ![(0 : ℝ), 0, softCoef g F t 3] = t • Rotation.zAxis := by
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [softCoef, Rotation.zAxis]
  have hF : WithLp.toLp 2 ![softCoef g F t 0, softCoef g F t 1, softCoef g F t 2] =
      g.rotation⁻¹.act F := toLp_vec3_eta _
  rw [hz, hF]
  simp only [Wrench.transform, Rotation.act_inv_act, map_smul]

/-- The grasp map of two soft-finger contacts on the coefficients `softCoef` (MLS eq. (5.6),
p. 219): net force `F₀ + F₁` and net moment `p₀ × F₀ + t₀ n₀ + p₁ × F₁ + t₁ n₁`. -/
private theorem graspMap_softCoef {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ)
    (frame : Fin 2 → RigidTransform) (F₀ F₁ : Vec3) (t₀ t₁ : ℝ) :
    (ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ) frame).graspMap
        ![softCoef (frame 0) F₀ t₀, softCoef (frame 1) F₁ t₁] =
      ⟨F₀ + F₁, Vec3.cross (frame 0).translation F₀ + t₀ • (frame 0).rotation.act Rotation.zAxis +
        (Vec3.cross (frame 1).translation F₁ + t₁ • (frame 1).rotation.act Rotation.zAxis)⟩ := by
  rw [ContactGrasp.graspMap_apply, Fin.sum_univ_two, ContactGrasp.spatial_contactMap_apply,
    ContactGrasp.spatial_contactMap_apply]
  change Wrench.transform (frame 0) ((ContactModel.softFinger μ γ hμ hγ).wrench
      (softCoef (frame 0) F₀ t₀)) + Wrench.transform (frame 1)
      ((ContactModel.softFinger μ γ hμ hγ).wrench (softCoef (frame 1) F₁ t₁)) = _
  rw [transform_softCoef, transform_softCoef]
  rfl

/-- The direction from contact `i` to contact `j` of a two-contact spatial grasp, written in the
contact frame `Cᵢ`: `Rᵢᵀ (pⱼ - pᵢ)`, with `g_{ocᵢ} = (pᵢ, Rᵢ)` taking contact coordinates to object
coordinates (MLS printed pp. 214–215); coordinate `2` is the component along the inward normal
(MLS Theorem 5.7, printed p. 233, "the line connecting the contact point"). -/
def contactDirection (frame : Fin 2 → RigidTransform) (i j : Fin 2) : Fin 3 → ℝ :=
  (frame i).rotation.valᵀ *ᵥ WithLp.ofLp ((frame j).translation - (frame i).translation)

/-- **MLS Theorem 5.7, "if" direction**, printed p. 233: a spatial grasp of two soft-finger
contacts (`μ > 0`, `γ > 0`) is force-closure when the line connecting the contacts lies inside
both friction cones (open cones: `√(x₁² + x₂²) < μ x₃` for the direction `x` to the other contact
in each contact frame). The strictly internal force is the pair of opposite forces along the
line with zero torsion; surjectivity uses the torsion about the first contact normal, which is
not perpendicular to the line. Finite-force caveat: unbounded contact forces at maintained rigid
contacts (MLS p. 214). -/
theorem spatial_softFinger_isForceClosure_of_lineInsideCones {μ γ : ℝ} (hμ : 0 < μ)
    (hγ : 0 < γ) (frame : Fin 2 → RigidTransform)
    (h0 : √(contactDirection frame 0 1 0 ^ 2 + contactDirection frame 0 1 1 ^ 2) <
      μ * contactDirection frame 0 1 2)
    (h1 : √(contactDirection frame 1 0 0 ^ 2 + contactDirection frame 1 0 1 ^ 2) <
      μ * contactDirection frame 1 0 2) :
    (ContactGrasp.spatial (fun _ => ContactModel.softFinger μ γ hμ hγ)
      frame).toGrasp.IsForceClosure := by
  have hpos : ∀ {a b : ℝ}, √a < μ * b → 0 < b := fun {a b} h => by
    have := Real.sqrt_nonneg a
    by_contra hb
    nlinarith
  have hx2 := hpos h0
  have hy2 := hpos h1
  rw [Grasp.isForceClosure_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨w, τ⟩
    obtain ⟨D, hD⟩ : ∃ D : Fin 3 → ℝ,
        D = WithLp.ofLp ((frame 1).translation - (frame 0).translation) := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : Fin 3 → ℝ,
        N = WithLp.ofLp ((frame 0).rotation.act Rotation.zAxis) := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : Fin 3 → ℝ,
        T = WithLp.ofLp (τ - Vec3.cross (frame 0).translation w) := ⟨_, rfl⟩
    -- the first contact normal is not perpendicular to the line: `n₀ · d = x₃ > 0`
    have hND : N ⬝ᵥ D = contactDirection frame 0 1 2 := by
      rw [hN, hD]
      simp [contactDirection, dotProduct, Fin.sum_univ_three, Matrix.mulVec, Rotation.act_apply,
        Rotation.zAxis, Matrix.transpose_apply]
    have hNDpos : 0 < N ⬝ᵥ D := hND ▸ hx2
    have hDD : D ⬝ᵥ D ≠ 0 := by
      intro h
      simp only [dotProduct, Fin.sum_univ_three] at h hNDpos
      have hsq : ∀ i, D i * D i = 0 := fun i => by
        fin_cases i <;> simp <;>
          nlinarith [mul_self_nonneg (D 0), mul_self_nonneg (D 1), mul_self_nonneg (D 2)]
      rw [mul_self_eq_zero.mp (hsq 0), mul_self_eq_zero.mp (hsq 1),
        mul_self_eq_zero.mp (hsq 2)] at hNDpos
      simp at hNDpos
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (T ⬝ᵥ D) / (N ⬝ᵥ D) := ⟨_, rfl⟩
    obtain ⟨U, hU⟩ : ∃ U : Fin 3 → ℝ, U = T - a • N := ⟨_, rfl⟩
    have hUD : U ⬝ᵥ D = 0 := by
      rw [hU, sub_dotProduct, smul_dotProduct, smul_eq_mul, ha, div_mul_cancel₀ _ hNDpos.ne',
        sub_self]
    -- `d × F' = u` for `F' = (u × d) / |d|²`, since `u · d = 0`
    obtain ⟨F', hF'⟩ : ∃ F' : Vec3,
        F' = WithLp.toLp 2 ((D ⬝ᵥ D)⁻¹ • crossProduct U D) := ⟨_, rfl⟩
    have hcross : crossProduct D (WithLp.ofLp F') = U := by
      rw [hF', WithLp.ofLp_toLp, map_smul, cross_cross_eq_smul_sub_smul', hUD, zero_smul,
        sub_zero, smul_smul, inv_mul_cancel₀ hDD, one_smul]
    refine ⟨![softCoef (frame 0) (w - F') a, softCoef (frame 1) F' 0], ?_⟩
    rw [ContactGrasp.toGrasp_map, graspMap_softCoef]
    apply Wrench.ext
    · simp
    · apply WithLp.ofLp_injective
      have key : crossProduct (WithLp.ofLp (frame 1).translation) (WithLp.ofLp F') =
          crossProduct (WithLp.ofLp (frame 0).translation) (WithLp.ofLp F') + (T - a • N) := by
        rw [← hU, ← hcross, hD, WithLp.ofLp_sub, map_sub, LinearMap.sub_apply]
        abel
      simp only [zero_smul, add_zero, WithLp.ofLp_add, WithLp.ofLp_smul, Vec3.cross_coordinates,
        WithLp.ofLp_sub, map_sub, key]
      rw [hT, hN]
      simp only [WithLp.ofLp_sub, Vec3.cross_coordinates]
      abel
  · refine ⟨![softCoef (frame 0) ((frame 1).translation - (frame 0).translation) 0,
      softCoef (frame 1) ((frame 0).translation - (frame 1).translation) 0], ?_, ?_⟩
    · rw [ContactGrasp.toGrasp_map, graspMap_softCoef]
      apply Wrench.ext
      · simp
      · apply WithLp.ofLp_injective
        simp only [zero_smul, add_zero, WithLp.ofLp_add, Vec3.cross_coordinates, WithLp.ofLp_sub,
          map_sub, WithLp.ofLp_zero, Wrench.zero_torque]
        rw [cross_self, cross_self]
        simp only [sub_zero]
        rw [cross_anticomm']
    · rw [ContactGrasp.toGrasp_cone, ContactGrasp.mem_interior_cone]
      intro i
      fin_cases i
      · exact mem_interior_softFingerCone h0 hx2 (by
          change |(0 : ℝ)| < γ * contactDirection frame 0 1 2
          rw [abs_zero]
          exact mul_pos hγ hx2)
      · exact mem_interior_softFingerCone h1 hy2 (by
          change |(0 : ℝ)| < γ * contactDirection frame 1 0 2
          rw [abs_zero]
          exact mul_pos hγ hy2)

end RoboLean.Grasp
