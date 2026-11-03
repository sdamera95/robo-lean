import RoboLean.Dynamics.KineticEnergyIntegral
import RoboLean.Dynamics.InertiaFrameChange

/-!
# A mass distribution seen from a second body frame: Chapter 4 Exercise 3 from the integrals

MLS Chapter 4, p. 163: "The block diagonal structure of this matrix relies on attaching the body
coordinate frame at center of mass (see Exercise 3)", and Exercise 3, p. 208: under a change of body
frame from `B` to `C`, `𝓜_c = Ad_{g_bc}ᵀ 𝓜_b Ad_{g_bc} =
[[m I, m R_bcᵀ p̂_bc R_bc], [−m R_bcᵀ p̂_bc R_bc, R_bcᵀ (𝓘 − m p̂_bc²) R_bc]]`, with `g_bc` the rigid
motion taking `C` to `B`.

**Formalized.** A body point with coordinates `r` in `B` has coordinates `g_bc⁻¹ r = Rᵀ (r − p)` in
`C` (`g_bc = (R, p)`), so the same body in `C` is the image measure `reframeDistribution g μ`. Its
generalized inertia computed from the integrals (`distributionInertia`, the form valid in any body
frame) is `Ad_gᵀ (distributionInertia μ) Ad_g` for every frame `B`
(`distributionInertia_reframe`); with `B` at the mass center this is the printed block matrix of
Exercise 3 (`distributionInertia_reframe_of_integral_id`), whose lower-right block is the
parallel-axis theorem `𝓘_c = Rᵀ (𝓘 − m p̂²) R` for the inertia tensor of the moved distribution
(`inertiaTensor_reframe_of_integral_id`). The proof compares the kinetic-energy integrals (4.8) in
the two frames point by point, `‖ω × Rᵀ(r − p) + v‖ = ‖Rω × r + (Rv + p × Rω)‖`, and uses that two
symmetric matrices with the same quadratic form are equal.

Hypotheses: a finite distribution with integrable second moment, as for (4.8)–(4.9). Twist order
`(v, ω)`. Nothing here concerns a physical body.
-/

noncomputable section

open Matrix MeasureTheory

namespace RoboLean
namespace RigidBody

/-- **The same body in a second body frame (MLS Chapter 4, Exercise 3, p. 208):** for
`g = g_bc = (R, p)`, the rigid motion taking `C` to `B`, a body point with coordinates `r` in `B`
has coordinates `g⁻¹ r = Rᵀ (r − p)` in `C`; the distribution in `C` is the image of `μ`. -/
def reframeDistribution (g : RigidTransform) (μ : Measure Vec3) : Measure Vec3 :=
  μ.map fun r => g⁻¹.applyPoint r

private theorem continuous_applyPoint (g : RigidTransform) :
    Continuous fun r : Vec3 => g.applyPoint r :=
  g.rotation.act.continuous_of_finiteDimensional.add continuous_const

/-- **The point speed in two body frames (MLS p. 161, eq. (4.8), and Exercise 3, p. 208):** for
`g = (R, p)` and a body velocity `V = (v, ω)` expressed in `C`,
`‖ω × g⁻¹ r + v‖ = ‖ω′ × r + v′‖` with `(v′, ω′) = Ad_g V` the same velocity expressed in `B`. -/
theorem norm_cross_reframe (g : RigidTransform) (V : Twist) (r : Vec3) :
    ‖Vec3.cross V.angular (g⁻¹.applyPoint r) + V.linear‖ =
      ‖Vec3.cross (Twist.adjoint g V).angular r + (Twist.adjoint g V).linear‖ := by
  rw [← Rotation.norm_act g.rotation]
  simp only [RigidTransform.applyPoint, RigidTransform.inv_rotation,
    RigidTransform.inv_translation, map_add, Rotation.act_cross, Twist.adjoint_angular,
    Twist.adjoint_linear, map_neg, Rotation.act_inv_act, Vec3.cross_add, Vec3.cross_neg]
  rw [Vec3.cross_anticomm g.translation]
  abel_nf

private theorem continuous_cross (ω : Vec3) : Continuous fun y : Vec3 => Vec3.cross ω y := by
  have e : (fun y : Vec3 => Vec3.cross ω y) = fun y => Matrix.toEuclideanLin (Vec3.hat ω) y := by
    funext y
    apply WithLp.ofLp_injective
    change _ = Vec3.hat ω *ᵥ WithLp.ofLp y
    rw [Vec3.hat_mulVec]
  rw [e]
  exact (Matrix.toEuclideanLin (Vec3.hat ω)).continuous_of_finiteDimensional

private theorem eq_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Matrix ι ι ℝ}
    (hM : M.IsSymm) (hN : N.IsSymm) (h : ∀ x, x ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (N *ᵥ x)) : M = N := by
  ext i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  have h2 := h (Pi.single i 1)
  have h3 := h (Pi.single j 1)
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single_one,
    single_dotProduct, one_mul, Matrix.col_apply] at h1 h2 h3
  have hm : M j i = M i j := by simpa using congrFun (congrFun hM i) j
  have hn : N j i = N i j := by simpa using congrFun (congrFun hN i) j
  linarith

private theorem integrable_reframe (g : RigidTransform) {μ : Measure Vec3} [IsFiniteMeasure μ]
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) :
    Integrable (fun r : Vec3 => ‖r‖ ^ 2) (reframeDistribution g μ) := by
  have hc := continuous_applyPoint g⁻¹
  rw [reframeDistribution]
  refine (integrable_map_measure (g := fun r : Vec3 => ‖r‖ ^ 2)
    (continuous_norm.pow 2).aestronglyMeasurable hc.aemeasurable).mpr ?_
  refine ((h2.const_mul 2).add (integrable_const (2 * ‖g⁻¹.translation‖ ^ 2))).mono'
    ((continuous_norm.pow 2).comp hc).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply, norm_pow, norm_norm, Pi.add_apply]
  have ht : ‖g⁻¹.applyPoint r‖ ≤ ‖r‖ + ‖g⁻¹.translation‖ := by
    rw [RigidTransform.applyPoint]
    exact (norm_add_le _ _).trans (by rw [Rotation.norm_act])
  have hsq : ‖g⁻¹.applyPoint r‖ ^ 2 ≤ (‖r‖ + ‖g⁻¹.translation‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖r‖ - ‖g⁻¹.translation‖)]

/-- **The generalized inertia of a distribution under a change of body frame, from the integrals
(MLS Chapter 4, Exercise 3, p. 208; eq. (4.28), p. 176):** for a finite distribution with integrable
second moment and any `g = g_bc`, the generalized inertia of the body in `C` is
`Ad_gᵀ 𝓜_b Ad_g`, with `𝓜_b = distributionInertia μ` in any frame `B` (not only at the mass
center). -/
theorem distributionInertia_reframe (g : RigidTransform) {μ : Measure Vec3} [IsFiniteMeasure μ]
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) :
    distributionInertia (reframeDistribution g μ) = transformInertia g (distributionInertia μ) := by
  have hfin : IsFiniteMeasure (reframeDistribution g μ) := Measure.isFiniteMeasure_map μ _
  refine eq_of_quadratic (distributionInertia_isSymm _)
    (transformInertia_isSymm g (distributionInertia_isSymm μ)) fun x => ?_
  have hx : x = (Twist.coordinatesEquiv.symm x).coordinates :=
    (Twist.coordinatesEquiv.apply_symm_apply x).symm
  set V := Twist.coordinatesEquiv.symm x with hV
  have hmeas : AEStronglyMeasurable (fun y : Vec3 => ‖Vec3.cross V.angular y + V.linear‖ ^ 2)
      (Measure.map (fun r => g⁻¹.applyPoint r) μ) :=
    (((continuous_cross _).add continuous_const).norm.pow 2).aestronglyMeasurable
  rw [hx, coordinates_dotProduct_distributionInertia_mulVec (reframeDistribution g μ),
    ← integral_norm_cross_add_sq (reframeDistribution g μ) (integrable_reframe g h2),
    coordinates_dotProduct_transformInertia_mulVec, coordinates_dotProduct_distributionInertia_mulVec μ,
    ← integral_norm_cross_add_sq μ h2, reframeDistribution,
    integral_map (continuous_applyPoint g⁻¹).aemeasurable hmeas]
  congr 1
  funext r
  rw [norm_cross_reframe]

/-- **MLS Chapter 4, Exercise 3, p. 208, from the integrals:** if the frame `B` is at the mass center
(`∫ r dμ = 0`), the generalized inertia of the body in `C`, computed from the mass integrals, is the
printed `[[m I, m Rᵀ p̂ R], [−m Rᵀ p̂ R, Rᵀ (𝓘 − m p̂²) R]]` for `g_bc = (R, p)`, with `m = mass μ`
and `𝓘 = inertiaTensor μ`; finite distribution with integrable second moment. -/
theorem distributionInertia_reframe_of_integral_id (g : RigidTransform) {μ : Measure Vec3}
    [IsFiniteMeasure μ] (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (h0 : ∫ r, r ∂μ = 0) :
    distributionInertia (reframeDistribution g μ) =
      Matrix.fromBlocks (mass μ • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (mass μ • (g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val))
        (-(mass μ • (g.rotation.valᵀ * Vec3.hat g.translation * g.rotation.val)))
        (g.rotation.valᵀ * (inertiaTensor μ - mass μ • (Vec3.hat g.translation *
          Vec3.hat g.translation)) * g.rotation.val) := by
  rw [distributionInertia_reframe g h2, distributionInertia_eq_generalizedInertia μ h0,
    transformInertia_generalizedInertia]

/-- **The parallel-axis theorem for a mass distribution (MLS Chapter 4, Exercise 3, p. 208, the
lower-right block):** for a frame `B` at the mass center and `g_bc = (R, p)`, the inertia tensor of
the body about the origin of `C`, in `C`, is `Rᵀ (𝓘 − m p̂²) R`; finite distribution with
integrable second moment. -/
theorem inertiaTensor_reframe_of_integral_id (g : RigidTransform) {μ : Measure Vec3}
    [IsFiniteMeasure μ] (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (h0 : ∫ r, r ∂μ = 0) :
    inertiaTensor (reframeDistribution g μ) =
      g.rotation.valᵀ * (inertiaTensor μ - mass μ • (Vec3.hat g.translation *
        Vec3.hat g.translation)) * g.rotation.val := by
  have h := distributionInertia_reframe_of_integral_id g h2 h0
  rw [distributionInertia, Matrix.fromBlocks_inj] at h
  exact h.2.2.2

/-- The mass of the body is the same in every body frame (MLS Chapter 4, Exercise 3, p. 208, the
upper-left block `m I`). -/
theorem mass_reframeDistribution (g : RigidTransform) (μ : Measure Vec3) :
    mass (reframeDistribution g μ) = mass μ := by
  rw [mass, mass, reframeDistribution, Measure.real, Measure.real,
    Measure.map_apply (continuous_applyPoint g⁻¹).measurable MeasurableSet.univ, Set.preimage_univ]

end RigidBody
end RoboLean
