import RoboLean.Dynamics.InertiaTensor
import RoboLean.Geometry.RigidVelocity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The kinetic energy of a rigid body as a mass integral

MLS Chapter 4, §2.2, printed pp. 161–162, eqs. (4.8)–(4.9). A body point with body-frame
coordinates `r` has inertial velocity `ṗ + Ṙ r` along a trajectory `(p, R)` of the body frame,
and the kinetic energy of the body is the volume integral

`T = ½ ∫_V ρ(r) ‖ṗ + Ṙ r‖² dV`  (4.8).

With the body frame at the mass center the cross term `∫ ρ ṗᵀ Ṙ r dV` vanishes and

`T = ½ m ‖ṗ‖² + ½ ωᵀ 𝓘 ω = ½ (Vᵇ)ᵀ [[m I, 0], [0, 𝓘]] Vᵇ`  (4.9),

with `ω` the body angular velocity and `Vᵇ` the body velocity.

**Carrier.** The mass distribution is a measure `μ` on body-frame coordinates, as in
`RoboLean.Dynamics.InertiaTensor` (the book's `ρ(r) dV`); `mass μ`, `inertiaTensor μ` and
`centerOfMass μ` are the definitions there. The trajectory is a pose curve `g` with an actual
derivative `D` of its homogeneous matrix at `t`; `ṗ` is `RigidTransform.translationDerivative D`,
`Ṙ` is the rotation block `D.toBlocks₁₁`, and `Vᵇ` is the library's body velocity
`RigidTransform.bodyVelocity g D t h`.

**Hypotheses the book does not print.** The integrals must exist: the statements assume a
finite measure (`IsFiniteMeasure μ`, or positive mass, which implies it) and an integrable second
moment `‖r‖²`; the first moment is then integrable (`integrable_id_of_secondMoment`).

**A body frame anywhere.** Without the mass-center hypothesis the same integral is the quadratic
form of `distributionInertia μ = [[m I, −ĉ], [ĉ, 𝓘]]` with `c = ∫ r dμ = m r̄` the first moment
and `𝓘` the inertia tensor about the body-frame origin (`kineticEnergyIntegral_bodyVelocity`):
the cross term is `m vᵀ (ω × r̄)`. With `c = 0` this is the block-diagonal matrix of (4.9)
(`distributionInertia_eq_generalizedInertia`). MLS p. 163 notes that the block-diagonal form
relies on the mass-center frame and refers to Exercise 3 for the general case.

Twist order `(v, ω)`, linear first, as printed and as in `Twist.coordinates`. Nothing here
concerns a physical body, units or the realizability of given inertial parameters.
-/

noncomputable section

open Matrix MeasureTheory

namespace RoboLean
namespace RigidBody

variable (μ : Measure Vec3)

/-- **MLS eq. (4.8), p. 161: the kinetic energy of a rigid body**,
`T = ½ ∫_V ρ(r) ‖ṗ + Ṙ r‖² dV`, for the mass distribution `μ` on body-frame coordinates `r`, the
velocity `ṗ` of the body-frame origin and the derivative `Ṙ` of the body-frame rotation (Bochner
integral; `0` when the integrand is not integrable). -/
def kineticEnergyIntegral (pdot : Vec3) (Rdot : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ r, ‖pdot + Matrix.toEuclideanLin Rdot r‖ ^ 2 ∂μ

/-- **The generalized inertia of a mass distribution in an arbitrary body frame** (MLS pp. 161–163,
the expansion of (4.8) before the mass-center frame is chosen; compare Exercise 3, p. 208):
`[[m I, −ĉ], [ĉ, 𝓘]]` with `m = mass μ`, `c = ∫ r dμ` the first moment (`m r̄`), `ĉ = Vec3.hat c`
and `𝓘 = inertiaTensor μ` about the body-frame origin. Twist order `(v, ω)`. -/
def distributionInertia : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (mass μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (-Vec3.hat (∫ r, r ∂μ))
    (Vec3.hat (∫ r, r ∂μ)) (inertiaTensor μ)

/-- **MLS p. 161: "the velocity of the point in the inertial frame is given by `ṗ + Ṙ r`".**
A body point with constant body coordinates `r` moves on `s ↦ g(s) r = R(s) r + p(s)`; its actual
derivative at `t` is `ṗ + Ṙ r`, with `ṗ` the translation column and `Ṙ` the rotation block of the
pose derivative `D`. -/
theorem hasDerivAt_applyPoint_body {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) (r : Vec3) :
    HasDerivAt (fun s => (g s).applyPoint r)
      (RigidTransform.translationDerivative D + Matrix.toEuclideanLin D.toBlocks₁₁ r) t := by
  have hd := (Rotation.hasDerivAt_act (RigidTransform.hasDerivAt_rotation h) r).add
    (RigidTransform.hasDerivAt_translation h)
  rw [add_comm (Matrix.toEuclideanLin D.toBlocks₁₁ r)] at hd
  exact hd

/-- The first moment of a finite mass distribution with integrable second moment is integrable
(`‖r‖ ≤ 1 + ‖r‖²`), so that `r̄` and `∫ ρ r dV` of MLS p. 161 exist. -/
theorem integrable_id_of_secondMoment [IsFiniteMeasure μ]
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) : Integrable (fun r : Vec3 => r) μ := by
  refine ((integrable_const (1 : ℝ)).add h2).mono' continuous_id.aestronglyMeasurable
    (Filter.Eventually.of_forall fun r => ?_)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖r‖ - 1), norm_nonneg r]

/-- The expansion of the squared point speed in body coordinates (MLS p. 162, the step
`‖ṗ‖² + 2 ṗᵀ Ṙ r + ‖Ṙ r‖²` written with `R⁻¹(ṗ + Ṙ r) = ω × r + v`):
`‖ω × r + v‖² = ‖v‖² + 2 ⟪v × ω, r⟫ + (r̂ ω)ᵀ (r̂ ω)`. -/
theorem norm_cross_add_sq (v ω r : Vec3) :
    ‖Vec3.cross ω r + v‖ ^ 2 =
      ‖v‖ ^ 2 + 2 * inner ℝ (Vec3.cross v ω) r +
        (Vec3.hat r *ᵥ WithLp.ofLp ω) ⬝ᵥ (Vec3.hat r *ᵥ WithLp.ofLp ω) := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [Vec3.cross, crossProduct, Vec3.hat, PiLp.inner_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three]
  ring

private theorem integrable_hat_quadratic {μ : Measure Vec3}
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (ω : Vec3) :
    Integrable (fun r : Vec3 =>
      (Vec3.hat r *ᵥ WithLp.ofLp ω) ⬝ᵥ (Vec3.hat r *ᵥ WithLp.ofLp ω)) μ := by
  have e : ∀ r : Vec3, (Vec3.hat r *ᵥ WithLp.ofLp ω) ⬝ᵥ (Vec3.hat r *ᵥ WithLp.ofLp ω) =
      ∑ i, ∑ j, ω i * ω j * ((if i = j then ‖r‖ ^ 2 else 0) - r i * r j) := by
    intro r
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Vec3.hat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  simp_rw [e]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_inertiaIntegrand h2 i j).const_mul _

/-- **The kinetic-energy integral in body coordinates (MLS pp. 161–162).** For a finite mass
distribution with integrable second moment and any body velocity `(v, ω)`,
`∫ ‖ω × r + v‖² dμ = m ‖v‖² + 2 ⟪v × ω, ∫ r dμ⟫ + ωᵀ 𝓘 ω`, with `𝓘` about the body-frame
origin. The middle term is the cross term `2 ∫ ρ ṗᵀ Ṙ r dV` of p. 162. -/
theorem integral_norm_cross_add_sq [IsFiniteMeasure μ]
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (v ω : Vec3) :
    ∫ r, ‖Vec3.cross ω r + v‖ ^ 2 ∂μ =
      mass μ * ‖v‖ ^ 2 + 2 * inner ℝ (Vec3.cross v ω) (∫ r, r ∂μ) +
        WithLp.ofLp ω ⬝ᵥ (inertiaTensor μ *ᵥ WithLp.ofLp ω) := by
  have h1 := integrable_id_of_secondMoment μ h2
  have hA : Integrable (fun r : Vec3 => 2 * inner ℝ (Vec3.cross v ω) r) μ :=
    (h1.const_inner _).const_mul 2
  have hB : Integrable (fun r : Vec3 => ‖v‖ ^ 2 + 2 * inner ℝ (Vec3.cross v ω) r) μ :=
    (integrable_const _).add hA
  simp_rw [norm_cross_add_sq]
  rw [integral_add hB (integrable_hat_quadratic h2 ω), integral_add (integrable_const _) hA,
    integral_const,
    integral_const_mul, integral_inner h1, dotProduct_inertiaTensor_mulVec μ h2, smul_eq_mul]
  rfl

private theorem quadratic_fromBlocks (m : ℝ) (c : Vec3) (𝓘 : Matrix (Fin 3) (Fin 3) ℝ)
    (V : Twist) :
    V.coordinates ⬝ᵥ (Matrix.fromBlocks (m • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (-Vec3.hat c)
      (Vec3.hat c) 𝓘 *ᵥ V.coordinates) =
      m * ‖V.linear‖ ^ 2 + 2 * inner ℝ (Vec3.cross V.linear V.angular) c +
        WithLp.ofLp V.angular ⬝ᵥ (𝓘 *ᵥ WithLp.ofLp V.angular) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Twist.coordinates, dotProduct, Fintype.sum_sum_type,
    Matrix.mulVec, Vec3.hat, Vec3.cross, crossProduct, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- **The quadratic form of `distributionInertia` (MLS pp. 161–163):**
`Vᵀ [[m I, −ĉ], [ĉ, 𝓘]] V = m ‖v‖² + 2 ⟪v × ω, c⟫ + ωᵀ 𝓘 ω` for `V = (v, ω)`. -/
theorem coordinates_dotProduct_distributionInertia_mulVec (V : Twist) :
    V.coordinates ⬝ᵥ (distributionInertia μ *ᵥ V.coordinates) =
      mass μ * ‖V.linear‖ ^ 2 + 2 * inner ℝ (Vec3.cross V.linear V.angular) (∫ r, r ∂μ) +
        WithLp.ofLp V.angular ⬝ᵥ (inertiaTensor μ *ᵥ WithLp.ofLp V.angular) :=
  quadratic_fromBlocks _ _ _ V

/-- **MLS eq. (4.8) is a quadratic form in the body velocity, for a body frame anywhere
(pp. 161–163).** Along a pose trajectory with actual derivative `D` at `t`, for a finite mass
distribution with integrable second moment,
`½ ∫ ‖ṗ + Ṙ r‖² dμ = ½ (Vᵇ)ᵀ [[m I, −ĉ], [ĉ, 𝓘]] Vᵇ`, with `c` the first moment and `𝓘` the
inertia tensor about the body-frame origin. The step `‖ṗ + Ṙ r‖ = ‖R⁻¹(ṗ + Ṙ r)‖ = ‖ω × r + v‖`
uses that rotations preserve length. -/
theorem kineticEnergyIntegral_bodyVelocity [IsFiniteMeasure μ]
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) {g : ℝ → RigidTransform}
    {D : HomogeneousMatrix} {t : ℝ} (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    kineticEnergyIntegral μ (RigidTransform.translationDerivative D) D.toBlocks₁₁ =
      kineticEnergy (distributionInertia μ) (RigidTransform.bodyVelocity g D t h) := by
  have e : ∀ r : Vec3,
      ‖RigidTransform.translationDerivative D + Matrix.toEuclideanLin D.toBlocks₁₁ r‖ =
        ‖Vec3.cross (RigidTransform.bodyVelocity g D t h).angular r +
          (RigidTransform.bodyVelocity g D t h).linear‖ := by
    intro r
    rw [← RigidTransform.body_point_velocity h r, Rotation.norm_act, add_comm]
  simp_rw [kineticEnergyIntegral, e]
  rw [integral_norm_cross_add_sq μ h2, kineticEnergy,
    coordinates_dotProduct_distributionInertia_mulVec]

/-- **MLS p. 162: the cross term vanishes at the mass center**,
`∫ ρ(r) (ṗᵀ Ṙ) r dV = (ṗᵀ Ṙ) ∫ ρ(r) r dV = 0`, for any `ṗ` and `Ṙ` when the first moment is
integrable and vanishes. -/
theorem integral_inner_rotationDerivative (h1 : Integrable (fun r : Vec3 => r) μ)
    (h0 : ∫ r, r ∂μ = 0) (pdot : Vec3) (Rdot : Matrix (Fin 3) (Fin 3) ℝ) :
    ∫ r, inner ℝ pdot (Matrix.toEuclideanLin Rdot r) ∂μ = 0 := by
  let L : Vec3 →L[ℝ] Vec3 := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Rdot)
  have hL : ∫ r, Matrix.toEuclideanLin Rdot r ∂μ = Matrix.toEuclideanLin Rdot (∫ r, r ∂μ) :=
    L.integral_comp_comm h1
  have hi : Integrable (fun r : Vec3 => Matrix.toEuclideanLin Rdot r) μ := L.integrable_comp h1
  rw [integral_inner hi, hL, h0, map_zero, inner_zero_right]

private theorem hat_zero : Vec3.hat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vec3.hat]

/-- **MLS eq. (4.9), p. 162: at the mass center the generalized inertia is block diagonal.** If
the first moment `∫ r dμ` vanishes (the body frame is at the mass center), the generalized
inertia of the distribution is `[[m I, 0], [0, 𝓘]]` with `m = mass μ` and `𝓘 = inertiaTensor μ`. -/
theorem distributionInertia_eq_generalizedInertia (h0 : ∫ r, r ∂μ = 0) :
    distributionInertia μ = generalizedInertia (mass μ) (inertiaTensor μ) := by
  rw [distributionInertia, generalizedInertia, h0, hat_zero, neg_zero]

/-- **MLS eqs. (4.8)–(4.9), p. 162, from the volume integral.** For a mass distribution of
positive (finite) mass with integrable second moment, with the body frame at its mass center
(`r̄ = 0`), the kinetic energy `½ ∫ ‖ṗ + Ṙ r‖² dμ` along a pose trajectory equals
`½ (Vᵇ)ᵀ [[m I, 0], [0, 𝓘]] Vᵇ` with `m = mass μ`, `𝓘 = inertiaTensor μ` and `Vᵇ` the body
velocity: the second line of (4.9). The finiteness and integrability hypotheses are not printed. -/
theorem kineticEnergyIntegral_eq_generalizedInertia (hm : 0 < mass μ)
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (hc : centerOfMass μ = 0)
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    kineticEnergyIntegral μ (RigidTransform.translationDerivative D) D.toBlocks₁₁ =
      kineticEnergy (generalizedInertia (mass μ) (inertiaTensor μ))
        (RigidTransform.bodyVelocity g D t h) := by
  have hfin : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr fun htop => hm.ne' (by
    simp [mass, Measure.real, htop])⟩
  rw [kineticEnergyIntegral_bodyVelocity μ h2 h, distributionInertia_eq_generalizedInertia μ
    ((centerOfMass_eq_zero_iff μ hm.ne').mp hc)]

/-- **MLS eq. (4.9), first line, p. 162, from the volume integral:**
`T = ½ m ‖ṗ‖² + ½ ωᵀ 𝓘 ω`, the sum of the translational and rotational kinetic energies, for a
mass distribution of positive mass with integrable second moment and the body frame at its mass
center; `ṗ` is the velocity of the frame origin and `ω` the body angular velocity. -/
theorem kineticEnergyIntegral_eq_translational_add_rotational (hm : 0 < mass μ)
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (hc : centerOfMass μ = 0)
    {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    kineticEnergyIntegral μ (RigidTransform.translationDerivative D) D.toBlocks₁₁ =
      (1 / 2 : ℝ) * mass μ * ‖RigidTransform.translationDerivative D‖ ^ 2 +
        (1 / 2 : ℝ) * (WithLp.ofLp (RigidTransform.bodyVelocity g D t h).angular ⬝ᵥ
          (inertiaTensor μ *ᵥ WithLp.ofLp (RigidTransform.bodyVelocity g D t h).angular)) := by
  rw [kineticEnergyIntegral_eq_generalizedInertia μ hm h2 hc h,
    kineticEnergy_generalizedInertia_bodyVelocity]

/-- The generalized inertia of a distribution (MLS pp. 161–163) is symmetric, for every body
frame: the off-diagonal blocks `−ĉ` and `ĉ` are transposes of each other, and `𝓘` is symmetric. -/
theorem distributionInertia_isSymm : (distributionInertia μ).IsSymm := by
  rw [distributionInertia, Matrix.IsSymm, Matrix.fromBlocks_transpose, Vec3.hat_transpose,
    Matrix.transpose_neg, Vec3.hat_transpose, neg_neg, (inertiaTensor_isSymm μ).eq,
    Matrix.transpose_smul, Matrix.transpose_one]

/-- **The generalized inertia of a distribution is positive semidefinite in every body frame
(MLS p. 162).** For a finite distribution with integrable second moment,
`Vᵀ 𝓜 V = ∫ ‖ω × r + v‖² dμ ≥ 0`, read off from the kinetic-energy integral. -/
theorem distributionInertia_posSemidef [IsFiniteMeasure μ]
    (h2 : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) : (distributionInertia μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simpa using distributionInertia_isSymm μ
  · simp only [star_trivial]
    have hx : x = (Twist.coordinatesEquiv.symm x).coordinates :=
      (Twist.coordinatesEquiv.apply_symm_apply x).symm
    rw [hx, coordinates_dotProduct_distributionInertia_mulVec, ← integral_norm_cross_add_sq μ h2]
    exact integral_nonneg fun r => by positivity

end RigidBody
end RoboLean
