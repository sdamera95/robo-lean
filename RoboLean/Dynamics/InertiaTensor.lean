import RoboLean.Dynamics.RigidBodyInertia
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mass, center of mass and inertia tensor of a mass distribution

MLS Chapter 4, §2.2, printed pp. 161–163. A rigid body occupies a volume `V ⊂ ℝ³` with mass
density `ρ(r)`; its mass is `m = ∫_V ρ(r) dV`, its center of mass `r̄ = (1/m) ∫_V ρ(r) r dV`, and
its inertia tensor in the body frame is

`𝓘 = −∫_V ρ(r) r̂² dV`, with entries `I_xx = ∫_V ρ (y² + z²)`, `I_xy = −∫_V ρ x y`, ….

MLS calls `𝓘` symmetric and the generalized inertia `[[m I, 0], [0, 𝓘]]` symmetric and
positive definite (p. 162), with no hypotheses printed.

**Carrier (a convention of this file).** The mass distribution is a measure `μ` on `Vec3`, the
body-frame coordinates `r` of body points: the book's `ρ(r) dV` on `V`. A density `ρ ≥ 0` on a
region `V` is the special case `volume.withDensity` (or, for a homogeneous body, a constant
multiple of `volume.restrict V`, as for the bar below); point masses and lower-dimensional
bodies are other measures. Because `μ` is a (nonnegative) measure, the nonnegativity of the
distribution is built into the type. Integrals are Mathlib's Bochner integrals. The mass is
`μ(univ)` as a real number (`Measure.real`), and the inertia tensor is defined entrywise,
`𝓘ᵢⱼ = −∫ (r̂ r̂)ᵢⱼ dμ`, so that only real-valued integrals occur (matrices carry no default norm).

**Hypotheses.** Where integrals must exist, the statements assume the second moment is
integrable, `Integrable (fun r => ‖r‖²) μ`; MLS presupposes that the integrals exist and states
no such condition. Symmetry needs no hypothesis.

**What the hypotheses on `𝓘` mean for a distribution.** `RigidBody.generalizedInertia m 𝓘`
is used with `𝓘` symmetric and positive (semi)definite as explicit hypotheses. For
`𝓘 = inertiaTensor μ`: symmetry always holds (`inertiaTensor_isSymm`); positive
semidefiniteness holds for every distribution with integrable second moment
(`inertiaTensor_posSemidef`), since `ωᵀ 𝓘 ω = ∫ (r̂ω)ᵀ(r̂ω) dμ` (`dotProduct_inertiaTensor_mulVec`,
the last step of the kinetic-energy computation on p. 162); and positive definiteness holds
exactly when `μ` is not concentrated on a line through the body-frame origin, i.e. for every
`ω ≠ 0` the set where `r̂ω = r × ω ≠ 0` has positive mass (`inertiaTensor_posDef_iff`). A point
mass or a thin rod through the origin is semidefinite but not definite. With `m = mass μ` these
give the generalized-inertia statements `generalizedInertia_posSemidef_of_distribution` and
`generalizedInertia_posDef_of_distribution`.

**Center of mass.** `centerOfMass μ = 0` exactly when `∫ r dμ = 0` (`centerOfMass_eq_zero_iff`),
the condition that makes the cross term of the kinetic energy vanish on p. 162; and
`∫ (r − r̄) dμ = 0` (`integral_sub_centerOfMass`).

**Example 4.2 (p. 163).** The homogeneous bar of mass `m`, length `l`, width `w`, height `h`,
with the frame at its center and axes along its edges, is `barDistribution m l w h`, the
measure `(m / (l w h)) · volume` on the box `[−l/2, l/2] × [−w/2, w/2] × [−h/2, h/2]`. Its mass
is `m`, its center of mass is the origin, and its inertia tensor is the printed
`diag(m(w² + h²)/12, m(l² + h²)/12, m(l² + w²)/12)`, positive definite for `m > 0`.

The kinetic-energy derivation (4.8)–(4.9) from the volume integral is not formalized here (the
block formula starts from `generalizedInertia`); nothing here concerns a physical body or the
realizability of given inertial parameters.
-/

noncomputable section

open Matrix MeasureTheory

namespace RoboLean
namespace RigidBody

variable (μ : Measure Vec3)

/-- **The mass of a body, MLS p. 161:** `m = ∫_V ρ(r) dV`, here the total mass `μ(univ)` of the
mass distribution `μ` as a real number (`0` if the measure is infinite, by the convention of
`Measure.real`). -/
def mass : ℝ := μ.real Set.univ

/-- **The center of mass, MLS p. 161:** `r̄ = (1/m) ∫_V ρ(r) r dV`, in body-frame coordinates, for
the mass distribution `μ` (Bochner integral; `0` when the first moment is not integrable). -/
def centerOfMass : Vec3 := (mass μ)⁻¹ • ∫ r, r ∂μ

/-- **The inertia tensor, MLS p. 162:** `𝓘 = −∫_V ρ(r) r̂² dV`, the inertia tensor of the body in
the body frame, defined entrywise as `𝓘ᵢⱼ = −∫ (r̂ r̂)ᵢⱼ dμ` with `r̂ = Vec3.hat r` (MLS eq. (2.4)).
The origin of the body frame need not be the center of mass here. -/
def inertiaTensor : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => -∫ r, (Vec3.hat r * Vec3.hat r) i j ∂μ

/-- The integrand of the inertia tensor, MLS p. 162: `−(r̂²)ᵢⱼ = ‖r‖² δᵢⱼ − rᵢ rⱼ`, so that
`−r̂² = rᵀr I − r rᵀ`. -/
theorem neg_hat_mul_hat_apply (r : Vec3) (i j : Fin 3) :
    -(Vec3.hat r * Vec3.hat r) i j = (if i = j then ‖r‖ ^ 2 else 0) - r i * r j := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Vec3.hat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- **The entries of the inertia tensor, MLS p. 162:** `𝓘ᵢⱼ = ∫ (‖r‖² δᵢⱼ − rᵢ rⱼ) dμ`. -/
theorem inertiaTensor_apply (i j : Fin 3) :
    inertiaTensor μ i j = ∫ r, ((if i = j then ‖r‖ ^ 2 else 0) - r i * r j) ∂μ := by
  rw [inertiaTensor, Matrix.of_apply, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun r => neg_hat_mul_hat_apply r i j)

/-- **MLS p. 162: `I_xx = ∫_V ρ(r)(y² + z²) dx dy dz`**, the first diagonal entry. -/
theorem inertiaTensor_zero_zero :
    inertiaTensor μ 0 0 = ∫ r, (r 1 ^ 2 + r 2 ^ 2) ∂μ := by
  rw [inertiaTensor_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

/-- **MLS p. 162: `I_xy = −∫_V ρ(r)(x y) dx dy dz`**, the first off-diagonal entry. -/
theorem inertiaTensor_zero_one : inertiaTensor μ 0 1 = -∫ r, r 0 * r 1 ∂μ := by
  rw [inertiaTensor_apply, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp

/-- **MLS p. 162: "the symmetric matrix `𝓘`".** The inertia tensor of every mass distribution is
symmetric; no integrability is needed. -/
theorem inertiaTensor_isSymm : (inertiaTensor μ).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, inertiaTensor_apply]
  congr 1
  funext r
  by_cases h : i = j
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_comm]

/-- If the second moment `‖r‖²` of a mass distribution is integrable, so is every product
`rᵢ rⱼ` of body-frame coordinates (`|rᵢ rⱼ| ≤ ‖r‖²`); the integrals of MLS p. 162 then exist. -/
theorem integrable_apply_mul_apply {μ : Measure Vec3} (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ)
    (i j : Fin 3) : Integrable (fun r : Vec3 => r i * r j) μ := by
  have hc : ∀ k : Fin 3, Continuous fun r : Vec3 => r k := fun k =>
    (EuclideanSpace.proj k : Vec3 →L[ℝ] ℝ).continuous
  refine h.mono' ((hc i).mul (hc j)).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  rw [norm_mul, pow_two]
  exact mul_le_mul (PiLp.norm_apply_le r i) (PiLp.norm_apply_le r j) (norm_nonneg _)
    (norm_nonneg _)


/-- The entries `‖r‖² δᵢⱼ − rᵢ rⱼ` of the inertia-tensor integrand (MLS p. 162) are integrable when
the second moment is. -/
theorem integrable_inertiaIntegrand {μ : Measure Vec3}
    (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (i j : Fin 3) :
    Integrable (fun r : Vec3 => (if i = j then ‖r‖ ^ 2 else 0) - r i * r j) μ := by
  refine Integrable.sub ?_ (integrable_apply_mul_apply h i j)
  split_ifs
  · exact h
  · exact integrable_zero _ _ _

private theorem hat_mulVec_dotProduct (r : Vec3) (ω : Fin 3 → ℝ) :
    (Vec3.hat r *ᵥ ω) ⬝ᵥ (Vec3.hat r *ᵥ ω) =
      ∑ i, ∑ j, ω i * ω j * ((if i = j then ‖r‖ ^ 2 else 0) - r i * r j) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Vec3.hat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- **MLS p. 162, the rotational kinetic energy:** `ωᵀ 𝓘 ω = ∫ (r̂ω)ᵀ(r̂ω) dμ`, the identity
`∫ ρ (r̂ω)ᵀ(r̂ω) dV = ωᵀ (−∫ ρ r̂² dV) ω` behind `T_rot = ½ ωᵀ 𝓘 ω`, for every distribution with
integrable second moment and every `ω`. -/
theorem dotProduct_inertiaTensor_mulVec (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ)
    (ω : Fin 3 → ℝ) :
    ω ⬝ᵥ (inertiaTensor μ *ᵥ ω) = ∫ r, (Vec3.hat r *ᵥ ω) ⬝ᵥ (Vec3.hat r *ᵥ ω) ∂μ := by
  simp_rw [hat_mulVec_dotProduct]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_inertiaIntegrand h i j).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (integrable_inertiaIntegrand h i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, inertiaTensor_apply]
  ring

private theorem integrable_hat_mulVec_dotProduct {μ : Measure Vec3}
    (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) (ω : Fin 3 → ℝ) :
    Integrable (fun r : Vec3 => (Vec3.hat r *ᵥ ω) ⬝ᵥ (Vec3.hat r *ᵥ ω)) μ := by
  simp_rw [hat_mulVec_dotProduct]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_inertiaIntegrand h i j).const_mul _

/-- **The inertia tensor of a mass distribution is positive semidefinite (MLS p. 162).** For every
(nonnegative) mass distribution with integrable second moment, `ωᵀ 𝓘 ω = ∫ ‖r̂ω‖² dμ ≥ 0`. -/
theorem inertiaTensor_posSemidef (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) :
    (inertiaTensor μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simpa using inertiaTensor_isSymm μ
  · simp only [star_trivial]
    rw [dotProduct_inertiaTensor_mulVec μ h]
    exact integral_nonneg fun r => by simpa using dotProduct_star_self_nonneg (Vec3.hat r *ᵥ x)

/-- **When the inertia tensor is positive definite (MLS p. 162).** For a mass distribution with
integrable second moment, `𝓘` is positive definite exactly when, for every `ω ≠ 0`, the body
points with `r̂ω = r × ω ≠ 0` carry positive mass: the distribution is not concentrated on any
line through the body-frame origin. MLS asserts positive definiteness without this condition;
a point mass or a thin rod through the origin violates it. -/
theorem inertiaTensor_posDef_iff (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) :
    (inertiaTensor μ).PosDef ↔
      ∀ ω : Fin 3 → ℝ, ω ≠ 0 → ¬ ∀ᵐ r ∂μ, Vec3.hat r *ᵥ ω = 0 := by
  have hnn : ∀ ω : Fin 3 → ℝ,
      0 ≤ fun r : Vec3 => (Vec3.hat r *ᵥ ω) ⬝ᵥ (Vec3.hat r *ᵥ ω) := fun ω r => by
    simpa using dotProduct_star_self_nonneg (Vec3.hat r *ᵥ ω)
  constructor
  · intro hP ω hω hae
    have hpos := hP.dotProduct_mulVec_pos hω
    simp only [star_trivial] at hpos
    rw [dotProduct_inertiaTensor_mulVec μ h] at hpos
    have h0 : ∫ r, (Vec3.hat r *ᵥ ω) ⬝ᵥ (Vec3.hat r *ᵥ ω) ∂μ = 0 := by
      rw [integral_eq_zero_iff_of_nonneg (hnn ω) (integrable_hat_mulVec_dotProduct h ω)]
      filter_upwards [hae] with r hr
      simp [hr]
    linarith
  · intro hline
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · simpa using inertiaTensor_isSymm μ
    · simp only [star_trivial]
      rw [dotProduct_inertiaTensor_mulVec μ h]
      refine lt_of_le_of_ne (integral_nonneg (hnn x)) fun h0 => hline x hx ?_
      have hz := (integral_eq_zero_iff_of_nonneg (hnn x)
        (integrable_hat_mulVec_dotProduct h x)).mp h0.symm
      filter_upwards [hz] with r hr
      exact dotProduct_self_eq_zero.mp hr

/-- **The body frame at the mass center (MLS pp. 161–162).** For nonzero mass, `r̄ = 0` exactly
when the first moment `∫ ρ(r) r dV` vanishes, the condition used on p. 162 to drop the cross term
of the kinetic energy. -/
theorem centerOfMass_eq_zero_iff (hm : mass μ ≠ 0) :
    centerOfMass μ = 0 ↔ ∫ r, r ∂μ = 0 := by
  rw [centerOfMass, smul_eq_zero]
  simp [hm]

/-- **The first moment about the center of mass vanishes (MLS pp. 161–162):**
`∫ (r − r̄) dμ = 0` for nonzero (hence finite) mass and integrable first moment. -/
theorem integral_sub_centerOfMass (hm : mass μ ≠ 0) (h1 : Integrable (fun r : Vec3 => r) μ) :
    ∫ r, (r - centerOfMass μ) ∂μ = 0 := by
  have hfin : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr fun htop => hm (by
    simp [mass, Measure.real, htop])⟩
  rw [integral_sub h1 (integrable_const _), integral_const, centerOfMass, smul_smul]
  change ∫ r, r ∂μ - (mass μ * (mass μ)⁻¹) • ∫ r, r ∂μ = 0
  rw [mul_inv_cancel₀ hm, one_smul, sub_self]

/-- The mass of a distribution is nonnegative (MLS p. 161). -/
theorem mass_nonneg : 0 ≤ mass μ := measureReal_nonneg

/-- **MLS eq. (4.9), p. 162, for a mass distribution:** the generalized inertia
`[[m I, 0], [0, 𝓘]]` with `m = mass μ` and `𝓘 = inertiaTensor μ` is positive semidefinite
whenever the second moment is integrable (the hypotheses of `generalizedInertia_posSemidef` are
theorems for distributions). -/
theorem generalizedInertia_posSemidef_of_distribution
    (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ) :
    (generalizedInertia (mass μ) (inertiaTensor μ)).PosSemidef :=
  generalizedInertia_posSemidef (mass_nonneg μ) (inertiaTensor_posSemidef μ h)

/-- **MLS p. 162, "positive definite", for a mass distribution:** the generalized inertia
`[[m I, 0], [0, 𝓘]]` of a distribution with positive mass and integrable second moment that is not
concentrated on a line through the body-frame origin is positive definite (the hypotheses of
`generalizedInertia_posDef`, read for distributions). -/
theorem generalizedInertia_posDef_of_distribution (hm : 0 < mass μ)
    (h : Integrable (fun r : Vec3 => ‖r‖ ^ 2) μ)
    (hline : ∀ ω : Fin 3 → ℝ, ω ≠ 0 → ¬ ∀ᵐ r ∂μ, Vec3.hat r *ᵥ ω = 0) :
    (generalizedInertia (mass μ) (inertiaTensor μ)).PosDef :=
  generalizedInertia_posDef hm ((inertiaTensor_posDef_iff μ h).mpr hline)


/-! ### MLS Example 4.2: the homogeneous bar (p. 163) -/

/-- The coordinate intervals of the bar of MLS Example 4.2, p. 163: `[−l/2, l/2]` (length, `x`),
`[−w/2, w/2]` (width, `y`), `[−h/2, h/2]` (height, `z`), the integration limits printed there. -/
def barIntervals (l w h : ℝ) : Fin 3 → Set ℝ :=
  ![Set.Icc (-(l / 2)) (l / 2), Set.Icc (-(w / 2)) (w / 2), Set.Icc (-(h / 2)) (h / 2)]

/-- **The volume `V` of the bar of MLS Example 4.2, Figure 4.3, p. 163:** the box
`[−l/2, l/2] × [−w/2, w/2] × [−h/2, h/2]` in body-frame coordinates, frame at the center of the
bar with axes along its principal axes. -/
def barRegion (l w h : ℝ) : Set Vec3 :=
  WithLp.toLp 2 '' Set.univ.pi (barIntervals l w h)

/-- **The homogeneous bar of MLS Example 4.2, p. 163:** mass density `ρ = m/(l w h)` on the box
`barRegion l w h`, as the measure `(m/(l w h)) · volume` restricted to the box (the density is
taken as `ENNReal.ofReal`, so the theorems assume `0 ≤ m` and positive side lengths). -/
def barDistribution (m l w h : ℝ) : Measure Vec3 :=
  ENNReal.ofReal (m / (l * w * h)) • volume.restrict (barRegion l w h)

private def barPi (l w h : ℝ) : Measure (Fin 3 → ℝ) :=
  Measure.pi fun i => (volume : Measure ℝ).restrict (barIntervals l w h i)

private theorem integral_barDistribution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m l w h : ℝ} (hρ : 0 ≤ m / (l * w * h)) (f : Vec3 → E) :
    ∫ r, f r ∂(barDistribution m l w h) =
      (m / (l * w * h)) • ∫ x, f (WithLp.toLp 2 x) ∂(barPi l w h) := by
  rw [barDistribution, integral_smul_measure, ENNReal.toReal_ofReal hρ]
  congr 1
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → Vec3) ⁻¹' barRegion l w h =
      Set.univ.pi (barIntervals l w h) :=
    Set.preimage_image_eq _ (WithLp.toLp_injective 2)
  have h := (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding f (barRegion l w h)
  rw [hpre, volume_pi, Measure.restrict_pi_pi] at h
  exact h.symm


private theorem integral_Icc_one {a : ℝ} (ha : 0 ≤ a) :
    ∫ _ in Set.Icc (-a) a, (1 : ℝ) = 2 * a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  simp
  ring

private theorem integral_Icc_id {a : ℝ} (ha : 0 ≤ a) : ∫ t in Set.Icc (-a) a, t = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_id]
  ring

private theorem integral_Icc_sq {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Set.Icc (-a) a, t ^ 2 = 2 * a ^ 3 / 3 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  ring

private theorem mul_eq_prod (x : Fin 3 → ℝ) (i j : Fin 3) :
    x i * x j = ∏ k, (if k = i then x k else 1) * (if k = j then x k else 1) := by
  fin_cases i <;> fin_cases j <;> simp [Fin.prod_univ_three] <;> ring

private theorem integral_barPi_mul {l w h : ℝ} (hl : 0 ≤ l) (hw : 0 ≤ w) (hh : 0 ≤ h)
    (i j : Fin 3) :
    ∫ x, x i * x j ∂(barPi l w h) =
      if i = j then ![l ^ 3 * w * h / 12, l * w ^ 3 * h / 12, l * w * h ^ 3 / 12] i else 0 := by
  simp_rw [mul_eq_prod]
  rw [barPi, integral_fintype_prod_eq_prod (fun k t => (if k = i then t else 1) *
    (if k = j then t else 1))]
  have h1 := integral_Icc_one (by linarith : 0 ≤ l / 2)
  have h2 := integral_Icc_one (by linarith : 0 ≤ w / 2)
  have h3 := integral_Icc_one (by linarith : 0 ≤ h / 2)
  have i1 := integral_Icc_id (by linarith : 0 ≤ l / 2)
  have i2 := integral_Icc_id (by linarith : 0 ≤ w / 2)
  have i3 := integral_Icc_id (by linarith : 0 ≤ h / 2)
  have q1 := integral_Icc_sq (by linarith : 0 ≤ l / 2)
  have q2 := integral_Icc_sq (by linarith : 0 ≤ w / 2)
  have q3 := integral_Icc_sq (by linarith : 0 ≤ h / 2)
  fin_cases i <;> fin_cases j <;>
    simp [Fin.prod_univ_three, barIntervals, ← pow_two, h1, h2, h3, i1, i2, i3, q1, q2, q3] <;>
    ring


private theorem integrable_barPi_mul (l w h : ℝ) (i j : Fin 3) :
    Integrable (fun x : Fin 3 → ℝ => x i * x j) (barPi l w h) := by
  simp_rw [mul_eq_prod]
  refine Integrable.fintype_prod (f := fun k t => (if k = i then t else 1) *
    (if k = j then t else 1)) fun k => ?_
  have hc : Continuous fun t : ℝ => (if k = i then t else 1) * (if k = j then t else 1) := by
    split_ifs <;> fun_prop
  fin_cases k <;> exact hc.integrableOn_Icc

private theorem integral_barPi_one {l w h : ℝ} (hl : 0 ≤ l) (hw : 0 ≤ w) (hh : 0 ≤ h) :
    ∫ _, (1 : ℝ) ∂(barPi l w h) = l * w * h := by
  have e := integral_fintype_prod_eq_prod (fun (_ : Fin 3) (_ : ℝ) => (1 : ℝ))
    (μ := fun i => (volume : Measure ℝ).restrict (barIntervals l w h i))
  simp only [Finset.prod_const_one] at e
  rw [barPi, e]
  simp [Fin.prod_univ_three, barIntervals, max_eq_left hl, max_eq_left hw, max_eq_left hh]

/-- **MLS Example 4.2, p. 163:** the homogeneous bar has mass `m`. -/
theorem mass_barDistribution {m l w h : ℝ} (hm : 0 ≤ m) (hl : 0 < l) (hw : 0 < w) (hh : 0 < h) :
    mass (barDistribution m l w h) = m := by
  have hρ : 0 ≤ m / (l * w * h) := by positivity
  have e : mass (barDistribution m l w h) = ∫ _, (1 : ℝ) ∂(barDistribution m l w h) := by
    rw [integral_const, smul_eq_mul, mul_one, mass]
  rw [e, integral_barDistribution hρ, integral_barPi_one hl.le hw.le hh.le, smul_eq_mul]
  field_simp

/-- **MLS Example 4.2, p. 163: the inertia tensor of the homogeneous bar**, computed from the
integral `−∫ ρ r̂² dV`:
`𝓘 = diag(m (w² + h²)/12, m (l² + h²)/12, m (l² + w²)/12)`, as printed. -/
theorem inertiaTensor_barDistribution {m l w h : ℝ} (hm : 0 ≤ m) (hl : 0 < l) (hw : 0 < w)
    (hh : 0 < h) :
    inertiaTensor (barDistribution m l w h) =
      Matrix.diagonal ![m / 12 * (w ^ 2 + h ^ 2), m / 12 * (l ^ 2 + h ^ 2),
        m / 12 * (l ^ 2 + w ^ 2)] := by
  have hρ : 0 ≤ m / (l * w * h) := by positivity
  ext i j
  rw [inertiaTensor_apply, integral_barDistribution hρ]
  have e : ∀ x : Fin 3 → ℝ, ((if i = j then ‖(WithLp.toLp 2 x : Vec3)‖ ^ 2 else 0) -
      (WithLp.toLp 2 x : Vec3) i * (WithLp.toLp 2 x : Vec3) j) =
      (if i = j then ∑ k, x k * x k else 0) - x i * x j := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [pow_two]
  simp_rw [e]
  have hI := integrable_barPi_mul l w h
  have hS : Integrable (fun x : Fin 3 → ℝ => if i = j then ∑ k, x k * x k else 0)
      (barPi l w h) := by
    split_ifs
    · exact integrable_finsetSum _ fun k _ => hI k k
    · exact integrable_zero _ _ _
  rw [integral_sub hS (hI i j), integral_barPi_mul hl.le hw.le hh.le]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [integral_finsetSum _ fun k _ => hI k k, Fin.sum_univ_three,
      integral_barPi_mul hl.le hw.le hh.le, integral_barPi_mul hl.le hw.le hh.le,
      integral_barPi_mul hl.le hw.le hh.le, Matrix.diagonal_apply_eq]
    fin_cases i <;> simp <;> field_simp <;> ring
  · simp [hij]


/-- The box of MLS Example 4.2 (p. 163) is compact. -/
theorem isCompact_barRegion (l w h : ℝ) : IsCompact (barRegion l w h) := by
  refine (isCompact_univ_pi fun i => ?_).image (PiLp.continuous_toLp 2 _)
  fin_cases i <;> exact isCompact_Icc

/-- Every continuous function is integrable for the homogeneous bar of MLS Example 4.2
(p. 163), a finite measure on a compact box; in particular its second moment is. -/
theorem integrable_barDistribution {E : Type*} [NormedAddCommGroup E] {f : Vec3 → E}
    (hf : Continuous f) (m l w h : ℝ) : Integrable f (barDistribution m l w h) :=
  (hf.continuousOn.integrableOn_compact (isCompact_barRegion l w h)).smul_measure
    ENNReal.ofReal_ne_top

private theorem integral_barPi_apply {l w h : ℝ} (hl : 0 ≤ l) (hw : 0 ≤ w) (hh : 0 ≤ h)
    (i : Fin 3) : ∫ x, x i ∂(barPi l w h) = 0 := by
  have e : ∀ x : Fin 3 → ℝ, x i = ∏ k, (if k = i then x k else 1) := by
    intro x
    simp
  simp_rw [e]
  rw [barPi, integral_fintype_prod_eq_prod (fun k t => if k = i then t else 1)]
  have i1 := integral_Icc_id (by linarith : 0 ≤ l / 2)
  have i2 := integral_Icc_id (by linarith : 0 ≤ w / 2)
  have i3 := integral_Icc_id (by linarith : 0 ≤ h / 2)
  fin_cases i <;> simp [Fin.prod_univ_three, barIntervals, i1, i2, i3]

/-- **MLS Example 4.2, p. 163:** the first moment of the homogeneous bar about the center of the
box vanishes, `∫ ρ(r) r dV = 0`. -/
theorem integral_id_barDistribution {m l w h : ℝ} (hm : 0 ≤ m) (hl : 0 < l) (hw : 0 < w)
    (hh : 0 < h) : ∫ r, r ∂(barDistribution m l w h) = 0 := by
  have hρ : 0 ≤ m / (l * w * h) := by positivity
  have hint := integrable_barDistribution (f := fun r : Vec3 => r) continuous_id m l w h
  ext i
  change EuclideanSpace.proj i (∫ r, r ∂(barDistribution m l w h)) = 0
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  change ∫ r, (r : Vec3) i ∂(barDistribution m l w h) = 0
  rw [integral_barDistribution hρ]
  simp [integral_barPi_apply hl.le hw.le hh.le]

/-- **MLS Example 4.2, p. 163: "we attach a coordinate frame at the center of mass of the bar"**:
the center of mass of the homogeneous bar is the origin of the box frame. -/
theorem centerOfMass_barDistribution {m l w h : ℝ} (hm : 0 ≤ m) (hl : 0 < l) (hw : 0 < w)
    (hh : 0 < h) : centerOfMass (barDistribution m l w h) = 0 := by
  rw [centerOfMass, integral_id_barDistribution hm hl hw hh, smul_zero]

/-- The inertia tensor of the homogeneous bar of MLS Example 4.2 (p. 163) is positive definite for
positive mass and side lengths. -/
theorem inertiaTensor_barDistribution_posDef {m l w h : ℝ} (hm : 0 < m) (hl : 0 < l)
    (hw : 0 < w) (hh : 0 < h) : (inertiaTensor (barDistribution m l w h)).PosDef := by
  rw [inertiaTensor_barDistribution hm.le hl hw hh]
  refine Matrix.PosDef.diagonal fun i => ?_
  fin_cases i <;> simp <;> positivity

/-- **MLS Example 4.2, p. 163: the generalized inertia matrix of the bar**,
`M = [[m I, 0], [0, diag(m (w² + h²)/12, m (l² + h²)/12, m (l² + w²)/12)]]`, from its mass and
inertia tensor. -/
theorem generalizedInertia_barDistribution {m l w h : ℝ} (hm : 0 ≤ m) (hl : 0 < l)
    (hw : 0 < w) (hh : 0 < h) :
    generalizedInertia (mass (barDistribution m l w h)) (inertiaTensor (barDistribution m l w h)) =
      generalizedInertia m (Matrix.diagonal ![m / 12 * (w ^ 2 + h ^ 2),
        m / 12 * (l ^ 2 + h ^ 2), m / 12 * (l ^ 2 + w ^ 2)]) := by
  rw [mass_barDistribution hm hl hw hh, inertiaTensor_barDistribution hm hl hw hh]

end RigidBody
end RoboLean
