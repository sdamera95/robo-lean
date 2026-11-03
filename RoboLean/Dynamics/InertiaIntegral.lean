import RoboLean.Dynamics.KineticEnergyIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Inertia tensors of homogeneous bodies: the ellipsoid and the cylinder of MLS Chapter 4, Exercise 2

MLS Chapter 4, Exercise 2, printed p. 208: "Compute the inertia tensor for the objects shown
below", (a) an ellipsoid with semi-axes `a, b, c` and (b) a cylinder of radius `r` and height `h`.
No mass, density or frame is printed.

**Reading (a convention of this file).** As in Example 4.2 (p. 163), the body is homogeneous with
mass `m`, `ρ = m / vol(V)` (MLS p. 161: "If the object is made from a homogeneous material, then
`ρ(r) = ρ`, a constant"), the body frame is at the center with its axes along the axes of the
figure. A homogeneous body of mass `m` filling a region `V` is the measure
`homogeneousDistribution m V = (m / vol V) · volume|_V`, the carrier of
`RoboLean.Dynamics.InertiaTensor`. The ellipsoid is
`{x : (x₁/a)² + (x₂/b)² + (x₃/c)² ≤ 1}` (`ellipsoidRegion`) and the cylinder
`{x : x₁² + x₂² ≤ r², |x₃| ≤ h/2}` (`cylinderRegion`, the `z`-axis along its axis).

**Result (a).** For `m ≥ 0` and `a, b, c > 0` the homogeneous ellipsoid has mass `m`, its center of mass
at the origin and the inertia tensor
`𝓘 = diag(m (b² + c²)/5, m (a² + c²)/5, m (a² + b²)/5)` (`inertiaTensor_ellipsoidDistribution`),
from the integral `−∫ ρ r̂² dV`. The route: the ellipsoid is the image of the unit ball under
`diag(a, b, c)`, so its integrals are `abc` times integrals over the ball; the second moments of
the ball are `∫ uₖ uₗ = δₖₗ vol(B)/5`, from the radial integral `∫_B ‖u‖² = (3/5) vol(B)` and the
symmetries of the ball under coordinate swaps and reflections.

With the frame at the mass center (`centerOfMass_ellipsoidDistribution`), the kinetic energy (4.8)
of the ellipsoid is the quadratic form (4.9) of `diag(m I, 𝓘)` in the body velocity
(`kineticEnergyIntegral_ellipsoidDistribution`).

**Result (b).** For `m ≥ 0` and `r, h > 0` the homogeneous cylinder has mass `m`, its center of mass at
the origin and `𝓘 = diag(m (3r² + h²)/12, m (3r² + h²)/12, m r²/2)`
(`inertiaTensor_cylinderDistribution`), with the same kinetic-energy corollary. The route: the
cylinder is the image of the unit cylinder `{x₁² + x₂² ≤ 1, |x₃| ≤ 1/2}` under `diag(r, r, h)`, whose
integrals split, through the volume-preserving maps `ℝ³ ≅ (Fin 3 → ℝ) ≅ ℝ × (Fin 2 → ℝ)`, into an
integral over `[−1/2, 1/2]` times one over the unit disc; the disc's second moments
`∫ uₖ uₗ = δₖₗ vol(D)/4` come from the same radial argument in the plane (the ball's moments are
proved in every dimension, `∫_B uₖ uₗ = δₖₗ vol(B)/(n + 2)` in `ℝⁿ`).

Nothing here concerns a physical body.
-/

noncomputable section

open Matrix MeasureTheory Metric Set

namespace RoboLean
namespace RigidBody

/-- **A homogeneous body (MLS p. 161, `ρ(r) = ρ` constant; Example 4.2, p. 163):** mass `m`
uniformly distributed on the region `V`, the measure `(m / vol V) · volume` restricted to `V`. -/
def homogeneousDistribution (m : ℝ) (V : Set Vec3) : Measure Vec3 :=
  ENNReal.ofReal (m / volume.real V) • volume.restrict V

/-- Integrals against a homogeneous body (MLS p. 161): `∫ f dμ = (m / vol V) ∫_V f dV`. -/
theorem integral_homogeneousDistribution {m : ℝ} (hm : 0 ≤ m) (V : Set Vec3) (f : Vec3 → ℝ) :
    ∫ r, f r ∂(homogeneousDistribution m V) = m / volume.real V * ∫ r in V, f r := by
  rw [homogeneousDistribution, integral_smul_measure,
    ENNReal.toReal_ofReal (div_nonneg hm measureReal_nonneg), smul_eq_mul]

/-- **The mass of a homogeneous body is `m` (MLS p. 161, `m = ∫_V ρ dV`)**, for a region of
positive finite volume and `m ≥ 0`. -/
theorem mass_homogeneousDistribution {m : ℝ} (hm : 0 ≤ m) {V : Set Vec3} (h0 : volume V ≠ 0)
    (htop : volume V ≠ ⊤) : mass (homogeneousDistribution m V) = m := by
  have hpos : 0 < volume.real V := ENNReal.toReal_pos h0 htop
  have e : mass (homogeneousDistribution m V) = ∫ _, (1 : ℝ) ∂(homogeneousDistribution m V) := by
    rw [integral_const, smul_eq_mul, mul_one, mass]
  rw [e, integral_homogeneousDistribution hm, setIntegral_const, smul_eq_mul, mul_one]
  field_simp

/-- **The solid ellipsoid of MLS Chapter 4, Exercise 2(a), p. 208** with semi-axes `a, b, c` along
the body-frame axes: `{x : (x₁/a)² + (x₂/b)² + (x₃/c)² ≤ 1}`. -/
def ellipsoidRegion (a b c : ℝ) : Set Vec3 :=
  {x | (x 0 / a) ^ 2 + (x 1 / b) ^ 2 + (x 2 / c) ^ 2 ≤ 1}

/-- **The homogeneous ellipsoid of MLS Chapter 4, Exercise 2(a), p. 208:** mass `m` uniformly
distributed on `ellipsoidRegion a b c`, frame at the center along the semi-axes. -/
def ellipsoidDistribution (m a b c : ℝ) : Measure Vec3 :=
  homogeneousDistribution m (ellipsoidRegion a b c)

/-! ### Second moments of the unit ball in `ℝⁿ` -/

private abbrev Bn (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 1

private theorem integrableOn_Bn {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) :
    IntegrableOn f (Bn n) :=
  hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)

private theorem integral_Bn_isometry {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : ∫ x in Bn n, g (e x) = ∫ x in Bn n, g x := by
  rw [← integral_indicator measurableSet_closedBall, ← integral_indicator measurableSet_closedBall]
  have h : (Bn n).indicator (fun x => g (e x)) = fun x => (Bn n).indicator g (e x) := by
    funext x
    simp [Set.indicator]
  rw [h]
  exact e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding _

private theorem integral_Bn_normSq (n : ℕ) :
    ∫ x in Bn (n + 1), ‖x‖ ^ 2 = (n + 1) / (n + 3) * volume.real (Bn (n + 1)) := by
  rw [← integral_indicator measurableSet_closedBall]
  have h : (Bn (n + 1)).indicator (fun x => ‖x‖ ^ 2) =
      fun x => (fun y : ℝ => if y ≤ 1 then y ^ 2 else 0) ‖x‖ := by
    funext x
    simp [Set.indicator]
  rw [h, integral_fun_norm_addHaar volume (fun y : ℝ => if y ≤ 1 then y ^ 2 else 0),
    finrank_euclideanSpace_fin]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (n + 1 - 1) • (if y ≤ 1 then y ^ 2 else 0) =
      1 / (n + 3) := by
    have e : (fun y : ℝ => y ^ (n + 1 - 1) • (if y ≤ 1 then y ^ 2 else 0)) =
        (Iic (1 : ℝ)).indicator fun y => y ^ (n + 2) := by
      funext y
      by_cases hy : y ≤ 1
      · simp [Set.indicator, hy]
        ring
      · simp [Set.indicator, hy]
    rw [e, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, ← intervalIntegral.integral_of_le
      zero_le_one, integral_pow]
    push_cast
    ring_nf
  rw [hI, nsmul_eq_mul, smul_eq_mul, Measure.real, Measure.real,
    Measure.addHaar_closedBall_eq_addHaar_ball]
  push_cast
  ring

private theorem hcoordn {n : ℕ} (k : Fin n) : Continuous fun x : EuclideanSpace ℝ (Fin n) => x k :=
  (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous

private theorem Bn_sq_swap {n : ℕ} (i j : Fin n) : ∫ x in Bn n, x i ^ 2 = ∫ x in Bn n, x j ^ 2 := by
  have h := integral_Bn_isometry (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j))
    (fun x => x i ^ 2)
  simpa [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply] using h.symm

private def coordReflection {n : ℕ} (k : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    if i = k then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

private theorem coordReflection_apply {n : ℕ} (k : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : coordReflection k x i = if i = k then -x i else x i := by
  by_cases h : i = k <;> simp [coordReflection, LinearIsometryEquiv.piLpCongrRight_apply, h]

private theorem Bn_cross {n : ℕ} {i j : Fin n} (hij : i ≠ j) : ∫ x in Bn n, x i * x j = 0 := by
  have h := integral_Bn_isometry (coordReflection i) (fun x => x i * x j)
  have hji : j ≠ i := Ne.symm hij
  simp only [coordReflection_apply, hji, ↓reduceIte, neg_mul, integral_neg] at h
  linarith

private theorem Bn_first {n : ℕ} (i : Fin n) : ∫ x in Bn n, x i = 0 := by
  have h := integral_Bn_isometry (coordReflection i) (fun x => x i)
  simp only [coordReflection_apply, ↓reduceIte, integral_neg] at h
  linarith

private theorem Bn_moment (n : ℕ) (k l : Fin (n + 1)) :
    ∫ x in Bn (n + 1), x k * x l = if k = l then volume.real (Bn (n + 1)) / (n + 3) else 0 := by
  split_ifs with hkl
  · subst hkl
    have hi : ∀ i : Fin (n + 1), IntegrableOn (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x i ^ 2)
        (Bn (n + 1)) := fun i => integrableOn_Bn ((hcoordn i).pow 2)
    have hs : ∫ x in Bn (n + 1), ‖x‖ ^ 2 = ∑ i, ∫ x in Bn (n + 1), x i ^ 2 := by
      rw [← integral_finsetSum _ fun i _ => hi i]
      congr 1
      funext x
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_congr rfl fun i _ => Bn_sq_swap i k, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, integral_Bn_normSq] at hs
    have e : ∫ x in Bn (n + 1), x k * x k = ∫ x in Bn (n + 1), x k ^ 2 := by
      congr 1
      funext x
      ring
    rw [e]
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [← hs]
    push_cast
    field_simp
  · exact Bn_cross hkl

private abbrev B : Set Vec3 := Bn 3

private theorem integrableOn_B {f : Vec3 → ℝ} (hf : Continuous f) : IntegrableOn f B :=
  integrableOn_Bn hf

private theorem hcoord (k : Fin 3) : Continuous fun x : Vec3 => x k := hcoordn k

private theorem B_first (i : Fin 3) : ∫ x in B, x i = 0 := Bn_first i

private theorem B_moment (k l : Fin 3) :
    ∫ x in B, x k * x l = if k = l then volume.real B / 5 else 0 := by
  have h := Bn_moment 2 k l
  norm_num at h
  exact h

private theorem B_quadratic (C : Fin 3 → Fin 3 → ℝ) :
    ∫ u in B, ∑ k, ∑ l, C k l * (u k * u l) = volume.real B / 5 * ∑ k, C k k := by
  have hi : ∀ k l : Fin 3, IntegrableOn (fun u : Vec3 => C k l * (u k * u l)) B :=
    fun k l => integrableOn_B (continuous_const.mul ((hcoord k).mul (hcoord l)))
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi k l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hi k l]
  simp_rw [integral_const_mul, B_moment]
  simp [mul_comm]

/-! ### The ellipsoid as the image of the ball -/

private def scaleMap (a b c : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  Matrix.toEuclideanLin (Matrix.diagonal ![a, b, c])

private theorem scaleMap_apply (a b c : ℝ) (u : Vec3) (i : Fin 3) :
    scaleMap a b c u i = ![a, b, c] i * u i := by
  change (Matrix.diagonal ![a, b, c] *ᵥ WithLp.ofLp u) i = _
  rw [Matrix.mulVec_diagonal]

private theorem det_scaleMap (a b c : ℝ) : LinearMap.det (scaleMap a b c) = a * b * c := by
  rw [scaleMap, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    Matrix.det_diagonal, Fin.prod_univ_three]
  simp [mul_assoc]

private theorem ellipsoidRegion_eq {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ellipsoidRegion a b c = scaleMap a b c '' B := by
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.toLp 2 ![x 0 / a, x 1 / b, x 2 / c], ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
        Fin.sum_univ_three]
      simpa [ellipsoidRegion] using hx
    · ext i
      fin_cases i <;> simp [scaleMap_apply] <;> field_simp
  · rintro ⟨u, hu, rfl⟩
    rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three] at hu
    show (scaleMap a b c u 0 / a) ^ 2 + (scaleMap a b c u 1 / b) ^ 2 +
      (scaleMap a b c u 2 / c) ^ 2 ≤ 1
    rw [scaleMap_apply, scaleMap_apply, scaleMap_apply]
    have e0 : ![a, b, c] 0 * u 0 / a = u 0 := by simp; field_simp
    have e1 : ![a, b, c] 1 * u 1 / b = u 1 := by simp; field_simp
    have e2 : ![a, b, c] 2 * u 2 / c = u 2 := by simp; field_simp
    rw [e0, e1, e2]
    simpa using hu

private theorem measurableEmbedding_scaleMap {a b c : ℝ} (h : a * b * c ≠ 0) :
    MeasurableEmbedding (scaleMap a b c) := by
  have hdet : LinearMap.det (scaleMap a b c) ≠ 0 := by rw [det_scaleMap]; exact h
  exact (LinearMap.equivOfDetNeZero (scaleMap a b c) hdet).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

private theorem integral_image_scaleMap {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (S : Set Vec3) (f : Vec3 → ℝ) :
    ∫ x in scaleMap a b c '' S, f x = a * b * c * ∫ u in S, f (scaleMap a b c u) := by
  have habc : 0 < a * b * c := by positivity
  have hdet : LinearMap.det (scaleMap a b c) ≠ 0 := by rw [det_scaleMap]; exact habc.ne'
  have hemb := measurableEmbedding_scaleMap habc.ne'
  have hmap : Measure.map (scaleMap a b c) (volume.restrict S) =
      ENNReal.ofReal |(a * b * c)⁻¹| • volume.restrict (scaleMap a b c '' S) := by
    rw [← Measure.restrict_smul, ← det_scaleMap,
      ← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, hemb.restrict_map,
      Set.preimage_image_eq _ hemb.injective]
  have h := hemb.integral_map (μ := volume.restrict S) f
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr habc), smul_eq_mul] at h
  rw [← h]
  field_simp

private theorem integral_ellipsoidRegion {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (f : Vec3 → ℝ) :
    ∫ x in ellipsoidRegion a b c, f x = a * b * c * ∫ u in B, f (scaleMap a b c u) := by
  rw [ellipsoidRegion_eq ha hb hc, integral_image_scaleMap ha hb hc]

private theorem volume_ellipsoidRegion {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume (ellipsoidRegion a b c) = ENNReal.ofReal (a * b * c) * volume B := by
  rw [ellipsoidRegion_eq ha hb hc, Measure.addHaar_image_linearMap, det_scaleMap,
    abs_of_pos (by positivity)]

private theorem volume_B_ne_zero : volume B ≠ 0 := (measure_closedBall_pos volume 0 one_pos).ne'

private theorem volume_B_ne_top : volume B ≠ ⊤ := measure_closedBall_lt_top.ne

private theorem volume_ellipsoidRegion_ne {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume (ellipsoidRegion a b c) ≠ 0 ∧ volume (ellipsoidRegion a b c) ≠ ⊤ := by
  rw [volume_ellipsoidRegion ha hb hc]
  exact ⟨mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' volume_B_ne_zero,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top volume_B_ne_top⟩

/-! ### MLS Chapter 4, Exercise 2(a) -/

/-- **MLS Chapter 4, Exercise 2(a), p. 208: the homogeneous ellipsoid has mass `m`**, for `m ≥ 0`
and positive semi-axes. -/
theorem mass_ellipsoidDistribution {m a b c : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : mass (ellipsoidDistribution m a b c) = m :=
  mass_homogeneousDistribution hm (volume_ellipsoidRegion_ne ha hb hc).1
    (volume_ellipsoidRegion_ne ha hb hc).2

/-- **MLS Chapter 4, Exercise 2(a), p. 208: the inertia tensor of the homogeneous ellipsoid**,
computed from `𝓘 = −∫ ρ r̂² dV` (p. 162) with `ρ = m / vol(V)`, frame at the center along the
semi-axes: `𝓘 = diag(m (b² + c²)/5, m (a² + c²)/5, m (a² + b²)/5)`, for `m ≥ 0` and
`a, b, c > 0`. -/
theorem inertiaTensor_ellipsoidDistribution {m a b c : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    inertiaTensor (ellipsoidDistribution m a b c) =
      Matrix.diagonal ![m / 5 * (b ^ 2 + c ^ 2), m / 5 * (a ^ 2 + c ^ 2),
        m / 5 * (a ^ 2 + b ^ 2)] := by
  have habc : 0 < a * b * c := by positivity
  have hV : volume.real (ellipsoidRegion a b c) = a * b * c * volume.real B := by
    rw [Measure.real, volume_ellipsoidRegion ha hb hc, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal habc.le]
    rfl
  have hB : 0 < volume.real B := ENNReal.toReal_pos volume_B_ne_zero volume_B_ne_top
  let d : Fin 3 → ℝ := ![a, b, c]
  ext i j
  let C : Fin 3 → Fin 3 → ℝ := fun k l =>
    (if i = j ∧ k = l then d k ^ 2 else 0) - (if k = i ∧ l = j then d i * d j else 0)
  have key : ∀ u : Vec3,
      ((if i = j then ‖scaleMap a b c u‖ ^ 2 else 0) - scaleMap a b c u i * scaleMap a b c u j) =
        ∑ k, ∑ l, C k l * (u k * u l) := by
    intro u
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> fin_cases j <;>
      simp [C, d, Fin.sum_univ_three, scaleMap_apply] <;> ring
  have hint : ∫ u in B, ((if i = j then ‖scaleMap a b c u‖ ^ 2 else 0) -
      scaleMap a b c u i * scaleMap a b c u j) = ∫ u in B, ∑ k, ∑ l, C k l * (u k * u l) := by
    congr 1
    funext u
    exact key u
  rw [inertiaTensor_apply, ellipsoidDistribution, integral_homogeneousDistribution hm,
    integral_ellipsoidRegion ha hb hc, hV, hint, B_quadratic]
  fin_cases i <;> fin_cases j <;>
    simp [C, d, Fin.sum_univ_three, Matrix.diagonal] <;> field_simp <;> ring

private theorem isCompact_ellipsoidRegion {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsCompact (ellipsoidRegion a b c) := by
  rw [ellipsoidRegion_eq ha hb hc]
  exact (isCompact_closedBall 0 1).image (scaleMap a b c).continuous_of_finiteDimensional

/-- Every continuous function is integrable for the homogeneous ellipsoid of MLS Chapter 4,
Exercise 2(a) (p. 208), a finite measure on a compact region; in particular its first and second
moments are. -/
theorem integrable_ellipsoidDistribution {E : Type*} [NormedAddCommGroup E] {f : Vec3 → E}
    (hf : Continuous f) (m : ℝ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Integrable f (ellipsoidDistribution m a b c) :=
  (hf.continuousOn.integrableOn_compact (isCompact_ellipsoidRegion ha hb hc)).smul_measure
    ENNReal.ofReal_ne_top

/-- **MLS Chapter 4, Exercise 2(a), p. 208: the frame at the center of the ellipsoid is at its
mass center**: the first moment `∫ ρ r dV` of the homogeneous ellipsoid vanishes. -/
theorem integral_id_ellipsoidDistribution {m a b c : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : ∫ r, r ∂(ellipsoidDistribution m a b c) = 0 := by
  have hint := integrable_ellipsoidDistribution (f := fun r : Vec3 => r) continuous_id m ha hb hc
  ext i
  change EuclideanSpace.proj i (∫ r, r ∂(ellipsoidDistribution m a b c)) = 0
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  change ∫ r, (r : Vec3) i ∂(ellipsoidDistribution m a b c) = 0
  rw [ellipsoidDistribution, integral_homogeneousDistribution hm, integral_ellipsoidRegion ha hb hc]
  simp_rw [scaleMap_apply]
  rw [integral_const_mul, B_first]
  simp

/-- **MLS Chapter 4, Exercise 2(a), p. 208:** the center of mass of the homogeneous ellipsoid is the
origin of its frame. -/
theorem centerOfMass_ellipsoidDistribution {m a b c : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : centerOfMass (ellipsoidDistribution m a b c) = 0 := by
  rw [centerOfMass, integral_id_ellipsoidDistribution hm ha hb hc, smul_zero]

/-- **MLS eqs. (4.8)–(4.9), p. 162, for the ellipsoid of Exercise 2(a), p. 208:** along any pose
trajectory of a frame at its center, the kinetic energy `½ ∫ ρ ‖ṗ + Ṙ r‖² dV` of the homogeneous
ellipsoid of mass `m > 0` is `½ (Vᵇ)ᵀ [[m I, 0], [0, 𝓘]] Vᵇ` with
`𝓘 = diag(m (b² + c²)/5, m (a² + c²)/5, m (a² + b²)/5)`. -/
theorem kineticEnergyIntegral_ellipsoidDistribution {m a b c : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (h : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    kineticEnergyIntegral (ellipsoidDistribution m a b c) (RigidTransform.translationDerivative D)
        D.toBlocks₁₁ =
      kineticEnergy (generalizedInertia m (Matrix.diagonal ![m / 5 * (b ^ 2 + c ^ 2),
        m / 5 * (a ^ 2 + c ^ 2), m / 5 * (a ^ 2 + b ^ 2)])) (RigidTransform.bodyVelocity g D t h) := by
  have hmass := mass_ellipsoidDistribution hm.le ha hb hc
  rw [kineticEnergyIntegral_eq_generalizedInertia _ (by rw [hmass]; exact hm)
    (integrable_ellipsoidDistribution (continuous_norm.pow 2) m ha hb hc)
    (centerOfMass_ellipsoidDistribution hm.le ha hb hc) h, hmass,
    inertiaTensor_ellipsoidDistribution hm.le ha hb hc]

/-! ### MLS Chapter 4, Exercise 2(b): the cylinder -/

/-- **The solid cylinder of MLS Chapter 4, Exercise 2(b), p. 208** of radius `r` and height `h`,
with the frame at its center and the `z`-axis along its axis:
`{x : x₁² + x₂² ≤ r², |x₃| ≤ h/2}`. -/
def cylinderRegion (r h : ℝ) : Set Vec3 := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2 ∧ |x 2| ≤ h / 2}

/-- **The homogeneous cylinder of MLS Chapter 4, Exercise 2(b), p. 208:** mass `m` uniformly
distributed on `cylinderRegion r h`. -/
def cylinderDistribution (m r h : ℝ) : Measure Vec3 :=
  homogeneousDistribution m (cylinderRegion r h)

private abbrev K : Set Vec3 := cylinderRegion 1 1

private abbrev D : Set (Fin 2 → ℝ) := {w | w 0 ^ 2 + w 1 ^ 2 ≤ 1}

private theorem succAbove_two_zero : (Fin.succAbove 2 (0 : Fin 2) : Fin 3) = 0 := by decide

private theorem succAbove_two_one : (Fin.succAbove 2 (1 : Fin 2) : Fin 3) = 1 := by decide

private theorem K_eq : K = {x : Vec3 | x 2 ∈ Icc (-(1 / 2)) (1 / 2) ∧
    (fun j => x (Fin.succAbove 2 j)) ∈ D} := by
  ext x
  simp only [cylinderRegion, mem_ofPred_eq, mem_Icc, succAbove_two_zero, succAbove_two_one,
    one_pow]
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, h1⟩
  · rintro ⟨⟨h2, h3⟩, h1⟩
    exact ⟨h1, by linarith, by linarith⟩

private theorem integral_split (f : ℝ → ℝ) (g : (Fin 2 → ℝ) → ℝ) (s : Set ℝ)
    (t : Set (Fin 2 → ℝ)) :
    ∫ x in {x : Vec3 | x 2 ∈ s ∧ (fun j => x (Fin.succAbove 2 j)) ∈ t},
        f (x 2) * g (fun j => x (Fin.succAbove 2 j)) =
      (∫ z in s, f z) * ∫ w in t, g w := by
  rw [← setIntegral_prod_mul f g s t]
  have h1 := (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (fun x : Vec3 => f (x 2) * g (fun j => x (Fin.succAbove 2 j)))
    {x : Vec3 | x 2 ∈ s ∧ (fun j => x (Fin.succAbove 2 j)) ∈ t}
  rw [← h1]
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).setIntegral_preimage_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).measurableEmbedding
    (fun p : ℝ × (Fin 2 → ℝ) => f p.1 * g p.2) (s ×ˢ t)
  rw [← Measure.volume_eq_prod, ← h2]
  rfl

private theorem integral_K (f : ℝ → ℝ) (g : (Fin 2 → ℝ) → ℝ) :
    ∫ x in K, f (x 2) * g (fun j => x (Fin.succAbove 2 j)) =
      (∫ z in Icc (-(1 / 2) : ℝ) (1 / 2), f z) * ∫ w in D, g w := by
  rw [K_eq]
  exact integral_split f g _ _

private theorem integral_D (g : (Fin 2 → ℝ) → ℝ) :
    ∫ w in D, g w = ∫ u in Bn 2, g (WithLp.ofLp u) := by
  have h := (PiLp.volume_preserving_toLp (Fin 2)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding (fun u => g (WithLp.ofLp u)) (Bn 2)
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹' Bn 2 = D := by
    ext w
    simp only [mem_preimage, mem_closedBall_zero_iff, mem_ofPred_eq]
    rw [← sq_le_one_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hpre] at h
  exact h

private abbrev A : ℝ := volume.real (Bn 2)

private theorem A_pos : 0 < A :=
  ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne

private theorem D_moment (k l : Fin 2) :
    ∫ w in D, w k * w l = if k = l then A / 4 else 0 := by
  rw [integral_D]
  have h := Bn_moment 1 k l
  norm_num at h
  exact h

private theorem D_one : ∫ _ in D, (1 : ℝ) = A := by
  rw [integral_D, setIntegral_const, smul_eq_mul, mul_one]

private theorem D_first (k : Fin 2) : ∫ w in D, w k = 0 := by
  rw [integral_D]
  exact Bn_first k

private theorem Icc_one : ∫ _ in Icc (-(1 / 2) : ℝ) (1 / 2), (1 : ℝ) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  norm_num

private theorem Icc_id : ∫ z in Icc (-(1 / 2) : ℝ) (1 / 2), z = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

private theorem Icc_sq : ∫ z in Icc (-(1 / 2) : ℝ) (1 / 2), z ^ 2 = 1 / 12 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
  norm_num

private theorem K_moment (k l : Fin 3) :
    ∫ x in K, x k * x l = if k = l then (if k = 2 then A / 12 else A / 4) else 0 := by
  have e00 := integral_K (fun _ => 1) (fun w => w 0 * w 0)
  have e01 := integral_K (fun _ => 1) (fun w => w 0 * w 1)
  have e11 := integral_K (fun _ => 1) (fun w => w 1 * w 1)
  have e02 := integral_K (fun z => z) (fun w => w 0)
  have e12 := integral_K (fun z => z) (fun w => w 1)
  have e22 := integral_K (fun z => z ^ 2) (fun _ => 1)
  simp only [succAbove_two_zero, succAbove_two_one, one_mul, mul_one] at e00 e01 e11 e02 e12 e22
  rw [Icc_one, D_moment] at e00 e01 e11
  rw [Icc_id, zero_mul] at e02 e12
  rw [Icc_sq, D_one] at e22
  have c02 : ∫ x in K, x 0 * x 2 = 0 := by
    rw [← e02]; congr 1; funext x; ring
  have c12 : ∫ x in K, x 1 * x 2 = 0 := by
    rw [← e12]; congr 1; funext x; ring
  have c20 : ∫ x in K, x 2 * x 0 = 0 := by rw [← e02]
  have c21 : ∫ x in K, x 2 * x 1 = 0 := by rw [← e12]
  have c10 : ∫ x in K, x 1 * x 0 = 0 := by
    rw [show (fun x : Vec3 => x 1 * x 0) = fun x => x 0 * x 1 from funext fun x => mul_comm _ _,
      e01]
    simp
  have c22 : ∫ x in K, x 2 * x 2 = A / 12 := by
    rw [show (fun x : Vec3 => x 2 * x 2) = fun x => x 2 ^ 2 from funext fun x => by ring, e22]
    ring
  fin_cases k <;> fin_cases l <;> simp [e00, e01, e11, c02, c12, c20, c21, c10, c22]

private theorem isCompact_K : IsCompact K := by
  rw [K_eq]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine IsClosed.inter (isClosed_Icc.preimage (hcoord 2)) (isClosed_le ?_ continuous_const)
    exact (((hcoord 0).pow 2).add ((hcoord 1).pow 2))
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨2, fun x hx => ?_⟩
    obtain ⟨⟨h2, h3⟩, h1⟩ := hx
    simp only [mem_ofPred_eq, succAbove_two_zero, succAbove_two_one] at h1
    have hn : ‖x‖ ^ 2 ≤ 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hn

private theorem K_quadratic (C : Fin 3 → Fin 3 → ℝ) :
    ∫ u in K, ∑ k, ∑ l, C k l * (u k * u l) = A / 4 * C 0 0 + A / 4 * C 1 1 + A / 12 * C 2 2 := by
  have hi : ∀ k l : Fin 3, IntegrableOn (fun u : Vec3 => C k l * (u k * u l)) K :=
    fun k l => (continuous_const.mul ((hcoord k).mul (hcoord l))).continuousOn.integrableOn_compact
      isCompact_K
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi k l]
  simp_rw [integral_finsetSum _ fun l _ => hi _ l, integral_const_mul, K_moment]
  simp [Fin.sum_univ_three]
  ring

private theorem volume_real_K : volume.real K = A := by
  have h := integral_K (fun _ => 1) (fun _ => 1)
  simp only [mul_one, Icc_one, D_one, one_mul] at h
  rw [← h, setIntegral_const, smul_eq_mul, mul_one]

private theorem cylinderRegion_eq {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    cylinderRegion r h = scaleMap r r h '' K := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨WithLp.toLp 2 ![x 0 / r, x 1 / r, x 2 / h], ⟨?_, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow]
      rw [div_pow, div_pow, ← add_div, div_le_one (by positivity)]
      exact h1
    · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
      linarith
    · ext i
      fin_cases i <;> simp [scaleMap_apply] <;> field_simp
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [scaleMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [one_pow] at h1
      nlinarith [sq_nonneg r]
    · simp only [scaleMap_apply, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [abs_mul, abs_of_pos hh]
      nlinarith [abs_nonneg (u 2)]

private theorem volume_cylinderRegion {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    volume.real (cylinderRegion r h) = r * r * h * A := by
  rw [Measure.real, cylinderRegion_eq hr hh, Measure.addHaar_image_linearMap, det_scaleMap,
    abs_of_pos (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [← volume_real_K]
  rfl

private theorem volume_cylinderRegion_ne {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    volume (cylinderRegion r h) ≠ 0 ∧ volume (cylinderRegion r h) ≠ ⊤ := by
  have hpos : 0 < volume.real (cylinderRegion r h) := by
    rw [volume_cylinderRegion hr hh]
    exact mul_pos (by positivity) A_pos
  exact ⟨fun h0 => by simp [Measure.real, h0] at hpos, fun ht => by simp [Measure.real, ht] at hpos⟩

/-- **MLS Chapter 4, Exercise 2(b), p. 208: the homogeneous cylinder has mass `m`**, for `m ≥ 0`
and positive radius and height. -/
theorem mass_cylinderDistribution {m r h : ℝ} (hm : 0 ≤ m) (hr : 0 < r) (hh : 0 < h) :
    mass (cylinderDistribution m r h) = m :=
  mass_homogeneousDistribution hm (volume_cylinderRegion_ne hr hh).1
    (volume_cylinderRegion_ne hr hh).2

/-- **MLS Chapter 4, Exercise 2(b), p. 208: the inertia tensor of the homogeneous cylinder**,
computed from `𝓘 = −∫ ρ r̂² dV` (p. 162) with `ρ = m / vol(V)`, frame at the center with the
`z`-axis along the axis: `𝓘 = diag(m (3r² + h²)/12, m (3r² + h²)/12, m r²/2)`, for `m ≥ 0` and
`r, h > 0`. -/
theorem inertiaTensor_cylinderDistribution {m r h : ℝ} (hm : 0 ≤ m) (hr : 0 < r) (hh : 0 < h) :
    inertiaTensor (cylinderDistribution m r h) =
      Matrix.diagonal ![m / 12 * (3 * r ^ 2 + h ^ 2), m / 12 * (3 * r ^ 2 + h ^ 2),
        m / 2 * r ^ 2] := by
  have hA := A_pos
  let d : Fin 3 → ℝ := ![r, r, h]
  ext i j
  let C : Fin 3 → Fin 3 → ℝ := fun k l =>
    (if i = j ∧ k = l then d k ^ 2 else 0) - (if k = i ∧ l = j then d i * d j else 0)
  have key : ∀ u : Vec3,
      ((if i = j then ‖scaleMap r r h u‖ ^ 2 else 0) - scaleMap r r h u i * scaleMap r r h u j) =
        ∑ k, ∑ l, C k l * (u k * u l) := by
    intro u
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> fin_cases j <;>
      simp [C, d, Fin.sum_univ_three, scaleMap_apply] <;> ring
  have hint : ∫ u in K, ((if i = j then ‖scaleMap r r h u‖ ^ 2 else 0) -
      scaleMap r r h u i * scaleMap r r h u j) = ∫ u in K, ∑ k, ∑ l, C k l * (u k * u l) := by
    congr 1
    funext u
    exact key u
  rw [inertiaTensor_apply, cylinderDistribution, integral_homogeneousDistribution hm,
    cylinderRegion_eq hr hh, integral_image_scaleMap hr hr hh, ← cylinderRegion_eq hr hh,
    volume_cylinderRegion hr hh, hint, K_quadratic]
  fin_cases i <;> fin_cases j <;>
    simp [C, d, Matrix.diagonal] <;> field_simp <;> ring

/-- Every continuous function is integrable for the homogeneous cylinder of MLS Chapter 4,
Exercise 2(b) (p. 208), a finite measure on a compact region. -/
theorem integrable_cylinderDistribution {E : Type*} [NormedAddCommGroup E] {f : Vec3 → E}
    (hf : Continuous f) (m : ℝ) {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    Integrable f (cylinderDistribution m r h) := by
  have hc : IsCompact (cylinderRegion r h) := by
    rw [cylinderRegion_eq hr hh]
    exact isCompact_K.image (scaleMap r r h).continuous_of_finiteDimensional
  exact (hf.continuousOn.integrableOn_compact hc).smul_measure ENNReal.ofReal_ne_top

/-- **MLS Chapter 4, Exercise 2(b), p. 208: the frame at the center of the cylinder is at its mass
center**: the first moment `∫ ρ r dV` of the homogeneous cylinder vanishes. -/
theorem integral_id_cylinderDistribution {m r h : ℝ} (hm : 0 ≤ m) (hr : 0 < r) (hh : 0 < h) :
    ∫ x, x ∂(cylinderDistribution m r h) = 0 := by
  have hint := integrable_cylinderDistribution (f := fun x : Vec3 => x) continuous_id m hr hh
  have f0 := integral_K (fun _ => 1) (fun w => w 0)
  have f1 := integral_K (fun _ => 1) (fun w => w 1)
  have f2 := integral_K (fun z => z) (fun _ => 1)
  simp only [succAbove_two_zero, succAbove_two_one, one_mul, mul_one] at f0 f1 f2
  rw [Icc_one, D_first, one_mul] at f0 f1
  rw [Icc_id, zero_mul] at f2
  ext i
  change EuclideanSpace.proj i (∫ x, x ∂(cylinderDistribution m r h)) = 0
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  change ∫ x, (x : Vec3) i ∂(cylinderDistribution m r h) = 0
  rw [cylinderDistribution, integral_homogeneousDistribution hm, cylinderRegion_eq hr hh,
    integral_image_scaleMap hr hr hh]
  simp_rw [scaleMap_apply]
  rw [integral_const_mul]
  fin_cases i <;> simp [f0, f1, f2]

/-- **MLS Chapter 4, Exercise 2(b), p. 208:** the center of mass of the homogeneous cylinder is the
origin of its frame. -/
theorem centerOfMass_cylinderDistribution {m r h : ℝ} (hm : 0 ≤ m) (hr : 0 < r) (hh : 0 < h) :
    centerOfMass (cylinderDistribution m r h) = 0 := by
  rw [centerOfMass, integral_id_cylinderDistribution hm hr hh, smul_zero]

/-- **MLS eqs. (4.8)–(4.9), p. 162, for the cylinder of Exercise 2(b), p. 208:** along any pose
trajectory of a frame at its center, the kinetic energy of the homogeneous cylinder of mass `m > 0`
is `½ (Vᵇ)ᵀ [[m I, 0], [0, 𝓘]] Vᵇ` with `𝓘 = diag(m (3r² + h²)/12, m (3r² + h²)/12, m r²/2)`. -/
theorem kineticEnergyIntegral_cylinderDistribution {m r h : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hh : 0 < h) {g : ℝ → RigidTransform} {D : HomogeneousMatrix} {t : ℝ}
    (hg : HasDerivAt (fun s => (g s).toHomogeneous) D t) :
    kineticEnergyIntegral (cylinderDistribution m r h) (RigidTransform.translationDerivative D)
        D.toBlocks₁₁ =
      kineticEnergy (generalizedInertia m (Matrix.diagonal ![m / 12 * (3 * r ^ 2 + h ^ 2),
        m / 12 * (3 * r ^ 2 + h ^ 2), m / 2 * r ^ 2])) (RigidTransform.bodyVelocity g D t hg) := by
  have hmass := mass_cylinderDistribution hm.le hr hh
  rw [kineticEnergyIntegral_eq_generalizedInertia _ (by rw [hmass]; exact hm)
    (integrable_cylinderDistribution (continuous_norm.pow 2) m hr hh)
    (centerOfMass_cylinderDistribution hm.le hr hh) hg, hmass,
    inertiaTensor_cylinderDistribution hm.le hr hh]

end RigidBody
end RoboLean
