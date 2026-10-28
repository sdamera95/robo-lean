import RoboLean.Nonholonomic.TwoInputs
import RoboLean.Nonholonomic.Integrability
import RoboLean.Nonholonomic.Controllability
import RoboLean.Examples.NonholonomicDisk
import RoboLean.Examples.NonholonomicCar
import RoboLean.Examples.NonholonomicFinger
import RoboLean.Examples.NonholonomicHopper

/-!
# Growth vectors and nonholonomy of MLS Examples 7.7, 7.9, 7.10 and 7.11

MLS Chapter 7, §4.2, printed pp. 341–344: the degree of nonholonomy and the (relative) growth
vectors of the hopping robot (Example 7.7: degree 2, `(2, 3)`, `(2, 1)`), the rolling disk
(Example 7.9: degree 3, `(2, 3, 4)`, `(2, 1, 1)`), the kinematic car (Example 7.10: degree 3,
`(2, 3, 4)`, `(2, 1, 1)`) and the spherical finger on a plane (Example 7.11: degree 3,
`(2, 3, 5)`, `(2, 1, 2)`); and the nonholonomy of their constraints, whose proof MLS defers to
Section 4 (p. 333).

**Formalized.** For each system, at every point of its domain (all `q` for the disk;
`cos φ ≠ 0` for the car; `cos q₁ ≠ 0` for the finger; `l + d ≠ 0` for the hopper, which at
`l = 0` is the unprinted hypothesis `d ≠ 0`): the growth and relative growth vectors, the degree of
nonholonomy, a regular filtration on the domain, the controllability rank condition of Theorem 7.5
(`L(g₁, g₂)` has full rank), the failure of the generator criterion of p. 325 (the distribution
`span{g₁, g₂}` is not involutive), and, by Proposition 7.4 ("only if", contrapositive), that the
Pfaffian constraints are not integrable with any `C²` map on any nonempty open subset of the
domain. For the disk and the hopper, whose fields are smooth everywhere, local controllability at
every point of the domain follows from Chow's theorem taken as the named statement
`ChowStatement`. Convention checks of the printed systems; nothing here concerns physical
vehicles, fingers or robots.
-/

noncomputable section

open Real Set VectorField
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-! ### The rolling disk (Examples 7.4 and 7.9) -/

/-- **MLS eq. (7.13), p. 336: the input fields `(g₁, g₂)` of the rolling disk.** -/
def diskFields (ρ : ℝ) : Fin 2 → (Fin 4 → ℝ) → Fin 4 → ℝ := ![diskG1 ρ, diskG2]

/-- **MLS Example 7.9, p. 342:** `[g₁, g₂] = g₃` as fields. -/
private theorem disk_bracket (ρ : ℝ) :
    lieBracket ℝ (diskFields ρ 0) (diskFields ρ 1) = diskG3 ρ :=
  funext (disk_lieBracket_g1_g2 ρ)

/-- **MLS Example 7.9, p. 343:** `g₁(q), g₂(q), [g₁, g₂](q)` are independent, for `ρ ≠ 0`. -/
private theorem disk_triple {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    LinearIndependent ℝ ![diskFields ρ 0 q, diskFields ρ 1 q,
      lieBracket ℝ (diskFields ρ 0) (diskFields ρ 1) q] := by
  have hc := (disk_linearIndependent hρ q).comp Fin.castSucc (Fin.castSucc_injective 3)
  convert hc using 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact disk_lieBracket_g1_g2 ρ q

/-- **MLS Example 7.9, p. 343:** `Δ₃(q) = ℝ⁴`, for `ρ ≠ 0`. -/
private theorem disk_filtrationAt_three {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    filtrationAt (diskFields ρ) 3 q = ⊤ := by
  refine filtrationAt_eq_top_of_linearIndependent (diskFields ρ) (Module.finrank_fin_fun ℝ)
    (disk_linearIndependent hρ q) ?_
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt (diskFields ρ) 0 (by norm_num) q
  · exact generator_mem_filtrationAt (diskFields ρ) 1 (by norm_num) q
  · have h := lieBracket_mem_filtrationAt_two (diskFields ρ) (i := 3) (by norm_num) q
    rwa [disk_bracket] at h
  · have h := lieBracket_lieBracket_mem_filtrationAt_three (diskFields ρ) 1 (i := 3) le_rfl q
    rwa [disk_bracket, show diskFields ρ 1 = diskG2 from rfl, disk_lieBracket_g2_g3] at h

/-- **MLS Example 7.9, p. 343: growth vector `(2, 3, 4)` and relative growth vector `(2, 1, 1)`**
at every `q`, for `ρ ≠ 0`. -/
theorem disk_growthVector {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    growthVector (diskFields ρ) 3 q = ![2, 3, 4] ∧
      relativeGrowthVector (diskFields ρ) 3 q = ![2, 1, 1] := by
  have h := growthVector_three (diskFields ρ) (disk_triple hρ q) (disk_filtrationAt_three hρ q)
  simpa using h

/-- **MLS Example 7.9, p. 343: degree of nonholonomy `3`** at every `q`, for `ρ ≠ 0`. -/
theorem disk_isDegreeOfNonholonomy {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    IsDegreeOfNonholonomy (diskFields ρ) q 3 := by
  exact isDegreeOfNonholonomy_three (diskFields ρ) (by simp) (disk_triple hρ q)
    (disk_filtrationAt_three hρ q)

/-- **MLS p. 340 for Example 7.9:** the filtration of the rolling disk is regular on all of `ℝ⁴`,
for `ρ ≠ 0`. -/
theorem disk_isRegularFiltrationOn {ρ : ℝ} (hρ : ρ ≠ 0) (q₀ : Fin 4 → ℝ) :
    IsRegularFiltrationOn (diskFields ρ) Set.univ q₀ := by
  exact isRegularFiltrationOn_three (diskFields ρ) (fun q _ => disk_triple hρ q)
    (fun q _ => disk_filtrationAt_three hρ q) (Set.mem_univ q₀)

/-- **MLS Example 7.9, p. 343, and Theorem 7.5, p. 329: the controllability rank condition,**
`L(g₁, g₂)` has rank `4` at every `q`, for `ρ ≠ 0`. -/
theorem disk_lieAlgebraAt {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    lieAlgebraAt (diskFields ρ) q = ⊤ := by
  exact lieAlgebraAt_eq_top_of_filtrationAt (diskFields ρ) (disk_filtrationAt_three hρ q)

/-- **MLS p. 325 for Example 7.9:** `span{g₁, g₂}` is not involutive on any nonempty set, for
`ρ ≠ 0`. -/
theorem disk_not_generatorsInvolutiveOn {ρ : ℝ} (hρ : ρ ≠ 0) {U : Set (Fin 4 → ℝ)}
    (hU : U.Nonempty) : ¬ GeneratorsInvolutiveOn (Set.range (diskFields ρ)) U := by
  obtain ⟨q, hq⟩ := hU
  exact not_generatorsInvolutiveOn_of_linearIndependent (diskFields ρ) hq (disk_triple hρ q)

/-- **MLS p. 333 and Proposition 7.4, p. 328, for Example 7.4:** the rolling constraint of the disk
is not integrable with a `C²` map on any nonempty open set, for `ρ ≠ 0`. -/
theorem disk_not_isC2IntegrableOn {ρ : ℝ} (hρ : ρ ≠ 0) {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) : ¬ IsC2IntegrableOn (diskConstraint ρ) U := by
  obtain ⟨q, hq⟩ := hne
  refine not_isC2IntegrableOn_of_lieBracket hU
    (fun x _ => (diskG1_contDiff ρ).differentiable (by simp) x)
    (fun x _ => diskG2_contDiff.differentiable (by simp) x)
    (fun x _ => diskConstraint_mulVec_g1 ρ x) (fun x _ => diskConstraint_mulVec_g2 ρ x) hq ?_
  rw [disk_lieBracket_g1_g2, diskConstraint_mulVec_g3]
  intro h0
  have hs : ρ * sin (q 2) = 0 := by simpa using congrFun h0 0
  have hc : ρ * cos (q 2) = 0 := by simpa using congrFun h0 1
  have : ρ ^ 2 * (sin (q 2) ^ 2 + cos (q 2) ^ 2) = 0 := by
    linear_combination (ρ * sin (q 2)) * hs + (ρ * cos (q 2)) * hc
  rw [sin_sq_add_cos_sq, mul_one] at this
  exact hρ (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- **MLS Theorem 7.5 (Chow), p. 329, for Example 7.9, from the named statement:** if Chow's
theorem holds on `ℝ⁴`, the rolling disk with unconstrained inputs is locally controllable at every
`q`, for `ρ ≠ 0`. -/
theorem disk_isLocallyControllableAt (hC : ChowStatement (Fin 4 → ℝ)) {ρ : ℝ} (hρ : ρ ≠ 0)
    (q : Fin 4 → ℝ) : IsLocallyControllableAt (diskFields ρ) Set.univ q := by
  refine hC 2 (diskFields ρ) ?_ q (disk_lieAlgebraAt hρ q)
  intro j
  fin_cases j
  · exact diskG1_contDiff ρ
  · exact diskG2_contDiff

/-! ### The kinematic car (Examples 7.5 and 7.10) -/

/-- **MLS eq. (7.14), p. 337: the input fields `(g₁, g₂)` of the kinematic car.** -/
def carFields (l : ℝ) : Fin 2 → (Fin 4 → ℝ) → Fin 4 → ℝ := ![carG1 l, carG2]

/-- **MLS p. 343: the domain of the car's fields,** `cos φ ≠ 0` ("at which point `g₁` is
undefined"). -/
def carDomain : Set (Fin 4 → ℝ) := {q | cos (q 3) ≠ 0}

/-- **MLS p. 343:** the car's domain is open. -/
theorem isOpen_carDomain : IsOpen carDomain := by
  exact isOpen_ne_fun (continuous_cos.comp (continuous_apply 3)) continuous_const

/-- **MLS Example 7.10, p. 343:** `[g₁, g₂] = g₃` near every point of the domain. -/
private theorem car_bracket_eventuallyEq {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ}
    (hq : q ∈ carDomain) :
    lieBracket ℝ (carFields l 0) (carFields l 1) =ᶠ[nhds q] carG3 l := by
  filter_upwards [isOpen_carDomain.mem_nhds hq] with x hx
  exact car_lieBracket_g1_g2 hl hx

/-- **MLS Example 7.10, p. 343:** `g₁(q), g₂(q), [g₁, g₂](q)` are independent on the domain. -/
private theorem car_triple {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : q ∈ carDomain) :
    LinearIndependent ℝ ![carFields l 0 q, carFields l 1 q,
      lieBracket ℝ (carFields l 0) (carFields l 1) q] := by
  have hc := (car_linearIndependent hl hq).comp Fin.castSucc (Fin.castSucc_injective 3)
  convert hc using 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact car_lieBracket_g1_g2 hl hq

/-- **MLS Example 7.10, p. 343:** `Δ₃(q) = ℝ⁴` on the domain. -/
private theorem car_filtrationAt_three {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ}
    (hq : q ∈ carDomain) : filtrationAt (carFields l) 3 q = ⊤ := by
  refine filtrationAt_eq_top_of_linearIndependent (carFields l) (Module.finrank_fin_fun ℝ)
    (car_linearIndependent hl hq) ?_
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt (carFields l) 0 (by norm_num) q
  · exact generator_mem_filtrationAt (carFields l) 1 (by norm_num) q
  · have h := lieBracket_mem_filtrationAt_two (carFields l) (i := 3) (by norm_num) q
    have e : lieBracket ℝ (carFields l 0) (carFields l 1) q = carG3 l q :=
      car_lieBracket_g1_g2 hl hq
    rwa [e] at h
  · have h := lieBracket_lieBracket_mem_filtrationAt_three (carFields l) 0 (i := 3) le_rfl q
    rwa [Filter.EventuallyEq.rfl.lieBracket_vectorField_eq (car_bracket_eventuallyEq hl hq),
      show carFields l 0 = carG1 l from rfl, car_lieBracket_g1_g3 hl hq] at h

/-- **MLS Example 7.10, p. 343: growth vector `(2, 3, 4)` and relative growth vector `(2, 1, 1)`**
at every `q` with `cos φ ≠ 0`, for `l ≠ 0`. -/
theorem car_growthVector {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : q ∈ carDomain) :
    growthVector (carFields l) 3 q = ![2, 3, 4] ∧
      relativeGrowthVector (carFields l) 3 q = ![2, 1, 1] := by
  have h := growthVector_three (carFields l) (car_triple hl hq) (car_filtrationAt_three hl hq)
  simpa using h

/-- **MLS Example 7.10, p. 343: degree of nonholonomy `3`** at every `q` with `cos φ ≠ 0`. -/
theorem car_isDegreeOfNonholonomy {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : q ∈ carDomain) :
    IsDegreeOfNonholonomy (carFields l) q 3 := by
  exact isDegreeOfNonholonomy_three (carFields l) (by simp) (car_triple hl hq)
    (car_filtrationAt_three hl hq)

/-- **MLS Example 7.10, p. 343, "regular away from `φ = ±π/2`":** the filtration of the car is
regular on the set `cos φ ≠ 0`. -/
theorem car_isRegularFiltrationOn {l : ℝ} (hl : l ≠ 0) {q₀ : Fin 4 → ℝ} (hq₀ : q₀ ∈ carDomain) :
    IsRegularFiltrationOn (carFields l) carDomain q₀ := by
  exact isRegularFiltrationOn_three (carFields l) (fun _ hq => car_triple hl hq)
    (fun _ hq => car_filtrationAt_three hl hq) hq₀

/-- **MLS Example 7.10, p. 343, and Theorem 7.5, p. 329: the controllability rank condition** at
every `q` with `cos φ ≠ 0`. -/
theorem car_lieAlgebraAt {l : ℝ} (hl : l ≠ 0) {q : Fin 4 → ℝ} (hq : q ∈ carDomain) :
    lieAlgebraAt (carFields l) q = ⊤ := by
  exact lieAlgebraAt_eq_top_of_filtrationAt (carFields l) (car_filtrationAt_three hl hq)

/-- **MLS p. 325 for Example 7.10:** `span{g₁, g₂}` is not involutive on any set meeting the
domain. -/
theorem car_not_generatorsInvolutiveOn {l : ℝ} (hl : l ≠ 0) {U : Set (Fin 4 → ℝ)}
    (hU : (U ∩ carDomain).Nonempty) : ¬ GeneratorsInvolutiveOn (Set.range (carFields l)) U := by
  obtain ⟨q, hqU, hqD⟩ := hU
  exact not_generatorsInvolutiveOn_of_linearIndependent (carFields l) hqU (car_triple hl hqD)

/-- **MLS p. 333 and Proposition 7.4, p. 328, for Example 7.5:** the no-slip constraints of the car
are not integrable with a `C²` map on any nonempty open subset of the domain. -/
theorem car_not_isC2IntegrableOn {l : ℝ} (hl : l ≠ 0) {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (hsub : U ⊆ carDomain) (hne : U.Nonempty) : ¬ IsC2IntegrableOn (carConstraint l) U := by
  obtain ⟨q, hq⟩ := hne
  refine not_isC2IntegrableOn_of_lieBracket hU
    (fun x hx => (carG1_contDiffAt l (hsub hx)).differentiableAt (by simp))
    (fun x _ => carG2_contDiff.differentiable (by simp) x)
    (fun x hx => carConstraint_mulVec_g1 hl (hsub hx)) (fun x _ => carConstraint_mulVec_g2 l x)
    hq ?_
  rw [car_lieBracket_g1_g2 hl (hsub hq), carConstraint_mulVec_g3 hl (hsub hq)]
  intro h0
  have h1 : (cos (q 3))⁻¹ = 0 := by simpa using congrFun h0 0
  exact hsub hq (inv_eq_zero.mp h1)

/-! ### The spherical finger on a plane (Examples 7.6 and 7.11) -/

/-- **MLS eq. (7.19), p. 339: the input fields `(g₁, g₂)` of the finger.** -/
def fingerFields : Fin 2 → (Fin 5 → ℝ) → Fin 5 → ℝ := ![fingerG1, fingerG2]

/-- **MLS p. 344: the domain of the finger's fields,** `cos q₁ ≠ 0` ("a neighborhood not
containing `q₁ = π/2`"). -/
def fingerDomain : Set (Fin 5 → ℝ) := {q | cos (q 0) ≠ 0}

/-- **MLS p. 344:** the finger's domain is open. -/
theorem isOpen_fingerDomain : IsOpen fingerDomain := by
  exact isOpen_ne_fun (continuous_cos.comp (continuous_apply 0)) continuous_const

/-- **MLS Example 7.11, p. 344:** `[g₁, g₂] = g₃` near every point of the domain. -/
private theorem finger_bracket_eventuallyEq {q : Fin 5 → ℝ} (hq : q ∈ fingerDomain) :
    lieBracket ℝ (fingerFields 0) (fingerFields 1) =ᶠ[nhds q] fingerG3 := by
  filter_upwards [isOpen_fingerDomain.mem_nhds hq] with x hx
  exact finger_lieBracket_g1_g2 hx

/-- **MLS Example 7.11, p. 344:** `g₁(q), g₂(q), [g₁, g₂](q)` are independent on the domain. -/
private theorem finger_triple {q : Fin 5 → ℝ} (hq : q ∈ fingerDomain) :
    LinearIndependent ℝ ![fingerFields 0 q, fingerFields 1 q,
      lieBracket ℝ (fingerFields 0) (fingerFields 1) q] := by
  have hc := (finger_linearIndependent hq).comp (Fin.castLE (by norm_num : 3 ≤ 5))
    (Fin.castLE_injective _)
  convert hc using 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact finger_lieBracket_g1_g2 hq

/-- **MLS Example 7.11, p. 344:** `Δ₃(q) = ℝ⁵` on the domain. -/
private theorem finger_filtrationAt_three {q : Fin 5 → ℝ} (hq : q ∈ fingerDomain) :
    filtrationAt fingerFields 3 q = ⊤ := by
  refine filtrationAt_eq_top_of_linearIndependent fingerFields (Module.finrank_fin_fun ℝ)
    (finger_linearIndependent hq) ?_
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt fingerFields 0 (by norm_num) q
  · exact generator_mem_filtrationAt fingerFields 1 (by norm_num) q
  · have h := lieBracket_mem_filtrationAt_two fingerFields (i := 3) (by norm_num) q
    have e : lieBracket ℝ (fingerFields 0) (fingerFields 1) q = fingerG3 q :=
      finger_lieBracket_g1_g2 hq
    rwa [e] at h
  · have h := lieBracket_lieBracket_mem_filtrationAt_three fingerFields 0 (i := 3) le_rfl q
    rwa [Filter.EventuallyEq.rfl.lieBracket_vectorField_eq (finger_bracket_eventuallyEq hq),
      show fingerFields 0 = fingerG1 from rfl, finger_lieBracket_g1_g3 hq] at h
  · have h := lieBracket_lieBracket_mem_filtrationAt_three fingerFields 1 (i := 3) le_rfl q
    rwa [Filter.EventuallyEq.rfl.lieBracket_vectorField_eq (finger_bracket_eventuallyEq hq),
      show fingerFields 1 = fingerG2 from rfl, finger_lieBracket_g2_g3 hq] at h

/-- **MLS Example 7.11, p. 344: growth vector `(2, 3, 5)` and relative growth vector `(2, 1, 2)`**
at every `q` with `cos q₁ ≠ 0`. -/
theorem finger_growthVector {q : Fin 5 → ℝ} (hq : q ∈ fingerDomain) :
    growthVector fingerFields 3 q = ![2, 3, 5] ∧
      relativeGrowthVector fingerFields 3 q = ![2, 1, 2] := by
  have h := growthVector_three fingerFields (finger_triple hq) (finger_filtrationAt_three hq)
  simp only [Module.finrank_fin_fun] at h
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num

/-- **MLS Example 7.11, p. 344: degree of nonholonomy `3`** at every `q` with `cos q₁ ≠ 0`. -/
theorem finger_isDegreeOfNonholonomy {q : Fin 5 → ℝ} (hq : q ∈ fingerDomain) :
    IsDegreeOfNonholonomy fingerFields q 3 := by
  exact isDegreeOfNonholonomy_three fingerFields (by simp) (finger_triple hq)
    (finger_filtrationAt_three hq)

/-- **MLS p. 340 for Example 7.11:** the filtration of the finger is regular on the set
`cos q₁ ≠ 0`. -/
theorem finger_isRegularFiltrationOn {q₀ : Fin 5 → ℝ} (hq₀ : q₀ ∈ fingerDomain) :
    IsRegularFiltrationOn fingerFields fingerDomain q₀ := by
  exact isRegularFiltrationOn_three fingerFields (fun _ hq => finger_triple hq)
    (fun _ hq => finger_filtrationAt_three hq) hq₀

/-- **MLS Example 7.11, p. 344, and Theorem 7.5, p. 329: the controllability rank condition** at
every `q` with `cos q₁ ≠ 0`. -/
theorem finger_lieAlgebraAt {q : Fin 5 → ℝ} (hq : q ∈ fingerDomain) :
    lieAlgebraAt fingerFields q = ⊤ := by
  exact lieAlgebraAt_eq_top_of_filtrationAt fingerFields (finger_filtrationAt_three hq)

/-- **MLS p. 325 for Example 7.11:** `span{g₁, g₂}` is not involutive on any set meeting the
domain. -/
theorem finger_not_generatorsInvolutiveOn {U : Set (Fin 5 → ℝ)}
    (hU : (U ∩ fingerDomain).Nonempty) : ¬ GeneratorsInvolutiveOn (Set.range fingerFields) U := by
  obtain ⟨q, hqU, hqD⟩ := hU
  exact not_generatorsInvolutiveOn_of_linearIndependent fingerFields hqU (finger_triple hqD)

/-- **MLS p. 333 and Proposition 7.4, p. 328, for Example 7.6:** the rolling constraints (7.17) of
the unit sphere on the plane are not integrable with a `C²` map on any nonempty open subset of the
domain. -/
theorem finger_not_isC2IntegrableOn {U : Set (Fin 5 → ℝ)} (hU : IsOpen U)
    (hsub : U ⊆ fingerDomain) (hne : U.Nonempty) : ¬ IsC2IntegrableOn fingerConstraint U := by
  obtain ⟨q, hq⟩ := hne
  refine not_isC2IntegrableOn_of_lieBracket hU
    (fun x hx => (fingerG1_contDiffAt (hsub hx)).differentiableAt (by simp))
    (fun x _ => fingerG2_contDiff.differentiable (by simp) x)
    (fun x hx => fingerConstraint_mulVec_g1 (hsub hx)) (fun x _ => fingerConstraint_mulVec_g2 x)
    hq ?_
  rw [finger_lieBracket_g1_g2 (hsub hq), fingerConstraint_mulVec_g3 (hsub hq)]
  intro h0
  have h1 : (-1 : ℝ) = 0 := by simpa using congrFun h0 2
  norm_num at h1

/-! ### The hopping robot (Examples 7.2 and 7.7) -/

/-- **MLS Example 7.2, p. 334: the input fields `(g₁, g₂)` of the hopper.** -/
def hopperFields (I m d : ℝ) : Fin 2 → (Fin 3 → ℝ) → Fin 3 → ℝ := ![hopperG1 I m d, hopperG2]

/-- **MLS Example 7.7, p. 342, with the unprinted hypothesis: the set `l + d ≠ 0`,** which
contains `l = 0` exactly when `d ≠ 0`. -/
def hopperDomain (d : ℝ) : Set (Fin 3 → ℝ) := {q | q 1 + d ≠ 0}

/-- **MLS p. 342:** the hopper's domain is open. -/
theorem isOpen_hopperDomain (d : ℝ) : IsOpen (hopperDomain d) := by
  exact isOpen_ne_fun ((continuous_apply 1).add continuous_const) continuous_const

/-- **MLS Example 7.7, p. 342:** `g₁(q), g₂(q), [g₁, g₂](q)` are independent on the set
`l + d ≠ 0`, for `0 < I` and `0 < m`. -/
private theorem hopper_triple {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ) {q : Fin 3 → ℝ}
    (hq : q ∈ hopperDomain d) :
    LinearIndependent ℝ ![hopperFields I m d 0 q, hopperFields I m d 1 q,
      lieBracket ℝ (hopperFields I m d 0) (hopperFields I m d 1) q] := by
  convert hopper_linearIndependent hI hm d hq using 1
  funext j
  fin_cases j
  · rfl
  · rfl
  · exact hopper_lieBracket_g1_g2 hI hm.le d q

/-- **MLS Example 7.7, p. 342:** `Δ₂(q) = ℝ³` on the set `l + d ≠ 0`. -/
private theorem hopper_filtrationAt_two {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ)
    {q : Fin 3 → ℝ} (hq : q ∈ hopperDomain d) : filtrationAt (hopperFields I m d) 2 q = ⊤ := by
  refine filtrationAt_eq_top_of_linearIndependent (hopperFields I m d)
    (Module.finrank_fin_fun ℝ) (hopper_triple hI hm d hq) ?_
  intro k
  fin_cases k
  · exact generator_mem_filtrationAt (hopperFields I m d) 0 (by norm_num) q
  · exact generator_mem_filtrationAt (hopperFields I m d) 1 (by norm_num) q
  · exact lieBracket_mem_filtrationAt_two (hopperFields I m d) le_rfl q

/-- **MLS Example 7.7, p. 342: growth vector `(2, 3)` and relative growth vector `(2, 1)`** at
every `q` with `l + d ≠ 0`, for `0 < I` and `0 < m`. -/
theorem hopper_growthVector {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ) {q : Fin 3 → ℝ}
    (hq : q ∈ hopperDomain d) :
    growthVector (hopperFields I m d) 2 q = ![2, 3] ∧
      relativeGrowthVector (hopperFields I m d) 2 q = ![2, 1] := by
  exact growthVector_two (hopperFields I m d) (hopper_triple hI hm d hq)

/-- **MLS Example 7.7, p. 342: degree of nonholonomy `2`** at every `q` with `l + d ≠ 0`. -/
theorem hopper_isDegreeOfNonholonomy {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ)
    {q : Fin 3 → ℝ} (hq : q ∈ hopperDomain d) :
    IsDegreeOfNonholonomy (hopperFields I m d) q 2 := by
  exact isDegreeOfNonholonomy_two (hopperFields I m d) (Module.finrank_fin_fun ℝ)
    (hopper_triple hI hm d hq)

/-- **MLS p. 340 for Example 7.7:** the filtration of the hopper is regular on the set
`l + d ≠ 0`. -/
theorem hopper_isRegularFiltrationOn {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ)
    {q₀ : Fin 3 → ℝ} (hq₀ : q₀ ∈ hopperDomain d) :
    IsRegularFiltrationOn (hopperFields I m d) (hopperDomain d) q₀ := by
  exact isRegularFiltrationOn_two (hopperFields I m d) (Module.finrank_fin_fun ℝ)
    (fun _ hq => hopper_triple hI hm d hq) hq₀

/-- **MLS Example 7.7, p. 342, and Theorem 7.5, p. 329: the controllability rank condition** at
every `q` with `l + d ≠ 0` ("in a neighborhood of `l = 0`" when `d ≠ 0`). -/
theorem hopper_lieAlgebraAt {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ) {q : Fin 3 → ℝ}
    (hq : q ∈ hopperDomain d) : lieAlgebraAt (hopperFields I m d) q = ⊤ := by
  exact lieAlgebraAt_eq_top_of_filtrationAt (hopperFields I m d) (hopper_filtrationAt_two hI hm d hq)

/-- **MLS p. 325 for Example 7.7:** `span{g₁, g₂}` is not involutive on any set meeting the
domain. -/
theorem hopper_not_generatorsInvolutiveOn {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ)
    {U : Set (Fin 3 → ℝ)} (hU : (U ∩ hopperDomain d).Nonempty) :
    ¬ GeneratorsInvolutiveOn (Set.range (hopperFields I m d)) U := by
  obtain ⟨q, hqU, hqD⟩ := hU
  exact not_generatorsInvolutiveOn_of_linearIndependent (hopperFields I m d) hqU
    (hopper_triple hI hm d hqD)

/-- **MLS p. 333 and Proposition 7.4, p. 328, for Example 7.2:** the angular momentum constraint
(7.11) is not integrable with a `C²` map on any open set meeting the domain. -/
theorem hopper_not_isC2IntegrableOn {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ)
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hne : (U ∩ hopperDomain d).Nonempty) :
    ¬ IsC2IntegrableOn (hopperConstraint I m d) U := by
  obtain ⟨q, hqU, hqD⟩ := hne
  refine not_isC2IntegrableOn_of_lieBracket hU
    (fun x _ => (hopperG1_contDiff hI hm.le d).differentiable (by simp) x)
    (fun x _ => hopperG2_contDiff.differentiable (by simp) x)
    (fun x _ => hopperConstraint_mulVec_g1 hI hm.le d x)
    (fun x _ => hopperConstraint_mulVec_g2 I m d x) hqU ?_
  rw [hopper_lieBracket_g1_g2 hI hm.le d, hopperConstraint_mulVec_g3 hI hm.le d]
  intro h0
  have hden : 0 < I + m * (q 1 + d) ^ 2 := by positivity
  have hne : 2 * I * m * (q 1 + d) / (I + m * (q 1 + d) ^ 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by positivity) hqD) hden.ne'
  exact hne (by simpa using congrFun h0 0)

/-- **MLS Theorem 7.5 (Chow), p. 329, for Example 7.7, from the named statement:** if Chow's
theorem holds on `ℝ³`, the hopper with unconstrained inputs is locally controllable at every `q`
with `l + d ≠ 0`. -/
theorem hopper_isLocallyControllableAt (hC : ChowStatement (Fin 3 → ℝ)) {I m : ℝ} (hI : 0 < I)
    (hm : 0 < m) (d : ℝ) {q : Fin 3 → ℝ} (hq : q ∈ hopperDomain d) :
    IsLocallyControllableAt (hopperFields I m d) Set.univ q := by
  refine hC 2 (hopperFields I m d) ?_ q (hopper_lieAlgebraAt hI hm d hq)
  intro j
  fin_cases j
  · exact hopperG1_contDiff hI hm.le d
  · exact hopperG2_contDiff

end Examples
end RoboLean
