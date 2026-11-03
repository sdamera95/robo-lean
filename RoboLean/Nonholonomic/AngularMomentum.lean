import RoboLean.Nonholonomic.Controllability
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Chapter 7, Exercise 13: the falling cat of two point-mass pendulums (MLS p. 352)

MLS Chapter 7, Exercise 13, printed p. 352: "The figure below shows a simplified model of a falling
cat. It consists of two pendulums coupled by a spherical joint. The configuration space of the
system is `Q = S² × S²` … (a) Derive the Pfaffian constraints arising from conservation of angular
momentum and dualize the results to obtain the control system for nonholonomic motion planning.
(b) Is the system in part (a) controllable?" The figure shows two masses `m` at the ends of two
rods of length `d` meeting at the joint.

**Recorded reading of the model.** Two point masses `m` at `r₁ = p + d s₁`, `r₂ = p + d s₂`, with
`p` the joint and `s₁, s₂ ∈ S²` the rod directions; the system floats freely (it falls), so its
angular momentum about the mass centre is conserved, and the mass centre is taken as origin,
`m r₁ + m r₂ = 0`. The rods are massless and the masses have no rotational inertia, as drawn.

**What is formalized.**
* The positions `r₁ = (d/2)(s₁ − s₂) = −r₂` and the angular momentum about the mass centre
  `m(r₁ × ṙ₁ + r₂ × ṙ₂) = (md²/2)(s₁ − s₂) × (ṡ₁ − ṡ₂)`, so that for `m, d ≠ 0` its vanishing is the
  Pfaffian constraint `(s₁ − s₂) × (ṡ₁ − ṡ₂) = 0` (three scalar constraints of rank two on
  `S² × S²` away from `s₁ = ±s₂`).
* The dual control system: the fields `g₁ = ((s₁ − s₂) × s₁, (s₁ − s₂) × s₂)` (rotation about the
  line through the two masses) and `g₂ = (s₂ − (s₁·s₂)s₁, s₁ − (s₁·s₂)s₂)` (bending) satisfy the
  constraint everywhere, are tangent to `S² × S²`, and where `s₁ × s₂ ≠ 0` they span every tangent
  velocity that satisfies the constraint (`catFields_span`).
* (b): along every trajectory of the dual system that avoids the folded configurations `s₁ = s₂`,
  the direction `(s₁ − s₂)/|s₁ − s₂|` of the line through the two masses is constant
  (`IsTrajectory.cat_direction`); so configurations of `S² × S²` whose lines point in different
  directions, such as `(e₁, −e₁)` and `(e₂, −e₂)`, are not joined by any such trajectory
  (`cat_not_joined`). On the open set of unfolded configurations the system is therefore not
  controllable. The general fact behind it: a curve with `r × ṙ = 0` and `r ≠ 0` keeps its
  direction (`unitDir_eq_of_cross_eq_zero`).

Through a folded configuration (`s₁ = s₂`, both masses at the mass centre) the constraint is
vacuous and the direction can change; the answer "not controllable" is the local one, on the
unfolded configurations.

**Conventions.** Vectors are `Fin 3 → ℝ` with Mathlib's cross product `⨯₃` and dot product `⬝ᵥ`;
the state is `(s₁, s₂) ∈ ℝ³ × ℝ³` with `S² × S²` the unit pairs; `unitDir v = |v|⁻¹ v` with the
Euclidean length `|v| = √(v ⬝ᵥ v)`; trajectories are those of `IsTrajectory`.
-/

noncomputable section

open Set Matrix

namespace RoboLean
namespace Nonholonomic

/-- **MLS Chapter 7, Exercise 13 (p. 352): the positions of the two masses relative to the mass
centre.** If `r₁ = p + d s₁`, `r₂ = p + d s₂` and `m r₁ + m r₂ = 0` with `m ≠ 0`, then
`r₁ = (d/2)(s₁ − s₂)` and `r₂ = (d/2)(s₂ − s₁)`. -/
theorem cat_positions {m d : ℝ} (hm : m ≠ 0) {p s₁ s₂ r₁ r₂ : Fin 3 → ℝ} (h₁ : r₁ = p + d • s₁)
    (h₂ : r₂ = p + d • s₂) (hc : m • r₁ + m • r₂ = 0) :
    r₁ = (d / 2) • (s₁ - s₂) ∧ r₂ = (d / 2) • (s₂ - s₁) := by
  have hp : p = -(d / 2) • (s₁ + s₂) := by
    have h : m • (2 • p + d • (s₁ + s₂)) = 0 := by
      rw [← hc, h₁, h₂]
      module
    have h' := (smul_eq_zero.1 h).resolve_left hm
    have h2 : (2 : ℝ) • p = -(d • (s₁ + s₂)) := eq_neg_of_add_eq_zero_left (by
      rw [two_smul] at h' ⊢; exact h')
    calc p = (1 / 2 : ℝ) • ((2 : ℝ) • p) := by rw [smul_smul]; norm_num
      _ = -(d / 2) • (s₁ + s₂) := by rw [h2]; module
  constructor
  · rw [h₁, hp]; module
  · rw [h₂, hp]; module

/-- **MLS Chapter 7, Exercise 13 (p. 352): the angular momentum about the mass centre**
`m(r₁ × ṙ₁ + r₂ × ṙ₂)` of the two masses at `r₁ = (d/2)(s₁ − s₂)`, `r₂ = −r₁`, for rod velocities
`(v₁, v₂) = (ṡ₁, ṡ₂)`. -/
def catMomentum (m d : ℝ) (s₁ s₂ v₁ v₂ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  m • (((d / 2) • (s₁ - s₂)) ⨯₃ ((d / 2) • (v₁ - v₂)) +
    ((d / 2) • (s₂ - s₁)) ⨯₃ ((d / 2) • (v₂ - v₁)))

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the angular momentum is
`(md²/2)(s₁ − s₂) × (ṡ₁ − ṡ₂)`.** -/
theorem catMomentum_eq (m d : ℝ) (s₁ s₂ v₁ v₂ : Fin 3 → ℝ) :
    catMomentum m d s₁ s₂ v₁ v₂ = (m * d ^ 2 / 2) • ((s₁ - s₂) ⨯₃ (v₁ - v₂)) := by
  ext i
  fin_cases i <;> simp [catMomentum, cross_apply] <;> ring

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the Pfaffian constraint.** For `m, d ≠ 0`, zero
angular momentum is `(s₁ − s₂) × (ṡ₁ − ṡ₂) = 0`. -/
theorem catMomentum_eq_zero_iff {m d : ℝ} (hm : m ≠ 0) (hd : d ≠ 0) (s₁ s₂ v₁ v₂ : Fin 3 → ℝ) :
    catMomentum m d s₁ s₂ v₁ v₂ = 0 ↔ (s₁ - s₂) ⨯₃ (v₁ - v₂) = 0 := by
  rw [catMomentum_eq, smul_eq_zero]
  have : m * d ^ 2 / 2 ≠ 0 := by positivity
  simp [this]

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the rotation about the line through the two masses,**
`g₁(s₁, s₂) = ((s₁ − s₂) × s₁, (s₁ − s₂) × s₂)`. -/
def catTwist (s : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  ((s.1 - s.2) ⨯₃ s.1, (s.1 - s.2) ⨯₃ s.2)

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the bending motion,**
`g₂(s₁, s₂) = (s₂ − (s₁·s₂)s₁, s₁ − (s₁·s₂)s₂)`. -/
def catBend (s : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  (s.2 - (s.1 ⬝ᵥ s.2) • s.1, s.1 - (s.1 ⬝ᵥ s.2) • s.2)

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the dual control system** `(g₁, g₂)` on
`ℝ³ × ℝ³ ⊃ S² × S²`. -/
def catFields : Fin 2 → (Fin 3 → ℝ) × (Fin 3 → ℝ) → (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  ![catTwist, catBend]

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the dual fields satisfy the constraint,**
`(s₁ − s₂) × (v₁ − v₂) = 0` for `(v₁, v₂) = gⱼ(s₁, s₂)`, at every configuration. -/
theorem catFields_constraint (j : Fin 2) (s : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    (s.1 - s.2) ⨯₃ ((catFields j s).1 - (catFields j s).2) = 0 := by
  fin_cases j
  · simp only [catFields, Fin.zero_eta, Matrix.cons_val_zero, catTwist]
    rw [← map_sub, cross_self, map_zero]
  · simp only [catFields, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, catBend]
    have : s.2 - (s.1 ⬝ᵥ s.2) • s.1 - (s.1 - (s.1 ⬝ᵥ s.2) • s.2) =
        (-(1 + s.1 ⬝ᵥ s.2)) • (s.1 - s.2) := by module
    rw [this, map_smul, cross_self, smul_zero]

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the dual fields are tangent to `S² × S²`:** at unit
`s₁, s₂`, `s₁ ⬝ᵥ v₁ = 0` and `s₂ ⬝ᵥ v₂ = 0` for `(v₁, v₂) = gⱼ(s₁, s₂)`. -/
theorem catFields_tangent (j : Fin 2) {s : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (h₁ : s.1 ⬝ᵥ s.1 = 1)
    (h₂ : s.2 ⬝ᵥ s.2 = 1) :
    s.1 ⬝ᵥ (catFields j s).1 = 0 ∧ s.2 ⬝ᵥ (catFields j s).2 = 0 := by
  fin_cases j
  · simp [catFields, catTwist, dot_cross_self]
  · simp only [catFields, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, catBend,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, h₁, h₂, dotProduct_comm s.2 s.1]
    constructor <;> ring

/-- A vector `w` with `a × w = 0` and `a ≠ 0` is a multiple of `a` (supporting lemma for MLS
p. 352). -/
private theorem exists_smul_of_cross_eq_zero {a w : Fin 3 → ℝ} (ha : a ≠ 0) (h : a ⨯₃ w = 0) :
    ∃ l : ℝ, w = l • a := by
  have hdep : ¬ LinearIndependent ℝ ![a, w] := fun hli =>
    (crossProduct_ne_zero_iff_linearIndependent.2 hli) h
  rw [LinearIndependent.pair_iff' ha] at hdep
  push Not at hdep
  obtain ⟨l, hl⟩ := hdep
  exact ⟨l, hl.symm⟩

/-- **MLS Chapter 7, Exercise 13(a), p. 352: the dual fields span the constraint distribution.** At
unit `s₁, s₂` with `s₁ × s₂ ≠ 0` (neither equal nor opposite), every velocity `(v₁, v₂)` tangent to
`S² × S²` (`s₁ ⬝ᵥ v₁ = 0`, `s₂ ⬝ᵥ v₂ = 0`) that satisfies the constraint
`(s₁ − s₂) × (v₁ − v₂) = 0` is `α g₁(s) + β g₂(s)` for some `α, β`. -/
theorem catFields_span {s : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (h₁ : s.1 ⬝ᵥ s.1 = 1)
    (h₂ : s.2 ⬝ᵥ s.2 = 1) (hn : s.1 ⨯₃ s.2 ≠ 0) {v : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hv₁ : s.1 ⬝ᵥ v.1 = 0) (hv₂ : s.2 ⬝ᵥ v.2 = 0) (hc : (s.1 - s.2) ⨯₃ (v.1 - v.2) = 0) :
    ∃ α β : ℝ, v = α • catTwist s + β • catBend s := by
  obtain ⟨s₁, s₂⟩ := s
  obtain ⟨v₁, v₂⟩ := v
  simp only at h₁ h₂ hn hv₁ hv₂ hc ⊢
  have ha : s₁ - s₂ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, cross_self] at hn
    exact hn rfl
  have hc1 : 1 + s₁ ⬝ᵥ s₂ ≠ 0 := by
    intro h
    have hsum : (s₁ + s₂) ⬝ᵥ (s₁ + s₂) = 0 := by
      simp only [add_dotProduct, dotProduct_add, h₁, h₂, dotProduct_comm s₂ s₁]
      linarith
    have h0 := dotProduct_self_eq_zero.1 hsum
    have : s₂ = -s₁ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0
    rw [this, map_neg, cross_self, neg_zero] at hn
    exact hn rfl
  obtain ⟨l, hl⟩ := exists_smul_of_cross_eq_zero ha hc
  set β : ℝ := -l / (1 + s₁ ⬝ᵥ s₂) with hβ
  set z : Fin 3 → ℝ := v₁ - β • (s₂ - (s₁ ⬝ᵥ s₂) • s₁) with hz
  have hz2 : v₂ - β • (s₁ - (s₁ ⬝ᵥ s₂) • s₂) = z := by
    have : v₂ = v₁ - l • (s₁ - s₂) := by rw [← hl]; abel
    rw [this, hz, hβ]
    have e : l • (s₁ - s₂) = (-l / (1 + s₁ ⬝ᵥ s₂)) • ((s₂ - (s₁ ⬝ᵥ s₂) • s₁) -
        (s₁ - (s₁ ⬝ᵥ s₂) • s₂)) := by
      rw [show (s₂ - (s₁ ⬝ᵥ s₂) • s₁) - (s₁ - (s₁ ⬝ᵥ s₂) • s₂) =
        (-(1 + s₁ ⬝ᵥ s₂)) • (s₁ - s₂) by module, smul_smul]
      congr 1
      field_simp
    rw [e]
    module
  have hzs1 : s₁ ⬝ᵥ z = 0 := by
    rw [hz, dotProduct_sub, dotProduct_smul, dotProduct_sub, dotProduct_smul, hv₁, h₁]
    simp
  have hzs2 : s₂ ⬝ᵥ z = 0 := by
    rw [← hz2, dotProduct_sub, dotProduct_smul, dotProduct_sub, dotProduct_smul, hv₂, h₂,
      dotProduct_comm s₂ s₁]
    simp
  have hnz : (s₁ ⨯₃ s₂) ⨯₃ z = 0 := by
    rw [cross_cross_eq_smul_sub_smul, hzs1, hzs2, zero_smul, zero_smul, sub_zero]
  obtain ⟨α, hα⟩ := exists_smul_of_cross_eq_zero hn hnz
  refine ⟨α, β, ?_⟩
  have htw : catTwist (s₁, s₂) = (s₁ ⨯₃ s₂, s₁ ⨯₃ s₂) := by
    simp only [catTwist, map_sub, LinearMap.sub_apply, cross_self, zero_sub, sub_zero]
    rw [← cross_anticomm s₂ s₁]
  rw [htw]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, catBend]
    rw [← hα, hz]
    abel
  · simp only [Prod.snd_add, Prod.smul_snd, catBend]
    rw [← hα, ← hz2]
    abel

/-- **MLS Chapter 7, Exercise 13(b), p. 352:** the direction `|v|⁻¹ v` of a vector, with the
Euclidean length `|v| = √(v ⬝ᵥ v)`. -/
def unitDir (v : Fin 3 → ℝ) : Fin 3 → ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v

/-- The derivative of `r ⬝ᵥ r` (supporting lemma for MLS p. 352). -/
private theorem hasDerivAt_dot_self {r : ℝ → Fin 3 → ℝ} {r' : Fin 3 → ℝ} {t : ℝ}
    (h : HasDerivAt r r' t) : HasDerivAt (fun s => r s ⬝ᵥ r s) (2 * (r t ⬝ᵥ r')) t := by
  have hc : ∀ i, HasDerivAt (fun s => r s i) (r' i) t := fun i => hasDerivAt_pi.1 h i
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).mul (hc i)
  convert hs using 1
  · funext s
    simp [dotProduct]
  · simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **MLS Chapter 7, Exercise 13(b), p. 352: a curve with `r × ṙ = 0` keeps its direction.** If `r`
is continuous on `[0, T]`, nowhere zero there, with derivative `r'` and `r × r' = 0` at every
`t ∈ (0, T)` outside a finite set, then `unitDir (r t) = unitDir (r 0)` on `[0, T]`. -/
theorem unitDir_eq_of_cross_eq_zero {r r' : ℝ → Fin 3 → ℝ} {T : ℝ} (hc : ContinuousOn r (Icc 0 T))
    (S : Finset ℝ) (hd : ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivAt r (r' t) t)
    (hne : ∀ t ∈ Icc 0 T, r t ≠ 0) (hx : ∀ t ∈ Ioo 0 T, t ∉ S → r t ⨯₃ r' t = 0) :
    ∀ t ∈ Icc 0 T, unitDir (r t) = unitDir (r 0) := by
  have hpos : ∀ t ∈ Icc 0 T, 0 < r t ⬝ᵥ r t := fun t ht =>
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (r t i)) fun h => hne t ht
      (dotProduct_self_eq_zero.1 h.symm)
  have hcont : ContinuousOn (fun t => unitDir (r t)) (Icc 0 T) := by
    have hdot : ContinuousOn (fun t => r t ⬝ᵥ r t) (Icc 0 T) := by
      simp only [dotProduct]
      exact continuousOn_finsetSum _ fun i _ =>
        (((continuous_apply i).comp_continuousOn hc).mul ((continuous_apply i).comp_continuousOn hc))
    have hinv : ContinuousOn (fun t => (Real.sqrt (r t ⬝ᵥ r t))⁻¹) (Icc 0 T) :=
      (hdot.sqrt).inv₀ fun t ht => (Real.sqrt_pos.2 (hpos t ht)).ne'
    exact hinv.smul hc
  have hder : ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivAt (fun s => unitDir (r s)) 0 t := by
    intro t ht htS
    have hT : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    have hN := (hasDerivAt_dot_self (hd t ht htS)).sqrt (hpos t hT).ne'
    have hNpos : 0 < Real.sqrt (r t ⬝ᵥ r t) := Real.sqrt_pos.2 (hpos t hT)
    have h := (hN.inv hNpos.ne').smul (hd t ht htS)
    convert h using 1
    · funext s
      simp [unitDir]
    have key : (r t ⬝ᵥ r' t) • r t = (r t ⬝ᵥ r t) • r' t := by
      have := cross_cross_eq_smul_sub_smul (r t) (r' t) (r t)
      rw [hx t ht htS, map_zero, LinearMap.zero_apply, dotProduct_comm (r' t) (r t)] at this
      exact (sub_eq_zero.1 this.symm).symm
    have hsq : Real.sqrt (r t ⬝ᵥ r t) ^ 2 = r t ⬝ᵥ r t := Real.sq_sqrt (hpos t hT).le
    have e : -(2 * (r t ⬝ᵥ r' t) / (2 * Real.sqrt (r t ⬝ᵥ r t))) / Real.sqrt (r t ⬝ᵥ r t) ^ 2 =
        -(1 / Real.sqrt (r t ⬝ᵥ r t) ^ 3) * (r t ⬝ᵥ r' t) := by
      field_simp
    rw [e, mul_smul, key, smul_smul]
    set N := Real.sqrt (r t ⬝ᵥ r t) with hNdef
    rw [← hsq, show -(1 / N ^ 3) * N ^ 2 = -N⁻¹ by field_simp]
    simp [hNdef]
  intro t ht
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun s => unitDir (r s))
    (fun _ => (0 : Fin 3 → ℝ)) ht.1 S.countable_toSet (hcont.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => hder s ⟨hs.1.1, lt_of_lt_of_le hs.1.2 ht.2⟩ hs.2) intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  exact (sub_eq_zero.1 h.symm)

/-- **MLS Chapter 7, Exercise 13(b), p. 352: the direction of the line through the two masses is a
first integral.** Along every trajectory of the dual system on `[0, T]` that avoids the folded
configurations (`s₁ ≠ s₂`), the direction of `s₁ − s₂` is constant. -/
theorem IsTrajectory.cat_direction {u : ℝ → Fin 2 → ℝ} {T : ℝ}
    {x : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : IsTrajectory catFields u T x)
    (hne : ∀ t ∈ Icc 0 T, (x t).1 ≠ (x t).2) :
    ∀ t ∈ Icc 0 T, unitDir ((x t).1 - (x t).2) = unitDir ((x 0).1 - (x 0).2) := by
  obtain ⟨hc, S, hS⟩ := hx
  refine unitDir_eq_of_cross_eq_zero (r' := fun t => (driftFree catFields (x t) (u t)).1 -
    (driftFree catFields (x t) (u t)).2) ((continuous_fst.comp_continuousOn hc).sub
    (continuous_snd.comp_continuousOn hc)) S (fun t ht htS => ?_)
    (fun t ht => sub_ne_zero.2 (hne t ht)) (fun t ht htS => ?_)
  · exact (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ) -
      ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)).hasFDerivAt.comp_hasDerivAt t
      (hS t ht htS)
  simp only [driftFree, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    ← Finset.sum_sub_distrib, ← smul_sub, map_sum, map_smul]
  exact Finset.sum_eq_zero fun j _ => by rw [catFields_constraint j (x t), smul_zero]

/-- **MLS Chapter 7, Exercise 13(b), p. 352: not controllable on the unfolded configurations.**
No trajectory of the dual system that avoids the folded configurations joins `(e₁, −e₁)` to
`(e₂, −e₂)` (both in `S² × S²`, with the lines through the masses along `e₁` and `e₂`). -/
theorem cat_not_joined {u : ℝ → Fin 2 → ℝ} {T : ℝ} {x : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : IsTrajectory catFields u T x) (hT : 0 ≤ T) (hne : ∀ t ∈ Icc 0 T, (x t).1 ≠ (x t).2)
    (h0 : x 0 = (Pi.single 0 1, -Pi.single 0 1)) :
    x T ≠ (Pi.single 1 1, -Pi.single 1 1) := by
  intro hT1
  have h := hx.cat_direction hne T ⟨hT, le_rfl⟩
  rw [hT1, h0] at h
  have := congrFun h 0
  simp [unitDir, dotProduct, Fin.sum_univ_three, Pi.single_apply] at this

end Nonholonomic
end RoboLean
