import RoboLean.Nonholonomic.OptimalInputs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Higher derivatives of optimal inputs, the drift case and minimum time: MLS Chapter 8,
# Exercises 7, 8 and 11

MLS Chapter 8, printed p. 393: Exercise 7, "Proposition 8.4 gave a formula for the first
derivative of the optimal inputs. Use the method of the proof of that proposition to obtain a
formula for `ü`. Express the answer in terms of Lie brackets of the input vector fields";
Exercise 8, "Use the results of Proposition 8.16 to show that the optimal input of that
proposition normalized by `‖u(0)‖`, that is, `u(t)/‖u(0)‖`, solves the minimum time steering
problem … subject to the constraint that `‖u(t)‖² ≤ 1`"; Exercise 11, the least squares problem for
`q̇ = f(q) + Σ gᵢ(q)uᵢ`: (a) the optimal Hamiltonian and the equation (8.38) for `u̇`, (b) the
second derivatives. Exercises 8 and 9 cite a "Proposition 8.16", which does not exist; the
proposition meant is Proposition 8.4 (p. 373), the only one about the optimal input of the least
squares problem.

**What is formalized.** As in the library's treatment of Proposition 8.4, the necessary conditions
(8.12)–(8.13) are hypotheses along a curve `(q, p)`; nothing here proves that an optimal input
exists or that a curve satisfying them is optimal (the book calls §3.3 "somewhat informal",
p. 371).
* The method of the proof of Proposition 8.4: along such a curve, for every field `h`
  differentiable along it, `d/dt pᵀh(q) = pᵀ[f, h](q) + Σⱼ uⱼ pᵀ[gⱼ, h](q)`.
* Exercise 11(a): the Hamiltonian `H = ½uᵀu + pᵀ(f(q) + Σ gᵢ(q)uᵢ)`, its stationary input
  `uᵢ = −pᵀgᵢ`, the optimal Hamiltonian `H* = pᵀf − ½ Σ (pᵀgᵢ)²` and, corrected printing of (8.38),
  `u̇ = Ω(q, p)u − (pᵀ[f, gᵢ])ᵢ` (the printed display equates `Ω(q, p)u` with the column
  `(pᵀ[f, gᵢ])ᵢ`; the drift term is added to `Ω(q, p)u`, with a minus sign in the convention
  `[f, g] = (∂g/∂q)f − (∂f/∂q)g` of p. 323).
* Exercise 11(b) and Exercise 7: the derivative of `u̇` in terms of brackets of order two; for
  `f = 0`, `üᵢ = Σⱼ Σₖ uₖuⱼ pᵀ[gₖ, [gᵢ, gⱼ]] + (Ω²u)ᵢ`. The general `u⁽ⁿ⁾` is not formalized.
* Exercise 8, with Proposition 8.4 for "Proposition 8.16": if `u` minimizes `∫₀¹ ‖u‖²` among
  continuous inputs steering `q₀` to `q_f` in unit time and `‖u(t)‖ = c > 0` is constant (the
  conclusion of Proposition 8.4), then the input `s ↦ u(s/c)/c` on `[0, c]` has unit norm and
  steers `q₀` to `q_f` in time `c`, and no continuous input with `‖w‖² ≤ 1` does so in a time
  `T < c`. The printed `u(t)/‖u(0)‖` without the change of time `t = s/c` reaches `q_f` only at
  time `c`; the statement here includes it.

**Conventions.** The state lies in a real normed space `E`, the multiplier `p(t)` in its dual;
`‖u‖² = u ⬝ᵥ u` on `Fin m → ℝ`; the bracket is the library's (MLS p. 324).
-/

noncomputable section

open Set Filter Topology VectorField Matrix

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS Chapter 8, Exercise 11, p. 393, with (8.11), p. 372: the Hamiltonian of the drift
system,** `H(q, p, u) = ½ uᵀu + pᵀ(f(q) + Σ gᵢ(q)uᵢ)`. -/
def driftHamiltonian (f : E → E) (g : Fin m → E → E) (q : E) (p : E →L[ℝ] ℝ) (u : Fin m → ℝ) :
    ℝ :=
  (1 / 2 : ℝ) * (u ⬝ᵥ u) + p (f q + driftFree g q u)

/-- **MLS Chapter 8, Exercise 11, p. 393, with (8.12), p. 372: `∂H/∂q = pᵀ ∂f/∂q + Σ uᵢ pᵀ ∂gᵢ/∂q`**
for fields differentiable at `q`. -/
theorem hasFDerivAt_driftHamiltonian (f : E → E) (g : Fin m → E → E) (p : E →L[ℝ] ℝ)
    (u : Fin m → ℝ) {q : E} (hf : DifferentiableAt ℝ f q) (hg : ∀ i, DifferentiableAt ℝ (g i) q) :
    HasFDerivAt (fun x => driftHamiltonian f g x p u)
      (p.comp (fderiv ℝ f q) + ∑ i, u i • p.comp (fderiv ℝ (g i) q)) q := by
  have h : HasFDerivAt (fun x => driftFree g x u) (∑ i, u i • fderiv ℝ (g i) q) q :=
    HasFDerivAt.fun_sum fun i _ => (hg i).hasFDerivAt.const_smul (u i)
  have h2 := (p.hasFDerivAt.comp q (hf.hasFDerivAt.add h)).const_add ((1 / 2 : ℝ) * (u ⬝ᵥ u))
  refine h2.congr_fderiv ?_
  ext v
  simp [map_sum, map_smul]

/-- **MLS Chapter 8, Exercise 11(a), p. 393: the stationary input is `uᵢ = −pᵀgᵢ(q)`,** as in
(8.13): the derivative of the Hamiltonian in the input vanishes there. -/
theorem hasFDerivAt_driftHamiltonian_input (f : E → E) (g : Fin m → E → E) (q : ℝ → E)
    (p : ℝ → E →L[ℝ] ℝ) (t : ℝ) :
    HasFDerivAt (fun v => driftHamiltonian f g (q t) (p t) v) (0 : (Fin m → ℝ) →L[ℝ] ℝ)
      (optimalInput g q p t) := by
  have h := (hasFDerivAt_hamiltonian_input g q p t).const_add (p t (f (q t)))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  simp [driftHamiltonian, hamiltonian, map_add]
  ring

/-- **MLS Chapter 8, Exercise 11(a), p. 393: the optimal Hamiltonian
`H* = pᵀf(q) − ½ Σ (pᵀgᵢ(q))²`.** -/
theorem driftHamiltonian_optimalInput (f : E → E) (g : Fin m → E → E) (q : ℝ → E)
    (p : ℝ → E →L[ℝ] ℝ) (t : ℝ) :
    driftHamiltonian f g (q t) (p t) (optimalInput g q p t) =
      p t (f (q t)) - (1 / 2 : ℝ) * ∑ i, (p t (g i (q t))) ^ 2 := by
  have h := hamiltonian_optimalInput g q p t
  simp only [hamiltonian] at h
  simp only [driftHamiltonian, map_add]
  linarith

/-- **The method of the proof of MLS Proposition 8.4, p. 373, used for Exercises 7 and 11,
p. 393.** Along a curve with `q̇ = f(q) + Σ gᵢ(q)uᵢ` and `ṗ = −∂H/∂q` (8.12) at `t`, for every
field `h` differentiable at `q(t)`: `d/dt pᵀh(q) = pᵀ[f, h](q) + Σⱼ uⱼ pᵀ[gⱼ, h](q)`. -/
theorem hasDerivAt_multiplier_apply {f : E → E} {g : Fin m → E → E} {q : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {u : ℝ → Fin m → ℝ} {t : ℝ}
    (hq : HasDerivAt q (f (q t) + driftFree g (q t) (u t)) t)
    (hp : HasDerivAt p
      (-((p t).comp (fderiv ℝ f (q t)) + ∑ i, u t i • (p t).comp (fderiv ℝ (g i) (q t)))) t)
    {h : E → E} (hh : DifferentiableAt ℝ h (q t)) :
    HasDerivAt (fun s => p s (h (q s)))
      (p t (lieBracket ℝ f h (q t)) + ∑ j, u t j * p t (lieBracket ℝ (g j) h (q t))) t := by
  have hhq : HasDerivAt (fun s => h (q s))
      (fderiv ℝ h (q t) (f (q t) + driftFree g (q t) (u t))) t :=
    hh.hasFDerivAt.comp_hasDerivAt t hq
  have hd := hp.clm_apply hhq
  convert hd using 1
  simp only [lieBracket, map_sub, map_add, driftFree, map_sum, map_smul, smul_eq_mul,
    _root_.neg_apply, _root_.add_apply, FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **MLS Chapter 8, Exercise 11(a), p. 393: the drift column `(pᵀ[f, gᵢ](q))ᵢ` of (8.38).** -/
def driftColumn (f : E → E) (g : Fin m → E → E) (q : E) (p : E →L[ℝ] ℝ) : Fin m → ℝ :=
  fun i => p (lieBracket ℝ f (g i) q)

/-- **MLS Chapter 8, Exercise 11(a), p. 393, eq. (8.38), corrected printing:
`u̇ = Ω(q, p)u − (pᵀ[f, gᵢ])ᵢ`.** Along a curve with `q̇ = f(q) + Σ gᵢ(q)uᵢ`, `ṗ = −∂H/∂q` (8.12)
and `uᵢ = −pᵀgᵢ(q)` (8.13) at `t`, for input fields differentiable at `q(t)`. -/
theorem hasDerivAt_optimalInput_drift {f : E → E} {g : Fin m → E → E} {q : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) (q t))
    (hq : HasDerivAt q (f (q t) + driftFree g (q t) (optimalInput g q p t)) t)
    (hp : HasDerivAt p (-((p t).comp (fderiv ℝ f (q t)) +
      ∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t)))) t) :
    HasDerivAt (optimalInput g q p)
      (optimalOmega g (q t) (p t) *ᵥ optimalInput g q p t - driftColumn f g (q t) (p t)) t := by
  rw [hasDerivAt_pi]
  intro i
  have h := (hasDerivAt_multiplier_apply hq hp (hg i)).neg
  convert h using 1
  · funext s
    simp [optimalInput]
  simp only [optimalOmega, Matrix.mulVec, dotProduct, Matrix.of_apply, driftColumn, Pi.sub_apply]
  rw [neg_add, ← Finset.sum_neg_distrib]
  have hs : ∀ j, p t (lieBracket ℝ (g i) (g j) (q t)) * optimalInput g q p t j =
      -(optimalInput g q p t j * p t (lieBracket ℝ (g j) (g i) (q t))) := by
    intro j
    rw [lieBracket_swap (V := g i), map_neg]
    ring
  simp only [hs]
  ring

/-- **MLS Chapter 8, Exercise 11, p. 393: the right-hand side `Ω(q, p)u − (pᵀ[f, gᵢ])ᵢ` of
(8.38) along the curve,** the first derivative of the optimal input. -/
def optimalInputRate (f : E → E) (g : Fin m → E → E) (q : ℝ → E) (p : ℝ → E →L[ℝ] ℝ) (s : ℝ) :
    Fin m → ℝ :=
  optimalOmega g (q s) (p s) *ᵥ optimalInput g q p s - driftColumn f g (q s) (p s)

/-- **MLS Chapter 8, Exercise 11(b), p. 393: the second derivatives of the optimal inputs.** With
`u = −pᵀg(q)` and `u̇ = Ω(q, p)u − (pᵀ[f, gᵢ])ᵢ` (8.38),
`üᵢ = Σⱼ (pᵀ[f, [gᵢ, gⱼ]] + Σₖ uₖ pᵀ[gₖ, [gᵢ, gⱼ]]) uⱼ + Σⱼ pᵀ[gᵢ, gⱼ] u̇ⱼ
  − (pᵀ[f, [f, gᵢ]] + Σₖ uₖ pᵀ[gₖ, [f, gᵢ]])`,
at `t`, for `gᵢ`, `[gᵢ, gⱼ]` and `[f, gᵢ]` differentiable at `q(t)`. -/
theorem hasDerivAt_optimalInputRate {f : E → E} {g : Fin m → E → E} {q : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) (q t))
    (hgg : ∀ i j, DifferentiableAt ℝ (lieBracket ℝ (g i) (g j)) (q t))
    (hfg : ∀ i, DifferentiableAt ℝ (lieBracket ℝ f (g i)) (q t))
    (hq : HasDerivAt q (f (q t) + driftFree g (q t) (optimalInput g q p t)) t)
    (hp : HasDerivAt p (-((p t).comp (fderiv ℝ f (q t)) +
      ∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t)))) t) :
    HasDerivAt (optimalInputRate f g q p)
      (fun i => ∑ j, (p t (lieBracket ℝ f (lieBracket ℝ (g i) (g j)) (q t)) +
          ∑ k, optimalInput g q p t k * p t (lieBracket ℝ (g k) (lieBracket ℝ (g i) (g j)) (q t))) *
            optimalInput g q p t j +
        ∑ j, p t (lieBracket ℝ (g i) (g j) (q t)) * optimalInputRate f g q p t j -
        (p t (lieBracket ℝ f (lieBracket ℝ f (g i)) (q t)) +
          ∑ k, optimalInput g q p t k * p t (lieBracket ℝ (g k) (lieBracket ℝ f (g i)) (q t)))) t := by
  have hu := hasDerivAt_optimalInput_drift hg hq hp
  rw [hasDerivAt_pi]
  intro i
  have hΩ : ∀ j, HasDerivAt (fun s => p s (lieBracket ℝ (g i) (g j) (q s))) _ t := fun j =>
    hasDerivAt_multiplier_apply hq hp (hgg i j)
  have hw := hasDerivAt_multiplier_apply hq hp (hfg i)
  have huj : ∀ j, HasDerivAt (fun s => optimalInput g q p s j) (optimalInputRate f g q p t j) t :=
    fun j => hasDerivAt_pi.1 hu j
  have h := (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hΩ j).mul (huj j)).sub hw
  convert h using 1
  · funext s
    simp [optimalInputRate, optimalOmega, Matrix.mulVec, dotProduct, driftColumn]
  · simp only [Finset.sum_add_distrib]

/-- **MLS Chapter 8, Exercise 7, p. 393: the second derivative of the optimal input of
Proposition 8.4,** `üᵢ = Σⱼ Σₖ uₖuⱼ pᵀ[gₖ, [gᵢ, gⱼ]](q) + (Ω(q, p)²u)ᵢ`, at `t`, along a curve
with (8.12)–(8.13) for the drift-free system, for `gᵢ` and `[gᵢ, gⱼ]` differentiable at `q(t)`:
the derivative of `u̇ = Ω(q, p)u` (8.16). -/
theorem hasDerivAt_optimalOmega_mulVec {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ}
    {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) (q t))
    (hgg : ∀ i j, DifferentiableAt ℝ (lieBracket ℝ (g i) (g j)) (q t))
    (hq : HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : HasDerivAt p (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t) :
    HasDerivAt (fun s => optimalOmega g (q s) (p s) *ᵥ optimalInput g q p s)
      (fun i => ∑ j, ∑ k, optimalInput g q p t k * optimalInput g q p t j *
          p t (lieBracket ℝ (g k) (lieBracket ℝ (g i) (g j)) (q t)) +
        (optimalOmega g (q t) (p t) *ᵥ (optimalOmega g (q t) (p t) *ᵥ optimalInput g q p t)) i) t := by
  have hq' : HasDerivAt q ((fun _ => (0 : E)) (q t) + driftFree g (q t) (optimalInput g q p t)) t := by
    simpa using hq
  have hp' : HasDerivAt p (-((p t).comp (fderiv ℝ (fun _ => (0 : E)) (q t)) +
      ∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t)))) t := by
    simpa using hp
  have hfg : ∀ i, DifferentiableAt ℝ (lieBracket ℝ (fun _ => (0 : E)) (g i)) (q t) := fun i => by
    rw [show (fun _ => (0 : E)) = (0 : E → E) from rfl, lieBracket_zero_left]
    exact differentiableAt_const _
  have h := hasDerivAt_optimalInputRate hg hgg hfg hq' hp'
  have hrate : optimalInputRate (fun _ => (0 : E)) g q p =
      fun s => optimalOmega g (q s) (p s) *ᵥ optimalInput g q p s := by
    funext s
    have : driftColumn (fun _ => (0 : E)) g (q s) (p s) = 0 := by
      funext i
      simp [driftColumn, show (fun _ => (0 : E)) = (0 : E → E) from rfl, lieBracket_zero_left]
    simp [optimalInputRate, this]
  rw [hrate] at h
  convert h using 1
  funext i
  have hz : (fun _ => (0 : E)) = (0 : E → E) := rfl
  simp only [hz, lieBracket_zero_left, lieBracket_zero_right, Pi.zero_apply, map_zero, zero_add,
    mul_zero, Finset.sum_const_zero, add_zero, sub_zero, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- **MLS p. 329 and Chapter 8, Exercise 8, p. 393: a change of time scale.** If `x` is a
trajectory on `[0, T]` for the input `u` and `k > 0`, then `t ↦ x(kt)` is a trajectory on
`[0, T/k]` for the input `t ↦ k u(kt)`. -/
theorem IsTrajectory.timeScale {g : Fin m → E → E} {u : ℝ → Fin m → ℝ} {T : ℝ} {x : ℝ → E}
    {k : ℝ} (hk : 0 < k) (hx : IsTrajectory g u T x) :
    IsTrajectory g (fun t => k • u (k * t)) (T / k) (fun t => x (k * t)) := by
  obtain ⟨hc, S, hS⟩ := hx
  refine ⟨hc.comp (continuous_const.mul continuous_id).continuousOn fun t ht =>
    ⟨mul_nonneg hk.le ht.1, ?_⟩, S.image (fun s => s / k), fun t ht htS => ?_⟩
  · have := ht.2
    rw [le_div_iff₀ hk] at this
    linarith
  · have h1 : k * t ∈ Ioo 0 T := by
      refine ⟨mul_pos hk ht.1, ?_⟩
      have := ht.2
      rw [lt_div_iff₀ hk] at this
      linarith
    have h2 : k * t ∉ S := fun h => htS (Finset.mem_image.2 ⟨k * t, h, by field_simp⟩)
    have hd' : HasDerivAt (fun s => k * s) k t := by
      simpa using (hasDerivAt_id t).const_mul k
    simpa [Function.comp_def, driftFree_smul] using (hS (k * t) h1 h2).scomp t hd'

/-- **MLS Chapter 8, Exercise 8, p. 393: least squares optimality in unit time** among continuous
inputs: `u` is continuous, steers `q₀` to `q_f` on `[0, 1]`, and `∫₀¹ ‖u‖² ≤ ∫₀¹ ‖v‖²` for every
continuous input `v` that does. -/
def IsLeastSquaresOptimal (g : Fin m → E → E) (q₀ qf : E) (u : ℝ → Fin m → ℝ) : Prop :=
  Continuous u ∧ (∃ x, IsTrajectory g u 1 x ∧ x 0 = q₀ ∧ x 1 = qf) ∧
    ∀ v : ℝ → Fin m → ℝ, Continuous v → (∃ x, IsTrajectory g v 1 x ∧ x 0 = q₀ ∧ x 1 = qf) →
      ∫ t in (0 : ℝ)..1, u t ⬝ᵥ u t ≤ ∫ t in (0 : ℝ)..1, v t ⬝ᵥ v t

/-- **MLS Chapter 8, Exercise 8, p. 393, with Proposition 8.4, p. 373, for the printed
"Proposition 8.16": the normalized optimal input is time optimal.** If `u` is least squares
optimal in unit time with constant norm `‖u(t)‖ = c > 0` on `[0, 1]` (the conclusion of
Proposition 8.4), then (1) the input `s ↦ u(s/c)/c` has unit norm on `[0, c]` and steers `q₀` to
`q_f` in time `c`, and (2) every continuous input `w` with `‖w(s)‖² ≤ 1` on `[0, T]` that steers
`q₀` to `q_f` in time `T > 0` has `T ≥ c`. -/
theorem IsLeastSquaresOptimal.minimumTime {g : Fin m → E → E} {q₀ qf : E} {u : ℝ → Fin m → ℝ}
    (hu : IsLeastSquaresOptimal g q₀ qf u) {c : ℝ} (hc : 0 < c)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, u t ⬝ᵥ u t = c ^ 2) :
    ((∀ s ∈ Icc 0 c, (c⁻¹ • u (c⁻¹ * s)) ⬝ᵥ (c⁻¹ • u (c⁻¹ * s)) = 1) ∧
      ∃ x, IsTrajectory g (fun s => c⁻¹ • u (c⁻¹ * s)) c x ∧ x 0 = q₀ ∧ x c = qf) ∧
    ∀ T : ℝ, 0 < T → ∀ w : ℝ → Fin m → ℝ, Continuous w → (∀ s ∈ Icc 0 T, w s ⬝ᵥ w s ≤ 1) →
      (∃ x, IsTrajectory g w T x ∧ x 0 = q₀ ∧ x T = qf) → c ≤ T := by
  obtain ⟨huc, ⟨x, hx, hx0, hx1⟩, hopt⟩ := hu
  refine ⟨⟨fun s hs => ?_, ?_⟩, fun T hT w hw hw1 ⟨y, hy, hy0, hyT⟩ => ?_⟩
  · have ht : c⁻¹ * s ∈ Icc (0 : ℝ) 1 := by
      refine ⟨mul_nonneg (inv_nonneg.2 hc.le) hs.1, ?_⟩
      rw [inv_mul_le_iff₀ hc]
      linarith [hs.2]
    rw [smul_dotProduct, dotProduct_smul, hnorm _ ht, smul_eq_mul, smul_eq_mul]
    field_simp
  · have h := hx.timeScale (k := c⁻¹) (inv_pos.2 hc)
    refine ⟨fun t => x (c⁻¹ * t), ?_, by simp [hx0], ?_⟩
    · simpa [div_inv_eq_mul] using h
    · show x (c⁻¹ * c) = qf
      rw [inv_mul_cancel₀ hc.ne']
      exact hx1
  · have hy' := hy.rescale hT
    have hcont : Continuous fun t => T • w (T * t) := by fun_prop
    have hle := hopt _ hcont ⟨_, hy', by simp [hy0], by simp [hyT]⟩
    have hL : ∫ t in (0 : ℝ)..1, u t ⬝ᵥ u t = c ^ 2 := by
      rw [intervalIntegral.integral_congr (g := fun _ => c ^ 2) (fun t ht => by
        rw [uIcc_of_le zero_le_one] at ht
        exact hnorm t ht)]
      simp
    have hR : ∫ t in (0 : ℝ)..1, (T • w (T * t)) ⬝ᵥ (T • w (T * t)) ≤ T ^ 2 := by
      have hm : ∫ t in (0 : ℝ)..1, (T • w (T * t)) ⬝ᵥ (T • w (T * t)) ≤
          ∫ t in (0 : ℝ)..1, T ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_ intervalIntegrable_const
          fun t ht => ?_
        · exact (Continuous.intervalIntegrable (by
            simp only [dotProduct]
            fun_prop) _ _)
        · have hts : T * t ∈ Icc 0 T := ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩
          rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
          have := hw1 _ hts
          nlinarith [sq_nonneg T]
      simpa using hm
    have hsq : c ^ 2 ≤ T ^ 2 := by linarith
    nlinarith

end Nonholonomic
end RoboLean
