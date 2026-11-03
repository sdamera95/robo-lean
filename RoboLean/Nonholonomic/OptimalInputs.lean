import RoboLean.Nonholonomic.Controllability
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Optimal inputs have constant norm: MLS Proposition 8.4 and Exercise 6 of Chapter 8

MLS Chapter 8, §3.3, printed pp. 371–373, and Exercise 6, pp. 391–392: for the least squares
problem of steering `q̇ = Σ gᵢ(q) uᵢ` with cost `½ ∫ ‖u‖²`, the Hamiltonian (8.11)
`H(q, p, u) = ½ uᵀu + pᵀ Σ gᵢ(q) uᵢ`, the necessary conditions (8.12) `ṗ = −∂H/∂q`, `∂H/∂u = 0`,
the optimal inputs (8.13) `uᵢ = −pᵀ gᵢ(q)` and the optimal Hamiltonian (8.14); Proposition 8.4:
the optimal input satisfies (8.16) `u̇ = Ω(q, p) u` with `Ω_{ij} = pᵀ [gᵢ, gⱼ]` skew-symmetric, and
`‖u(t)‖² = ‖u(0)‖²`; Exercise 6: a solution of `u̇ = Ω(t) u` with `Ω(t) ∈ so(m)` keeps its norm.

**What is formalized.** The book calls this section "somewhat informal" (p. 371) and derives
(8.12)–(8.13) heuristically. Here (8.12)–(8.13) are hypotheses along a curve `(q, p)` on `[0, T]`,
and the conclusions (8.16) and the constant norm are proved from them. Proposition 8.4 assumes the
controllability rank condition; the proof does not use it, and it is not a hypothesis here. Nothing
here proves that an optimal input exists or that a curve satisfying (8.12)–(8.13) is optimal.

**Conventions.** The state lies in a real normed space `E`, the multiplier `p(t)` in its dual
`E →L[ℝ] ℝ` (the book's `pᵀ`, `p ∈ ℝⁿ`); `‖u‖²` is the Euclidean `u ⬝ᵥ u = Σ uᵢ²` on `Fin m → ℝ`
(not Mathlib's sup norm). The fields `gᵢ` are differentiable along the curve (MLS: smooth). The
bracket is the library's (MLS p. 324).
-/

noncomputable section

open Set Filter Topology VectorField Matrix

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS Exercise 6, pp. 391–392: a solution of `u̇ = Ω(t) u` with `Ω(t)` skew-symmetric keeps
its norm,** `‖u(t)‖² = ‖u(0)‖²` on `[0, T]` (the part of "`u(t) = U(t) u(0)`, `U(t) ∈ SO(m)`" that
Proposition 8.4 uses). -/
theorem dotProduct_self_eq_of_skew {Ω : ℝ → Matrix (Fin m) (Fin m) ℝ} {u : ℝ → Fin m → ℝ} {T : ℝ}
    (hΩ : ∀ t ∈ Icc 0 T, (Ω t)ᵀ = -Ω t) (hu : ∀ t ∈ Icc 0 T, HasDerivAt u (Ω t *ᵥ u t) t) :
    ∀ t ∈ Icc 0 T, u t ⬝ᵥ u t = u 0 ⬝ᵥ u 0 := by
  have hskew : ∀ t ∈ Icc 0 T, u t ⬝ᵥ (Ω t *ᵥ u t) = 0 := by
    intro t ht
    have h : u t ⬝ᵥ (Ω t *ᵥ u t) = -(u t ⬝ᵥ (Ω t *ᵥ u t)) := by
      calc u t ⬝ᵥ (Ω t *ᵥ u t) = (u t ᵥ* Ω t) ⬝ᵥ u t := Matrix.dotProduct_mulVec _ _ _
        _ = ((Ω t)ᵀ *ᵥ u t) ⬝ᵥ u t := by rw [Matrix.mulVec_transpose]
        _ = -(u t ⬝ᵥ (Ω t *ᵥ u t)) := by
          rw [hΩ t ht, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => u s ⬝ᵥ u s) 0 t := by
    intro t ht
    have hi : ∀ i, HasDerivAt (fun s => u s i) ((Ω t *ᵥ u t) i) t := fun i =>
      hasDerivAt_pi.1 (hu t ht) i
    have h : HasDerivAt (fun s => ∑ i, u s i * u s i)
        (∑ i, ((Ω t *ᵥ u t) i * u t i + u t i * (Ω t *ᵥ u t) i)) t :=
      HasDerivAt.fun_sum fun i _ => (hi i).mul (hi i)
    show HasDerivAt (fun s => ∑ i, u s i * u s i) 0 t
    convert h using 1
    have h2 := hskew t ht
    simp only [dotProduct] at h2
    have : ∑ i, ((Ω t *ᵥ u t) i * u t i + u t i * (Ω t *ᵥ u t) i) =
        2 * ∑ i, u t i * (Ω t *ᵥ u t) i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h2, mul_zero]
  intro t ht
  refine constant_of_has_deriv_right_zero (f := fun s => u s ⬝ᵥ u s) ?_ ?_ t ht
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · exact fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt

/-- **MLS eq. (8.11), p. 372: the Hamiltonian `H(q, p, u) = ½ uᵀu + pᵀ Σ gᵢ(q) uᵢ`.** -/
def hamiltonian (g : Fin m → E → E) (q : E) (p : E →L[ℝ] ℝ) (u : Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (u ⬝ᵥ u) + p (driftFree g q u)

/-- **MLS eq. (8.12), p. 372: `∂H/∂q = Σ uᵢ pᵀ ∂gᵢ/∂q`,** the derivative of the Hamiltonian in the
state, for fields differentiable at `q`. -/
theorem hasFDerivAt_hamiltonian (g : Fin m → E → E) (p : E →L[ℝ] ℝ) (u : Fin m → ℝ) {q : E}
    (hg : ∀ i, DifferentiableAt ℝ (g i) q) :
    HasFDerivAt (fun x => hamiltonian g x p u) (∑ i, u i • p.comp (fderiv ℝ (g i) q)) q := by
  have h : HasFDerivAt (fun x => driftFree g x u) (∑ i, u i • fderiv ℝ (g i) q) q :=
    HasFDerivAt.fun_sum fun i _ => (hg i).hasFDerivAt.const_smul (u i)
  have h2 := (p.hasFDerivAt.comp q h).const_add ((1 / 2 : ℝ) * (u ⬝ᵥ u))
  refine h2.congr_fderiv ?_
  ext v
  simp [map_sum, map_smul]

/-- **MLS eq. (8.13), p. 372: the optimal input `uᵢ = −pᵀ gᵢ(q)`** along a curve `(q, p)`. -/
def optimalInput (g : Fin m → E → E) (q : ℝ → E) (p : ℝ → E →L[ℝ] ℝ) (t : ℝ) : Fin m → ℝ :=
  fun i => -p t (g i (q t))

/-- **MLS eq. (8.12), p. 372: `∂H/∂u = 0` is (8.13):** the derivative of the Hamiltonian in the
input at `uᵢ = −pᵀ gᵢ(q)` is zero. -/
theorem hasFDerivAt_hamiltonian_input (g : Fin m → E → E) (q : ℝ → E) (p : ℝ → E →L[ℝ] ℝ)
    (t : ℝ) :
    HasFDerivAt (fun v => hamiltonian g (q t) (p t) v) (0 : (Fin m → ℝ) →L[ℝ] ℝ)
      (optimalInput g q p t) := by
  set c : Fin m → ℝ := fun i => p t (g i (q t)) with hc
  have hH : (fun v => hamiltonian g (q t) (p t) v) =
      fun v => ∑ i, ((1 / 2 : ℝ) * (v i * v i) + v i * c i) := by
    funext v
    simp [hamiltonian, driftFree, dotProduct, map_sum, map_smul, Finset.mul_sum,
      Finset.sum_add_distrib, hc]
  rw [hH]
  have hpr : ∀ i, HasFDerivAt (fun v : Fin m → ℝ => v i)
      (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) (optimalInput g q p t) := fun i =>
    hasFDerivAt_apply i _
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((((hpr i).mul (hpr i)).const_mul (1 / 2 : ℝ)).add ((hpr i).mul_const (c i)))
  convert h using 1
  refine (Finset.sum_eq_zero fun i _ => ?_).symm
  ext w
  simp [optimalInput, hc]
  ring

/-- **MLS eq. (8.14), p. 372: the optimal Hamiltonian `H* = −½ Σ (pᵀ gᵢ(q))²`.** -/
theorem hamiltonian_optimalInput (g : Fin m → E → E) (q : ℝ → E) (p : ℝ → E →L[ℝ] ℝ) (t : ℝ) :
    hamiltonian g (q t) (p t) (optimalInput g q p t) =
      -(1 / 2 : ℝ) * ∑ i, (p t (g i (q t))) ^ 2 := by
  simp only [hamiltonian, optimalInput, driftFree, dotProduct, map_sum, map_smul, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **MLS eq. (8.16), p. 373: the matrix `Ω(q, p)`, `Ω_{ij} = pᵀ [gᵢ, gⱼ](q)`.** -/
def optimalOmega (g : Fin m → E → E) (q : E) (p : E →L[ℝ] ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => p (lieBracket ℝ (g i) (g j) q)

/-- **MLS p. 373: `Ω(q, p)` is skew-symmetric** (it lies in `so(m)`). -/
theorem optimalOmega_transpose (g : Fin m → E → E) (q : E) (p : E →L[ℝ] ℝ) :
    (optimalOmega g q p)ᵀ = -optimalOmega g q p := by
  ext i j
  simp [optimalOmega, lieBracket_swap (V := g j)]

/-- **MLS Proposition 8.4, p. 373, eq. (8.16): `u̇ = Ω(q, p) u`.** Along a curve `(q, p)` on
`[0, T]` with `q̇ = Σ gᵢ(q) uᵢ` and `ṗ = −∂H/∂q` (8.12), the optimal input (8.13) has derivative
`Ω(q, p) u`, for fields differentiable along the curve. -/
theorem hasDerivAt_optimalInput {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ} {T : ℝ}
    (hg : ∀ i, ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (g i) (q t))
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t) :
    ∀ t ∈ Icc 0 T, HasDerivAt (optimalInput g q p)
      (optimalOmega g (q t) (p t) *ᵥ optimalInput g q p t) t := by
  intro t ht
  rw [hasDerivAt_pi]
  intro i
  have hgq : HasDerivAt (fun s => g i (q s))
      (fderiv ℝ (g i) (q t) (driftFree g (q t) (optimalInput g q p t))) t :=
    (hg i t ht).hasFDerivAt.comp_hasDerivAt t (hq t ht)
  have h := ((hp t ht).clm_apply hgq).neg
  convert h using 1
  · funext s
    simp [optimalInput]
  simp only [optimalOmega, Matrix.mulVec, dotProduct, Matrix.of_apply, lieBracket, map_sub,
    driftFree, map_sum, map_smul, smul_eq_mul, optimalInput]
  simp
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **MLS Proposition 8.4, p. 373: the optimal input has constant norm,** `‖u(t)‖² = ‖u(0)‖²` for
`t ∈ [0, T]`, under the necessary conditions (8.12)–(8.13) (the rank condition the book also
assumes is not used). -/
theorem optimalInput_dotProduct_self {g : Fin m → E → E} {q : ℝ → E} {p : ℝ → E →L[ℝ] ℝ} {T : ℝ}
    (hg : ∀ i, ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (g i) (q t))
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q (driftFree g (q t) (optimalInput g q p t)) t)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt p
      (-∑ i, optimalInput g q p t i • (p t).comp (fderiv ℝ (g i) (q t))) t) :
    ∀ t ∈ Icc 0 T, optimalInput g q p t ⬝ᵥ optimalInput g q p t =
      optimalInput g q p 0 ⬝ᵥ optimalInput g q p 0 := by
  exact dotProduct_self_eq_of_skew (Ω := fun t => optimalOmega g (q t) (p t))
    (fun t _ => optimalOmega_transpose g (q t) (p t)) (hasDerivAt_optimalInput hg hq hp)

end Nonholonomic
end RoboLean
