import RoboLean.Dynamics.MassMatrix
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Christoffel symbols, the Coriolis matrix and the skew symmetry of `Ṁ − 2C`

MLS Chapter 4, §3.2, printed pp. 169–171. For a joint-space inertia matrix `M(θ)`, the
Christoffel symbols are (eq. (4.22))

`Γᵢⱼₖ = ½ (∂Mᵢⱼ/∂θₖ + ∂Mᵢₖ/∂θⱼ − ∂Mₖⱼ/∂θᵢ)`,

the Coriolis matrix is `Cᵢⱼ(θ, θ̇) = ∑ₖ Γᵢⱼₖ θ̇ₖ` (eq. (4.23)), and MLS Lemma 4.2(2) (p. 171)
states that `Ṁ − 2C` is skew-symmetric. MLS stresses that the skew symmetry depends on this
particular choice of `C`.

The derivative data are explicit. The algebraic part takes the partial derivatives as a
family `dM : Fin n → Matrix (Fin n) (Fin n) ℝ`, `dM k = ∂M/∂θₖ` at one configuration, and
`Ṁ = ∑ₖ θ̇ₖ ∂M/∂θₖ` (`Christoffel.rate`). The skew symmetry then needs only that every `dM k` is
symmetric (`skew_rate_sub_two_coriolisMatrix`). The trajectory part takes a field
`M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ`, symmetric at every configuration, with a
Fréchet derivative `M' i j` of every entry at `θ(t)` and actual derivatives of the joint
coordinates; it derives the chain rule for `s ↦ M(θ(s))`, the symmetry of the partial
derivatives, and the skew symmetry of `Ṁ − 2C` for every actual derivative `Ṁ`
(`skew_deriv_sub_two_coriolisMatrix`).

The equations of motion (4.21)/(4.24) themselves, Lagrange's equations (Theorem 4.1) and the
gravity term `N` are not formalized here.
-/

noncomputable section

open Matrix

namespace RoboLean
namespace Christoffel

variable {n : ℕ}

/-- **MLS eq. (4.22), p. 170: the Christoffel symbols** of an inertia matrix with partial
derivatives `dM k = ∂M/∂θₖ`: `Γᵢⱼₖ = ½ (∂Mᵢⱼ/∂θₖ + ∂Mᵢₖ/∂θⱼ − ∂Mₖⱼ/∂θᵢ)`, i.e.
`(dM k i j + dM j i k - dM i k j) / 2`. Lean indices `i, j, k : Fin n` are the book's
`i + 1, j + 1, k + 1`. -/
def symbol (dM : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) : ℝ :=
  (dM k i j + dM j i k - dM i k j) / 2

/-- **MLS eq. (4.23), p. 171: the Coriolis matrix** `Cᵢⱼ(θ, θ̇) = ∑ₖ Γᵢⱼₖ θ̇ₖ`, from the partial
derivatives `dM` at `θ` and the joint rates `θ̇`. -/
def coriolisMatrix (dM : Fin n → Matrix (Fin n) (Fin n) ℝ) (θ' : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k, symbol dM i j k * θ' k

/-- The rate `Ṁ = ∑ₖ θ̇ₖ ∂M/∂θₖ` of the inertia matrix along a motion with joint rates `θ̇`, the
chain-rule expansion used on MLS pp. 169–171 (`Ṁᵢⱼ = ∑ₖ ∂Mᵢⱼ/∂θₖ θ̇ₖ`). -/
def rate (dM : Fin n → Matrix (Fin n) (Fin n) ℝ) (θ' : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k, θ' k • dM k

/-- `Ṁᵢⱼ = ∑ₖ ∂Mᵢⱼ/∂θₖ θ̇ₖ` entrywise (MLS p. 171). -/
theorem rate_apply (dM : Fin n → Matrix (Fin n) (Fin n) ℝ) (θ' : Fin n → ℝ) (i j : Fin n) :
    rate dM θ' i j = ∑ k, dM k i j * θ' k := by
  simp [rate, Matrix.sum_apply, mul_comm]

/-- **MLS eq. (4.21), p. 170: the Coriolis and centrifugal terms.**
`(C(θ, θ̇) θ̇)ᵢ = ∑ⱼ,ₖ Γᵢⱼₖ θ̇ⱼ θ̇ₖ`. -/
theorem coriolisMatrix_mulVec (dM : Fin n → Matrix (Fin n) (Fin n) ℝ) (θ' : Fin n → ℝ)
    (i : Fin n) :
    (coriolisMatrix dM θ' *ᵥ θ') i = ∑ j, ∑ k, symbol dM i j k * θ' j * θ' k := by
  simp only [coriolisMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The entries of `Ṁ − 2C`, as computed in the proof of MLS Lemma 4.2, p. 171:**
`(Ṁ − 2C)ᵢⱼ = ∑ₖ (∂Mₖⱼ/∂θᵢ − ∂Mᵢₖ/∂θⱼ) θ̇ₖ`. This step uses no symmetry. -/
theorem rate_sub_two_coriolisMatrix_apply (dM : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (θ' : Fin n → ℝ) (i j : Fin n) :
    (rate dM θ' - (2 : ℝ) • coriolisMatrix dM θ') i j = ∑ k, (dM i k j - dM j i k) * θ' k := by
  rw [Matrix.sub_apply, Matrix.smul_apply, rate_apply, coriolisMatrix, Matrix.of_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [symbol]
  ring

/-- **MLS Lemma 4.2(2), p. 171, algebraic form.** If every partial derivative `∂M/∂θₖ` is
symmetric (as it is when `M(θ)` is symmetric at every configuration, `partials_isSymm`), then
`Ṁ − 2C` is skew-symmetric: `(Ṁ − 2C)ᵀ = −(Ṁ − 2C)`, for every joint rate `θ̇`. The printed
proof "switching `i` and `j`" uses this symmetry implicitly. -/
theorem skew_rate_sub_two_coriolisMatrix {dM : Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hdM : ∀ k, (dM k).IsSymm) (θ' : Fin n → ℝ) :
    (rate dM θ' - (2 : ℝ) • coriolisMatrix dM θ')ᵀ =
      -(rate dM θ' - (2 : ℝ) • coriolisMatrix dM θ') := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.neg_apply, rate_sub_two_coriolisMatrix_apply,
    rate_sub_two_coriolisMatrix_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hdM j).apply k i, (hdM i).apply j k]
  ring

/-- A skew-symmetric real matrix has zero quadratic form, `x ⬝ A x = 0` when `Aᵀ = −A`
(used for the passivity identity of MLS p. 172). -/
theorem dotProduct_mulVec_eq_zero_of_transpose_eq_neg {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = -A) (x : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ x) = 0 := by
  have h : x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (Aᵀ *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
  rw [hA, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- **MLS p. 172 (the passivity property): `θ̇ᵀ (Ṁ − 2C) θ̇ = 0`**, a consequence of the skew
symmetry of `Ṁ − 2C` (Lemma 4.2(2)) under the same symmetry hypothesis on the partial
derivatives. -/
theorem dotProduct_rate_sub_two_coriolisMatrix_mulVec {dM : Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hdM : ∀ k, (dM k).IsSymm) (θ' : Fin n → ℝ) :
    θ' ⬝ᵥ ((rate dM θ' - (2 : ℝ) • coriolisMatrix dM θ') *ᵥ θ') = 0 :=
  dotProduct_mulVec_eq_zero_of_transpose_eq_neg (skew_rate_sub_two_coriolisMatrix hdM θ') θ'

/-! ### From a differentiable inertia field along a joint trajectory -/

/-- The partial derivatives `∂M/∂θₖ` read off from Fréchet derivatives `M' i j` of the entries
of an inertia field at one configuration: `(partials M' k) i j = M' i j eₖ`, with `eₖ` the
`k`th coordinate vector (MLS p. 169, `∂Mᵢⱼ/∂θₖ`). -/
def partials (M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)) : Fin n → Matrix (Fin n) (Fin n) ℝ :=
  fun k => Matrix.of fun i j => M' i j (Pi.single k 1)

/-- **The chain rule for the inertia matrix along a motion (MLS pp. 169–171).** If every entry
of the field `M` has Fréchet derivative `M' i j` at `θ(t)` and every joint coordinate has an
actual derivative `θ̇ₖ` at `t`, then every entry of `s ↦ M(θ(s))` has the actual derivative
`(∑ₖ θ̇ₖ ∂M/∂θₖ)ᵢⱼ` at `t`. -/
theorem hasDerivAt_comp {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t) (i j : Fin n) :
    HasDerivAt (fun s => M (θ s) i j) (rate (partials M') θ' i j) t := by
  have hcurve : HasDerivAt θ θ' t := hasDerivAt_pi.mpr hθ
  have h := (hM i j).comp_hasDerivAt t hcurve
  have e : M' i j θ' = rate (partials M') θ' i j := by
    rw [rate_apply]
    conv_lhs => rw [pi_eq_sum_univ' θ']
    simp [map_sum, partials, mul_comm]
  rw [← e]
  exact h

/-- **Symmetry of the partial derivatives.** If `M(q)` is symmetric at every configuration and
its entries have Fréchet derivatives `M' i j` at `q₀`, then every partial derivative
`∂M/∂θₖ` at `q₀` is symmetric (uniqueness of the Fréchet derivative). This is the hypothesis of
`skew_rate_sub_two_coriolisMatrix` for an inertia matrix symmetric by MLS Lemma 4.2(1). -/
theorem partials_isSymm {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ q, (M q).IsSymm) {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {q₀ : Fin n → ℝ} (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) q₀) (k : Fin n) :
    (partials M' k).IsSymm := by
  have hji : ∀ i j, M' j i = M' i j := by
    intro i j
    have hfun : (fun q => M q j i) = fun q => M q i j := by
      funext q
      exact (hsymm q).apply i j
    have h := hM j i
    rw [hfun] at h
    exact h.unique (hM i j)
  ext i j
  simp [partials, Matrix.transpose_apply, hji i j]

/-- **MLS Lemma 4.2(2), p. 171, along a joint trajectory.** Let `M` be an inertia field that is
symmetric at every configuration, with Fréchet derivatives `M' i j` of its entries at `θ(t)`,
and let the joint coordinates have actual derivatives `θ̇` at `t`. For every matrix `Mdot`
(the book's `Ṁ`) whose entries are actual derivatives of `s ↦ M(θ(s))ᵢⱼ` at `t`, the matrix
`Mdot − 2C`, with `C = C(θ(t), θ̇)` the Christoffel Coriolis matrix of eq. (4.23), is
skew-symmetric. -/
theorem skew_deriv_sub_two_coriolisMatrix {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ q, (M q).IsSymm) {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t) {Mdot : Matrix (Fin n) (Fin n) ℝ}
    (hMdot : ∀ i j, HasDerivAt (fun s => M (θ s) i j) (Mdot i j) t) :
    (Mdot - (2 : ℝ) • coriolisMatrix (partials M') θ')ᵀ =
      -(Mdot - (2 : ℝ) • coriolisMatrix (partials M') θ') := by
  have hrate : Mdot = rate (partials M') θ' := by
    ext i j
    exact (hMdot i j).unique (hasDerivAt_comp hM hθ i j)
  rw [hrate]
  exact skew_rate_sub_two_coriolisMatrix (partials_isSymm hsymm hM) θ'

end Christoffel

namespace InertialChain

variable {n : ℕ} (ch : InertialChain n)

/-- **MLS Lemma 4.2(2), p. 171, for the inertia matrix `M(θ) = ∑ₖ J_kᵀ 𝓜_k J_k` of an open
chain (eq. (4.19)).** With symmetric link inertias, along a joint trajectory with actual
derivatives `θ̇`, and given Fréchet derivatives `M' i j` of the entries of `M` at `θ(t)`, every
actual derivative `Mdot` (the book's `Ṁ`) of `s ↦ M(θ(s))` makes `Mdot − 2C` skew-symmetric.
The differentiability hypothesis `hM` is not discharged here for a general chain (MLS
Proposition 4.3, eq. (4.30), is not formalized); `RoboLean.Examples.PlanarTwoLinkDynamics`
discharges it for one arm. -/
theorem skew_deriv_massMatrix_sub_two_coriolisMatrix (h : ∀ k, (ch.linkInertia k).IsSymm)
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hM : ∀ i j, HasFDerivAt (fun q => ch.massMatrix q i j) (M' i j) (θ t))
    (hθ : ∀ k, HasDerivAt (fun s => θ s k) (θ' k) t) {Mdot : Matrix (Fin n) (Fin n) ℝ}
    (hMdot : ∀ i j, HasDerivAt (fun s => ch.massMatrix (θ s) i j) (Mdot i j) t) :
    (Mdot - (2 : ℝ) • Christoffel.coriolisMatrix (Christoffel.partials M') θ')ᵀ =
      -(Mdot - (2 : ℝ) • Christoffel.coriolisMatrix (Christoffel.partials M') θ') :=
  Christoffel.skew_deriv_sub_two_coriolisMatrix (ch.massMatrix_isSymm h) hM hθ hMdot

end InertialChain
end RoboLean
