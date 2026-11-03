import RoboLean.Nonholonomic.CommutingFlows
import RoboLean.Control.FlowDifferentiable

/-!
# A nonlinear pair of commuting vector fields (MLS p. 324, eq. (7.8))

**The fields.** On `ℝ × ℝ` with the sup norm, `X(x) = (sin x₁, 0)` and `Y(x) = (0, sin x₂)`
(`sinFirst`, `sinSecond`). Their derivatives `h ↦ (cos x₁ · h₁, 0)` and `h ↦ (0, cos x₂ · h₂)` are
continuous and bounded by `1`, so `X`, `Y`, `−X` and `−Y` have flows differentiable in the initial
state (`exists_isDifferentiableFlow_autonomous`), and `[X, Y] = 0` (Mathlib's bracket, the book's
sign; `lieBracket_sinFirst_sinSecond`). Hence their flows commute and the square of flows (7.8)
closes exactly (`exists_flows_sin_square_eq`): every hypothesis of
`flow_comm_of_lieBracket_eq_zero` and `flow_square_eq_of_lieBracket_eq_zero` is met.

**Carrier.** `ℝ × ℝ` with the sup norm; the systems are time-invariant, written `fun _ => X` (time
first, ignored). This is an instance of a general theorem; it is not a claim about a mechanism.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean.Examples

/-- **The field `X(x) = (sin x₁, 0)` on `ℝ × ℝ` (for MLS p. 324, eq. (7.8)).** -/
def sinFirst : ℝ × ℝ → ℝ × ℝ := fun x => (Real.sin x.1, 0)

/-- **The field `Y(x) = (0, sin x₂)` on `ℝ × ℝ` (for MLS p. 324, eq. (7.8)).** -/
def sinSecond : ℝ × ℝ → ℝ × ℝ := fun x => (0, Real.sin x.2)

/-- **The derivative of `sinFirst` (for MLS p. 324):** `h ↦ (cos x₁ · h₁, 0)`. -/
def sinFirstDeriv (x : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Real.cos x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0

/-- **The derivative of `sinSecond` (for MLS p. 324):** `h ↦ (0, cos x₂ · h₂)`. -/
def sinSecondDeriv (x : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (Real.cos x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- **`sinFirst` has the derivative `sinFirstDeriv x` at every `x` (for MLS p. 324).** -/
theorem hasFDerivAt_sinFirst (x : ℝ × ℝ) : HasFDerivAt sinFirst (sinFirstDeriv x) x := by
  have hsin : HasFDerivAt (fun y : ℝ × ℝ => Real.sin y.1)
      (Real.cos x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (Real.hasDerivAt_sin x.1).comp_hasFDerivAt x hasFDerivAt_fst
  exact hsin.prodMk (hasFDerivAt_const (0 : ℝ) x)

/-- **`sinSecond` has the derivative `sinSecondDeriv x` at every `x` (for MLS p. 324).** -/
theorem hasFDerivAt_sinSecond (x : ℝ × ℝ) : HasFDerivAt sinSecond (sinSecondDeriv x) x := by
  have hsin : HasFDerivAt (fun y : ℝ × ℝ => Real.sin y.2)
      (Real.cos x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (Real.hasDerivAt_sin x.2).comp_hasFDerivAt x hasFDerivAt_snd
  exact (hasFDerivAt_const (0 : ℝ) x).prodMk hsin

/-- **The derivative of `sinFirst` is continuous (for MLS p. 324).** -/
theorem continuous_sinFirstDeriv : Continuous sinFirstDeriv := by
  have h : Continuous fun x : ℝ × ℝ => Real.cos x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ :=
    (Real.continuous_cos.comp continuous_fst).smul continuous_const
  exact (ContinuousLinearMap.prodL ℝ).continuous.comp (h.prodMk continuous_const)

/-- **The derivative of `sinSecond` is continuous (for MLS p. 324).** -/
theorem continuous_sinSecondDeriv : Continuous sinSecondDeriv := by
  have h : Continuous fun x : ℝ × ℝ => Real.cos x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    (Real.continuous_cos.comp continuous_snd).smul continuous_const
  exact (ContinuousLinearMap.prodL ℝ).continuous.comp (continuous_const.prodMk h)

/-- **The derivative of `sinFirst` is bounded by `1` (for MLS p. 324)**, operator norm for the sup
norm on `ℝ × ℝ`. -/
theorem norm_sinFirstDeriv_le (x : ℝ × ℝ) : ‖sinFirstDeriv x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
  simp only [sinFirstDeriv, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', zero_apply, Prod.norm_mk, smul_eq_mul,
    norm_zero, norm_mul, one_mul]
  have h1 := norm_fst_le h
  have hc := Real.abs_cos_le_one x.1
  rw [← Real.norm_eq_abs] at hc
  refine max_le ?_ (norm_nonneg h)
  nlinarith [norm_nonneg (Real.cos x.1), norm_nonneg h.1]

/-- **The derivative of `sinSecond` is bounded by `1` (for MLS p. 324)**, operator norm for the sup
norm on `ℝ × ℝ`. -/
theorem norm_sinSecondDeriv_le (x : ℝ × ℝ) : ‖sinSecondDeriv x‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
  simp only [sinSecondDeriv, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_snd', zero_apply, Prod.norm_mk, smul_eq_mul,
    norm_zero, norm_mul, one_mul]
  have h2 := norm_snd_le h
  have hc := Real.abs_cos_le_one x.2
  rw [← Real.norm_eq_abs] at hc
  refine max_le (norm_nonneg h) ?_
  nlinarith [norm_nonneg (Real.cos x.2), norm_nonneg h.2]

/-- **`sinFirst` and `sinSecond` commute (MLS p. 324):** `lieBracket ℝ sinFirst sinSecond = 0`
(Mathlib's bracket, the book's sign `[X, Y] = DY · X − DX · Y`). -/
theorem lieBracket_sinFirst_sinSecond (q : ℝ × ℝ) : lieBracket ℝ sinFirst sinSecond q = 0 := by
  rw [lieBracket, (hasFDerivAt_sinFirst q).fderiv, (hasFDerivAt_sinSecond q).fderiv]
  simp [sinFirstDeriv, sinSecondDeriv, sinFirst, sinSecond]

/-- **The flows of `sinFirst` and `sinSecond` exist, commute, and close the square (7.8) (MLS
p. 324):** there are flows `φ, ψ, φ', ψ'` of `X, Y, −X, −Y` differentiable in the initial state
(`IsDifferentiableFlow`, time first) with `φ^X_t ∘ φ^Y_s = φ^Y_s ∘ φ^X_t` for `t, s ≥ 0` and
`φ^{−Y}_ε ∘ φ^{−X}_ε ∘ φ^Y_ε ∘ φ^X_ε (q₀) = q₀` for `ε ≥ 0`. -/
theorem exists_flows_sin_square_eq :
    ∃ φ ψ φ' ψ' : ℝ → ℝ → ℝ × ℝ → ℝ × ℝ,
      ∃ DX' DY' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      ∃ D₁ D₂ D₃ D₄ : ℝ → ℝ → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
        Stability.IsDifferentiableFlow (fun _ => sinFirst) (fun _ => sinFirstDeriv) φ D₁ ∧
        Stability.IsDifferentiableFlow (fun _ => sinSecond) (fun _ => sinSecondDeriv) ψ D₂ ∧
        Stability.IsDifferentiableFlow (fun _ => -sinFirst) (fun _ => DX') φ' D₃ ∧
        Stability.IsDifferentiableFlow (fun _ => -sinSecond) (fun _ => DY') ψ' D₄ ∧
        (∀ t s, 0 ≤ t → 0 ≤ s → ∀ q, φ t 0 (ψ s 0 q) = ψ s 0 (φ t 0 q)) ∧
        ∀ ε, 0 ≤ ε → ∀ q₀, ψ' ε 0 (φ' ε 0 (ψ ε 0 (φ ε 0 q₀))) = q₀ := by
  have hK1 : ∀ y, ‖sinFirstDeriv y‖ ≤ ((1 : NNReal) : ℝ) := fun y => by
    simpa using norm_sinFirstDeriv_le y
  have hK2 : ∀ y, ‖sinSecondDeriv y‖ ≤ ((1 : NNReal) : ℝ) := fun y => by
    simpa using norm_sinSecondDeriv_le y
  obtain ⟨φ, D₁, hX⟩ :=
    Stability.exists_isDifferentiableFlow_autonomous hasFDerivAt_sinFirst
      continuous_sinFirstDeriv hK1
  obtain ⟨ψ, D₂, hY⟩ :=
    Stability.exists_isDifferentiableFlow_autonomous hasFDerivAt_sinSecond
      continuous_sinSecondDeriv hK2
  obtain ⟨φ', D₃, hX'⟩ :=
    Stability.exists_isDifferentiableFlow_autonomous (F := -sinFirst)
      (DF := fun x => -sinFirstDeriv x) (fun y => (hasFDerivAt_sinFirst y).neg)
      continuous_sinFirstDeriv.neg fun y => by rw [norm_neg]; exact hK1 y
  obtain ⟨ψ', D₄, hY'⟩ :=
    Stability.exists_isDifferentiableFlow_autonomous (F := -sinSecond)
      (DF := fun x => -sinSecondDeriv x) (fun y => (hasFDerivAt_sinSecond y).neg)
      continuous_sinSecondDeriv.neg fun y => by rw [norm_neg]; exact hK2 y
  refine ⟨φ, ψ, φ', ψ', _, _, D₁, D₂, D₃, D₄, hX, hY, hX', hY', ?_, ?_⟩
  · intro t s ht hs q
    exact Nonholonomic.flow_comm_of_lieBracket_eq_zero hX hY (K := 1) norm_sinFirstDeriv_le
      lieBracket_sinFirst_sinSecond ht hs q
  · intro ε hε q₀
    exact Nonholonomic.flow_square_eq_of_lieBracket_eq_zero hX hY hX' hY' (K := 1)
      norm_sinFirstDeriv_le lieBracket_sinFirst_sinSecond hε q₀

end RoboLean.Examples
