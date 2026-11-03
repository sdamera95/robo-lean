import RoboLean.Examples.NonholonomicEngel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Example 8.2's change of coordinates for the car (p. 368) and Engel's system: the optimal
Hamiltonian, the constant multipliers and the pendulum equation (MLS Example 8.4, p. 374)

**Example 8.2 (p. 368).** "We use a change of coordinates `z₁ = x`, `z₂ = φ`, `z₃ = sin θ`, `z₄ = y`,
and a change of inputs `v₁ = cos θ u₁`, `v₂ = u₂` to put the equations in the form `ż₁ = v₁`,
`ż₂ = v₂`, `ż₃ = (1/l) tan z₂ v₁`, `ż₄ = z₃/√(1 − z₃²) v₁`." The rewriting is exact along every
solution of (7.14) where `cos θ > 0` (`car_example82_hasDerivAt`), a hypothesis the book does not
print: for `cos θ < 0` the last equation holds with the opposite sign, since
`√(1 − sin²θ) = |cos θ|`. The Taylor and Fourier treatment that follows on p. 368 is approximate and
not formalized.

**Example 8.4: what MLS prints.** For Engel's system `q̇ = (u₁, u₂, q₁u₂ − q₂u₁, q₁²u₂)` the optimal inputs
satisfy (8.18) `u̇₁ = 2(p₃ + q₁p₄)u₂`, `u̇₂ = −2(p₃ + q₁p₄)u₁`. "The solution of this equation is of
the form `u₁(t) = r sin α(t)`, `u₂(t) = r cos α(t)` … Further, since the optimal Hamiltonian given by
`H*(q, p) = −½(p₁ − q₂p₃)² − ½(p₂ + q₁p₃ + q₁²p₄)²` is independent of `q₃` and `q₄`, it follows that
`ṗ₃ = ṗ₄ = 0` so that `p₃` and `p₄` are constant. Using the functional form of `u₁` and `u₂` in
(8.18) we get `α̈ = 2p₄r sin α`. To integrate this equation, multiply both sides by `2α̇`, integrate
and define `δ = 2p₄r` to get `(α̇)² = b − 2δ cos α`, where `b` is a constant of the integration"
(p. 374).

**Formalized here.** The optimal Hamiltonian of Engel's system as printed (from (8.14)); the state
derivative of the Hamiltonian `∂H/∂q` has zero components along `q₃` and `q₄`, so along (8.12)
`ṗ₃ = ṗ₄ = 0`; for `α̇ = 2(p₃ + q₁p₄)` with constant `p₃, p₄` and `q̇₁ = u₁ = r sin α`, the inputs
`(r sin α, r cos α)` solve (8.18), `α̈ = 2p₄r sin α`, and `(α̇)² = b − 2δ cos α` on the interval for a
constant `b`.

**Conventions.** Coordinates `q 0 = q₁, …, q 3 = q₄` as in the Engel example; `pᵢ = p(eᵢ)` with
`eᵢ = Pi.single (i − 1) 1`; the curve `(q, p)` is not assumed optimal, only to satisfy the necessary
conditions, as in Proposition 8.4. **Not formalized:** the converse that every solution of (8.18) has
the polar form, and the elliptic integral (8.19).
-/

noncomputable section

open Set Real
open RoboLean.Nonholonomic RoboLean.Examples

namespace RoboLean
namespace Nonholonomic

/-! ### Example 8.2: the car in the coordinates `(x, φ, sin θ, y)` (p. 368) -/

/-- **MLS Example 8.2, p. 368: the change of coordinates `z = (x, φ, sin θ, y)`,
`v = (cos θ u₁, u₂)`.** At a time `t` where `(x, y, θ, φ)` solves the car (7.14),
`ẋ = cos θ u₁`, `ẏ = sin θ u₁`, `θ̇ = (1/l) tan φ u₁`, `φ̇ = u₂`, and `cos θ(t) > 0` (not printed),
the new coordinates satisfy `ż₁ = v₁`, `ż₂ = v₂`, `ż₃ = (1/l) tan z₂ v₁` and
`ż₄ = z₃/√(1 − z₃²) v₁`. -/
theorem car_example82_hasDerivAt {x y θ φ : ℝ → ℝ} {u₁ u₂ l t : ℝ}
    (hx : HasDerivAt x (cos (θ t) * u₁) t) (hy : HasDerivAt y (sin (θ t) * u₁) t)
    (hθ : HasDerivAt θ (1 / l * tan (φ t) * u₁) t) (hφ : HasDerivAt φ u₂ t)
    (hcos : 0 < cos (θ t)) :
    HasDerivAt x (cos (θ t) * u₁) t ∧ HasDerivAt φ u₂ t ∧
      HasDerivAt (fun s => sin (θ s)) (1 / l * tan (φ t) * (cos (θ t) * u₁)) t ∧
      HasDerivAt y (sin (θ t) / Real.sqrt (1 - sin (θ t) ^ 2) * (cos (θ t) * u₁)) t := by
  refine ⟨hx, hφ, ?_, ?_⟩
  · convert hθ.sin using 1
    ring
  · have hsq : Real.sqrt (1 - sin (θ t) ^ 2) = cos (θ t) := by
      rw [← cos_sq', Real.sqrt_sq hcos.le]
    convert hy using 1
    rw [hsq]
    field_simp

/-- **MLS Example 8.4, p. 374: `pᵀg₁(q) = p₁ − q₂p₃`** with `pᵢ = p(eᵢ)`. -/
theorem engel_p_g1 (p : (Fin 4 → ℝ) →L[ℝ] ℝ) (q : Fin 4 → ℝ) :
    p (engelG1 q) = p (Pi.single 0 1) - q 1 * p (Pi.single 2 1) := by
  have h : engelG1 q = Pi.single 0 1 - q 1 • Pi.single 2 1 := by
    ext i; fin_cases i <;> simp [engelG1]
  rw [h, map_sub, map_smul, smul_eq_mul]

/-- **MLS Example 8.4, p. 374: `pᵀg₂(q) = p₂ + q₁p₃ + q₁²p₄`** with `pᵢ = p(eᵢ)`. -/
theorem engel_p_g2 (p : (Fin 4 → ℝ) →L[ℝ] ℝ) (q : Fin 4 → ℝ) :
    p (engelG2 q) =
      p (Pi.single 1 1) + q 0 * p (Pi.single 2 1) + q 0 ^ 2 * p (Pi.single 3 1) := by
  have h : engelG2 q = Pi.single 1 1 + q 0 • Pi.single 2 1 + q 0 ^ 2 • Pi.single 3 1 := by
    ext i; fin_cases i <;> simp [engelG2]
  rw [h, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **MLS Example 8.4, p. 374: the optimal Hamiltonian of Engel's system,**
`H*(q, p) = −½(p₁ − q₂p₃)² − ½(p₂ + q₁p₃ + q₁²p₄)²`: the Hamiltonian (8.11) at the input (8.13)
along any curve `(q, p)`. -/
theorem engel_hamiltonian_optimalInput (q : ℝ → Fin 4 → ℝ) (p : ℝ → (Fin 4 → ℝ) →L[ℝ] ℝ)
    (t : ℝ) :
    hamiltonian engelFields (q t) (p t) (optimalInput engelFields q p t) =
      -(1 / 2 : ℝ) * (p t (Pi.single 0 1) - q t 1 * p t (Pi.single 2 1)) ^ 2 -
        (1 / 2 : ℝ) * (p t (Pi.single 1 1) + q t 0 * p t (Pi.single 2 1) +
          q t 0 ^ 2 * p t (Pi.single 3 1)) ^ 2 := by
  rw [hamiltonian_optimalInput, Fin.sum_univ_two]
  simp only [engelFields, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [engel_p_g1, engel_p_g2]
  ring

private theorem engelG1_hasFDerivAt (q : Fin 4 → ℝ) :
    HasFDerivAt engelG1 (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).smulRight
      (Pi.single 2 1 : Fin 4 → ℝ)) q := by
  have h : engelG1 = fun x => Pi.single 0 1 +
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).smulRight
        (Pi.single 2 1 : Fin 4 → ℝ)) x := by
    funext x; ext i; fin_cases i <;> simp [engelG1]
  rw [h]
  exact (ContinuousLinearMap.hasFDerivAt _).const_add _

private theorem engelG2_hasFDerivAt (q : Fin 4 → ℝ) :
    HasFDerivAt engelG2
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).smulRight
        (Pi.single 2 1 + (2 * q 0) • Pi.single 3 1 : Fin 4 → ℝ)) q := by
  have h0 : HasFDerivAt (fun x : Fin 4 → ℝ => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) q := hasFDerivAt_apply 0 q
  have h : engelG2 = fun x => Pi.single 1 1 + x 0 • (Pi.single 2 1 : Fin 4 → ℝ) +
      (x 0 ^ 2) • (Pi.single 3 1 : Fin 4 → ℝ) := by
    funext x; ext i; fin_cases i <;> simp [engelG2]
  rw [h]
  have h2 := ((h0.smul_const (Pi.single 2 1 : Fin 4 → ℝ)).const_add (Pi.single 1 1)).add
    ((h0.pow 2).smul_const (Pi.single 3 1 : Fin 4 → ℝ))
  convert h2 using 1
  ext v i
  fin_cases i <;> simp [smul_eq_mul]
  ring

/-- **MLS Example 8.4, p. 374: "`H*(q, p)` is independent of `q₃` and `q₄`, it follows that
`ṗ₃ = ṗ₄ = 0`":** the state derivative of the Hamiltonian, `∂H/∂q = Σ uᵢ pᵀ∂gᵢ/∂q` (8.12), has
zero components along `e₃` and `e₄` at every `(q, p, u)`; along `ṗ = −∂H/∂q` the multipliers
`p₃ = p(e₃)` and `p₄ = p(e₄)` therefore have zero derivative. -/
theorem engel_hamiltonian_deriv_q34 (p : (Fin 4 → ℝ) →L[ℝ] ℝ) (u : Fin 2 → ℝ)
    (q : Fin 4 → ℝ) :
    (∑ i, u i • p.comp (fderiv ℝ (engelFields i) q)) (Pi.single 2 1) = 0 ∧
      (∑ i, u i • p.comp (fderiv ℝ (engelFields i) q)) (Pi.single 3 1) = 0 := by
  have e1 : fderiv ℝ (engelFields 0) q = _ := (engelG1_hasFDerivAt q).fderiv
  have e2 : fderiv ℝ (engelFields 1) q = _ := (engelG2_hasFDerivAt q).fderiv
  rw [Fin.sum_univ_two]
  simp [e1, e2]

/-- **MLS (8.12) for Example 8.4, p. 374: `p₃` and `p₄` are constant** along every curve `p` on
`[0, T]` with `ṗ = −∂H/∂q` at some input `u(t)` and state `q(t)`. -/
theorem engel_p34_const {q : ℝ → Fin 4 → ℝ} {p : ℝ → (Fin 4 → ℝ) →L[ℝ] ℝ}
    {u : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hp : ∀ t ∈ Icc 0 T,
      HasDerivAt p (-(∑ i, u t i • (p t).comp (fderiv ℝ (engelFields i) (q t)))) t) :
    ∀ t ∈ Icc 0 T, p t (Pi.single 2 1) = p 0 (Pi.single 2 1) ∧
      p t (Pi.single 3 1) = p 0 (Pi.single 3 1) := by
  have hk : ∀ k : Fin 4, (k = 2 ∨ k = 3) → ∀ t ∈ Icc 0 T,
      p t (Pi.single k 1) = p 0 (Pi.single k 1) := by
    intro k hk2
    have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => p s (Pi.single k 1)) 0 t := by
      intro t ht
      have h := (ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1 : Fin 4 → ℝ)).hasFDerivAt.comp_hasDerivAt
        t (hp t ht)
      have hz := engel_hamiltonian_deriv_q34 (p t) (u t) (q t)
      rw [ContinuousLinearMap.apply_apply, neg_apply] at h
      rcases hk2 with rfl | rfl
      · rw [hz.1, neg_zero] at h; exact h
      · rw [hz.2, neg_zero] at h; exact h
    exact fun t ht => constant_of_has_deriv_right_zero
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
  exact fun t ht => ⟨hk 2 (Or.inl rfl) t ht, hk 3 (Or.inr rfl) t ht⟩

/-- **MLS Example 8.4, p. 374: the polar form solves (8.18), `α̈ = 2p₄r sin α`, and
`(α̇)² = b − 2δ cos α` with `δ = 2p₄r`.** On `[0, T]`, let `q₁` and `α` satisfy `q̇₁ = r sin α`
(`q̇₁ = u₁`) and `α̇ = 2(p₃ + q₁p₄)` with constants `p₃, p₄` (the entry `Ω₁₂` of (8.18)). Then
`u₁ = r sin α`, `u₂ = r cos α` satisfy (8.18), the derivative of `α̇` is `2p₄r sin α`, and
`(α̇)² + 2δ cos α` is constant. -/
theorem engel_alpha {q₁ α : ℝ → ℝ} {p₃ p₄ r T : ℝ}
    (hq : ∀ t ∈ Icc 0 T, HasDerivAt q₁ (r * sin (α t)) t)
    (hα : ∀ t ∈ Icc 0 T, HasDerivAt α (2 * (p₃ + q₁ t * p₄)) t) :
    (∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => r * sin (α s)) (2 * (p₃ + q₁ t * p₄) * (r * cos (α t))) t ∧
        HasDerivAt (fun s => r * cos (α s)) (-(2 * (p₃ + q₁ t * p₄)) * (r * sin (α t))) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivAt (fun s => 2 * (p₃ + q₁ s * p₄)) (2 * p₄ * r * sin (α t)) t) ∧
      ∃ b : ℝ, ∀ t ∈ Icc 0 T,
        (2 * (p₃ + q₁ t * p₄)) ^ 2 = b - 2 * (2 * p₄ * r) * cos (α t) := by
  have h818 : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => r * sin (α s)) (2 * (p₃ + q₁ t * p₄) * (r * cos (α t))) t ∧
        HasDerivAt (fun s => r * cos (α s)) (-(2 * (p₃ + q₁ t * p₄)) * (r * sin (α t))) t := by
    intro t ht
    constructor
    · convert ((hα t ht).sin).const_mul r using 1; ring
    · convert ((hα t ht).cos).const_mul r using 1; ring
  have hdd : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => 2 * (p₃ + q₁ s * p₄)) (2 * p₄ * r * sin (α t)) t := by
    intro t ht
    convert (((hq t ht).mul_const p₄).const_add p₃).const_mul 2 using 1; ring
  refine ⟨h818, hdd, ?_⟩
  set f : ℝ → ℝ := fun s => (2 * (p₃ + q₁ s * p₄)) ^ 2 + 2 * (2 * p₄ * r) * cos (α s) with hf
  have hfd : ∀ t ∈ Icc 0 T, HasDerivAt f 0 t := by
    intro t ht
    have h := ((hdd t ht).pow 2).add (((hα t ht).cos).const_mul (2 * (2 * p₄ * r)))
    convert h using 1
    norm_num
    ring
  refine ⟨f 0, fun t ht => ?_⟩
  have hc := constant_of_has_deriv_right_zero
    (fun s hs => (hfd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
  simp only [hf] at hc ⊢
  linarith

end Nonholonomic
end RoboLean
