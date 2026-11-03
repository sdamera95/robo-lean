import RoboLean.Grasp.ContactEquations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rolling a sphere on a plane: MLS Chapter 8, §4.3

MLS Chapter 8, printed pp. 384–387: the kinematic equations of rolling contact (8.34)
`M_f α̇_f − R_ψ M_o α̇_o = 0`, `T_f M_f α̇_f + T_o M_o α̇_o − ψ̇ = 0`; for a spherical finger of
radius `ρ` on a plane `M_o = I`, `T_o = 0`, `T_f = (0, −(1/ρ) tan u_f)`, `M_f = diag(ρ, ρ cos u_f)`;
the lift (8.35) `α̇_o = M_o⁻¹ R_ψ M_f u`, `ψ̇ = (T_f + T_o R_ψ) M_f u`; (8.36) `ψ̇ = −sin u_f u₂`;
Theorem 8.6 ("Gauss–Bonnet", p. 385) `Δψ = −Area of Ω` for a closed path enclosing a cap-shaped
region `Ω` on the unit sphere, proved by Green's theorem with the area form `cos u_f du_f dv_f`
(p. 386); and Proposition 8.7 (p. 386), whose proof reduces to the equation
`2(x − tan⁻¹(x/(π/2))) = l` having a unique solution `x ∈ [0, π/2]` for `l < π/2` (p. 387).

**What is formalized.** (8.34) as the rows of the library's contact equations (5.37) under pure
rolling; (8.35) from (8.34) for invertible `M_o` (with `R_ψ⁻¹ = R_ψ`); (8.36) for the sphere on the
plane where `cos u_f ≠ 0`, `ρ ≠ 0`; the change of `ψ` along a path as `−∫ sin u_f dv_f`; Theorem 8.6
for the boundary of a coordinate rectangle `[u₀, u₁] × [v₀, v₁]` of the chart, traversed
counterclockwise as four coordinate segments, with the area `∫∫ cos u_f du_f dv_f` (the book's
area form, p. 386); this replaces the printed cap-shaped region and Green's theorem by a direct
computation, and is narrower than the printed statement. Proposition 8.7: the existence and
uniqueness of `x`; the geometric part of its proof (Figure 8.5) is not formalized.

**Conventions.** `R_ψ` is the library's `angleMatrix ψ` (p. 250); `α_f = (u_f, v_f)` is a curve in
`Fin 2 → ℝ` with `u_f` entry `0` and `v_f` entry `1`; the segment from `p` to `q` is
`t ↦ p + t (q − p)`, `t ∈ [0, 1]`.
-/

noncomputable section

open Set Real Matrix
open RoboLean.Rolling

namespace RoboLean
namespace Nonholonomic

/-- **MLS eq. (8.34), p. 385: the kinematic equations of rolling contact,**
`M_f α̇_f − R_ψ M_o α̇_o = 0` and `T_f M_f α̇_f + T_o M_o α̇_o − ψ̇ = 0`. -/
def RollingKinematics (Mf Mo : Matrix (Fin 2) (Fin 2) ℝ) (Tf To : Fin 2 → ℝ) (ψ : ℝ)
    (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ) : Prop :=
  Mf *ᵥ αf' - angleMatrix ψ *ᵥ (Mo *ᵥ αo') = 0 ∧ Tf ⬝ᵥ (Mf *ᵥ αf') + To ⬝ᵥ (Mo *ᵥ αo') - ψ' = 0

/-- **MLS eq. (8.34), p. 385, from Chapter 5:** the contact equations (5.37) under pure rolling
(p. 249) give (8.34). -/
theorem rollingKinematics_of_contactEquations {Mf Kf Mo Ko : Matrix (Fin 2) (Fin 2) ℝ}
    {Tf To : Fin 2 → ℝ} {ψ : ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' : ℝ} {V : Twist}
    (h : ContactEquations Mf Kf Mo Ko Tf To ψ αf' αo' ψ' V) (hr : IsRolling V) :
    RollingKinematics Mf Mo Tf To ψ αf' αo' ψ' := by
  obtain ⟨h0, h1, h2⟩ := hr
  have hl := h.linear_tangent
  have ha := h.angular_normal
  rw [h0, h1] at hl
  rw [h2] at ha
  have hz : (![0, 0] : Fin 2 → ℝ) = 0 := by
    ext i
    fin_cases i <;> rfl
  rw [hz, add_zero] at hl
  exact ⟨sub_eq_zero.2 hl, by linarith⟩

/-- **MLS eq. (8.35), p. 385: the lift of a path of the finger,** `α̇_o = M_o⁻¹ R_ψ M_f α̇_f`,
`ψ̇ = (T_f + T_o R_ψ) M_f α̇_f`, equivalent to (8.34) when `M_o` is invertible. -/
theorem rollingKinematics_iff {Mf Mo : Matrix (Fin 2) (Fin 2) ℝ} (hMo : IsUnit Mo.det)
    (Tf To : Fin 2 → ℝ) (ψ : ℝ) (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ) :
    RollingKinematics Mf Mo Tf To ψ αf' αo' ψ' ↔
      αo' = Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ (Mf *ᵥ αf')) ∧
        ψ' = (Tf + To ᵥ* angleMatrix ψ) ⬝ᵥ (Mf *ᵥ αf') := by
  have hRR : ∀ x : Fin 2 → ℝ, angleMatrix ψ *ᵥ (angleMatrix ψ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, angleMatrix_mul_self, one_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : Mf *ᵥ αf' = angleMatrix ψ *ᵥ (Mo *ᵥ αo') := sub_eq_zero.1 h1
    have hαo : αo' = Mo⁻¹ *ᵥ (angleMatrix ψ *ᵥ (Mf *ᵥ αf')) := by
      rw [h1', hRR, mulVec_mulVec, nonsing_inv_mul _ hMo, one_mulVec]
    refine ⟨hαo, ?_⟩
    have hMoαo : Mo *ᵥ αo' = angleMatrix ψ *ᵥ (Mf *ᵥ αf') := by
      rw [hαo, mulVec_mulVec, mul_nonsing_inv _ hMo, one_mulVec]
    rw [add_dotProduct, ← dotProduct_mulVec, ← hMoαo]
    linarith
  · rintro ⟨h1, h2⟩
    have hMoαo : Mo *ᵥ αo' = angleMatrix ψ *ᵥ (Mf *ᵥ αf') := by
      rw [h1, mulVec_mulVec, mul_nonsing_inv _ hMo, one_mulVec]
    refine ⟨?_, ?_⟩
    · rw [hMoαo, hRR, sub_self]
    · rw [h2, add_dotProduct, ← dotProduct_mulVec, ← hMoαo]
      ring

/-- **MLS p. 385: `M_f = diag(ρ, ρ cos u_f)`** for a spherical finger of radius `ρ`. -/
def sphereMf (ρ u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ρ, 0; 0, ρ * cos u]

/-- **MLS p. 385: `T_f = (0, −(1/ρ) tan u_f)`** for a spherical finger of radius `ρ`. -/
def sphereTf (ρ u : ℝ) : Fin 2 → ℝ := ![0, -(tan u / ρ)]

/-- **MLS eq. (8.36), p. 385: `ψ̇ = −sin u_f u₂`** for the sphere rolling on a plane: with
`M_o = I`, `T_o = 0`, (8.34) holds exactly when `α̇_o = R_ψ M_f α̇_f` and `ψ̇ = −sin u_f · v̇_f`,
for `ρ ≠ 0` and `cos u_f ≠ 0`; the rate of `ψ` does not depend on `ρ`. -/
theorem sphere_rollingKinematics_iff {ρ u : ℝ} (hρ : ρ ≠ 0) (hu : cos u ≠ 0) (ψ : ℝ)
    (αf' αo' : Fin 2 → ℝ) (ψ' : ℝ) :
    RollingKinematics (sphereMf ρ u) 1 (sphereTf ρ u) 0 ψ αf' αo' ψ' ↔
      αo' = angleMatrix ψ *ᵥ (sphereMf ρ u *ᵥ αf') ∧ ψ' = -(sin u * αf' 1) := by
  have hrate : (sphereTf ρ u + (0 : Fin 2 → ℝ) ᵥ* angleMatrix ψ) ⬝ᵥ (sphereMf ρ u *ᵥ αf') =
      -(sin u * αf' 1) := by
    simp [sphereTf, sphereMf, dotProduct, mulVec, Fin.sum_univ_two, tan_eq_sin_div_cos]
    field_simp
  rw [rollingKinematics_iff (by simp) _ _ ψ αf' αo' ψ', inv_one, one_mulVec, hrate]

/-- **MLS eq. (8.36), p. 385, along a path:** `ψ` is the contact angle obtained by rolling the
sphere on the plane along `α_f = (u_f, v_f)` on `[0, T]` when `ψ̇ = −sin u_f · v̇_f` there. -/
def IsContactAngleAlong (αf : ℝ → Fin 2 → ℝ) (ψ : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, HasDerivAt ψ (-(sin (αf t 0) * deriv (fun s => αf s 1) t)) t

/-- **MLS proof of Theorem 8.6, p. 386: `Δψ = ∫₀ᵀ ψ̇ dt = −∫ sin u_f dv_f`** along a path whose
coordinates are continuously differentiable on `[0, T]`, `T ≥ 0`. -/
theorem IsContactAngleAlong.sub_eq_integral {αf : ℝ → Fin 2 → ℝ} {ψ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (h : IsContactAngleAlong αf ψ T) (hα : ContDiff ℝ 1 αf) :
    ψ T - ψ 0 = -∫ t in (0 : ℝ)..T, sin (αf t 0) * deriv (fun s => αf s 1) t := by
  have h0 : ContDiff ℝ 1 fun s => αf s 0 := contDiff_pi.1 hα 0
  have h1 : ContDiff ℝ 1 fun s => αf s 1 := contDiff_pi.1 hα 1
  have hc : Continuous fun t => -(sin (αf t 0) * deriv (fun s => αf s 1) t) :=
    ((continuous_sin.comp h0.continuous).mul (h1.continuous_deriv le_rfl)).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => h t (by rwa [uIcc_of_le hT] at ht)) (hc.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at hftc
  linarith

/-- **The segment from `p` to `q`,** `t ↦ p + t (q − p)` (a coordinate line of the chart of MLS
p. 385 when `p` and `q` share a coordinate). -/
def chartSegment (p q : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ := p + t • (q - p)

/-- **MLS Theorem 8.6, p. 385, for coordinate rectangles: `Δψ = −Area`.** Rolling the sphere on the
plane once around the boundary of the chart rectangle `[u₀, u₁] × [v₀, v₁]`, counterclockwise as
the four segments `(u₀, v₀) → (u₁, v₀) → (u₁, v₁) → (u₀, v₁) → (u₀, v₀)` (each in unit time, each
starting where the previous ended), changes `ψ` by `−∫_{u₀}^{u₁} ∫_{v₀}^{v₁} cos u dv du`, minus the
area of the rectangle in the book's area form `cos u_f du_f dv_f` on the unit sphere (p. 386). -/
theorem sphere_geometricPhase_rectangle (u₀ u₁ v₀ v₁ : ℝ) {ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ}
    (h₁ : IsContactAngleAlong (chartSegment ![u₀, v₀] ![u₁, v₀]) ψ₁ 1)
    (h₂ : IsContactAngleAlong (chartSegment ![u₁, v₀] ![u₁, v₁]) ψ₂ 1)
    (h₃ : IsContactAngleAlong (chartSegment ![u₁, v₁] ![u₀, v₁]) ψ₃ 1)
    (h₄ : IsContactAngleAlong (chartSegment ![u₀, v₁] ![u₀, v₀]) ψ₄ 1)
    (h₁₂ : ψ₂ 0 = ψ₁ 1) (h₂₃ : ψ₃ 0 = ψ₂ 1) (h₃₄ : ψ₄ 0 = ψ₃ 1) :
    ψ₄ 1 - ψ₁ 0 = -∫ u in u₀..u₁, ∫ _v in v₀..v₁, cos u := by
  have hseg : ∀ (p q : Fin 2 → ℝ) (t : ℝ), deriv (fun s => chartSegment p q s 1) t = q 1 - p 1 := by
    intro p q t
    have : HasDerivAt (fun s => chartSegment p q s 1) (q 1 - p 1) t := by
      simpa [chartSegment] using ((hasDerivAt_id t).mul_const (q 1 - p 1)).const_add (p 1)
    exact this.deriv
  have hconst : ∀ {φ : ℝ → ℝ} {c : ℝ}, (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ c t) → φ 1 - φ 0 = c := by
    intro φ c hφ
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hφ t (by rwa [uIcc_of_le zero_le_one] at ht))
      (intervalIntegrable_const (c := c))
    simpa using this.symm
  have e₁ : ψ₁ 1 - ψ₁ 0 = 0 := hconst fun t ht => by
    simpa [hseg, chartSegment] using h₁ t ht
  have e₂ : ψ₂ 1 - ψ₂ 0 = -(sin u₁ * (v₁ - v₀)) := hconst fun t ht => by
    simpa [hseg, chartSegment] using h₂ t ht
  have e₃ : ψ₃ 1 - ψ₃ 0 = 0 := hconst fun t ht => by
    simpa [hseg, chartSegment] using h₃ t ht
  have e₄ : ψ₄ 1 - ψ₄ 0 = -(sin u₀ * (v₀ - v₁)) := hconst fun t ht => by
    simpa [hseg, chartSegment] using h₄ t ht
  have harea : ∫ u in u₀..u₁, ∫ _v in v₀..v₁, cos u = (v₁ - v₀) * (sin u₁ - sin u₀) := by
    simp [intervalIntegral.integral_const_mul, integral_cos]
  rw [harea]
  linarith

/-- **MLS Proposition 8.7, p. 387, the equation for `x`:** for `0 ≤ l < π/2`, the equation
`2(x − tan⁻¹(x/(π/2))) = l` has exactly one solution `x ∈ [0, π/2]` ("because `f(0) = 0`,
`f(π/2) = π/2 > l` and `f′(x) > 0`"). -/
theorem prop87_existsUnique {l : ℝ} (hl₀ : 0 ≤ l) (hl : l < π / 2) :
    ∃! x, x ∈ Icc 0 (π / 2) ∧ 2 * (x - arctan (x / (π / 2))) = l := by
  set f : ℝ → ℝ := fun x => 2 * (x - arctan (x / (π / 2))) with hf
  have hπ : (0 : ℝ) < π / 2 := by positivity
  have hcont : Continuous f := by
    simp only [hf]
    fun_prop
  have hd : ∀ x, HasDerivAt f (2 * (1 - 1 / (1 + (x / (π / 2)) ^ 2) * (1 / (π / 2)))) x := by
    intro x
    have h := ((Real.hasDerivAt_arctan (x / (π / 2))).comp x
      ((hasDerivAt_id x).div_const (π / 2)))
    simpa [hf, Function.comp_def] using ((hasDerivAt_id x).sub h).const_mul 2
  have hpos : ∀ x, 0 < 2 * (1 - 1 / (1 + (x / (π / 2)) ^ 2) * (1 / (π / 2))) := by
    intro x
    have h1 : 1 / (1 + (x / (π / 2)) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg (x / (π / 2))]
    have h2 : 1 / (π / 2) < 1 := by
      rw [div_lt_one hπ]
      linarith [pi_gt_three]
    have h3 : 1 / (1 + (x / (π / 2)) ^ 2) * (1 / (π / 2)) < 1 := by
      calc 1 / (1 + (x / (π / 2)) ^ 2) * (1 / (π / 2)) ≤ 1 * (1 / (π / 2)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ < 1 := by rw [one_mul]; exact h2
    linarith
  have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hd hpos
  have hf0 : f 0 = 0 := by simp [hf]
  have hf1 : f (π / 2) = π / 2 := by
    simp only [hf, div_self hπ.ne', arctan_one]
    ring
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hπ.le hcont.continuousOn
    (show l ∈ Icc (f 0) (f (π / 2)) by rw [hf0, hf1]; exact ⟨hl₀, hl.le⟩)
  exact ⟨x, ⟨hx, hfx⟩, fun y hy => hmono.injective (hy.2.trans hfx.symm)⟩

end Nonholonomic
end RoboLean
