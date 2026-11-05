import Mathlib.Analysis.Complex.ExponentialBounds
import RoboLean.Demo.ArrivalTime

/-!
# Explicit arrival constants for the planar arm demo's parameters

The demo's arm (the demo report's parameters; MLS prints none for this arm): link lengths
`l₁ = 1`, `l₂ = 1/2`, unit masses, homogeneous bars with mass centres at mid-link
(`r₁ = 1/2`, `r₂ = 1/4`) and moments `I_{z1} = 1/12`, `I_{z2} = 1/48` about the joint axes, under
the PD law (4.51) of MLS p. 193 with compensation of `N` and `K_p = K_v = I`. Only the moments about
the joint axes enter the planar mass matrix (4.10), p. 165, so the other principal moments are
arbitrary here (a thin bar has a zero moment about its own axis).

For this arm the bounds that the library's proof of Proposition 4.10 (p. 194) uses are computed:
`(1/48) ‖v‖² ≤ vᵀ M(θ) v` (`demoArm_massMatrix_lower`), `|vᵀ M(θ) w| ≤ (8/3) ‖v‖ ‖w‖`
(`demoArm_massMatrix_upper`) and `|vᵀ C(θ, u) w| ≤ ‖u‖ ‖v‖ ‖w‖` (`demoArm_coriolis_bound`), all in
the sup norm. With them the closed loop at every set point has the exponential bound with the
explicit constants `C = 34` and `α(ρ) = 1 / (24 (256 + (2 + 34ρ)²))` on the initial state errors
smaller than `ρ` (`demoArm_exponentialBoundOn`), so the arrival time of the demo is explicit
(`demo_planarDist_le_at_sample_of_run`). For the demo's tolerance `0.02` and initial state errors
below `ρ = 8` the certified arrival time lies between `1 807 968` s and `19 887 648` s
(`demo_le_arrivalTime`, `demo_arrivalTime_le`, `demo_lt_arrivalTime`), so the demo's period
`0.5` s times its age bound `232`, `116` s, is far below it: these constants do not certify
the demo's timeout; an age bound of `39 775 296` ticks at `0.5` s would
(`demo_planarDist_le_at_bound_of_run`). The constants come from the tube form of the proof of
Proposition 4.10, valid for every manipulator, and are conservative; they are not a statement
about the arm's actual convergence time. The sharper constants of `RoboLean.Demo.ArrivalRate`,
from the same Lyapunov function with estimates specific to this arm, certify the demo's age bound
(`demo_planarDist_le_at_bound_of_run_sharp`).

Statements about the ideal continuous model with exact model cancellation and a fixed target per
command; not the sampled loop, the floating-point simulation or a physical arm.
-/

noncomputable section

namespace RoboLean.Demo

open Matrix RoboLean.Examples RoboLean.Stability

/-- **The certified rate for the demo's arm**, `α(ρ) = 1 / (24 (256 + (2 + 34ρ)²))`, for initial
state errors smaller than `ρ` (MLS Definition 4.3, eq. (4.34), p. 180; the demo report's
parameters). -/
def demoRate (ρ : ℝ) : ℝ :=
  1 / (24 * (256 + (2 + 34 * ρ) ^ 2))

/-- The square of the sup norm on `ℝ²` is at most the sum of the squares of the coordinates. -/
private theorem sq_norm_le_two (v : Fin 2 → ℝ) : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
  have h : ‖v‖ ≤ √(v 0 ^ 2 + v 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr ?_
    rw [Fin.forall_fin_two, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨Real.abs_le_sqrt (by nlinarith [sq_nonneg (v 1)]),
      Real.abs_le_sqrt (by nlinarith [sq_nonneg (v 0)])⟩
  calc ‖v‖ ^ 2 ≤ (√(v 0 ^ 2 + v 1 ^ 2)) ^ 2 := by gcongr
    _ = v 0 ^ 2 + v 1 ^ 2 := Real.sq_sqrt (by positivity)

/-- Each coordinate squared is at most the square of the sup norm on `ℝ²`. -/
private theorem sq_apply_le (v : Fin 2 → ℝ) (i : Fin 2) : v i ^ 2 ≤ ‖v‖ ^ 2 := by
  have h : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **The demo arm's mass matrix is bounded below (MLS eq. (4.10), p. 165, with the demo report's
parameters).** For moments `I_{z1} = 1/12` and `I_{z2} = 1/48` about the joint axes, unit masses,
`r₁ = 1/2`, `r₂ = 1/4`, `l₁ = 1`: `(1/48) ‖v‖² ≤ vᵀ M(θ) v` for every `θ` and `v` (sup norm). -/
theorem demoArm_massMatrix_lower {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48)
    (q v : Fin 2 → ℝ) :
    1 / 48 * ‖v‖ ^ 2 ≤
      v ⬝ᵥ ((planarTwoLinkArm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂).massMatrix q *ᵥ v) := by
  have hn := sq_norm_le_two v
  rw [planarTwoLinkArm_massMatrix, hI₁, hI₂]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  have hc1 := Real.cos_le_one (q 1)
  have hc2 := Real.neg_one_le_cos (q 1)
  have h1 : 0 ≤ 1 + Real.cos (q 1) := by linarith
  have h2 : 0 ≤ 1 - Real.cos (q 1) := by linarith
  nlinarith [mul_nonneg h1 (sq_nonneg (91 * v 0 + 16 * v 1)), mul_nonneg h1 (sq_nonneg (v 1)),
    mul_nonneg h2 (sq_nonneg (43 * v 0 - 8 * v 1)), mul_nonneg h2 (sq_nonneg (v 1))]

/-- **The demo arm's mass matrix is bounded above (MLS eq. (4.10), p. 165, with the demo report's
parameters).** `|vᵀ M(θ) w| ≤ (8/3) ‖v‖ ‖w‖` for every `θ`, `v`, `w` (sup norm). -/
theorem demoArm_massMatrix_upper {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48)
    (q v w : Fin 2 → ℝ) :
    |v ⬝ᵥ ((planarTwoLinkArm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂).massMatrix q *ᵥ w)| ≤
      8 / 3 * ‖v‖ * ‖w‖ := by
  refine (Control.abs_dotProduct_mulVec_le _ v w).trans ?_
  gcongr
  rw [planarTwoLinkArm_massMatrix, hI₁, hI₂]
  simp only [Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  have hc1 := Real.cos_le_one (q 1)
  have hc2 := Real.neg_one_le_cos (q 1)
  have e1 : |1 / 12 + 1 / 48 + 1 * (1 / 2) ^ 2 + 1 * (1 ^ 2 + (1 / 4) ^ 2) +
      2 * (1 * 1 * (1 / 4)) * Real.cos (q 1)| ≤ 23 / 12 := by
    rw [abs_le]
    constructor <;> nlinarith
  have e2 : |1 / 48 + 1 * (1 / 4) ^ 2 + 1 * 1 * (1 / 4) * Real.cos (q 1)| ≤ 1 / 3 := by
    rw [abs_le]
    constructor <;> nlinarith
  have e3 : |(1 : ℝ) / 48 + 1 * (1 / 4) ^ 2| ≤ 1 / 12 := by
    rw [abs_le]
    constructor <;> norm_num
  linarith

/-- **The demo arm's Coriolis matrix is bounded by the joint rate (MLS eq. (4.11), p. 165, with
the demo report's parameters).** `|vᵀ C(θ, u) w| ≤ ‖u‖ ‖v‖ ‖w‖` for every `θ`, `u`, `v`, `w` (sup
norm), for any gravity data and joint forces. -/
theorem demoArm_coriolis_bound (I₁ I₂ : Fin 3 → ℝ) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) (q u v w : Fin 2 → ℝ) :
    |v ⬝ᵥ ((planarTwoLinkModel 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne).C q u *ᵥ w)| ≤
      ‖u‖ * ‖v‖ * ‖w‖ := by
  refine (Control.abs_dotProduct_mulVec_le _ v w).trans ?_
  gcongr
  rw [planarTwoLinkModel_C]
  simp [Fin.sum_univ_two]
  have hu0 : |u 0| ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm u 0
  have hu1 : |u 1| ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm u 1
  have h01 : |u 0 + u 1| ≤ 2 * ‖u‖ := by
    have := abs_add_le (u 0) (u 1)
    linarith
  have hs := Real.abs_sin_le_one (q 1)
  have hs0 : 0 ≤ |Real.sin (q 1)| := abs_nonneg _
  have k1 : |Real.sin (q 1)| * |u 1| ≤ ‖u‖ := by nlinarith [abs_nonneg (u 1)]
  have k2 : |Real.sin (q 1)| * |u 0 + u 1| ≤ 2 * ‖u‖ := by nlinarith [abs_nonneg (u 0 + u 1)]
  have k3 : |Real.sin (q 1)| * |u 0| ≤ ‖u‖ := by nlinarith [abs_nonneg (u 0)]
  nlinarith

/-- **Explicit exponential constants for the demo's closed loop (MLS Proposition 4.10, p. 194, at
a constant set point; Definition 4.3, p. 180; the demo report's parameters).** For every radius
`ρ > 0` and every set point `θ_d`, the demo arm under the PD law with compensation of `N` and
`K_p = K_v = I` has the exponential bound with constants `C = 34` and `α = demoRate ρ` at
`(θ_d, 0)` on the initial state errors smaller than `ρ` (sup norm), for any gravity data, joint
forces and moments about the other axes. -/
theorem demoArm_exponentialBoundOn {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12)
    (hI₂ : I₂ 2 = 1 / 48) (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (θd : Fin 2 → ℝ) :
    ExponentialBoundOn (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne θd) (θd, 0) 34
      (demoRate ρ) ρ := by
  set P := planarTwoLinkModel 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne with hP
  have hMeq : ∀ q, P.M q = (planarTwoLinkArm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂).massMatrix q :=
    fun q => by rw [hP, planarTwoLinkModel_M]
  have hsymm : ∀ k, (P.chain.linkInertia k).IsSymm :=
    planarTwoLinkArm_linkInertia_isSymm 1 1 (1 / 2) (1 / 4) 1 I₁ I₂
  have hM : ∀ q, (P.M q).PosDef := by
    intro q
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hMeq, planarTwoLinkArm_massMatrix]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
    · have hl := demoArm_massMatrix_lower hI₁ hI₂ q x
      rw [← hMeq] at hl
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [star_trivial]
      nlinarith
  have hR : 0 < 34 * ρ := by positivity
  set R := 34 * ρ with hRdef
  set ε := 1 / (256 + (2 + R) ^ 2) with hεdef
  have hε : 0 < ε := by positivity
  have hε256 : ε ≤ 1 / 256 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith [sq_nonneg (2 + R)])
  have hrate : demoRate ρ = ε / 24 := by
    rw [demoRate, hεdef, hRdef]
    field_simp
  have hmin : min (1 / 48 : ℝ) 1 = 1 / 48 := min_eq_left (by norm_num)
  have hεμ : 2 * ε * (8 / 3) ≤ min (1 / 48 : ℝ) 1 := by
    rw [hmin]
    linarith
  have hεc : ε * (2 * 1 * (8 / 3) + (2 + R) ^ 2) ≤ 1 * 1 := by
    rw [hεdef, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  set a₂ := (8 / 3 : ℝ) + 2 + ε * (8 / 3) + 1 with ha₂def
  have ha₂ : a₂ ≤ 6 := by
    rw [ha₂def]
    linarith
  have ha₂0 : 0 < a₂ := by positivity
  have hdemo : (0 : ℝ) < demoRate ρ := by rw [hrate]; positivity
  refine ⟨by norm_num, hdemo, fun t₀ ht₀ x hx hx₀ t ht => ?_⟩
  have hx' : IsSolution (P.field (P.augmentedPDTorque 1 1 (fun _ => θd) (fun _ => 0)
      (fun _ => 0))) t₀ x := by
    rw [ManipulatorModel.augmentedPDTorque_const_eq_pdCompensatedTorque]
    exact hx
  have hCu : ∀ t : ℝ, 0 ≤ t → ∀ z : (Fin 2 → ℝ) × (Fin 2 → ℝ), ‖z‖ ≤ R →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (P.C (θd + z.1) (0 + z.2) *ᵥ v₂)| ≤ R * ‖v₁‖ * ‖v₂‖ := by
    intro t _ z hz v₁ v₂
    have h2 : ‖(0 : Fin 2 → ℝ) + z.2‖ ≤ R := by
      simpa using (norm_snd_le z).trans hz
    calc |v₁ ⬝ᵥ (P.C (θd + z.1) (0 + z.2) *ᵥ v₂)|
        ≤ ‖(0 : Fin 2 → ℝ) + z.2‖ * ‖v₁‖ * ‖v₂‖ := demoArm_coriolis_bound I₁ I₂ g up Ne _ _ _ _
      _ ≤ R * ‖v₁‖ * ‖v₂‖ := by gcongr
  have hkp : ∀ v : Fin 2 → ℝ, 1 * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v) := by
    intro v
    rw [Matrix.one_mulVec, one_mul]
    simpa [dotProduct, Fin.sum_univ_two, sq] using sq_norm_le_two v
  have hκpb : ∀ v : Fin 2 → ℝ, v ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v) ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    rw [Matrix.one_mulVec]
    have h0 := sq_apply_le v 0
    have h1 := sq_apply_le v 1
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith
  have hκv : ∀ v₁ v₂ : Fin 2 → ℝ,
      |v₁ ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v₂)| ≤ 2 * ‖v₁‖ * ‖v₂‖ := by
    intro v₁ v₂
    refine (Control.abs_dotProduct_mulVec_le _ v₁ v₂).trans (le_of_eq ?_)
    simp [Fin.sum_univ_two, Matrix.one_apply]
    norm_num
  have hx₀' : ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin 2 → ℝ)) t₀)‖ <
      min R (R * Real.sqrt (min (1 / 48 : ℝ) 1 / 4 / (8 / 3 + 2 + ε * (8 / 3) + 1))) := by
    have hs : 1 / 34 ≤ Real.sqrt (min (1 / 48 : ℝ) 1 / 4 / a₂) := by
      rw [hmin, Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ ha₂0]
      nlinarith
    refine lt_min (lt_of_lt_of_le hx₀ (by rw [hRdef]; linarith)) ?_
    calc ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin 2 → ℝ)) t₀)‖ < ρ := hx₀
      _ = R * (1 / 34) := by rw [hRdef]; ring_nf
      _ ≤ R * Real.sqrt (min (1 / 48 : ℝ) 1 / 4 / a₂) := by gcongr
  have key := P.norm_le_augmentedPD_of_bounds hsymm hM Matrix.isSymm_one
    (fun t => hasDerivAt_const t θd) (fun t => hasDerivAt_const t (0 : Fin 2 → ℝ)) hR hε
    (by norm_num : (0 : ℝ) < 1 / 48) (by norm_num : (0 : ℝ) ≤ 8 / 3) one_pos
    (by norm_num : (0 : ℝ) ≤ 2) one_pos
    (fun t _ z _ v => by rw [hMeq]; exact demoArm_massMatrix_lower hI₁ hI₂ _ v)
    (fun t _ z _ v₁ v₂ => by rw [hMeq]; exact demoArm_massMatrix_upper hI₁ hI₂ _ v₁ v₂)
    hCu hkp hκpb hkp hκv hεμ hεc ht₀ hx' hx₀' ht
  refine key.trans ?_
  have hC : Real.sqrt (a₂ / (min (1 / 48 : ℝ) 1 / 4)) ≤ 34 := by
    rw [Real.sqrt_le_iff, hmin]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hα : demoRate ρ * (t - t₀) ≤ min (1 / 2) (ε * 1 / 2) / (2 * a₂) * (t - t₀) := by
    have hm : min (1 / 2 : ℝ) (ε * 1 / 2) = ε / 2 := by
      rw [min_eq_right (by linarith)]
      rw [mul_one]
    rw [hm, hrate]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [show ε / 2 / (2 * a₂) = ε / (4 * a₂) by ring_nf]
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  have hexp : Real.exp (-(min (1 / 2) (ε * 1 / 2) / (2 * a₂)) * (t - t₀)) ≤
      Real.exp (-demoRate ρ * (t - t₀)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hn : 0 ≤ ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin 2 → ℝ)) t₀)‖ := norm_nonneg _
  calc Real.sqrt (a₂ / (min (1 / 48 : ℝ) 1 / 4)) *
        Real.exp (-(min (1 / 2) (ε * 1 / 2) / (2 * a₂)) * (t - t₀)) *
        ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin 2 → ℝ)) t₀)‖
      ≤ 34 * Real.exp (-demoRate ρ * (t - t₀)) *
        ‖x t₀ - ((fun _ => θd) t₀, (fun _ => (0 : Fin 2 → ℝ)) t₀)‖ := by gcongr
    _ = 34 * Real.exp (-demoRate ρ * (t - t₀)) * ‖x t₀ - (θd, 0)‖ := rfl

/-- **The demo's sampled arrival test with explicit constants (MLS eq. (3.16), p. 98, Proposition
4.10, p. 194, and Definition 4.3, p. 180; the demo report's parameters and conventions).** For the
demo's link lengths `a = 1`, `b = 1/2`, every run of the executable supervisor from `State.init`,
every commanded target, every solution of the demo's closed loop at its set point from `t₀ ≥ 0`
starting within `ρ > 0`, every tolerance `ε > 0` and every sample `k` of period `h` with
`k h ≥ arrivalTime 34 (demoRate ρ) ρ (ε / 2)`, the end effector is within `ε` of the target at
`t₀ + k h`. -/
theorem demo_planarDist_le_at_sample_of_run {p : Params} (hpa : p.a = 1) (hpb : p.b = 1 / 2)
    {acts : List Action} {s : State} (hrun : run p State.init acts = some s) {tgt : Target}
    (htgt : tgt ∈ s.commanded) {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48)
    (g : ℝ) (up : Vec3) (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hx : IsSolution (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne (setPoint p tgt)) t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < ρ) {ε : ℝ} (hε : 0 < ε) {h : ℝ} {k : ℕ}
    (hk : arrivalTime 34 (demoRate ρ) ρ (ε / 2) ≤ k * h) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + k * h)).1) ![(tgt.1 : ℝ), tgt.2] ≤ ε := by
  have ha : 0 < p.a := by rw [hpa]; norm_num
  have hb : 0 < p.b := by rw [hpb]; norm_num
  have hab : p.a ≠ p.b := by rw [hpa, hpb]; norm_num
  have hL : ((p.a : ℝ) + 2 * p.b) = 2 := by rw [hpa, hpb]; norm_num
  refine planarDist_le_at_sample_of_run ha hb hab hrun htgt
    (demoArm_exponentialBoundOn hI₁ hI₂ g up Ne hρ (setPoint p tgt)) ht₀ hx hx₀ hε ?_
  rw [hL]
  exact hk

/-- **The certified arrival time for the demo's tolerance is at most `19 887 648` s (the demo
report's parameters; MLS Definition 4.3, p. 180).** For initial state errors below `ρ = 8` and the
tolerance `0.02` (so `ε / (a + 2b) = 1/100`), `arrivalTime 34 (demoRate 8) 8 (1/100) ≤ 19 887 648`,
from `log 27 200 ≤ 11`. -/
theorem demo_arrivalTime_le : arrivalTime 34 (demoRate 8) 8 (1 / 100) ≤ 19887648 := by
  have hlog : Real.log (34 * 8 / (1 / 100)) ≤ 11 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num,
      ← Real.exp_one_pow]
    calc (34 : ℝ) * 8 / (1 / 100) ≤ 2.7182818283 ^ 11 := by norm_num
      _ ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 11
  refine max_le (by norm_num) ?_
  rw [demoRate, div_le_iff₀ (by norm_num)]
  norm_num
  linarith

/-- **The certified arrival time for the demo's tolerance is at least `1 807 968` s (the demo
report's parameters; MLS Definition 4.3, p. 180).** For initial state errors below `ρ = 8` and the
tolerance `0.02`, `1 807 968 ≤ arrivalTime 34 (demoRate 8) 8 (1/100)`, from `log 27 200 ≥ 1`. -/
theorem demo_le_arrivalTime : 1807968 ≤ arrivalTime 34 (demoRate 8) 8 (1 / 100) := by
  have hlog : 1 ≤ Real.log (34 * 8 / (1 / 100)) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      _ ≤ 34 * 8 / (1 / 100) := by norm_num
  refine le_max_of_le_right ?_
  rw [demoRate, le_div_iff₀ (by norm_num)]
  norm_num
  linarith

/-- **The demo's own timeout is below the arrival time of these constants (the demo report's
parameters; MLS Definition 4.3, p. 180).** The demo's period `0.5` s times its age bound `232` is
`116` s, and `116 < arrivalTime 34 (demoRate 8) 8 (1/100)` (`demo_le_arrivalTime`): the constants
of this module do not certify the demo's configuration; those of `RoboLean.Demo.ArrivalRate` do. -/
theorem demo_lt_arrivalTime : (232 : ℝ) * (1 / 2) < arrivalTime 34 (demoRate 8) 8 (1 / 100) :=
  lt_of_lt_of_le (by norm_num) demo_le_arrivalTime

/-- **Design statement with explicit numbers (MLS eq. (3.16), p. 98, Proposition 4.10, p. 194;
the demo report's parameters and conventions).** For the demo's link lengths, period `h = 1/2`,
tolerance `1/50`, initial state errors below `8` and an age bound of at least `39 775 296`, the end
effector is within `1/50` of every commanded target at the sample `t₀ + bound · h` at which the
age reaches the bound, for every run, commanded target and solution of the demo's closed loop at its
set point from `t₀ ≥ 0`. -/
theorem demo_planarDist_le_at_bound_of_run {p : Params} (hpa : p.a = 1) (hpb : p.b = 1 / 2)
    (hN : 39775296 ≤ p.bound) {acts : List Action} {s : State}
    (hrun : run p State.init acts = some s) {tgt : Target} (htgt : tgt ∈ s.commanded)
    {I₁ I₂ : Fin 3 → ℝ} (hI₁ : I₁ 2 = 1 / 12) (hI₂ : I₂ 2 = 1 / 48) (g : ℝ) (up : Vec3)
    (Ne : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Fin 2 → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)}
    (hx : IsSolution (armClosedLoop 1 1 (1 / 2) (1 / 4) 1 I₁ I₂ g up Ne (setPoint p tgt)) t₀ x)
    (hx₀ : ‖x t₀ - (setPoint p tgt, 0)‖ < 8) :
    planarDist (planarArmXY (p.a : ℝ) (p.b : ℝ) (x (t₀ + p.bound * (1 / 2))).1)
      ![(tgt.1 : ℝ), tgt.2] ≤ 1 / 50 := by
  refine demo_planarDist_le_at_sample_of_run hpa hpb hrun htgt hI₁ hI₂ g up Ne (by norm_num) ht₀
    hx hx₀ (by norm_num) ?_
  have hN' : (39775296 : ℝ) ≤ p.bound := by exact_mod_cast hN
  calc arrivalTime 34 (demoRate 8) 8 (1 / 50 / 2) = arrivalTime 34 (demoRate 8) 8 (1 / 100) := by
        norm_num
    _ ≤ 19887648 := demo_arrivalTime_le
    _ ≤ p.bound * (1 / 2) := by linarith

end RoboLean.Demo
