import RoboLean.Control.ManipulatorSystem
import RoboLean.Control.QuadraticBounds

/-!
# The error dynamics of computed-torque control and its skewed energy

MLS Chapter 4, Proposition 4.8 (the computed torque law, printed p. 192) and Example 4.5
(printed pp. 186–187).

Under the computed-torque law the tracking error `e = θ − θ_d` satisfies the linear,
time-invariant second-order system `ë + K_v ė + K_p e = 0` (MLS eq. (4.50), p. 191). Here it is
the first-order system on the state `(e, ė) ∈ ℝⁿ × ℝⁿ`

  `d/dt (e, ė) = (ė, −K_v ė − K_p e)` (`errorField`),

with time as first argument of the field, as in `RoboLean.Stability`. The Lyapunov function is the
skewed energy `V(e, ė) = ½ ėᵀė + ½ eᵀK_p e + ε eᵀė`: MLS Example 4.5 (pp. 186–187) skews the
energy `½ M q̇² + ½ K q²` of a scalar spring–mass system to `½ q̇ M q̇ + ½ q K q + ε q̇ M q`, and
p. 194 uses `½ ėᵀM(θ)ė + ½ eᵀK_p e + ε eᵀM(θ)ė` for the PD law; here it is the matrix form with
unit inertia `M = I`, the inertia of the linear error system (4.50). For symmetric positive
definite `K_p, K_v` and small `ε > 0` it satisfies the quadratic bounds of MLS Theorem 4.5
(p. 183), which gives global exponential stability of the origin (Definition 4.3), the
stability part of Proposition 4.8. MLS proves Proposition 4.8 by the eigenvalue argument for
linear systems (p. 192); the route here is the Lyapunov one, through
`Stability.globallyExponentiallyStable_of_quadratic_lyapunov`.

Conventions: the state is `(e, ė)` with `e` first; the norm on the state space is Mathlib's norm
on `(Fin n → ℝ) × (Fin n → ℝ)`, the maximum of the two sup norms (the constants depend on that
choice, the stability statement does not); positive definiteness is Mathlib's `Matrix.PosDef`,
which includes symmetry.
-/

noncomputable section
open Matrix Set Filter Topology

namespace RoboLean
namespace Control

variable {n : ℕ}

/-- **The error dynamics (4.50) (MLS p. 191) in the proof of Proposition 4.8, p. 192,**
`ë + K_v ė + K_p e = 0`, as the first-order linear system
`d/dt (e, ė) = [[0, I], [−K_p, −K_v]] (e, ė)` on the state `(e, ė)` (`e` first). It is
time-invariant: the time argument (first, as in `RoboLean.Stability`) is ignored. -/
def errorField (Kp Kv : Matrix (Fin n) (Fin n) ℝ) :
    ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun _ z => (z.2, -(Kv *ᵥ z.2) - Kp *ᵥ z.1)

/-- **The skewed energy of MLS Example 4.5, pp. 186–187** (in the matrix form of p. 194, with unit
inertia `M = I`): `V(e, ė) = ½ ėᵀė + ½ eᵀ K_p e + ε eᵀ ė` on the state `z = (e, ė)` (`e` first),
time-invariant. -/
def skewedEnergy (Kp : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / 2 : ℝ) * (z.2 ⬝ᵥ z.2) + (1 / 2 : ℝ) * (z.1 ⬝ᵥ (Kp *ᵥ z.1)) + ε * (z.1 ⬝ᵥ z.2)

/-- **The derivative of the skewed energy along `errorField`** (MLS Example 4.5, pp. 186–187, for
the error system of p. 192), by the product rule and without using symmetry of `K_p`: with
`z = (e, w)` and `w' = −K_v w − K_p e`,
`V̇ = w ⬝ w' + ½ (w ⬝ K_p e + e ⬝ K_p w) + ε (w ⬝ w + e ⬝ w')`. -/
def skewedEnergyRate (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  z.2 ⬝ᵥ (-(Kv *ᵥ z.2) - Kp *ᵥ z.1) + (1 / 2 : ℝ) * (z.2 ⬝ᵥ (Kp *ᵥ z.1) + z.1 ⬝ᵥ (Kp *ᵥ z.2)) +
    ε * (z.2 ⬝ᵥ z.2 + z.1 ⬝ᵥ (-(Kv *ᵥ z.2) - Kp *ᵥ z.1))

/-- **`skewedEnergyRate` is the derivative of `skewedEnergy` along every solution of
`errorField`** (MLS p. 182, the derivative along trajectories, for the energy of Example 4.5,
pp. 186–187, and the error system of p. 192), on the whole state space. Time-invariant `V` and
`V̇`; state `(e, ė)`. -/
theorem hasDerivAlongSolutions_skewedEnergy (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Stability.HasDerivAlongSolutions (errorField Kp Kv) (fun _ => skewedEnergy Kp ε)
      (fun _ => skewedEnergyRate Kp Kv ε) univ := by
  intro t₀ _ z hz t ht _
  have hd := hz.2 t ht
  have h1 : HasDerivAt (fun s => (z s).1) (z t).2 t :=
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt t hd
  have h2 : HasDerivAt (fun s => (z s).2) (-(Kv *ᵥ (z t).2) - Kp *ᵥ (z t).1) t :=
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt.comp_hasDerivAt t hd
  have hww := hasDerivAt_dotProduct h2 h2
  have hee := hasDerivAt_dotProduct h1 (hasDerivAt_mulVec_const Kp h1)
  have hew := hasDerivAt_dotProduct h1 h2
  have h := ((hww.const_mul (1 / 2 : ℝ)).add (hee.const_mul (1 / 2 : ℝ))).add (hew.const_mul ε)
  convert h using 1
  · funext s
    simp only [skewedEnergy, Pi.add_apply]
  · simp only [skewedEnergyRate]
    rw [dotProduct_comm (-(Kv *ᵥ (z t).2) - Kp *ᵥ (z t).1) (z t).2]
    ring

/-- Over `ℝ` the quadratic form of a symmetric matrix is symmetric in its two arguments. -/
private lemma dotProduct_mulVec_comm_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]

private lemma dotProduct_self_nonneg' (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma dotProduct_self_pos' {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dotProduct_self_nonneg' v) (Ne.symm (mt dotProduct_self_eq_zero.mp hv))

private lemma posDef_quad_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  by_cases hv : v = 0
  · simp [hv]
  · simpa using (hA.dotProduct_mulVec_pos hv).le

/-- The scalar core of the rate bound: `X = w⬝w`, `U = w⬝K_v w`, `R = e⬝K_v w`, `Y = e⬝K_p e`,
`Z = e⬝K_v e`. -/
private lemma rate_scalar {a b ε c X U R Y Z : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (hεb : ε ≤ b) (hεa : ε ≤ a / 4) (hca : c ≤ a / 4) (hcε : c ≤ ε / 2) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hU : a * X ≤ U) (hZ : b * Z ≤ Y) (hpsd : 0 ≤ b ^ 2 * Z + 2 * b * R + U) :
    c * (X + Y) ≤ U - ε * X + ε * R + ε * Y := by
  have h1 : 0 ≤ ε * (b ^ 2 * Z + 2 * b * R + U) := mul_nonneg hε.le hpsd
  have h2 : ε * b * (b * Z) ≤ ε * b * Y := mul_le_mul_of_nonneg_left hZ (by positivity)
  have h3 : (2 * b - ε) * (a * X) ≤ (2 * b - ε) * U :=
    mul_le_mul_of_nonneg_left hU (by linarith)
  have h4 : 0 ≤ a * X * (b - ε) := mul_nonneg (mul_nonneg ha.le hX) (by linarith)
  have h5 : 0 ≤ b * X * (a / 4 - ε) := mul_nonneg (mul_nonneg hb.le hX) (by linarith)
  have key : 0 ≤ 2 * b * (U - ε * X + ε * R + ε * Y - (a / 4 * X + ε / 2 * Y)) := by
    nlinarith
  have h6 : a / 4 * X + ε / 2 * Y ≤ U - ε * X + ε * R + ε * Y := by
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * b)).mp key
    linarith
  have h7 : c * X ≤ a / 4 * X := mul_le_mul_of_nonneg_right hca hX
  have h8 : c * Y ≤ ε / 2 * Y := mul_le_mul_of_nonneg_right hcε hY
  linarith

/-- The scalar core of the energy lower bound: `X = w⬝w`, `Y = e⬝K_p e`, `S = e⬝e`,
`P = e⬝w`. -/
private lemma energy_scalar {c ε S X Y P : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (hεc : ε ≤ c / 2)
    (hS : 0 ≤ S) (hX : 0 ≤ X) (hSY : c * S ≤ Y) (hP : 0 ≤ S + 2 * P + X) :
    (1 / 4 : ℝ) * (X + Y) ≤ (1 / 2 : ℝ) * X + (1 / 2 : ℝ) * Y + ε * P := by
  have h1 : 0 ≤ ε * (S + 2 * P + X) := mul_nonneg hε hP
  have h2 : ε * S ≤ c / 2 * S := mul_le_mul_of_nonneg_right hεc hS
  have h3 : ε * X ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hε1 hX
  nlinarith

/-- **The skewed-energy bounds of MLS Example 4.5, pp. 186–187, for the error system of p. 192.**
For symmetric positive definite `K_p, K_v` (Mathlib's `Matrix.PosDef`) there is `ε > 0` such that,
on the state `z = (e, ė)`, `V ≥ ¼(ėᵀė + eᵀK_p e)` and `−V̇ ≥ c (ėᵀė + eᵀK_p e)` for some
`c > 0`. -/
theorem exists_skewedEnergy_bounds {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef)
    (hKv : Kv.PosDef) :
    ∃ ε > 0, ∃ c > 0, ∀ z : (Fin n → ℝ) × (Fin n → ℝ),
      (1 / 4 : ℝ) * (z.2 ⬝ᵥ z.2 + z.1 ⬝ᵥ (Kp *ᵥ z.1)) ≤ skewedEnergy Kp ε z ∧
      c * (z.2 ⬝ᵥ z.2 + z.1 ⬝ᵥ (Kp *ᵥ z.1)) ≤ -skewedEnergyRate Kp Kv ε z := by
  obtain ⟨a, ha, hav⟩ := QuadraticBounds.exists_pos_mul_dotProduct_mulVec_le hKv 1
  obtain ⟨b, hb, hbv⟩ := QuadraticBounds.exists_pos_mul_dotProduct_mulVec_le hKp Kv
  obtain ⟨c, hc, hcv⟩ := QuadraticBounds.exists_pos_mul_dotProduct_mulVec_le hKp 1
  set ε := min (min b (a / 4)) (min (1 / 2) (c / 2)) with hεdef
  have hε : 0 < ε := lt_min (lt_min hb (by positivity)) (lt_min (by norm_num) (by positivity))
  have hεb : ε ≤ b := (min_le_left _ _).trans (min_le_left _ _)
  have hεa : ε ≤ a / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεc : ε ≤ c / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hp : 0 < min (a / 4) (ε / 2) := lt_min (by positivity) (by positivity)
  refine ⟨ε, hε, min (a / 4) (ε / 2), hp, fun z => ?_⟩
  obtain ⟨e, w⟩ := z
  have sKp := hKp.isHermitian.isSymm
  have sKv := hKv.isHermitian.isSymm
  have hX := dotProduct_self_nonneg' w
  have hS := dotProduct_self_nonneg' e
  have hU : a * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Kv *ᵥ w) := by simpa using hav w
  have hZ : b * (e ⬝ᵥ (Kv *ᵥ e)) ≤ e ⬝ᵥ (Kp *ᵥ e) := hbv e
  have hSY : c * (e ⬝ᵥ e) ≤ e ⬝ᵥ (Kp *ᵥ e) := by simpa using hcv e
  have hY : 0 ≤ e ⬝ᵥ (Kp *ᵥ e) := posDef_quad_nonneg hKp e
  have hpsd : 0 ≤ b ^ 2 * (e ⬝ᵥ (Kv *ᵥ e)) + 2 * b * (e ⬝ᵥ (Kv *ᵥ w)) + w ⬝ᵥ (Kv *ᵥ w) := by
    have h := posDef_quad_nonneg hKv (b • e + w)
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
    rw [dotProduct_mulVec_comm_of_isSymm sKv w e] at h
    linarith
  have hP : 0 ≤ e ⬝ᵥ e + 2 * (e ⬝ᵥ w) + w ⬝ᵥ w := by
    have h := dotProduct_self_nonneg' (e + w)
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm w e] at h
    linarith
  have hrate : -skewedEnergyRate Kp Kv ε (e, w) =
      w ⬝ᵥ (Kv *ᵥ w) - ε * (w ⬝ᵥ w) + ε * (e ⬝ᵥ (Kv *ᵥ w)) + ε * (e ⬝ᵥ (Kp *ᵥ e)) := by
    simp only [skewedEnergyRate, dotProduct_sub, dotProduct_neg]
    rw [dotProduct_mulVec_comm_of_isSymm sKp w e]
    ring
  refine ⟨?_, ?_⟩
  · exact energy_scalar hε.le hε1 hεc hS hX hSY hP
  · rw [hrate]
    exact rate_scalar ha hb hε hεb hεa (min_le_left _ _) (min_le_right _ _) hX hY hU hZ hpsd

/-- The quadratic form `ėᵀė + eᵀK_p e` on the state `(e, ė)`. -/
private def gainForm (Kp : Matrix (Fin n) (Fin n) ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  z.2 ⬝ᵥ z.2 + z.1 ⬝ᵥ (Kp *ᵥ z.1)

private lemma continuous_gainForm (Kp : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (gainForm Kp) :=
  (continuous_snd.dotProduct continuous_snd).add
    (continuous_fst.dotProduct (continuous_const.matrix_mulVec continuous_fst))

private lemma continuous_skewedEnergy (Kp : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Continuous (skewedEnergy Kp ε) :=
  ((continuous_const.mul (continuous_snd.dotProduct continuous_snd)).add
    (continuous_const.mul
      (continuous_fst.dotProduct (continuous_const.matrix_mulVec continuous_fst)))).add
    (continuous_const.mul (continuous_fst.dotProduct continuous_snd))

private lemma gainForm_smul (Kp : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : gainForm Kp (r • z) = r ^ 2 * gainForm Kp z := by
  simp only [gainForm, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

private lemma skewedEnergy_smul (Kp : Matrix (Fin n) (Fin n) ℝ) (ε r : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : skewedEnergy Kp ε (r • z) = r ^ 2 * skewedEnergy Kp ε z := by
  simp only [skewedEnergy, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

private lemma gainForm_pos {Kp : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ≠ 0) : 0 < gainForm Kp z := by
  obtain ⟨e, w⟩ := z
  simp only [gainForm]
  by_cases hw : w = 0
  · have he : e ≠ 0 := by
      rintro rfl
      exact hz (by simp [hw])
    have := hKp.dotProduct_mulVec_pos he
    simp only [star_trivial] at this
    linarith [dotProduct_self_nonneg' w]
  · linarith [dotProduct_self_pos' hw, posDef_quad_nonneg hKp e]

/-- **MLS Proposition 4.8, p. 192, stability part:** for symmetric positive definite gains
`K_p, K_v` (Mathlib's `Matrix.PosDef`) the origin of the error system (4.50), on the state
`(e, ė)`, is globally exponentially stable (Definition 4.3, global form, p. 181), in the norm of
`(Fin n → ℝ) × (Fin n → ℝ)` (the maximum of the two sup norms). The proof uses the skewed energy
of Example 4.5 (pp. 186–187) and Theorem 4.5 (p. 183) rather than MLS's eigenvalue argument. -/
theorem globallyExponentiallyStable_errorField {Kp Kv : Matrix (Fin n) (Fin n) ℝ}
    (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    Stability.GloballyExponentiallyStable (errorField Kp Kv) 0 := by
  obtain ⟨ε, hε, c, hc, hb⟩ := exists_skewedEnergy_bounds hKp hKv
  obtain ⟨w₀, hw₀, hW⟩ := QuadraticBounds.exists_pos_mul_sq_norm_le_of_continuous
    (continuous_gainForm Kp) (gainForm_smul Kp) fun z hz => gainForm_pos hKp hz
  obtain ⟨a₂, ha₂, hup⟩ := QuadraticBounds.exists_le_mul_sq_norm_of_continuous
    (continuous_skewedEnergy Kp ε) (skewedEnergy_smul Kp ε)
  refine Stability.globallyExponentiallyStable_of_quadratic_lyapunov (a₁ := w₀ / 4) (a₂ := a₂)
    (a₃ := c * w₀) (V := fun _ => skewedEnergy Kp ε) (Vdot := fun _ => skewedEnergyRate Kp Kv ε)
    (by positivity) ha₂ (by positivity)
    ((continuous_skewedEnergy Kp ε).comp continuous_snd).continuousOn
    (fun _ _ z => ?_) (fun _ _ z => hup z) (hasDerivAlongSolutions_skewedEnergy Kp Kv ε)
    (fun _ _ z => ?_)
  · have h1 := hW z
    have h2 := (hb z).1
    simp only [gainForm] at h1
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (hW z) hc.le
    have h2 := (hb z).2
    simp only [gainForm] at h1
    linarith

end Control
end RoboLean
