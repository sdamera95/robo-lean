import RoboLean.Control.RobotPDControl
import RoboLean.Control.WorkspacePDControl

/-!
# Augmented PD control for every robot (MLS Proposition 4.10, pp. 194–195, §6.5, Exercise 9)

**What MLS states.** Proposition 4.10 (p. 194): "The control law (4.53) applied to the system (4.47)
results in exponential trajectory tracking if `K_v, K_p > 0`", with the augmented PD law (4.53)
`τ = M(θ) θ̈_d + C(θ, θ̇) θ̇_d + N(θ, θ̇) − K_v ė − K_p e`, the closed loop (4.54)
`M(θ) ë + C(θ, θ̇) ė + K_v ė + K_p e = 0` and the skewed energy
`V = ½ ėᵀ M ė + ½ eᵀ K_p e + ε eᵀ M ė` (pp. 194–195). On p. 301: "since the only essential
properties required by the proofs of convergence are that `M(q)` be positive definite and `Ṁ − 2C`
skew-symmetric, all of the previous proofs apply directly", for every robot
`M(q) q̈ + C(q, q̇) q̇ + N(q, q̇) = F` (p. 303). Exercise 9 (p. 209): "Show that the workspace
version of the PD control law results in exponential trajectory tracking."

**Formalized**, for a robot `Control.RobotSystem p` on the state `(x, ẋ)`:

* the law (4.53) (`augmentedPDTorque`) and the closed loop (4.54) at each instant
  (`equations_augmentedPDTorque_iff`, no hypothesis);
* `Ṁ = C + Cᵀ` along motions from the skew property and the symmetry of `M`
  (`Control.eq_add_transpose_of_skew`, `deriv_eq_add_transpose`), so that the derivative of the
  skewed energy along the closed loop, `V̇ = −ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε(−eᵀ K_v ė + ėᵀ C e)`
  (`augmentedEnergyRate`), contains no `Ṁ` (`hasDerivAt_augmentedEnergy`,
  `hasDerivAlongSolutions_augmentedEnergy`); MLS's last line `ε eᵀ(−K_v + ½Ṁ)ė` differs from it by
  `ε eᵀ(½Ṁ − C)ė`, the form of a skew-symmetric matrix;
* the bounds of the proof with an explicit smallness condition on `ε` on a tube around the desired
  trajectory (`augmentedEnergy_bounds`, `augmentedEnergyRate_le`), exponential decay on the tube by
  Theorem 4.5, local form (`norm_le_augmentedPD_of_bounds`), and **semiglobal exponential tracking**
  (`augmentedPD_tracking`) and exponential stability of the tracking error
  (`exponentiallyStable_augmentedPD`), as the library states Proposition 4.10 for the manipulator;
* **global** exponential tracking when the Coriolis matrix is bounded uniformly in the velocity
  (`augmentedPD_tracking_of_bounded_C`; for instance `C = 0`);
* the manipulator's statement re-derived from the robot one
  (`ManipulatorModel.augmentedPD_tracking_of_robot`);
* Exercise 9: the augmented PD law of the workspace robot applied through `τ = Jᵀ F`
  (`ManipulatorModel.workspaceAugmentedPDTorque`) gives semiglobal exponential tracking of the
  workspace trajectory (`ManipulatorModel.workspaceAugmentedPD_tracking`).

**Hypotheses MLS does not state**, as for the manipulator: `M(x)` positive definite for every `x`
(Mathlib's `PosDef`, symmetric), `M` continuous and differentiable along motions
(`Control.DifferentiableAlongMotions`; a robot carries no regularity), the skew property
`HasSkewProperty`; `M` uniformly positive definite and bounded; the Coriolis matrix bounded by the
velocity, `|vᵀ C(x, u) w| ≤ δ ‖u‖ ‖v‖ ‖w‖`; the desired velocity bounded for `t ≥ 0`. The rate
shrinks as the region of initial errors grows when `δ > 0` (no single `ε` serves every initial error
for the planar two-link arm; see `Examples.planarTwoLinkModel_exists_augmentedEnergyRate_pos`). For
the workspace law: `f` of class `C²` with a differentiable inverse `g` (MLS's "smooth and
invertible", p. 196) and the same bounds for the workspace robot. Exact model cancellation is
assumed, as in MLS. State `(x, ẋ) ∈ ℝᵖ × ℝᵖ`, sup norms; gains `Matrix.PosDef`.
-/

noncomputable section

open Matrix Filter Topology Set
open RoboLean.MapJacobian

namespace RoboLean
namespace Control

/-- **`Ṁ = C + Cᵀ` from the skew property (MLS Lemma 4.2(2), p. 171; p. 300):** if `Ṁ` is symmetric
and `Ṁ − 2C` is skew-symmetric, then `Ṁ = C + Cᵀ`. -/
theorem eq_add_transpose_of_skew {k : ℕ} {Md C : Matrix (Fin k) (Fin k) ℝ} (hMd : Mdᵀ = Md)
    (hskew : (Md - (2 : ℝ) • C)ᵀ = -(Md - (2 : ℝ) • C)) : Md = C + Cᵀ := by
  ext i j
  have h1 := congrFun (congrFun hskew i) j
  have h2 := congrFun (congrFun hMd i) j
  simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul] at h1 h2
  simp only [Matrix.add_apply, Matrix.transpose_apply]
  linarith

namespace RobotSystem

variable {p : ℕ} (R : RobotSystem p)

/-- **The rate of a symmetric inertia field along a motion is symmetric, and equals `C + Cᵀ` under
the skew property (MLS p. 300; Lemma 4.2(2), p. 171).** With `M(x)` symmetric for every `x` and the
skew property, every actual entrywise derivative `Ṁ` of `s ↦ M(x(s))` at `t` along a motion with
velocity `x'` is `C(x(t), x') + C(x(t), x')ᵀ`. -/
theorem deriv_eq_add_transpose (hM : ∀ q, (R.M q).IsSymm) (hskew : R.HasSkewProperty)
    {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ} {Md : Matrix (Fin p) (Fin p) ℝ}
    (hx : HasDerivAt x x' t) (hMd : ∀ i j, HasDerivAt (fun s => R.M (x s) i j) (Md i j) t) :
    Md = R.C (x t) x' + (R.C (x t) x')ᵀ := by
  have hT : Mdᵀ = Md := by
    ext i j
    rw [Matrix.transpose_apply]
    refine (hMd j i).unique ?_
    convert hMd i j using 1
    funext s
    exact (hM (x s)).apply i j
  exact eq_add_transpose_of_skew hT (hskew hx hMd)

/-- **MLS eq. (4.53), p. 194, for a robot (MLS p. 301): the augmented PD control law**
`F = M(x) ẍ_d + C(x, ẋ) ẋ_d + N(x, ẋ) − K_v ė − K_p e`, `e = x − x_d`, `ė = ẋ − ẋ_d`, for a desired
trajectory `x_d` with velocity `x_d'` and acceleration `x_d''`, as a feedback law `u(t, x, ẋ)`. -/
def augmentedPDTorque (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd xd' xd'' : ℝ → Fin p → ℝ) :
    ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ :=
  fun t q v => R.M q *ᵥ xd'' t + R.C q v *ᵥ xd' t + R.N q v - Kv *ᵥ (v - xd' t) -
    Kp *ᵥ (q - xd t)

/-- **MLS eq. (4.54), p. 194, for a robot: the closed loop of the augmented PD law.** At every
instant, `M(x) a + C(x, v) v + N(x, v)` equals the law (4.53) exactly when
`M(x)(a − ẍ_d) + C(x, v)(v − ẋ_d) + K_v (v − ẋ_d) + K_p (x − x_d) = 0`. No hypothesis is needed. -/
theorem equations_augmentedPDTorque_iff (Kp Kv : Matrix (Fin p) (Fin p) ℝ)
    (xd xd' xd'' : ℝ → Fin p → ℝ) (t : ℝ) (q v a : Fin p → ℝ) :
    R.M q *ᵥ a + R.C q v *ᵥ v + R.N q v = R.augmentedPDTorque Kp Kv xd xd' xd'' t q v ↔
      R.M q *ᵥ (a - xd'' t) + R.C q v *ᵥ (v - xd' t) + Kv *ᵥ (v - xd' t) +
        Kp *ᵥ (q - xd t) = 0 := by
  rw [← sub_eq_zero]
  have e : R.M q *ᵥ a + R.C q v *ᵥ v + R.N q v - R.augmentedPDTorque Kp Kv xd xd' xd'' t q v =
      R.M q *ᵥ (a - xd'' t) + R.C q v *ᵥ (v - xd' t) + Kv *ᵥ (v - xd' t) + Kp *ᵥ (q - xd t) := by
    simp only [augmentedPDTorque, Matrix.mulVec_sub]
    abel
  rw [e]

/-- **The Lyapunov function of the proof of MLS Proposition 4.10, p. 194, for a robot:**
`V = ½ ėᵀ M(x) ė + ½ eᵀ K_p e + ε eᵀ M(x) ė` at the configuration `q = x`, with position error `e`
and velocity error `w = ė`. -/
def augmentedEnergy (Kp : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (q e w : Fin p → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (w ⬝ᵥ (R.M q *ᵥ w)) + (1 / 2 : ℝ) * (e ⬝ᵥ (Kp *ᵥ e)) + ε * (e ⬝ᵥ (R.M q *ᵥ w))

/-- **The derivative of the skewed energy along the closed loop (4.54), MLS p. 195, for a robot,
written without `Ṁ`:** `V̇ = −ėᵀ K_v ė + ε ėᵀ M ė − ε eᵀ K_p e + ε(−eᵀ K_v ė + ėᵀ C(x, ẋ) e)` at the
configuration `q = x` and velocity `v = ẋ`; it is MLS's
`−ėᵀ(K_v − εM)ė − ε eᵀ K_p e + ε eᵀ(−K_v + Ṁ − C)ė` with `Ṁ − C = Cᵀ` (`deriv_eq_add_transpose`);
MLS's last line prints `½ Ṁ` in place of `Ṁ − C`. -/
def augmentedEnergyRate (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (q v e w : Fin p → ℝ) : ℝ :=
  -(w ⬝ᵥ (Kv *ᵥ w)) + ε * (w ⬝ᵥ (R.M q *ᵥ w)) - ε * (e ⬝ᵥ (Kp *ᵥ e)) +
    ε * (-(e ⬝ᵥ (Kv *ᵥ w)) + w ⬝ᵥ (R.C q v *ᵥ e))

/-- **MLS proof of Proposition 4.10, p. 195, for a robot: the derivative of `V` along a motion of
the closed loop.** With `M(x)` symmetric for every `x`, the skew property and `K_p` symmetric, along
a motion `x` with velocity `x'(t)` and acceleration `a` at `t`, an actual entrywise derivative `Ṁ`
of `s ↦ M(x(s))` at `t`, and a desired trajectory with `ẋ_d(t) = x_d'(t)`, `ẍ_d(t) = x_d''(t)` at
`t`: if the equations of motion hold at `t` under the law (4.53), then
`s ↦ V(x(s), x(s) − x_d(s), x'(s) − x_d'(s))` has the derivative `augmentedEnergyRate` at `t`. -/
theorem hasDerivAt_augmentedEnergy (hM : ∀ q, (R.M q).IsSymm) (hskew : R.HasSkewProperty)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.IsSymm) (ε : ℝ)
    {xd xd' xd'' : ℝ → Fin p → ℝ} {x x' : ℝ → Fin p → ℝ} {a : Fin p → ℝ}
    {Md : Matrix (Fin p) (Fin p) ℝ} {t : ℝ} (hx : HasDerivAt x (x' t) t) (hx' : HasDerivAt x' a t)
    (hMd : ∀ i j, HasDerivAt (fun s => R.M (x s) i j) (Md i j) t)
    (hd : HasDerivAt xd (xd' t) t) (hd' : HasDerivAt xd' (xd'' t) t)
    (hE : R.M (x t) *ᵥ a + R.C (x t) (x' t) *ᵥ x' t + R.N (x t) (x' t) =
      R.augmentedPDTorque Kp Kv xd xd' xd'' t (x t) (x' t)) :
    HasDerivAt (fun s => R.augmentedEnergy Kp ε (x s) (x s - xd s) (x' s - xd' s))
      (R.augmentedEnergyRate Kp Kv ε (x t) (x' t) (x t - xd t) (x' t - xd' t)) t := by
  have hcl := (R.equations_augmentedPDTorque_iff Kp Kv xd xd' xd'' t (x t) (x' t) a).mp hE
  set e := x t - xd t with he_def
  set w := x' t - xd' t with hw_def
  set α := a - xd'' t with hα_def
  set C := R.C (x t) (x' t) with hC_def
  have he : HasDerivAt (fun s => x s - xd s) w t := hx.sub hd
  have hw : HasDerivAt (fun s => x' s - xd' s) α t := hx'.sub hd'
  have hMw := Control.hasDerivAt_matrix_mulVec hMd hw
  have h1 := Control.hasDerivAt_dotProduct hw hMw
  have h2 := Control.hasDerivAt_dotProduct he (Control.hasDerivAt_mulVec_const Kp he)
  have h3 := Control.hasDerivAt_dotProduct he hMw
  have key := ((h1.const_mul (1 / 2 : ℝ)).add (h2.const_mul (1 / 2 : ℝ))).add (h3.const_mul ε)
  rw [← he_def, ← hw_def] at key
  convert key using 1
  · funext s
    simp only [augmentedEnergy, Pi.add_apply]
  -- the algebra of p. 195, with `Ṁ = C + Cᵀ`
  have hMdC : Md = C + Cᵀ := R.deriv_eq_add_transpose hM hskew hx hMd
  have hMa : R.M (x t) *ᵥ α = -(C *ᵥ w) - Kv *ᵥ w - Kp *ᵥ e := by
    rw [← sub_eq_zero, ← hcl]
    abel
  have hs1 : α ⬝ᵥ (R.M (x t) *ᵥ w) = w ⬝ᵥ (R.M (x t) *ᵥ α) :=
    Control.dotProduct_mulVec_comm (hM (x t)) α w
  have hs2 : w ⬝ᵥ (Kp *ᵥ e) = e ⬝ᵥ (Kp *ᵥ w) := Control.dotProduct_mulVec_comm hKp w e
  have hT : ∀ u v : Fin p → ℝ, u ⬝ᵥ (Cᵀ *ᵥ v) = v ⬝ᵥ (C *ᵥ u) := fun u v => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hs1, hMa, hMdC]
  simp only [augmentedEnergyRate, Matrix.add_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_neg]
  rw [hs2, hT e w, hT w w]
  ring

/-- **The derivative of the skewed energy along the tracking-error system (MLS p. 195, for a robot,
p. 301).** With `M(x)` positive definite for every `x`, `M` differentiable along motions, the skew
property and `K_p` symmetric, for a desired trajectory with `ẋ_d = x_d'`, `ẍ_d = x_d''` at every
time, along every solution `(e, ė)` of the error system of the closed loop under (4.53) relative to
`(x_d, ẋ_d)`, `V(t, (e, ė)) = augmentedEnergy (x_d(t) + e) e ė` has the derivative
`augmentedEnergyRate (x_d(t) + e) (ẋ_d(t) + ė) e ė`, on the whole error space. -/
theorem hasDerivAlongSolutions_augmentedEnergy (hM : ∀ q, (R.M q).PosDef)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.IsSymm) (ε : ℝ)
    {xd xd' xd'' : ℝ → Fin p → ℝ} (hd : ∀ t, HasDerivAt xd (xd' t) t)
    (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) :
    Stability.HasDerivAlongSolutions
      (Stability.errorSystem (R.field (R.augmentedPDTorque Kp Kv xd xd' xd''))
        (fun t => (xd t, xd' t)) (fun t => (xd' t, xd'' t)))
      (fun t z => R.augmentedEnergy Kp ε (xd t + z.1) z.1 z.2)
      (fun t z => R.augmentedEnergyRate Kp Kv ε (xd t + z.1) (xd' t + z.2) z.1 z.2) univ := by
  intro t₀ _ z hz t ht _
  have hxd : ∀ s, HasDerivAt (fun s => (xd s, xd' s)) (xd' s, xd'' s) s :=
    fun s => (hd s).prodMk (hd' s)
  set x : ℝ → (Fin p → ℝ) × (Fin p → ℝ) := fun s => z s + (xd s, xd' s) with hxdef
  have hx : Stability.IsSolution (R.field (R.augmentedPDTorque Kp Kv xd xd' xd'')) t₀ x := by
    refine (Stability.isSolution_errorSystem_iff hxd).mp ?_
    simpa [hxdef] using hz
  obtain ⟨h1, h2⟩ := R.equations_of_isSolution hM hx ht
  obtain ⟨Md, hMd'⟩ := hMd h1
  have key := R.hasDerivAt_augmentedEnergy (fun q => (hM q).isHermitian.isSymm) hskew hKp ε
    (x := fun s => (x s).1) (x' := fun s => (x s).2) h1 (hx.2 t ht).snd hMd' (hd t) (hd' t) h2
  convert key using 1
  · funext s
    simp [hxdef, add_comm]
  · simp [hxdef, add_comm]

/-- The skewed energy along the desired trajectory is jointly continuous in `(t, (e, ė))` when `M`
is continuous (MLS p. 194). -/
theorem continuous_augmentedEnergy_comp (hMc : Continuous R.M) (Kp : Matrix (Fin p) (Fin p) ℝ)
    (ε : ℝ) {xd : ℝ → Fin p → ℝ} (hxd : Continuous xd) :
    Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) =>
      R.augmentedEnergy Kp ε (xd z.1 + z.2.1) z.2.1 z.2.2 := by
  have he : Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => z.2.1 :=
    continuous_fst.comp continuous_snd
  have hw : Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => z.2.2 :=
    continuous_snd.comp continuous_snd
  have hq : Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => xd z.1 + z.2.1 :=
    (hxd.comp continuous_fst).add he
  have hMq := hMc.comp hq
  unfold augmentedEnergy
  exact ((continuous_const.mul (hw.dotProduct (hMq.matrix_mulVec hw))).add
    (continuous_const.mul (he.dotProduct (continuous_const.matrix_mulVec he)))).add
    (continuous_const.mul (he.dotProduct (hMq.matrix_mulVec hw)))

/-- The scalar core of the energy bounds of MLS p. 195: `Y = ėᵀMė`, `Z = eᵀK_pe`, `Q = eᵀMė`. -/
private lemma energy_bounds_scalar' {lam kp μ κp ε a b Y Z Q : ℝ}
    (hμ : 0 ≤ μ) (hκp : 0 ≤ κp) (hε : 0 ≤ ε) (hεμ : 2 * ε * μ ≤ min lam kp)
    (hY : lam * b ^ 2 ≤ Y) (hY' : Y ≤ μ * b ^ 2) (hZ : kp * a ^ 2 ≤ Z) (hZ' : Z ≤ κp * a ^ 2)
    (hQ : |Q| ≤ μ * a * b) :
    min lam kp / 4 * (a ^ 2 + b ^ 2) ≤ 1 / 2 * Y + 1 / 2 * Z + ε * Q ∧
      1 / 2 * Y + 1 / 2 * Z + ε * Q ≤ (μ + κp + ε * μ) / 2 * (a ^ 2 + b ^ 2) := by
  have hab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hQ1 : -(μ * a * b) ≤ Q := (abs_le.mp hQ).1
  have hQ2 : Q ≤ μ * a * b := (abs_le.mp hQ).2
  have hεQ1 : ε * (-(μ * a * b)) ≤ ε * Q := mul_le_mul_of_nonneg_left hQ1 hε
  have hεQ2 : ε * Q ≤ ε * (μ * a * b) := mul_le_mul_of_nonneg_left hQ2 hε
  have hεμ0 : 0 ≤ ε * μ := mul_nonneg hε hμ
  have hcross : ε * μ * (2 * (a * b)) ≤ ε * μ * (a ^ 2 + b ^ 2) :=
    mul_le_mul_of_nonneg_left hab hεμ0
  have hm1 := min_le_left lam kp
  have hm2 := min_le_right lam kp
  have ha2 := sq_nonneg a
  have hb2 := sq_nonneg b
  constructor
  · have h1 : min lam kp * b ^ 2 ≤ lam * b ^ 2 := mul_le_mul_of_nonneg_right hm1 hb2
    have h2 : min lam kp * a ^ 2 ≤ kp * a ^ 2 := mul_le_mul_of_nonneg_right hm2 ha2
    have h3 : 2 * ε * μ * (a ^ 2 + b ^ 2) ≤ min lam kp * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_right hεμ (by positivity)
    nlinarith
  · have h1 : 0 ≤ μ * a ^ 2 := mul_nonneg hμ ha2
    have h2 : 0 ≤ κp * b ^ 2 := mul_nonneg hκp hb2
    nlinarith

/-- The scalar core of the rate bound of MLS p. 195: `V̇ ≤ −min(k_v/2, εk_p/2)(a² + b²)`. -/
private lemma rate_bound_scalar' {kv kp ε μ K a b X Y Z W : ℝ} (hkp : 0 < kp) (hε : 0 < ε)
    (hX : kv * b ^ 2 ≤ X) (hY : Y ≤ μ * b ^ 2) (hZ : kp * a ^ 2 ≤ Z) (hW : W ≤ K * a * b)
    (hc : ε * (2 * kp * μ + K ^ 2) ≤ kp * kv) :
    -X + ε * Y - ε * Z + ε * W ≤ -(min (kv / 2) (ε * kp / 2) * (a ^ 2 + b ^ 2)) := by
  have h1 : 2 * kp * (K * a * b) ≤ kp ^ 2 * a ^ 2 + K ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (kp * a - K * b)]
  have e1 : ε * W ≤ ε * (K * a * b) := mul_le_mul_of_nonneg_left hW hε.le
  have e2 : ε * Y ≤ ε * (μ * b ^ 2) := mul_le_mul_of_nonneg_left hY hε.le
  have e3 : ε * (kp * a ^ 2) ≤ ε * Z := mul_le_mul_of_nonneg_left hZ hε.le
  have e4 : ε * (2 * kp * (K * a * b)) ≤ ε * (kp ^ 2 * a ^ 2 + K ^ 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hε.le
  have e5 : ε * (2 * kp * μ + K ^ 2) * b ^ 2 ≤ kp * kv * b ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg b)
  have hB : -X + ε * Y - ε * Z + ε * W ≤
      -(kv * b ^ 2) + ε * (μ * b ^ 2) - ε * (kp * a ^ 2) + ε * (K * a * b) := by linarith
  have hL : -X + ε * Y - ε * Z + ε * W ≤ -(ε * kp / 2 * a ^ 2 + kv / 2 * b ^ 2) := by
    have h2 : 2 * kp * (-X + ε * Y - ε * Z + ε * W) ≤
        2 * kp * (-(ε * kp / 2 * a ^ 2 + kv / 2 * b ^ 2)) := by
      have h3 := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 * kp)
      nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hm1 : min (kv / 2) (ε * kp / 2) * b ^ 2 ≤ kv / 2 * b ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg b)
  have hm2 : min (kv / 2) (ε * kp / 2) * a ^ 2 ≤ ε * kp / 2 * a ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg a)
  nlinarith

/-- **The skewed energy is positive definite for `ε` small (MLS p. 195), for a robot, with explicit
constants.** At a configuration `q` where `λ‖v‖² ≤ vᵀM(q)v` and `|vᵀM(q)v'| ≤ μ‖v‖‖v'‖`, with
`k_p‖v‖² ≤ vᵀK_pv ≤ κ_p‖v‖²`, `μ, κ_p, ε ≥ 0` and `2εμ ≤ min(λ, k_p)`:
`¼ min(λ, k_p)(‖e‖² + ‖ė‖²) ≤ V ≤ ½(μ + κ_p + εμ)(‖e‖² + ‖ė‖²)` (sup norms). -/
theorem augmentedEnergy_bounds {Kp : Matrix (Fin p) (Fin p) ℝ} {ε lam μ kp κp : ℝ}
    {q e w : Fin p → ℝ} (hμ : 0 ≤ μ) (hκp : 0 ≤ κp) (hε : 0 ≤ ε)
    (hεμ : 2 * ε * μ ≤ min lam kp) (hMl : ∀ v, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    (hMu : ∀ v v', |v ⬝ᵥ (R.M q *ᵥ v')| ≤ μ * ‖v‖ * ‖v'‖)
    (hkp : ∀ v, kp * ‖v‖ ^ 2 ≤ v ⬝ᵥ (Kp *ᵥ v)) (hκpb : ∀ v, v ⬝ᵥ (Kp *ᵥ v) ≤ κp * ‖v‖ ^ 2) :
    min lam kp / 4 * (‖e‖ ^ 2 + ‖w‖ ^ 2) ≤ R.augmentedEnergy Kp ε q e w ∧
      R.augmentedEnergy Kp ε q e w ≤ (μ + κp + ε * μ) / 2 * (‖e‖ ^ 2 + ‖w‖ ^ 2) := by
  have hY' : w ⬝ᵥ (R.M q *ᵥ w) ≤ μ * ‖w‖ ^ 2 := by
    have := (le_abs_self _).trans (hMu w w)
    nlinarith
  exact energy_bounds_scalar' hμ hκp hε hεμ (hMl w) hY' (hkp e) (hκpb e) (hMu e w)

/-- **`V̇` is negative definite for `ε` small (MLS p. 195), for a robot, with an explicit
condition.** At a configuration `q` and velocity `v` where `|v₁ᵀM(q)v₂| ≤ μ‖v₁‖‖v₂‖` and
`|v₁ᵀC(q, v)v₂| ≤ c‖v₁‖‖v₂‖`, with `k_p‖v‖² ≤ vᵀK_pv`, `k_v‖v‖² ≤ vᵀK_vv`,
`|v₁ᵀK_vv₂| ≤ κ_v‖v₁‖‖v₂‖`, `k_p, ε > 0` and `ε(2k_pμ + (κ_v + c)²) ≤ k_p k_v`:
`V̇ ≤ −min(k_v/2, εk_p/2)(‖e‖² + ‖ė‖²)`. -/
theorem augmentedEnergyRate_le {Kp Kv : Matrix (Fin p) (Fin p) ℝ} {ε μ c kp kv κv : ℝ}
    {q v e w : Fin p → ℝ} (hkp0 : 0 < kp) (hε : 0 < ε)
    (hMu : ∀ v₁ v₂, |v₁ ⬝ᵥ (R.M q *ᵥ v₂)| ≤ μ * ‖v₁‖ * ‖v₂‖)
    (hCu : ∀ v₁ v₂, |v₁ ⬝ᵥ (R.C q v *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖)
    (hkp : ∀ v₁, kp * ‖v₁‖ ^ 2 ≤ v₁ ⬝ᵥ (Kp *ᵥ v₁)) (hkv : ∀ v₁, kv * ‖v₁‖ ^ 2 ≤ v₁ ⬝ᵥ (Kv *ᵥ v₁))
    (hκv : ∀ v₁ v₂, |v₁ ⬝ᵥ (Kv *ᵥ v₂)| ≤ κv * ‖v₁‖ * ‖v₂‖)
    (hεc : ε * (2 * kp * μ + (κv + c) ^ 2) ≤ kp * kv) :
    R.augmentedEnergyRate Kp Kv ε q v e w ≤ -(min (kv / 2) (ε * kp / 2) * (‖e‖ ^ 2 + ‖w‖ ^ 2)) := by
  have hWb : -(e ⬝ᵥ (Kv *ᵥ w)) + w ⬝ᵥ (R.C q v *ᵥ e) ≤ (κv + c) * ‖e‖ * ‖w‖ := by
    have h1 := (neg_le_abs _).trans (hκv e w)
    have h2 := (le_abs_self _).trans (hCu w e)
    nlinarith
  have hY : w ⬝ᵥ (R.M q *ᵥ w) ≤ μ * ‖w‖ ^ 2 := by
    have := (le_abs_self _).trans (hMu w w)
    nlinarith
  unfold augmentedEnergyRate
  exact rate_bound_scalar' hkp0 hε (hkv w) hY (hkp e) hWb hεc

/-- **MLS Proposition 4.10 (p. 194) for a robot on a tube, with explicit constants: exponential
decay of the tracking error by Theorem 4.5 (local form).** Hypotheses: `M(x)` positive definite for
every `x`, `M` continuous and differentiable along motions, the skew property; `K_p` symmetric; a
desired trajectory with `ẋ_d = x_d'`, `ẍ_d = x_d''`; on the tube `‖(e, ė)‖ ≤ R₀` around it, for
`t ≥ 0`, with `x = x_d(t) + e`, `ẋ = ẋ_d(t) + ė`: `λ‖v‖² ≤ vᵀM(x)v`, `|v₁ᵀM(x)v₂| ≤ μ‖v₁‖‖v₂‖`,
`|v₁ᵀC(x, ẋ)v₂| ≤ c‖v₁‖‖v₂‖`; gain bounds as in `augmentedEnergyRate_le` with `vᵀK_pv ≤ κ_p‖v‖²`;
`ε > 0` with `2εμ ≤ min(λ, k_p)` and `ε(2k_pμ + (κ_v + c)²) ≤ k_p k_v`. Then, with
`a₁ = min(λ, k_p)/4`, `a₂ = μ + κ_p + εμ + 1`, `a₃ = min(k_v/2, εk_p/2)`, every closed-loop solution
from `t₀ ≥ 0` with `‖(e, ė)(t₀)‖ < min(R₀, R₀√(a₁/a₂))` obeys
`‖(e, ė)(t)‖ ≤ √(a₂/a₁) e^{−(a₃/(2a₂))(t − t₀)} ‖(e, ė)(t₀)‖` for `t ≥ t₀`. -/
theorem norm_le_augmentedPD_of_bounds (hM : ∀ q, (R.M q).PosDef) (hMc : Continuous R.M)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.IsSymm)
    {xd xd' xd'' : ℝ → Fin p → ℝ} (hd : ∀ t, HasDerivAt xd (xd' t) t)
    (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) {R₀ ε lam μ c kp κp kv κv : ℝ} (hR : 0 < R₀)
    (hε : 0 < ε) (hlam : 0 < lam) (hμ : 0 ≤ μ) (hkp0 : 0 < kp) (hκp : 0 ≤ κp) (hkv0 : 0 < kv)
    (hMl : ∀ t, 0 ≤ t → ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z‖ ≤ R₀ →
      ∀ v, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M (xd t + z.1) *ᵥ v))
    (hMu : ∀ t, 0 ≤ t → ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z‖ ≤ R₀ →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (R.M (xd t + z.1) *ᵥ v₂)| ≤ μ * ‖v₁‖ * ‖v₂‖)
    (hCu : ∀ t, 0 ≤ t → ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z‖ ≤ R₀ →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (R.C (xd t + z.1) (xd' t + z.2) *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖)
    (hkp : ∀ v, kp * ‖v‖ ^ 2 ≤ v ⬝ᵥ (Kp *ᵥ v)) (hκpb : ∀ v, v ⬝ᵥ (Kp *ᵥ v) ≤ κp * ‖v‖ ^ 2)
    (hkv : ∀ v, kv * ‖v‖ ^ 2 ≤ v ⬝ᵥ (Kv *ᵥ v))
    (hκv : ∀ v₁ v₂, |v₁ ⬝ᵥ (Kv *ᵥ v₂)| ≤ κv * ‖v₁‖ * ‖v₂‖)
    (hεμ : 2 * ε * μ ≤ min lam kp) (hεc : ε * (2 * kp * μ + (κv + c) ^ 2) ≤ kp * kv)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → (Fin p → ℝ) × (Fin p → ℝ)}
    (hx : Stability.IsSolution (R.field (R.augmentedPDTorque Kp Kv xd xd' xd'')) t₀ x)
    (hx₀ : ‖x t₀ - (xd t₀, xd' t₀)‖ <
      min R₀ (R₀ * Real.sqrt (min lam kp / 4 / (μ + κp + ε * μ + 1))))
    {t : ℝ} (ht : t₀ ≤ t) :
    ‖x t - (xd t, xd' t)‖ ≤ Real.sqrt ((μ + κp + ε * μ + 1) / (min lam kp / 4)) *
      Real.exp (-(min (kv / 2) (ε * kp / 2) / (2 * (μ + κp + ε * μ + 1))) * (t - t₀)) *
        ‖x t₀ - (xd t₀, xd' t₀)‖ := by
  have hxd : ∀ s, HasDerivAt (fun s => (xd s, xd' s)) (xd' s, xd'' s) s :=
    fun s => (hd s).prodMk (hd' s)
  have hxdc : Continuous xd := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hz := (Stability.isSolution_errorSystem_iff hxd (f := R.field
    (R.augmentedPDTorque Kp Kv xd xd' xd''))).mpr hx
  have ha₁ : 0 < min lam kp / 4 := by have := lt_min hlam hkp0; positivity
  have ha₂ : 0 < μ + κp + ε * μ + 1 := by positivity
  have ha₃ : 0 < min (kv / 2) (ε * kp / 2) := lt_min (by positivity) (by positivity)
  have hsq : ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 :=
    Control.sq_norm_prod_le
  have hsq' : ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    intro z
    have h1 := norm_fst_le z
    have h2 := norm_snd_le z
    have := norm_nonneg z.1
    have := norm_nonneg z.2
    nlinarith
  have hbounds : ∀ t, 0 ≤ t → ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z‖ ≤ R₀ →
      min lam kp / 4 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ R.augmentedEnergy Kp ε (xd t + z.1) z.1 z.2 ∧
        R.augmentedEnergy Kp ε (xd t + z.1) z.1 z.2 ≤
          (μ + κp + ε * μ) / 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) :=
    fun t ht z hz => R.augmentedEnergy_bounds hμ hκp hε.le hεμ (hMl t ht z hz) (hMu t ht z hz)
      hkp hκpb
  have key := Stability.norm_le_of_quadratic_lyapunov_local
    (f := Stability.errorSystem (R.field (R.augmentedPDTorque Kp Kv xd xd' xd''))
      (fun t => (xd t, xd' t)) (fun t => (xd' t, xd'' t)))
    (V := fun t z => R.augmentedEnergy Kp ε (xd t + z.1) z.1 z.2)
    (Vdot := fun t z => R.augmentedEnergyRate Kp Kv ε (xd t + z.1) (xd' t + z.2) z.1 z.2)
    ha₁ ha₂ ha₃ hR (R.continuous_augmentedEnergy_comp hMc Kp ε hxdc).continuousOn
    (fun t ht z hz => by
      have h1 := (hbounds t ht z hz).1
      have h2 := mul_le_mul_of_nonneg_left (hsq z) ha₁.le
      exact h2.trans h1)
    (fun t ht z hz => by
      have h1 := (hbounds t ht z hz).2
      have h2 := hsq' z
      have hc0 : 0 ≤ (μ + κp + ε * μ) / 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left h2 hc0
      have h4 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
      nlinarith)
    ((R.hasDerivAlongSolutions_augmentedEnergy hM hMd hskew hKp ε hd hd').mono (subset_univ _))
    (fun t ht z hz => by
      have h1 := R.augmentedEnergyRate_le (q := xd t + z.1) (v := xd' t + z.2) (e := z.1)
        (w := z.2) hkp0 hε (hMu t ht z hz) (hCu t ht z hz) hkp hkv hκv hεc
      have h2 := mul_le_mul_of_nonneg_left (hsq z) ha₃.le
      linarith)
    ht₀ hz hx₀ ht
  simpa using key

/-- The tracking error of a closed-loop state as a pair (MLS p. 194, sup norm on the product). -/
private lemma sub_pair' (x : (Fin p → ℝ) × (Fin p → ℝ)) (a b : Fin p → ℝ) :
    x - (a, b) = (x.1 - a, x.2 - b) := rfl

/-- **MLS Proposition 4.10 (p. 194) for every robot (p. 301), as the library states it: semiglobal
exponential trajectory tracking under the augmented PD law (4.53).** Hypotheses: `M(x)` positive
definite for every `x`, `M` continuous and differentiable along motions, the skew property; `M`
uniformly positive definite and bounded (`λ‖v‖² ≤ vᵀM(x)v`, `|vᵀM(x)w| ≤ μ‖v‖‖w‖` for all `x`); the
Coriolis matrix bounded by the velocity, `|vᵀC(x, u)w| ≤ δ‖u‖‖v‖‖w‖`; `K_p, K_v` positive definite;
a desired trajectory with `ẋ_d = x_d'`, `ẍ_d = x_d''` and `‖ẋ_d(t)‖ ≤ v_d` for `t ≥ 0`. Then there
is `m > 0` and, for every `ρ > 0`, a rate `α > 0` such that every closed-loop solution from `t₀ ≥ 0`
with initial tracking error smaller than `ρ` satisfies
`‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀` (sup norm on `ℝᵖ × ℝᵖ`). -/
theorem augmentedPD_tracking (hM : ∀ q, (R.M q).PosDef) (hMc : Continuous R.M)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    (hMl : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin p → ℝ, |v ⬝ᵥ (R.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ q u v w : Fin p → ℝ, |v ⬝ᵥ (R.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef)
    {xd xd' xd'' : ℝ → Fin p → ℝ} (hd : ∀ t, HasDerivAt xd (xd' t) t)
    (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖xd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin p → ℝ) × (Fin p → ℝ),
      Stability.IsSolution (R.field (R.augmentedPDTorque Kp Kv xd xd' xd'')) t₀ x →
      ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ < ρ → ∀ t, t₀ ≤ t →
        ‖((x t).1 - xd t, (x t).2 - xd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ := by
  obtain ⟨lam, hlam, hMl⟩ := hMl
  obtain ⟨μ₀, hMb⟩ := hMb
  obtain ⟨δ₀, hCb⟩ := hCb
  obtain ⟨vd₀, hvd⟩ := hvd
  set μ := max μ₀ 0 with hμdef
  set δ := max δ₀ 0 with hδdef
  set vd := max vd₀ 0 with hvddef
  have hμ : 0 ≤ μ := le_max_right _ _
  have hδ : 0 ≤ δ := le_max_right _ _
  have hvd0 : 0 ≤ vd := le_max_right _ _
  have hMb' : ∀ q v w : Fin p → ℝ, |v ⬝ᵥ (R.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := fun q v w =>
    (hMb q v w).trans (by gcongr; exact le_max_left _ _)
  have hCb' : ∀ q u v w : Fin p → ℝ, |v ⬝ᵥ (R.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖ :=
    fun q u v w => (hCb q u v w).trans (by gcongr; exact le_max_left _ _)
  obtain ⟨kp, hkp0, hkp⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKp
  obtain ⟨κp, hκp0, hκpb⟩ := QuadraticBounds.exists_dotProduct_mulVec_le_mul_sq_norm Kp
  obtain ⟨kv, hkv0, hkv⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKv
  obtain ⟨κv, hκv0, hκv⟩ := Control.exists_abs_dotProduct_mulVec_le Kv
  have hmm : 0 < min lam kp := lt_min hlam hkp0
  set ε₀ := min lam kp / (2 * (μ + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀μ : 2 * ε₀ * μ ≤ min lam kp := by
    have e : 2 * ε₀ * μ = min lam kp * (μ / (μ + 1)) := by
      rw [hε₀def]
      field_simp
    have : μ / (μ + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    rw [e]
    nlinarith
  set A := μ + κp + ε₀ * μ + 1 with hAdef
  have hA : 0 < A := by positivity
  set s₁ := Real.sqrt (min lam kp / 4 / A) with hs₁def
  have hs₁ : 0 < s₁ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt (A / (min lam kp / 4)), Real.sqrt_pos.mpr (by positivity), fun ρ hρ => ?_⟩
  set r := ρ / s₁ + ρ with hrdef
  have hr : 0 < r := by positivity
  set c := δ * (vd + r) with hcdef
  have hc : 0 ≤ c := by positivity
  set D := 2 * kp * μ + (κv + c) ^ 2 with hDdef
  have hD : 0 ≤ D := by positivity
  set ε := min ε₀ (kp * kv / (D + 1)) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεμ : 2 * ε * μ ≤ min lam kp := le_trans (by gcongr) hε₀μ
  have hεc : ε * D ≤ kp * kv := by
    have h1 : ε ≤ kp * kv / (D + 1) := min_le_right _ _
    have h2 : ε * (D + 1) ≤ kp * kv := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  set a₂ := μ + κp + ε * μ + 1 with ha₂def
  have ha₂ : 0 < a₂ := by positivity
  have ha₂A : a₂ ≤ A := by
    have := mul_le_mul_of_nonneg_right hεε₀ hμ
    linarith
  refine ⟨min (kv / 2) (ε * kp / 2) / (2 * a₂),
    div_pos (lt_min (by positivity) (by positivity)) (by positivity),
    fun t₀ ht₀ x hx hx₀ t ht => ?_⟩
  have hCu : ∀ t, 0 ≤ t → ∀ z : (Fin p → ℝ) × (Fin p → ℝ), ‖z‖ ≤ r →
      ∀ v₁ v₂, |v₁ ⬝ᵥ (R.C (xd t + z.1) (xd' t + z.2) *ᵥ v₂)| ≤ c * ‖v₁‖ * ‖v₂‖ := by
    intro t ht z hz v₁ v₂
    have h2 : ‖xd' t + z.2‖ ≤ vd + r :=
      (norm_add_le _ _).trans (add_le_add ((hvd t ht).trans (le_max_left _ _))
        ((norm_snd_le z).trans hz))
    calc |v₁ ⬝ᵥ (R.C (xd t + z.1) (xd' t + z.2) *ᵥ v₂)|
        ≤ δ * ‖xd' t + z.2‖ * ‖v₁‖ * ‖v₂‖ := hCb' _ _ _ _
      _ ≤ δ * (vd + r) * ‖v₁‖ * ‖v₂‖ := by gcongr
  have hx₀' : ‖x t₀ - (xd t₀, xd' t₀)‖ <
      min r (r * Real.sqrt (min lam kp / 4 / (μ + κp + ε * μ + 1))) := by
    rw [sub_pair']
    have hs : s₁ ≤ Real.sqrt (min lam kp / 4 / a₂) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) ha₂ ha₂A)
    have hrs : r * s₁ = ρ + ρ * s₁ := by
      rw [hrdef]
      field_simp
    refine lt_min (by
      have : 0 < ρ / s₁ := by positivity
      linarith) ?_
    calc ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ < ρ := hx₀
      _ < ρ + ρ * s₁ := lt_add_of_pos_right ρ (by positivity)
      _ = r * s₁ := hrs.symm
      _ ≤ r * Real.sqrt (min lam kp / 4 / a₂) := by gcongr
  have key := R.norm_le_augmentedPD_of_bounds hM hMc hMd hskew hKp.isHermitian.isSymm hd hd' hr
    hε hlam hμ hkp0 hκp0.le hkv0 (fun t _ z _ v => hMl _ v) (fun t _ z _ => hMb' _) hCu hkp
    (fun v => hκpb v) hkv hκv hεμ hεc ht₀ hx hx₀' ht
  rw [sub_pair', sub_pair'] at key
  refine key.trans ?_
  gcongr

/-- **MLS Proposition 4.10 (p. 194) for every robot, in the form of Definition 4.3 (p. 180): the
tracking error is exponentially stable.** Under the hypotheses of `augmentedPD_tracking`, the origin
of the tracking-error system (the closed loop under (4.53) relative to `(x_d, ẋ_d)`) is
exponentially stable. -/
theorem exponentiallyStable_augmentedPD (hM : ∀ q, (R.M q).PosDef) (hMc : Continuous R.M)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    (hMl : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin p → ℝ, |v ⬝ᵥ (R.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ q u v w : Fin p → ℝ, |v ⬝ᵥ (R.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef)
    {xd xd' xd'' : ℝ → Fin p → ℝ} (hd : ∀ t, HasDerivAt xd (xd' t) t)
    (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖xd' t‖ ≤ vd) :
    Stability.ExponentiallyStable
      (Stability.errorSystem (R.field (R.augmentedPDTorque Kp Kv xd xd' xd''))
        (fun t => (xd t, xd' t)) (fun t => (xd' t, xd'' t))) 0 := by
  obtain ⟨m, hm, H⟩ := R.augmentedPD_tracking hM hMc hMd hskew hMl hMb hCb hKp hKv hd hd' hvd
  obtain ⟨α, hα, H⟩ := H 1 one_pos
  refine ⟨m, hm, α, hα, 1 / 2, by norm_num, fun t₀ ht₀ z hz hz₀ t ht => ?_⟩
  have hxd : ∀ s, HasDerivAt (fun s => (xd s, xd' s)) (xd' s, xd'' s) s :=
    fun s => (hd s).prodMk (hd' s)
  have hx : Stability.IsSolution (R.field (R.augmentedPDTorque Kp Kv xd xd' xd'')) t₀
      (fun s => z s + (xd s, xd' s)) :=
    (Stability.isSolution_errorSystem_iff hxd).mp (by simpa using hz)
  have hz₀' : ‖z t₀‖ < 1 := by
    rw [sub_zero] at hz₀
    linarith
  have := H t₀ ht₀ _ hx (by simpa using hz₀') t ht
  simpa using this

/-- **MLS Proposition 4.10 (p. 194) for a robot whose Coriolis matrix is bounded uniformly in the
velocity: global exponential tracking.** With `M(x)` positive definite for every `x`, `M` continuous
and differentiable along motions, the skew property, `M` uniformly positive definite and bounded,
`|vᵀC(x, u)w| ≤ c‖v‖‖w‖` for all `x, u` (for instance `C = 0`), and `K_p, K_v` positive definite,
there are `m, α > 0`, depending only on the bounds and the gains, such that for every desired
trajectory with `ẋ_d = x_d'`, `ẍ_d = x_d''` (no bound on them) every closed-loop solution from
`t₀ ≥ 0` satisfies `‖(e(t), ė(t))‖ ≤ m e^{−α(t − t₀)} ‖(e(t₀), ė(t₀))‖` for `t ≥ t₀`: one `ε` serves
every initial error. -/
theorem augmentedPD_tracking_of_bounded_C (hM : ∀ q, (R.M q).PosDef) (hMc : Continuous R.M)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    (hMl : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin p → ℝ, |v ⬝ᵥ (R.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ c, ∀ q u v w : Fin p → ℝ, |v ⬝ᵥ (R.C q u *ᵥ w)| ≤ c * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) :
    ∃ m > 0, ∃ α > 0, ∀ {xd xd' xd'' : ℝ → Fin p → ℝ}, (∀ t, HasDerivAt xd (xd' t) t) →
      (∀ t, HasDerivAt xd' (xd'' t) t) → ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin p → ℝ) × (Fin p → ℝ),
      Stability.IsSolution (R.field (R.augmentedPDTorque Kp Kv xd xd' xd'')) t₀ x →
      ∀ t, t₀ ≤ t → ‖((x t).1 - xd t, (x t).2 - xd' t)‖ ≤
        m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - xd t₀, (x t₀).2 - xd' t₀)‖ := by
  obtain ⟨lam, hlam, hMl⟩ := hMl
  obtain ⟨μ₀, hMb⟩ := hMb
  obtain ⟨c₀, hCb⟩ := hCb
  set μ := max μ₀ 0 with hμdef
  set c := max c₀ 0 with hcdef
  have hμ : 0 ≤ μ := le_max_right _ _
  have hc : 0 ≤ c := le_max_right _ _
  have hMb' : ∀ q v w : Fin p → ℝ, |v ⬝ᵥ (R.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖ := fun q v w =>
    (hMb q v w).trans (by gcongr; exact le_max_left _ _)
  have hCb' : ∀ q u v w : Fin p → ℝ, |v ⬝ᵥ (R.C q u *ᵥ w)| ≤ c * ‖v‖ * ‖w‖ :=
    fun q u v w => (hCb q u v w).trans (by gcongr; exact le_max_left _ _)
  obtain ⟨kp, hkp0, hkp⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKp
  obtain ⟨κp, hκp0, hκpb⟩ := QuadraticBounds.exists_dotProduct_mulVec_le_mul_sq_norm Kp
  obtain ⟨kv, hkv0, hkv⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKv
  obtain ⟨κv, hκv0, hκv⟩ := Control.exists_abs_dotProduct_mulVec_le Kv
  have hmm : 0 < min lam kp := lt_min hlam hkp0
  set ε₀ := min lam kp / (2 * (μ + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀μ : 2 * ε₀ * μ ≤ min lam kp := by
    have e : 2 * ε₀ * μ = min lam kp * (μ / (μ + 1)) := by
      rw [hε₀def]
      field_simp
    have : μ / (μ + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    rw [e]
    nlinarith
  set D := 2 * kp * μ + (κv + c) ^ 2 with hDdef
  have hD : 0 ≤ D := by positivity
  set ε := min ε₀ (kp * kv / (D + 1)) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεμ : 2 * ε * μ ≤ min lam kp := le_trans (by gcongr; exact min_le_left _ _) hε₀μ
  have hεc : ε * D ≤ kp * kv := by
    have h1 : ε ≤ kp * kv / (D + 1) := min_le_right _ _
    have h2 : ε * (D + 1) ≤ kp * kv := (le_div_iff₀ (by positivity)).mp h1
    nlinarith
  set a₂ := μ + κp + ε * μ + 1 with ha₂def
  have ha₂ : 0 < a₂ := by positivity
  set s₁ := Real.sqrt (min lam kp / 4 / a₂) with hs₁def
  have hs₁ : 0 < s₁ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt (a₂ / (min lam kp / 4)), Real.sqrt_pos.mpr (by positivity),
    min (kv / 2) (ε * kp / 2) / (2 * a₂),
    div_pos (lt_min (by positivity) (by positivity)) (by positivity),
    fun {xd xd' xd''} hd hd' t₀ ht₀ x hx t ht => ?_⟩
  set e₀ := ‖x t₀ - (xd t₀, xd' t₀)‖ with he₀def
  set r := (e₀ + 1) / s₁ + (e₀ + 1) with hrdef
  have he₀ : 0 ≤ e₀ := norm_nonneg _
  have hr : 0 < r := by positivity
  have hx₀' : ‖x t₀ - (xd t₀, xd' t₀)‖ < min r (r * s₁) := by
    have hrs : r * s₁ = (e₀ + 1) + (e₀ + 1) * s₁ := by
      rw [hrdef]
      field_simp
    refine lt_min ?_ ?_
    · have : 0 < (e₀ + 1) / s₁ := by positivity
      linarith
    · rw [hrs]
      have : 0 < (e₀ + 1) * s₁ := by positivity
      linarith
  have key := R.norm_le_augmentedPD_of_bounds hM hMc hMd hskew hKp.isHermitian.isSymm hd hd' hr
    hε hlam hμ hkp0 hκp0.le hkv0 (fun t _ z _ v => hMl _ v) (fun t _ z _ => hMb' _)
    (fun t _ z _ => hCb' _ _) hkp (fun v => hκpb v) hkv hκv hεμ hεc ht₀ hx hx₀' ht
  rw [sub_pair', sub_pair'] at key
  exact key

end RobotSystem
end Control

namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **The robot's augmented PD law is the manipulator's law (4.53), MLS p. 194**, by definition. -/
theorem toRobotSystem_augmentedPDTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ)
    (θd θd' θd'' : ℝ → Fin n → ℝ) :
    P.toRobotSystem.augmentedPDTorque Kp Kv θd θd' θd'' = P.augmentedPDTorque Kp Kv θd θd' θd'' :=
  rfl

/-- **MLS Proposition 4.10 (p. 194) for the open-chain manipulator, re-derived from the robot
version (MLS p. 301).** The hypotheses of `ManipulatorModel.augmentedPD_tracking` (symmetric link
inertias, `M(θ)` positive definite, the bounds on `M` and `C`, positive definite gains, a desired
velocity bounded for `t ≥ 0`) give its conclusion through `Control.RobotSystem.augmentedPD_tracking`
for `toRobotSystem`. -/
theorem augmentedPD_tracking_of_robot (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMl : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin n → ℝ, |v ⬝ᵥ (P.M q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ q u v w : Fin n → ℝ, |v ⬝ᵥ (P.C q u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef)
    {θd θd' θd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt θd (θd' t) t)
    (hd' : ∀ t, HasDerivAt θd' (θd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖θd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ x : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.augmentedPDTorque Kp Kv θd θd' θd'')) t₀ x →
      ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ < ρ → ∀ t, t₀ ≤ t →
        ‖((x t).1 - θd t, (x t).2 - θd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) * ‖((x t₀).1 - θd t₀, (x t₀).2 - θd' t₀)‖ := by
  exact P.toRobotSystem.augmentedPD_tracking hM P.continuous_M
    (fun hx => ⟨_, P.hasDerivAt_M_comp hx⟩) (P.toRobotSystem_hasSkewProperty h) hMl hMb hCb hKp
    hKv hd hd' hvd

variable (f : (Fin n → ℝ) → Fin n → ℝ)

/-- **The workspace version of the augmented PD law (MLS Exercise 9, p. 209, with p. 198):**
`τ = Jᵀ F` with `F` the augmented PD law (4.53) of the workspace robot `(M̃, C̃, Ñ)` in the
workspace coordinates `x = f(θ)`, `ẋ = J(θ) θ̇`, for a desired workspace trajectory `x_d` with
velocity `x_d'` and acceleration `x_d''` and an inverse `g` of `f`. -/
def workspaceAugmentedPDTorque (g : (Fin n → ℝ) → Fin n → ℝ) (Kp Kv : Matrix (Fin n) (Fin n) ℝ)
    (xd xd' xd'' : ℝ → Fin n → ℝ) : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  workspaceTorque f ((P.workspaceRobot f g).augmentedPDTorque Kp Kv xd xd' xd'')

/-- **MLS Exercise 9 (p. 209): the workspace version of the augmented PD law gives exponential
trajectory tracking, in the semiglobal form of Proposition 4.10 as formalized.** With symmetric link
inertias, `M(θ)` positive definite for every `θ`, `f` of class `C²` with a differentiable inverse
`g`, `M̃` uniformly positive definite and bounded, the workspace robot's Coriolis matrix bounded by
the velocity (`|vᵀ C̃(g(x), J⁻¹u) w| ≤ δ‖u‖‖v‖‖w‖`), `K_p, K_v` positive definite and a desired
workspace trajectory with `ẋ_d = x_d'`, `ẍ_d = x_d''` and bounded velocity for `t ≥ 0`: there is
`m > 0` and, for every `ρ > 0`, a rate `α > 0` such that every joint solution `(θ, θ̇)` from
`t₀ ≥ 0` under `τ = Jᵀ F` whose initial workspace error `(f(θ) − x_d, Jθ̇ − ẋ_d)` is smaller than
`ρ` has workspace error bounded by `m e^{−α(t − t₀)}` times the initial one for `t ≥ t₀`. -/
theorem workspaceAugmentedPD_tracking (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {g : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : Differentiable ℝ g) (hfg : ∀ y, f (g y) = y) (hgf : ∀ q, g (f q) = q)
    (hMl : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.workspaceM f q *ᵥ v))
    (hMb : ∃ μ, ∀ q v w : Fin n → ℝ, |v ⬝ᵥ (P.workspaceM f q *ᵥ w)| ≤ μ * ‖v‖ * ‖w‖)
    (hCb : ∃ δ, ∀ x u v w : Fin n → ℝ,
      |v ⬝ᵥ ((P.workspaceRobot f g).C x u *ᵥ w)| ≤ δ * ‖u‖ * ‖v‖ * ‖w‖)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef)
    {xd xd' xd'' : ℝ → Fin n → ℝ} (hd : ∀ t, HasDerivAt xd (xd' t) t)
    (hd' : ∀ t, HasDerivAt xd' (xd'' t) t) (hvd : ∃ vd, ∀ t, 0 ≤ t → ‖xd' t‖ ≤ vd) :
    ∃ m > 0, ∀ ρ > 0, ∃ α > 0, ∀ t₀, 0 ≤ t₀ → ∀ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ),
      Stability.IsSolution (P.field (P.workspaceAugmentedPDTorque f g Kp Kv xd xd' xd'')) t₀ z →
      ‖(f (z t₀).1 - xd t₀, jac f (z t₀).1 *ᵥ (z t₀).2 - xd' t₀)‖ < ρ → ∀ t, t₀ ≤ t →
        ‖(f (z t).1 - xd t, jac f (z t).1 *ᵥ (z t).2 - xd' t)‖ ≤
          m * Real.exp (-α * (t - t₀)) *
            ‖(f (z t₀).1 - xd t₀, jac f (z t₀).1 *ᵥ (z t₀).2 - xd' t₀)‖ := by
  have hd₁ : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hJ : ∀ q, IsUnit (jac f q).det := isUnit_det_jac_of_inverse f hd₁ hg hfg hgf
  obtain ⟨lam, hlam, hb⟩ := hMl
  obtain ⟨μ, hμ⟩ := hMb
  obtain ⟨m, hm, H⟩ := (P.workspaceRobot f g).augmentedPD_tracking
    (P.workspaceRobot_M_posDef f g hM hJ) (P.continuous_workspaceRobot_M f hf hg.continuous hJ)
    (P.differentiableAlongMotions_workspaceRobot f hf hg hfg hgf)
    (P.workspaceRobot_hasSkewProperty f h hf hg hfg hgf) ⟨lam, hlam, fun q v => hb (g q) v⟩
    ⟨μ, fun q v w => hμ (g q) v w⟩ hCb hKp hKv hd hd' hvd
  refine ⟨m, hm, fun ρ hρ => ?_⟩
  obtain ⟨α, hα, H⟩ := H ρ hρ
  refine ⟨α, hα, fun t₀ ht₀ z hz hz₀ t ht => ?_⟩
  have hy := P.isSolution_workspaceRobot_of_isSolution f hM hf hgf hJ
    (F := (P.workspaceRobot f g).augmentedPDTorque Kp Kv xd xd' xd'') hz
  exact H t₀ ht₀ _ hy hz₀ t ht

end ManipulatorModel
end RoboLean
