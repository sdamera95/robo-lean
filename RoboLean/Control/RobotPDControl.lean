import RoboLean.Control.RobotSystem
import RoboLean.Control.LaSalle
import RoboLean.Control.StabilityTheorems
import RoboLean.Control.QuadraticBounds

/-!
# PD control with compensation of `N` for every robot (MLS Proposition 4.9, pp. 193–194, §6.5)

**What MLS states.** Proposition 4.9 (p. 193): "If `θ̇_d ≡ 0` and `K_v, K_p > 0`, the control law
(4.51) applied to the system (4.47) renders the equilibrium point `θ = θ_d` globally asymptotically
stable." The proof takes `V = ½ θ̇ᵀ M θ̇ + ½ θᵀ K_p θ`, gets `V̇ = −θ̇ᵀ K_v θ̇` "since `Ṁ − 2C` is
skew-symmetric", and concludes by Lasalle's principle with the largest invariant set in `{θ̇ = 0}`
reduced to `θ = 0` by `K_p θ = 0` (p. 194). On p. 190 MLS says that a control law whose stability
"requires only those properties given in Lemma 4.2" works "for general open-chain robot
manipulators"; on p. 301 that "the only essential properties required by the proofs of convergence
are that `M(q)` be positive definite and `Ṁ − 2C` skew-symmetric", so the controllers of Chapter 4
apply to every robot `M(q) q̈ + C(q, q̇) q̇ + N(q, q̇) = F` (p. 303).

**Formalized**, for a robot `Control.RobotSystem p` on the state `(x, ẋ)`, with the law with
compensation of `N`, `F = N(x, ẋ) − K_v ẋ − K_p (x − x_d)` (MLS (4.53) with `ẋ_d ≡ 0`; for the
manipulator the library shows that the bare law (4.51) has `θ_d` as a rest point only where
`N(θ_d, 0) = 0`), whose closed loop is MLS's (4.52):

* the energy identity of the proof in a time-varying form (`Control.hasDerivAt_pdEnergy_along`):
  along any motion whose closed loop `M ẍ + C ẋ + K_v ẋ + K_p (x − x_d) = 0` holds with matrix
  curves `M(s)`, `C(s)`, `M(s)` symmetric and `Ṁ − 2C` skew at `t`, the energy
  `½ ẋᵀ M ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` has derivative `−ẋᵀ K_v ẋ`. The matrices may depend on
  time through coordinates that are not part of the state (MLS p. 301), which is how the workspace
  law is obtained;
* for a robot: `V̇ = −ẋᵀ K_v ẋ` along every closed-loop solution
  (`RobotSystem.hasDerivAlongSolutions_pdEnergy`), stability in the sense of Lyapunov
  (`RobotSystem.stableAt_pdCompensatedTorque`, Theorem 4.4(1)), and, under a solution flow and a
  uniform lower bound on `M`, convergence of every solution and global asymptotic stability
  (`RobotSystem.tendsto_pdCompensatedTorque`,
  `RobotSystem.globallyAsymptoticallyStableAt_pdCompensatedTorque`, Lasalle's principle).

**Hypotheses.** `M(x)` positive definite for every `x` (Mathlib's `PosDef`, which includes
symmetry); `M` continuous; `M` has an entrywise derivative along every motion
(`Control.DifferentiableAlongMotions`; a robot carries no regularity of its own); the skew property
`RobotSystem.HasSkewProperty`; `K_p` symmetric positive definite and `K_v` positive semidefinite
(stability) or positive definite (convergence); for convergence `λ‖v‖² ≤ vᵀ M(x) v` for one `λ > 0`
(MLS p. 191, "uniformly positive definite") and a solution flow of the closed loop
(`Stability.HasFlow`), as in the manipulator case. Exact model cancellation is assumed, as in MLS;
nothing here concerns model error, sampling or actuator limits. State `(x, ẋ) ∈ ℝᵖ × ℝᵖ`, sup norm.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace Control

/-- **An inertia field with an entrywise derivative along every motion (MLS p. 300, the `Ṁ` of the
skew property of a robot):** for every motion `x` with velocity `x'` at `t`, the entries of
`s ↦ M(x(s))` have derivatives at `t`. A hypothesis on a robot's `M(x)`; for a `C¹` field it holds
by the chain rule. Configurations `x ∈ ℝᵖ` (`Fin p → ℝ`), `k × k` matrices. -/
def DifferentiableAlongMotions {p k : ℕ} (M : (Fin p → ℝ) → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ {x : ℝ → Fin p → ℝ} {x' : Fin p → ℝ} {t : ℝ}, HasDerivAt x x' t →
    ∃ Md : Matrix (Fin k) (Fin k) ℝ, ∀ i j, HasDerivAt (fun s => M (x s) i j) (Md i j) t

/-- A skew-symmetric matrix has a vanishing quadratic form, `vᵀ S v = 0` (MLS p. 193). -/
private lemma dotProduct_mulVec_self_eq_zero_of_skew {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : Sᵀ = -S) (v : Fin p → ℝ) : v ⬝ᵥ (S *ᵥ v) = 0 := by
  have h1 : v ⬝ᵥ (Sᵀ *ᵥ v) = v ⬝ᵥ (S *ᵥ v) := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  rw [hS, Matrix.neg_mulVec, dotProduct_neg] at h1
  linarith

/-- **The energy identity of the proof of MLS Proposition 4.9 (p. 193), along a motion, for matrix
curves (MLS p. 301).** Let `K_p` be symmetric, `x` a motion with velocity `x'(t)` at `t` whose
velocity curve `x'` has the derivative `a` at `t`, `M(s)` a matrix curve with entrywise derivative
`Ṁ` at `t` and `M(t)` symmetric, and `C` a matrix with `Ṁ − 2C` skew-symmetric. If the closed loop
(4.52), `M(t) a + C x'(t) + K_v x'(t) + K_p (x(t) − x_d) = 0`, holds at `t`, then
`s ↦ ½ x'(s)ᵀ M(s) x'(s) + ½ (x(s) − x_d)ᵀ K_p (x(s) − x_d)` has the derivative `−x'(t)ᵀ K_v x'(t)`
at `t`. -/
theorem hasDerivAt_pdEnergy_along {p : ℕ} {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.IsSymm)
    (xd : Fin p → ℝ) {x x' : ℝ → Fin p → ℝ} {a : Fin p → ℝ} {Mt : ℝ → Matrix (Fin p) (Fin p) ℝ}
    {Md Ct : Matrix (Fin p) (Fin p) ℝ} {t : ℝ} (hx : HasDerivAt x (x' t) t)
    (hx' : HasDerivAt x' a t) (hM : ∀ i j, HasDerivAt (fun s => Mt s i j) (Md i j) t)
    (hMs : (Mt t).IsSymm) (hskew : (Md - (2 : ℝ) • Ct)ᵀ = -(Md - (2 : ℝ) • Ct))
    (hE : Mt t *ᵥ a + Ct *ᵥ x' t + Kv *ᵥ x' t + Kp *ᵥ (x t - xd) = 0) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * (x' s ⬝ᵥ (Mt s *ᵥ x' s)) +
        (1 / 2 : ℝ) * ((x s - xd) ⬝ᵥ (Kp *ᵥ (x s - xd))))
      (-(x' t ⬝ᵥ (Kv *ᵥ x' t))) t := by
  have hMv : HasDerivAt (fun s => Mt s *ᵥ x' s) (Md *ᵥ x' t + Mt t *ᵥ a) t :=
    Control.hasDerivAt_matrix_mulVec hM hx'
  have hk := Control.hasDerivAt_dotProduct hx' hMv
  have he : HasDerivAt (fun s => x s - xd) (x' t) t := hx.sub_const xd
  have hq := Control.hasDerivAt_dotProduct he (Control.hasDerivAt_mulVec_const Kp he)
  have hsum := (hk.const_mul (1 / 2 : ℝ)).add (hq.const_mul (1 / 2 : ℝ))
  convert hsum using 1
  have hsM := Control.dotProduct_mulVec_comm hMs a (x' t)
  have hsK := Control.dotProduct_mulVec_comm hKp (x t - xd) (x' t)
  have hS := dotProduct_mulVec_self_eq_zero_of_skew hskew (x' t)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at hS
  have h4 : x' t ⬝ᵥ (Mt t *ᵥ a) + x' t ⬝ᵥ (Ct *ᵥ x' t) + x' t ⬝ᵥ (Kv *ᵥ x' t) +
      x' t ⬝ᵥ (Kp *ᵥ (x t - xd)) = 0 := by
    rw [← dotProduct_add, ← dotProduct_add, ← dotProduct_add, hE, dotProduct_zero]
  rw [dotProduct_add, hsM, hsK]
  linarith

namespace RobotSystem

variable {p : ℕ} (R : RobotSystem p)

/-- **PD set-point control with compensation of `N` for a robot (MLS eq. (4.53), p. 194, with
`ẋ_d ≡ 0`; MLS p. 301 for robots):** `F = N(x, ẋ) − K_v ẋ − K_p (x − x_d)`, as a feedback law
`u(t, x, ẋ)` for a constant set point `x_d`. Under it the closed loop is MLS's (4.52). -/
def pdCompensatedTorque (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd : Fin p → ℝ) :
    ℝ → (Fin p → ℝ) → (Fin p → ℝ) → Fin p → ℝ :=
  fun _ q v => R.N q v - Kv *ᵥ v - Kp *ᵥ (q - xd)

/-- **The Lyapunov function of the proof of MLS Proposition 4.9 (p. 193) for a robot:**
`V(x, ẋ) = ½ ẋᵀ M(x) ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` (MLS shifts to `x_d = 0`). -/
def pdEnergy (Kp : Matrix (Fin p) (Fin p) ℝ) (xd q v : Fin p → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (v ⬝ᵥ (R.M q *ᵥ v)) + (1 / 2 : ℝ) * ((q - xd) ⬝ᵥ (Kp *ᵥ (q - xd)))

/-- **The closed loop (4.52) of MLS p. 193 for a robot, as an autonomous field** on the state
`(x, ẋ)`: the robot's first-order system under PD control with compensation of `N`, which does not
depend on time. -/
def pdClosedLoop (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd : Fin p → ℝ) :
    (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ) :=
  R.field (R.pdCompensatedTorque Kp Kv xd) 0

/-- The robot's closed loop under compensated PD is autonomous (MLS eq. (4.46), p. 188). -/
theorem field_pdCompensatedTorque (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd : Fin p → ℝ) :
    R.field (R.pdCompensatedTorque Kp Kv xd) = fun _ => R.pdClosedLoop Kp Kv xd :=
  rfl

/-- **The closed loop is MLS's (4.52), p. 193, for a robot:**
`ẍ = M(x)⁻¹(−K_v ẋ − K_p (x − x_d) − C(x, ẋ) ẋ)`; the compensation cancels `N`. -/
theorem pdClosedLoop_apply (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd q v : Fin p → ℝ) :
    R.pdClosedLoop Kp Kv xd (q, v) =
      (v, (R.M q)⁻¹ *ᵥ (-(Kv *ᵥ v) - Kp *ᵥ (q - xd) - R.C q v *ᵥ v)) := by
  simp only [pdClosedLoop, field, pdCompensatedTorque, Prod.mk.injEq, true_and]
  congr 1
  abel

/-- **The set point is an equilibrium (MLS p. 193):** `(x_d, 0)` is an equilibrium of the robot
under PD control with compensation of `N`, for all gains. -/
theorem isEquilibrium_pdCompensatedTorque (Kp Kv : Matrix (Fin p) (Fin p) ℝ) (xd : Fin p → ℝ) :
    Stability.IsEquilibrium (R.field (R.pdCompensatedTorque Kp Kv xd)) (xd, 0) := by
  intro t
  simp [field, pdCompensatedTorque]

/-- **`V̇ = −ẋᵀ K_v ẋ` along every solution of the closed loop (MLS p. 193, for a robot, p. 301).**
With `M(x)` positive definite for every `x`, `M` differentiable along motions, the skew property and
`K_p` symmetric, `V = ½ ẋᵀ M ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` has the derivative `−ẋᵀ K_v ẋ` along
the solutions of (4.52), on the whole state space. -/
theorem hasDerivAlongSolutions_pdEnergy (hM : ∀ q, (R.M q).PosDef)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    {Kp : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.IsSymm) (Kv : Matrix (Fin p) (Fin p) ℝ)
    (xd : Fin p → ℝ) :
    Stability.HasDerivAlongSolutions (R.field (R.pdCompensatedTorque Kp Kv xd))
      (fun _ z => R.pdEnergy Kp xd z.1 z.2) (fun _ z => -(z.2 ⬝ᵥ (Kv *ᵥ z.2))) univ := by
  intro s₀ _ z hz t ht _
  obtain ⟨h1, h2⟩ := R.equations_of_isSolution hM hz ht
  obtain ⟨Md, hMd'⟩ := hMd h1
  have hE : R.M (z t).1 *ᵥ (R.field (R.pdCompensatedTorque Kp Kv xd) t (z t)).2 +
      R.C (z t).1 (z t).2 *ᵥ (z t).2 + Kv *ᵥ (z t).2 + Kp *ᵥ ((z t).1 - xd) = 0 := by
    calc _ = (R.M (z t).1 *ᵥ (R.field (R.pdCompensatedTorque Kp Kv xd) t (z t)).2 +
          R.C (z t).1 (z t).2 *ᵥ (z t).2 + R.N (z t).1 (z t).2) -
          R.pdCompensatedTorque Kp Kv xd t (z t).1 (z t).2 := by
          simp only [pdCompensatedTorque]
          abel
      _ = 0 := by rw [h2, sub_self]
  exact hasDerivAt_pdEnergy_along hKp xd h1 (hz.2 t ht).snd hMd' (hM _).isHermitian.isSymm
    (hskew h1 hMd') hE

/-- The Lyapunov function `V = ½ ẋᵀ M ẋ + ½ (x − x_d)ᵀ K_p (x − x_d)` of MLS p. 193 is continuous on
the state space `(x, ẋ)` when `M` is continuous. -/
theorem continuous_pdEnergy (hMc : Continuous R.M) (Kp : Matrix (Fin p) (Fin p) ℝ)
    (xd : Fin p → ℝ) :
    Continuous fun z : (Fin p → ℝ) × (Fin p → ℝ) => R.pdEnergy Kp xd z.1 z.2 := by
  have he : Continuous fun z : (Fin p → ℝ) × (Fin p → ℝ) => z.1 - xd :=
    continuous_fst.sub continuous_const
  simp only [pdEnergy]
  exact (continuous_const.mul (continuous_snd.dotProduct
    ((hMc.comp continuous_fst).matrix_mulVec continuous_snd))).add
    (continuous_const.mul (he.dotProduct (continuous_const.matrix_mulVec he)))

/-- **MLS Proposition 4.9 (p. 193), stability part, for every robot (MLS p. 301).** With `M(x)`
positive definite for every `x`, `M` continuous and differentiable along motions, the skew property,
`K_p` symmetric positive definite and `K_v` positive semidefinite, the set point `(x_d, 0)` of the
closed loop (4.52) is stable in the sense of Lyapunov (Definition 4.1) at every initial time
`t₀ ≥ 0`. Proof: Theorem 4.4(1) with `V`, locally positive definite by compactness, and
`V̇ = −ẋᵀ K_v ẋ ≤ 0`. -/
theorem stableAt_pdCompensatedTorque (hM : ∀ q, (R.M q).PosDef) (hMc : Continuous R.M)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosSemidef) (xd : Fin p → ℝ)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.StableAt (R.field (R.pdCompensatedTorque Kp Kv xd)) (xd, 0) t₀ := by
  rw [← Stability.stableAt_shift_iff]
  obtain ⟨aM, haM, hMb⟩ := QuadraticBounds.exists_pos_mul_sq_norm_le_dotProduct_mulVec
    (isCompact_closedBall xd 1) hMc fun q _ => hM q
  obtain ⟨ap, hap, hpb⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKp
  set a := min aM ap / 2 with ha
  have ha0 : 0 < a := by positivity
  refine Stability.stableAt_of_lyapunov (V := fun _ z => R.pdEnergy Kp xd (z.1 + xd) z.2)
    (Vdot := fun _ z => -(z.2 ⬝ᵥ (Kv *ᵥ z.2))) (r := 1) ?_ one_pos ?_ ?_ ht₀
  · refine ⟨?_, 1, one_pos, fun r => a * r ^ 2, Stability.isClassK_mul_sq ha0, fun t _ => ⟨?_, ?_⟩⟩
    · refine Continuous.continuousOn ?_
      have hq : Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => z.2.1 + xd :=
        (continuous_fst.comp continuous_snd).add continuous_const
      have hv : Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => z.2.2 :=
        continuous_snd.comp continuous_snd
      have he : Continuous fun z : ℝ × (Fin p → ℝ) × (Fin p → ℝ) => z.2.1 + xd - xd :=
        hq.sub continuous_const
      simp only [pdEnergy]
      exact (continuous_const.mul (hv.dotProduct ((hMc.comp hq).matrix_mulVec hv))).add
        (continuous_const.mul (he.dotProduct (continuous_const.matrix_mulVec he)))
    · simp [pdEnergy]
    · intro z hz
      have h1 : ‖z.1‖ < 1 := (norm_fst_le z).trans_lt hz
      have hmem : z.1 + xd ∈ Metric.closedBall xd 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        exact h1.le
      have hMz := hMb _ hmem z.2
      have hpz := hpb z.1
      have hsq := Control.sq_norm_prod_le z
      have hmin1 : min aM ap ≤ aM := min_le_left _ _
      have hmin2 : min aM ap ≤ ap := min_le_right _ _
      simp only [pdEnergy, add_sub_cancel_right]
      have hn1 := sq_nonneg ‖z.1‖
      have hn2 := sq_nonneg ‖z.2‖
      nlinarith [mul_le_mul_of_nonneg_right hmin1 hn2, mul_le_mul_of_nonneg_right hmin2 hn1]
  · intro s₀ hs₀ z hz t ht _
    have hx : Stability.IsSolution (R.field (R.pdCompensatedTorque Kp Kv xd)) s₀
        (fun s => z s + (xd, 0)) :=
      (Stability.isSolution_shift_iff (xe := (xd, 0))).mp (by simpa using hz)
    have key := R.hasDerivAlongSolutions_pdEnergy hM hMd hskew hKp.isHermitian.isSymm Kv xd s₀
      hs₀ _ hx t ht (mem_univ _)
    convert key using 1
    · funext s
      simp
    · simp
  · intro t _ y _
    have := hKv.dotProduct_mulVec_nonneg y.2
    simp only [star_trivial] at this
    linarith

/-- The sublevel sets of `V` are bounded: `a ‖(x, ẋ) − (x_d, 0)‖² ≤ V(x, ẋ)` (MLS pp. 191, 193). -/
private lemma exists_pos_mul_sq_norm_le_pdEnergy
    (hMu : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    {Kp : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (xd : Fin p → ℝ) :
    ∃ a > 0, ∀ z : (Fin p → ℝ) × (Fin p → ℝ), a * ‖z - (xd, 0)‖ ^ 2 ≤ R.pdEnergy Kp xd z.1 z.2 := by
  obtain ⟨lam, hlam, hMb⟩ := hMu
  obtain ⟨ap, hap, hpb⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKp
  refine ⟨min lam ap / 2, by positivity, fun z => ?_⟩
  have hsq := Control.sq_norm_prod_le (z - (xd, 0))
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at hsq
  have h1 := hMb z.1 z.2
  have h2 := hpb (z.1 - xd)
  have hmin1 : min lam ap ≤ lam := min_le_left _ _
  have hmin2 : min lam ap ≤ ap := min_le_right _ _
  have hn1 := sq_nonneg ‖z.1 - xd‖
  have hn2 := sq_nonneg ‖z.2‖
  simp only [pdEnergy]
  have hm0 : 0 ≤ min lam ap := le_min hlam.le hap.le
  have h3 : min lam ap * ‖z - (xd, 0)‖ ^ 2 ≤
      min lam ap * ‖z.1 - xd‖ ^ 2 + min lam ap * ‖z.2‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hm0]
  nlinarith [mul_le_mul_of_nonneg_right hmin1 hn2, mul_le_mul_of_nonneg_right hmin2 hn1]

/-- **The sublevel sets `Ω_c = {V ≤ c}` are compact (MLS Theorem 4.7's hypothesis, p. 188, for the
proof of Proposition 4.9, p. 194, for a robot)**, for `M` continuous and uniformly positive definite
(`λ‖v‖² ≤ vᵀ M(x) v`, MLS p. 191) and `K_p` positive definite. -/
theorem isCompact_pdEnergy_sublevel (hMc : Continuous R.M)
    (hMu : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    {Kp : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (xd : Fin p → ℝ) (c : ℝ) :
    IsCompact {z : (Fin p → ℝ) × (Fin p → ℝ) | R.pdEnergy Kp xd z.1 z.2 ≤ c} := by
  obtain ⟨a, ha, hb⟩ := R.exists_pos_mul_sq_norm_le_pdEnergy hMu hKp xd
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (R.continuous_pdEnergy hMc Kp xd) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (xd, (0 : Fin p → ℝ))) (r := max 1 (c / a))).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 := hb z
  have hz' : R.pdEnergy Kp xd z.1 z.2 ≤ c := hz
  have h2 : ‖z - (xd, 0)‖ ^ 2 ≤ c / a := by
    rw [le_div_iff₀ ha]
    linarith
  by_contra hcon
  push Not at hcon
  have h3 : 1 < ‖z - (xd, 0)‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have h4 : c / a < ‖z - (xd, 0)‖ := lt_of_le_of_lt (le_max_right _ _) hcon
  nlinarith

/-- A positive definite matrix has no nonzero isotropic vector (MLS p. 194). -/
private lemma eq_zero_of_dotProduct_mulVec_eq_zero {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.PosDef)
    {v : Fin p → ℝ} (hv : v ⬝ᵥ (A *ᵥ v) = 0) : v = 0 := by
  by_contra hne
  have := hA.dotProduct_mulVec_pos hne
  simp only [star_trivial] at this
  linarith

/-- **The invariant-set step of the proof of MLS Proposition 4.9 (p. 194), for a robot.** With
`M(x)` positive definite for every `x`, `K_p` and `K_v` positive definite and a flow `φ` of the
closed loop (4.52), the largest invariant set inside `{(x, ẋ) : V ≤ c, −ẋᵀ K_v ẋ = 0}` is contained
in `{(x_d, 0)}`: a trajectory with `ẋ ≡ 0` has `ẍ = 0`, so (4.52) gives `K_p (x − x_d) = 0`. -/
theorem largestInvariantSubset_pdClosedLoop_subset (hM : ∀ q, (R.M q).PosDef)
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {xd : Fin p → ℝ}
    {φ : ℝ → (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ)}
    (hφ : Stability.HasFlow (R.pdClosedLoop Kp Kv xd) φ) (c : ℝ) :
    Stability.largestInvariantSubset φ
        {z | R.pdEnergy Kp xd z.1 z.2 ≤ c ∧ -(z.2 ⬝ᵥ (Kv *ᵥ z.2)) = 0} ⊆ {(xd, 0)} := by
  intro y hy
  rw [Stability.mem_largestInvariantSubset_iff hφ] at hy
  have hv : ∀ t, 0 ≤ t → (φ t y).2 = 0 := by
    intro t ht
    have := (hy t ht).2
    exact eq_zero_of_dotProduct_mulVec_eq_zero hKv (by linarith)
  have hpos : ∀ t, 0 < t → φ t y = (xd, 0) := by
    intro t ht
    have hd : HasDerivAt (fun s => (φ s y).2) (R.pdClosedLoop Kp Kv xd (φ t y)).2 t :=
      ((hφ.isSolution y).2 t ht).snd
    have hconst : (fun s => (φ s y).2) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hv s (le_of_lt hs)
    have h0 := hd.unique ((hasDerivAt_const t (0 : Fin p → ℝ)).congr_of_eventuallyEq hconst)
    have hpair : φ t y = ((φ t y).1, 0) := Prod.ext rfl (hv t ht.le)
    rw [hpair, pdClosedLoop_apply] at h0
    simp only [Matrix.mulVec_zero, neg_zero, zero_sub, sub_zero] at h0
    have h1 := Control.PosDef.mulVec_inv_mulVec (hM (φ t y).1) (-(Kp *ᵥ ((φ t y).1 - xd)))
    rw [h0, Matrix.mulVec_zero] at h1
    have h2 : Kp *ᵥ ((φ t y).1 - xd) = 0 := by
      have := congrArg Neg.neg h1
      simpa using this.symm
    have h3 : (φ t y).1 - xd = 0 :=
      eq_zero_of_dotProduct_mulVec_eq_zero hKp (by rw [h2, dotProduct_zero])
    rw [hpair, sub_eq_zero.mp h3]
  have htraj : Tendsto (fun t => φ t y) (𝓝[>] 0) (𝓝 y) := by
    have := ((hφ.continuousOn_trajectory y) 0 self_mem_Ici).mono
      (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
    simpa [hφ.map_zero] using this.tendsto
  have hlim : Tendsto (fun t => φ t y) (𝓝[>] 0) (𝓝 (xd, 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpos t ht).symm
  exact tendsto_nhds_unique htraj hlim

/-- **MLS Proposition 4.9 (p. 193), convergence, for every robot (MLS p. 301).** With `M(x)`
positive definite for every `x`, continuous, differentiable along motions and uniformly positive
definite (`λ‖v‖² ≤ vᵀ M(x) v`), the skew property, `K_p`, `K_v` positive definite and a flow `φ` of
the closed loop (4.52), every solution of the closed loop from `t₀ ≥ 0`, from any initial state,
tends to `(x_d, 0)`. Proof: Lasalle's principle (Theorem 4.7) on `Ω_c = {V ≤ c}`,
`c = V(x(t₀)) + 1`. -/
theorem tendsto_pdCompensatedTorque (hM : ∀ q, (R.M q).PosDef) (hMc : Continuous R.M)
    (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    (hMu : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {xd : Fin p → ℝ}
    {φ : ℝ → (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ)}
    (hφ : Stability.HasFlow (R.pdClosedLoop Kp Kv xd) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin p → ℝ) × (Fin p → ℝ)}
    (hx : Stability.IsSolution (R.field (R.pdCompensatedTorque Kp Kv xd)) t₀ x) :
    Tendsto x atTop (𝓝 (xd, 0)) := by
  set c := R.pdEnergy Kp xd (x t₀).1 (x t₀).2 + 1 with hc
  have hVdot := R.hasDerivAlongSolutions_pdEnergy hM hMd hskew hKp.isHermitian.isSymm Kv xd
  rw [field_pdCompensatedTorque] at hVdot hx
  have hVdotc : Continuous fun z : (Fin p → ℝ) × (Fin p → ℝ) => -(z.2 ⬝ᵥ (Kv *ᵥ z.2)) :=
    (continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)).neg
  have hneg : ∀ z : (Fin p → ℝ) × (Fin p → ℝ), R.pdEnergy Kp xd z.1 z.2 ≤ c →
      -(z.2 ⬝ᵥ (Kv *ᵥ z.2)) ≤ 0 := by
    intro z _
    have := hKv.posSemidef.dotProduct_mulVec_nonneg z.2
    simp only [star_trivial] at this
    linarith
  refine tendsto_nhds.mpr fun U hU hmem => ?_
  exact Stability.lasalle_isSolution hφ (R.continuous_pdEnergy hMc Kp xd)
    (R.isCompact_pdEnergy_sublevel hMc hMu hKp xd c) (hVdot.mono (subset_univ _))
    hVdotc.continuousOn hneg ht₀ hx (by rw [hc]; linarith) hU
    ((R.largestInvariantSubset_pdClosedLoop_subset hM hKp hKv hφ c).trans
      (singleton_subset_iff.mpr hmem))

/-- **MLS Proposition 4.9 (p. 193): global asymptotic stability for every robot (MLS p. 301), for PD
control with compensation of `N`.** Under the hypotheses of `tendsto_pdCompensatedTorque`, the set
point `(x_d, 0)` of the closed loop (4.52) is globally asymptotically stable at every initial time
`t₀ ≥ 0`: stable (Theorem 4.4(1)) and attracting every solution. -/
theorem globallyAsymptoticallyStableAt_pdCompensatedTorque (hM : ∀ q, (R.M q).PosDef)
    (hMc : Continuous R.M) (hMd : DifferentiableAlongMotions R.M) (hskew : R.HasSkewProperty)
    (hMu : ∃ lam > 0, ∀ q v : Fin p → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (R.M q *ᵥ v))
    {Kp Kv : Matrix (Fin p) (Fin p) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {xd : Fin p → ℝ}
    {φ : ℝ → (Fin p → ℝ) × (Fin p → ℝ) → (Fin p → ℝ) × (Fin p → ℝ)}
    (hφ : Stability.HasFlow (R.pdClosedLoop Kp Kv xd) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt (R.field (R.pdCompensatedTorque Kp Kv xd))
      (xd, 0) t₀ := by
  exact ⟨R.stableAt_pdCompensatedTorque hM hMc hMd hskew hKp hKv.posSemidef xd ht₀,
    fun _ hx => R.tendsto_pdCompensatedTorque hM hMc hMd hskew hMu hKp hKv hφ ht₀ hx⟩

end RobotSystem
end Control
end RoboLean
