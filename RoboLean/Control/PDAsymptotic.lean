import RoboLean.Control.PDControl
import RoboLean.Control.LaSalle
import RoboLean.Control.StabilityTheorems

/-!
# Asymptotic stability of PD set-point control (MLS Proposition 4.9, pp. 193–194)

**What MLS prints (read this session).** Proposition 4.9 (p. 193): "If `θ̇_d ≡ 0` and
`K_v, K_p > 0`, the control law (4.51) applied to the system (4.47) renders the equilibrium point
`θ = θ_d` globally asymptotically stable." After `V̇ = −θ̇ᵀ K_v θ̇` the proof continues (p. 194):
"To check for asymptotic stability, we appeal to Lasalle's principle. The set `S` for which
`V̇ ≡ 0` is given by `S = {(θ, θ̇) : θ̇ ≡ 0}`. To find the largest invariant set contained in `S`,
we substitute `θ̇ ≡ 0` into the closed loop equations 4.52. This gives `K_p θ = 0` (recalling that
`θ_d = 0`) and since `K_p` is positive definite, it follows that the largest invariant set
contained within `S` is the single point `θ = 0`." Computed torque (p. 191) uses that `M(θ)` is
"uniformly positive definite in `θ`".

**Formalized** for the law with compensation of `N` (E016: the bare law (4.51) has `θ_d` as a
rest point only where `N(θ_d, 0) = 0`), whose closed loop is (4.52) (`pdClosedLoop_apply`), under:

* symmetric link inertias and `M(q)` positive definite for every `q` (as in E016);
* `M` uniformly positive definite: `λ‖v‖² ≤ vᵀ M(q) v` for one `λ > 0` and all `q, v` (MLS
  p. 191's phrase, used for computed torque; here it makes the sublevel sets of
  `V = ½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e` bounded, hence compact, which Lasalle's principle needs);
* `K_p`, `K_v` positive definite (Mathlib's `PosDef`, which includes symmetry);
* a solution flow of the closed loop (`Stability.HasFlow`, the interface of `SolutionFlow`):
  existence of solutions for all forward time, uniqueness and continuous dependence. This is a
  hypothesis in general: deriving it needs local Lipschitz bounds on `M(q)⁻¹` and on `C(q, v)`
  (built from the first derivatives of `M`, so a second-order bound on `M`) and an extension of
  Mathlib's local Picard–Lindelöf solutions to all forward time, none of which is in the library.
  For constant inertia the closed loop is linear and the flow is constructed
  (`hasFlow_pdClosedLoop_of_const`), so the theorem holds with no flow hypothesis
  (`globallyAsymptoticallyStableAt_pdCompensatedTorque_of_const`).

Proved: every closed-loop solution tends to `(θ_d, 0)` (`tendsto_pdCompensatedTorque`), and
`(θ_d, 0)` is globally asymptotically stable at every `t₀ ≥ 0`
(`globallyAsymptoticallyStableAt_pdCompensatedTorque`), hence asymptotically stable
(`asymptoticallyStableAt_pdCompensatedTorque`), the printed conclusion for (4.52). The
invariant-set step is `largestInvariantSubset_pdClosedLoop_subset`.
-/

noncomputable section

open Matrix Filter Topology Set

namespace RoboLean
namespace ManipulatorModel

variable {n : ℕ} (P : ManipulatorModel n)

/-- **The closed loop (4.52) of MLS p. 193 as an autonomous field:** the system (4.47) under
PD control with compensation of `N`, `τ = N(θ, θ̇) − K_v θ̇ − K_p (θ − θ_d)`, on the state
`(θ, θ̇)`. The feedback law does not depend on time, so the field is `field u` at any time. -/
def pdClosedLoop (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  P.field (P.pdCompensatedTorque Kp Kv θd) 0

/-- The closed-loop field under compensated PD is autonomous (MLS eq. (4.46), p. 188). -/
theorem field_pdCompensatedTorque (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    P.field (P.pdCompensatedTorque Kp Kv θd) = fun _ => P.pdClosedLoop Kp Kv θd :=
  rfl

/-- **The closed loop is MLS's (4.52), p. 193:** `θ̈ = M(θ)⁻¹(−K_v θ̇ − K_p(θ − θ_d) − C(θ, θ̇)θ̇)`;
the compensation cancels `N`. -/
theorem pdClosedLoop_apply (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd q v : Fin n → ℝ) :
    P.pdClosedLoop Kp Kv θd (q, v) =
      (v, (P.M q)⁻¹ *ᵥ (-(Kv *ᵥ v) - Kp *ᵥ (q - θd) - P.C q v *ᵥ v)) := by
  simp only [pdClosedLoop, field, pdCompensatedTorque, Prod.mk.injEq, true_and]
  congr 1
  abel

/-- The Lyapunov function of the proof of MLS Proposition 4.9 (p. 193),
`V(θ, θ̇) = ½ θ̇ᵀ M(θ) θ̇ + ½ eᵀ K_p e`, is continuous on the state space `(θ, θ̇)`. -/
theorem continuous_pdEnergy (Kp : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    Continuous fun z : (Fin n → ℝ) × (Fin n → ℝ) => P.pdEnergy Kp θd z.1 z.2 := by
  have he : Continuous fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1 - θd :=
    continuous_fst.sub continuous_const
  simp only [pdEnergy, InertialChain.kineticEnergy]
  exact (continuous_const.mul (continuous_snd.dotProduct
    ((P.continuous_M.comp continuous_fst).matrix_mulVec continuous_snd))).add
    (continuous_const.mul (he.dotProduct (continuous_const.matrix_mulVec he)))

/-- **`V̇ = −θ̇ᵀ K_v θ̇` along every solution of the closed loop (MLS p. 193).** With symmetric
link inertias, `M(q)` positive definite for every `q` and `K_p` symmetric, the energy
`V = ½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e` has the derivative `−θ̇ᵀ K_v θ̇` along the solutions of (4.52), on the
whole state space. -/
theorem hasDerivAlongSolutions_pdEnergy (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef) {Kp : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.IsSymm)
    (Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    Stability.HasDerivAlongSolutions (P.field (P.pdCompensatedTorque Kp Kv θd))
      (fun _ z => P.pdEnergy Kp θd z.1 z.2) (fun _ z => -(z.2 ⬝ᵥ (Kv *ᵥ z.2))) univ := by
  intro s₀ _ x hx t ht _
  have hE := P.equationsOfMotionAt_of_isSolution h hM hx ht
  exact P.hasDerivAt_pdEnergy h hKp θd (P.eventually_hasDerivAt_fst hx ht) (hx.2 t ht).snd hE

/-- **The sublevel sets of `V` are bounded (MLS pp. 191, 193).** If `M` is uniformly positive
definite (`λ‖v‖² ≤ vᵀ M(q) v`) and `K_p` is positive definite, then
`a ‖(θ, θ̇) − (θ_d, 0)‖² ≤ V(θ, θ̇)` for some `a > 0` (sup norm on the state). -/
theorem exists_pos_mul_sq_norm_le_pdEnergy
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (θd : Fin n → ℝ) :
    ∃ a > 0, ∀ z : (Fin n → ℝ) × (Fin n → ℝ), a * ‖z - (θd, 0)‖ ^ 2 ≤ P.pdEnergy Kp θd z.1 z.2 := by
  obtain ⟨lam, hlam, hMb⟩ := hMu
  obtain ⟨ap, hap, hpb⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hKp
  refine ⟨min lam ap / 2, by positivity, fun z => ?_⟩
  have hsq := Control.sq_norm_prod_le (z - (θd, 0))
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero] at hsq
  have h1 := hMb z.1 z.2
  have h2 := hpb (z.1 - θd)
  have hmin1 : min lam ap ≤ lam := min_le_left _ _
  have hmin2 : min lam ap ≤ ap := min_le_right _ _
  have hn1 := sq_nonneg ‖z.1 - θd‖
  have hn2 := sq_nonneg ‖z.2‖
  simp only [pdEnergy, InertialChain.kineticEnergy]
  have hP : P.chain.massMatrix z.1 = P.M z.1 := rfl
  rw [hP]
  have hm0 : 0 ≤ min lam ap := le_min hlam.le hap.le
  have h3 : min lam ap * ‖z - (θd, 0)‖ ^ 2 ≤
      min lam ap * ‖z.1 - θd‖ ^ 2 + min lam ap * ‖z.2‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hm0]
  nlinarith [mul_le_mul_of_nonneg_right hmin1 hn2, mul_le_mul_of_nonneg_right hmin2 hn1]

/-- **The sublevel sets `Ω_c = {V ≤ c}` are compact (MLS Theorem 4.7's hypothesis, p. 188, for
the proof of Proposition 4.9, p. 194)**, for `M` uniformly positive definite and `K_p` positive
definite: they are closed and bounded in the finite-dimensional state space. -/
theorem isCompact_pdEnergy_sublevel
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (θd : Fin n → ℝ) (c : ℝ) :
    IsCompact {z : (Fin n → ℝ) × (Fin n → ℝ) | P.pdEnergy Kp θd z.1 z.2 ≤ c} := by
  obtain ⟨a, ha, hb⟩ := P.exists_pos_mul_sq_norm_le_pdEnergy hMu hKp θd
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (P.continuous_pdEnergy Kp θd) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (θd, (0 : Fin n → ℝ))) (r := max 1 (c / a))).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 := hb z
  have hz' : P.pdEnergy Kp θd z.1 z.2 ≤ c := hz
  have h2 : ‖z - (θd, 0)‖ ^ 2 ≤ c / a := by
    rw [le_div_iff₀ ha]
    linarith
  by_contra hcon
  push Not at hcon
  have h3 : 1 < ‖z - (θd, 0)‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have h4 : c / a < ‖z - (θd, 0)‖ := lt_of_le_of_lt (le_max_right _ _) hcon
  nlinarith

/-- A positive definite matrix has no nonzero isotropic vector. -/
private lemma eq_zero_of_dotProduct_mulVec_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {v : Fin n → ℝ} (hv : v ⬝ᵥ (A *ᵥ v) = 0) : v = 0 := by
  by_contra hne
  have := hA.dotProduct_mulVec_pos hne
  simp only [star_trivial] at this
  linarith

/-- **The invariant-set step of the proof of MLS Proposition 4.9 (p. 194).** With `M(q)` positive
definite for every `q`, `K_p` and `K_v` positive definite and a flow `φ` of the closed loop (4.52),
the largest invariant set inside `S = {(θ, θ̇) ∈ Ω_c : V̇ = −θ̇ᵀ K_v θ̇ = 0}` is contained in
`{(θ_d, 0)}`: a trajectory along which `θ̇ ≡ 0` has `θ̈ = 0`, so (4.52) gives `K_p(θ − θ_d) = 0`,
so `θ = θ_d`. -/
theorem largestInvariantSubset_pdClosedLoop_subset (hM : ∀ q, (P.M q).PosDef)
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {θd : Fin n → ℝ}
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.pdClosedLoop Kp Kv θd) φ) (c : ℝ) :
    Stability.largestInvariantSubset φ
        {z | P.pdEnergy Kp θd z.1 z.2 ≤ c ∧ -(z.2 ⬝ᵥ (Kv *ᵥ z.2)) = 0} ⊆ {(θd, 0)} := by
  intro y hy
  rw [Stability.mem_largestInvariantSubset_iff hφ] at hy
  have hv : ∀ t, 0 ≤ t → (φ t y).2 = 0 := by
    intro t ht
    have := (hy t ht).2
    exact eq_zero_of_dotProduct_mulVec_eq_zero hKv (by linarith)
  have hpos : ∀ t, 0 < t → φ t y = (θd, 0) := by
    intro t ht
    have hd : HasDerivAt (fun s => (φ s y).2) (P.pdClosedLoop Kp Kv θd (φ t y)).2 t :=
      ((hφ.isSolution y).2 t ht).snd
    have hconst : (fun s => (φ s y).2) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hv s (le_of_lt hs)
    have h0 := hd.unique ((hasDerivAt_const t (0 : Fin n → ℝ)).congr_of_eventuallyEq hconst)
    have hpair : φ t y = ((φ t y).1, 0) := Prod.ext rfl (hv t ht.le)
    rw [hpair, pdClosedLoop_apply] at h0
    simp only [Matrix.mulVec_zero, neg_zero, zero_sub, sub_zero] at h0
    have h1 := Control.PosDef.mulVec_inv_mulVec (hM (φ t y).1) (-(Kp *ᵥ ((φ t y).1 - θd)))
    rw [h0, Matrix.mulVec_zero] at h1
    have h2 : Kp *ᵥ ((φ t y).1 - θd) = 0 := by
      have := congrArg Neg.neg h1
      simpa using this.symm
    have h3 : (φ t y).1 - θd = 0 :=
      eq_zero_of_dotProduct_mulVec_eq_zero hKp (by rw [h2, dotProduct_zero])
    rw [hpair, sub_eq_zero.mp h3]
  have htraj : Tendsto (fun t => φ t y) (𝓝[>] 0) (𝓝 y) := by
    have := ((hφ.continuousOn_trajectory y) 0 self_mem_Ici).mono
      (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
    simpa [hφ.map_zero] using this.tendsto
  have hlim : Tendsto (fun t => φ t y) (𝓝[>] 0) (𝓝 (θd, 0)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpos t ht).symm
  exact tendsto_nhds_unique htraj hlim

/-- **MLS Proposition 4.9 (p. 193), convergence, for PD control with compensation of `N`.** With
symmetric link inertias, `M(q)` positive definite for every `q` and uniformly positive definite
(`λ‖v‖² ≤ vᵀ M(q) v`), `K_p`, `K_v` positive definite, and a flow `φ` of the closed loop (4.52),
every solution of the closed loop from `t₀ ≥ 0`, from any initial state, tends to `(θ_d, 0)`.
Proof: Lasalle's principle (Theorem 4.7) on `Ω_c = {V ≤ c}`, `c = V(x(t₀)) + 1`. -/
theorem tendsto_pdCompensatedTorque (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {θd : Fin n → ℝ}
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.pdClosedLoop Kp Kv θd) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {x : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : Stability.IsSolution (P.field (P.pdCompensatedTorque Kp Kv θd)) t₀ x) :
    Tendsto x atTop (𝓝 (θd, 0)) := by
  set c := P.pdEnergy Kp θd (x t₀).1 (x t₀).2 + 1 with hc
  have hVdot := P.hasDerivAlongSolutions_pdEnergy h hM hKp.isHermitian.isSymm Kv θd
  rw [field_pdCompensatedTorque] at hVdot hx
  have hVdotc : Continuous fun z : (Fin n → ℝ) × (Fin n → ℝ) => -(z.2 ⬝ᵥ (Kv *ᵥ z.2)) :=
    (continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)).neg
  have hneg : ∀ z : (Fin n → ℝ) × (Fin n → ℝ), P.pdEnergy Kp θd z.1 z.2 ≤ c →
      -(z.2 ⬝ᵥ (Kv *ᵥ z.2)) ≤ 0 := by
    intro z _
    have := hKv.posSemidef.dotProduct_mulVec_nonneg z.2
    simp only [star_trivial] at this
    linarith
  refine tendsto_nhds.mpr fun U hU hmem => ?_
  exact Stability.lasalle_isSolution hφ (P.continuous_pdEnergy Kp θd)
    (P.isCompact_pdEnergy_sublevel hMu hKp θd c) (hVdot.mono (subset_univ _))
    hVdotc.continuousOn hneg ht₀ hx (by rw [hc]; linarith) hU
    ((P.largestInvariantSubset_pdClosedLoop_subset hM hKp hKv hφ c).trans
      (singleton_subset_iff.mpr hmem))

/-- **MLS Proposition 4.9 (p. 193): global asymptotic stability, for PD control with
compensation of `N`.** Under the hypotheses of `tendsto_pdCompensatedTorque`, the set point
`(θ_d, 0)` of the closed loop (4.52) is globally asymptotically stable at every initial time
`t₀ ≥ 0`: stable (Theorem 4.4(1), E016) and attracting every solution. -/
theorem globallyAsymptoticallyStableAt_pdCompensatedTorque (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {θd : Fin n → ℝ}
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.pdClosedLoop Kp Kv θd) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt (P.field (P.pdCompensatedTorque Kp Kv θd))
      (θd, 0) t₀ :=
  ⟨P.stableAt_pdCompensatedTorque h hM hKp hKv.posSemidef θd ht₀,
    fun _ hx => P.tendsto_pdCompensatedTorque h hM hMu hKp hKv hφ ht₀ hx⟩

/-- **MLS Proposition 4.9 (p. 193): asymptotic stability (Definition 4.2), for PD control with
compensation of `N`,** at every initial time `t₀ ≥ 0`, under the hypotheses of
`tendsto_pdCompensatedTorque`. -/
theorem asymptoticallyStableAt_pdCompensatedTorque (h : ∀ k, (P.chain.linkInertia k).IsSymm)
    (hM : ∀ q, (P.M q).PosDef)
    (hMu : ∃ lam > 0, ∀ q v : Fin n → ℝ, lam * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P.M q *ᵥ v))
    {Kp Kv : Matrix (Fin n) (Fin n) ℝ} (hKp : Kp.PosDef) (hKv : Kv.PosDef) {θd : Fin n → ℝ}
    {φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hφ : Stability.HasFlow (P.pdClosedLoop Kp Kv θd) φ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.AsymptoticallyStableAt (P.field (P.pdCompensatedTorque Kp Kv θd)) (θd, 0) t₀ :=
  (P.globallyAsymptoticallyStableAt_pdCompensatedTorque h hM hMu hKp hKv hφ
    ht₀).asymptoticallyStableAt

/-! ### Manipulators with constant inertia: the flow exists -/

/-- The matrix–vector product `v ↦ A v` as a continuous linear map on `ℝⁿ`. -/
private def mulVecCLM (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

private lemma mulVecCLM_apply (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    mulVecCLM A v = A *ᵥ v := by
  simp [mulVecCLM]

/-- **The linear closed loop of PD control for a constant inertia matrix `M₀`** (MLS (4.52),
p. 193, with `C = 0`): `(e, θ̇) ↦ (θ̇, M₀⁻¹(−K_v θ̇ − K_p e))` on the state `(e, θ̇)`, as a
continuous linear map. -/
def pdLinearPart (M₀ Kp Kv : Matrix (Fin n) (Fin n) ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
    (mulVecCLM (-(M₀⁻¹ * Kp)) ∘L ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) +
      mulVecCLM (-(M₀⁻¹ * Kv)) ∘L ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

/-- `pdLinearPart M₀ K_p K_v (e, θ̇) = (θ̇, M₀⁻¹(−K_v θ̇ − K_p e))` (MLS (4.52), p. 193, with
`C = 0`). -/
theorem pdLinearPart_apply (M₀ Kp Kv : Matrix (Fin n) (Fin n) ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    pdLinearPart M₀ Kp Kv z = (z.2, M₀⁻¹ *ᵥ (-(Kv *ᵥ z.2) - Kp *ᵥ z.1)) := by
  simp only [pdLinearPart, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd',
    _root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    mulVecCLM_apply, Prod.mk.injEq, true_and]
  rw [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.neg_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  abel

/-- **With constant inertia the Coriolis matrix vanishes** (MLS eq. (4.23), p. 171: `C` is built
from the partial derivatives of `M`). -/
theorem C_eq_zero_of_const {M₀ : Matrix (Fin n) (Fin n) ℝ} (hM0 : ∀ q, P.M q = M₀)
    (q v : Fin n → ℝ) : P.C q v = 0 := by
  have hd : ∀ i j, P.chain.massMatrixDeriv q i j = 0 := by
    intro i j
    have : (fun q' => P.chain.massMatrix q' i j) = fun _ => M₀ i j := by
      funext q'
      exact congrFun (congrFun (hM0 q') i) j
    rw [InertialChain.massMatrixDeriv, this]
    exact fderiv_const_apply _
  ext i j
  simp [C, Christoffel.coriolisMatrix, Christoffel.symbol, Christoffel.partials, hd]

/-- **With constant inertia `M₀` the closed loop (4.52) is affine** (MLS p. 193): it is
`x ↦ pdLinearPart M₀ K_p K_v (x − (θ_d, 0))`. -/
theorem pdClosedLoop_eq_of_const {M₀ : Matrix (Fin n) (Fin n) ℝ} (hM0 : ∀ q, P.M q = M₀)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    P.pdClosedLoop Kp Kv θd = fun x => pdLinearPart M₀ Kp Kv (x - (θd, 0)) := by
  funext x
  rw [show x = (x.1, x.2) from rfl, pdClosedLoop_apply, pdLinearPart_apply, hM0,
    P.C_eq_zero_of_const hM0]
  simp

/-- **With constant inertia the closed loop has a flow** (the interface `Stability.HasFlow`,
MLS p. 188): `φ t x = exp(t A)(x − (θ_d, 0)) + (θ_d, 0)` with `A = pdLinearPart M₀ K_p K_v`
(Mathlib's `NormedSpace.exp`). -/
theorem hasFlow_pdClosedLoop_of_const {M₀ : Matrix (Fin n) (Fin n) ℝ} (hM0 : ∀ q, P.M q = M₀)
    (Kp Kv : Matrix (Fin n) (Fin n) ℝ) (θd : Fin n → ℝ) :
    Stability.HasFlow (P.pdClosedLoop Kp Kv θd) (fun t x =>
      NormedSpace.exp (t • pdLinearPart M₀ Kp Kv) (x - (θd, 0)) + (θd, 0)) := by
  rw [P.pdClosedLoop_eq_of_const hM0]
  exact (Stability.hasFlow_linear (pdLinearPart M₀ Kp Kv)).comp_sub_const (θd, 0)

/-- **MLS Proposition 4.9 (p. 193) for a manipulator with constant positive definite inertia**,
with no flow hypothesis: with symmetric link inertias, `M(q) = M₀` positive definite for every
`q`, and `K_p`, `K_v` positive definite, PD control with compensation of `N` makes `(θ_d, 0)`
globally asymptotically stable at every `t₀ ≥ 0`. -/
theorem globallyAsymptoticallyStableAt_pdCompensatedTorque_of_const
    (h : ∀ k, (P.chain.linkInertia k).IsSymm) {M₀ : Matrix (Fin n) (Fin n) ℝ}
    (hM0 : ∀ q, P.M q = M₀) (hM₀ : M₀.PosDef) {Kp Kv : Matrix (Fin n) (Fin n) ℝ}
    (hKp : Kp.PosDef) (hKv : Kv.PosDef) (θd : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Stability.GloballyAsymptoticallyStableAt (P.field (P.pdCompensatedTorque Kp Kv θd))
      (θd, 0) t₀ := by
  have hM : ∀ q, (P.M q).PosDef := fun q => hM0 q ▸ hM₀
  obtain ⟨lam, hlam, hb⟩ := QuadraticBounds.posDef_exists_pos_mul_sq_norm_le hM₀
  exact P.globallyAsymptoticallyStableAt_pdCompensatedTorque h hM
    ⟨lam, hlam, fun q v => hM0 q ▸ hb v⟩ hKp hKv (P.hasFlow_pdClosedLoop_of_const hM0 Kp Kv θd)
    ht₀

end ManipulatorModel
end RoboLean
