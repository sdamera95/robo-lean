import RoboLean.Control.FlowDifferentiableC1
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Flows of class `C^k` in the initial state (MLS pp. 322–323, with the standing assumption of p. 179)

**What MLS prints.** For a smooth vector field `f` on `ℝⁿ`, `φ^f_t(q)` is the state at time `t` of
the solution of `q̇ = f(q)` from `q`, and "by the existence and uniqueness theorem of ordinary
differential equations, for each fixed `t`, `φ^f_t` is a local diffeomorphism of `ℝⁿ` onto itself"
(pp. 322–323). For Chapter 4 MLS assumes "the standard conditions for the existence and uniqueness
of solutions" (p. 179). No proof of the regularity of the flow in the initial state is given.

**Proved here.** On a finite-dimensional real space, let `F` be of class `C^k`, `k ≥ 1`, with
bounded derivatives of orders `1, …, k` (`HasBoundedIteratedFDeriv 1 k F`). Every flow `φ` of
`ẋ = F(x)` differentiable in the initial state (`IsDifferentiableFlow`, time first) has
`x ↦ φ(t, s, x)` of class `C^k` for `0 ≤ s ≤ t` (`IsDifferentiableFlow.contDiff_flow`), its
derivative `x ↦ D(t, s, x)` of class `C^{k−1}` (`IsDifferentiableFlow.contDiff_fderiv_flow`), and
for a smooth `F` with every derivative bounded the flow is smooth in the initial state
(`IsDifferentiableFlow.contDiff_flow_infty`); such a flow exists
(`exists_isDifferentiableFlow_contDiff`). The step of the induction is exposed as
`IsDifferentiableFlow.exists_augmentedFlow`, for the second variational equation
(`Control/FlowSecondDerivative`).

**Route.** Induction on `k`. The case `k = 1` is the continuity of the derivative in the initial
state (`IsDifferentiableFlow.continuous_fderiv`). For the step, the pair `(φ, D)` solves the
augmented system `(x, M)' = (F(x), DF(x) M)` on `E × (E →L[ℝ] E)`, whose derivative is unbounded
in `M`. On a window `[s, t]` the derivative stays in the ball `‖D‖ ≤ e^{K(t − s)}` (Grönwall), so
the field `G(x, M) = (F(x), DF(x) ψ(M))` with `ψ(M) = ρ(M) M`, `ρ` a smooth bump equal to `1` on
that ball, agrees with the augmented field along `(φ, D)`. `G` is of class `C^{k−1}` with bounded
derivatives of orders `1, …, k − 1` (Leibniz's bound for the bilinear composition, the derivatives
of `ψ` bounded by compact support), so its flow exists and is `C^{k−1}` in the initial state by the
induction hypothesis; by uniqueness on `[s, t]` it carries `(x, 1)` to `(φ(t, s, x), D(t, s, x))`,
so `x ↦ D(t, s, x)` is `C^{k−1}` and `φ(t, s, ·)` is `C^k`.

**Hypotheses against MLS.** MLS's fields are smooth on `ℝⁿ` and its flows are assumed defined for
all time ("complete", p. 323). Here the space is any finite-dimensional real normed space (for the
smooth bump on `E →L[ℝ] E`), the field is `C^k` with bounded derivatives of orders `1` to `k`, which
makes it globally Lipschitz and its flow global; a smooth field with compact support, or a smooth
field cut off outside a ball, meets every bound.

**Conventions.** As in `Control/FlowDerivative`: time first, `φ t s x` the state at time `t` of the
solution from `x` at time `s`, initial times `s ≥ 0`; derivatives are Fréchet derivatives and the
iterated derivatives are Mathlib's `iteratedFDeriv` with the operator norm.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Stability

universe u

/-- **Bounded derivatives of orders `a` to `b` (the hypothesis of `C^k` dependence of flows on the
initial state, MLS pp. 322–323):** for every `j` with `a ≤ j ≤ b` the `j`-th iterated Fréchet
derivative of `f` is bounded in operator norm on the whole space. -/
def HasBoundedIteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : ℕ) (f : E → F) : Prop :=
  ∀ j, a ≤ j → j ≤ b → ∃ C, ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Bounds

variable {X Y Z W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **The first derivative and the first iterated derivative have the same norm** (for the bounds
behind MLS pp. 322–323; Mathlib's `iteratedFDeriv`, operator norms). -/
theorem norm_fderiv_eq_norm_iteratedFDeriv_one (f : X → Y) (y : X) :
    ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ := by
  have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 0)
  rwa [norm_iteratedFDeriv_zero, zero_add] at e

/-- **Precomposition with a continuous linear map of norm at most `1` does not increase the norm of
an iterated derivative** (for the bounds behind MLS pp. 322–323; Mathlib's `iteratedFDeriv`,
operator norms). -/
theorem norm_iteratedFDeriv_comp_clm_le {f : Y → Z} {N : ℕ∞ω} (hf : ContDiff ℝ N f)
    (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1) (x : X) {j : ℕ} (hj : (j : ℕ∞ω) ≤ N) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x hj]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hL))

/-- **A smooth map with compact support has bounded iterated derivatives of every order** (for the
cut-off behind MLS pp. 322–323; Mathlib's `iteratedFDeriv`, operator norms). -/
theorem exists_bound_iteratedFDeriv_of_hasCompactSupport {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (m : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hf.continuous_iteratedFDeriv (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
    (hs.iteratedFDeriv m).norm
  exact ⟨C, fun x => hC ⟨x, rfl⟩⟩

/-- **Leibniz's bound for a bilinear map:** bounds on the iterated derivatives of `f` and `g` of
orders at most `j` give a bound on the `j`-th iterated derivative of `y ↦ B(f(y), g(y))` (for the
cut-off behind MLS pp. 322–323; Mathlib's `iteratedFDeriv`, operator norms). -/
theorem exists_bound_iteratedFDeriv_bilinear {f : X → Y} {g : X → Z} {N : ℕ∞ω}
    (B : Y →L[ℝ] Z →L[ℝ] W) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) {j : ℕ}
    (hj : (j : ℕ∞ω) ≤ N) (hfb : ∀ i ≤ j, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ j, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ j (fun y => B (f y) (g y)) x‖ ≤ C := by
  choose! Cf hCf using hfb
  choose! Cg hCg using hgb
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cf i * Cg (j - i), fun x => ?_⟩
  refine (B.norm_iteratedFDeriv_le_of_bilinear hf hg x hj).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg B)
  have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := hCf i hij x
  have h2 := hCg (j - i) (Nat.sub_le j i) x
  have h3 : 0 ≤ Cf i := (norm_nonneg _).trans h1
  have h4 : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h4) h2 (norm_nonneg _) (mul_nonneg h4 h3)

/-- **The iterated derivative of a map into a product is bounded by the sum of those of its two
components** (for the cut-off behind MLS pp. 322–323; Mathlib's `iteratedFDeriv`, the product
norm). -/
theorem norm_iteratedFDeriv_prodMk_le {f : X → Y} {g : X → Z} {N : ℕ∞ω}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) {j : ℕ} (hj : (j : ℕ∞ω) ≤ N) (x : X) :
    ‖iteratedFDeriv ℝ j (fun y => (f y, g y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖ := by
  have e : (fun y => (f y, g y)) =
      (ContinuousLinearMap.inl ℝ Y Z ∘ f) + (ContinuousLinearMap.inr ℝ Y Z ∘ g) := by
    funext y
    simp
  rw [e, iteratedFDeriv_add_apply
    (((ContinuousLinearMap.inl ℝ Y Z).contDiff.comp hf).contDiffAt.of_le hj)
    (((ContinuousLinearMap.inr ℝ Y Z).contDiff.comp hg).contDiffAt.of_le hj)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((ContinuousLinearMap.inl ℝ Y Z).norm_iteratedFDeriv_comp_left hf.contDiffAt hj).trans
      (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ Y Z))
  · exact ((ContinuousLinearMap.inr ℝ Y Z).norm_iteratedFDeriv_comp_left hg.contDiffAt hj).trans
      (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ Y Z))

/-- **A smooth map with compact support has bounded derivatives of all orders** (for the fields
cut off outside a ball behind MLS pp. 322–323): `HasBoundedIteratedFDeriv a b f` for all `a`, `b`. -/
theorem hasBoundedIteratedFDeriv_of_hasCompactSupport {f : X → Y} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (a b : ℕ) : HasBoundedIteratedFDeriv a b f :=
  fun j _ _ => exists_bound_iteratedFDeriv_of_hasCompactSupport hf hs j

/-- At every time `τ ≥ s` a solution of an autonomous continuous field has the right derivative
`G(x(τ))` (MLS eq. (7.7), p. 322); at `τ = s` it follows from the limit of the derivatives. -/
private theorem IsSolution.hasDerivWithinAt_Ici_autonomous {G : X → X} (hG : Continuous G)
    {s : ℝ} {x : ℝ → X} (hx : IsSolution (fun _ => G) s x) {τ : ℝ} (hτ : s ≤ τ) :
    HasDerivWithinAt x (G (x τ)) (Ici τ) τ := by
  rcases eq_or_lt_of_le hτ with h | h
  · subst h
    have hcw : ContinuousWithinAt x (Ioi s) s := (hx.1 s self_mem_Ici).mono Ioi_subset_Ici_self
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi s)
      (fun t ht => (hx.2 t ht).differentiableAt.differentiableWithinAt) hcw self_mem_nhdsWithin ?_
    have hlim : Tendsto (fun t => G (x t)) (𝓝[>] s) (𝓝 (G (x s))) :=
      (hG.tendsto (x s)).comp hcw.tendsto
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((hx.2 t ht).deriv).symm
  · exact (hx.2 τ h).hasDerivWithinAt

end Bounds

namespace IsDifferentiableFlow

/-- **The cut-off augmented flow (the induction step behind MLS pp. 322–323):** on a
finite-dimensional real space, let `F` be of class `C^{m+2}` with bounded derivatives of orders `1`
to `m + 2`, `φ` a flow of `ẋ = F(x)` with derivative `D` in the initial state
(`IsDifferentiableFlow`, time first), `s ≥ 0` and `T` real. Then there is a field `G` on
`E × (E →L[ℝ] E)` of class `C^{m+1}` with bounded derivatives of orders `1` to `m + 1`, with a flow
`φ_G` differentiable in the initial state, equal near every `(φ(τ, s, x), D(τ, s, x))`,
`τ ∈ [s, T]`, to the augmented field `(y, M) ↦ (F(y), DF(y) M)`, and with
`φ_G(τ, s, (x, 1)) = (φ(τ, s, x), D(τ, s, x))` for `τ ∈ [s, T]`. -/
theorem exists_augmentedFlow [FiniteDimensional ℝ E] {m : ℕ} {F : E → E} {DF : E → E →L[ℝ] E}
    {φ : ℝ → ℝ → E → E} {D : ℝ → ℝ → E → E →L[ℝ] E}
    (hF : ContDiff ℝ (m + 1 + 1 : ℕ) F) (hb : HasBoundedIteratedFDeriv 1 (m + 1 + 1) F)
    (h : IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D) {s : ℝ} (hs : 0 ≤ s) (T : ℝ) :
    ∃ (G : E × (E →L[ℝ] E) → E × (E →L[ℝ] E))
      (φG : ℝ → ℝ → E × (E →L[ℝ] E) → E × (E →L[ℝ] E))
      (DG : ℝ → ℝ → E × (E →L[ℝ] E) → E × (E →L[ℝ] E) →L[ℝ] E × (E →L[ℝ] E)),
      ContDiff ℝ (m + 1 : ℕ) G ∧ HasBoundedIteratedFDeriv 1 (m + 1) G ∧
      IsDifferentiableFlow (fun _ => G) (fun _ => fderiv ℝ G) φG DG ∧
      (∀ τ ∈ Icc s T, ∀ x, G =ᶠ[𝓝 (φ τ s x, D τ s x)]
        fun q => (F q.1, ContinuousLinearMap.compL ℝ E E E (fderiv ℝ F q.1) q.2)) ∧
      ∀ τ ∈ Icc s T, ∀ x, φG τ s (x, 1) = (φ τ s x, D τ s x) := by
  have hDF : ∀ y, DF y = fderiv ℝ F y := fun y => (h.hasFDerivAt_field 0 le_rfl y).fderiv.symm
  obtain ⟨K, hK⟩ := hb 1 le_rfl (by omega)
  have hK' : ∀ y, ‖DF y‖ ≤ K.toNNReal := fun y => by
    rw [hDF, norm_fderiv_eq_norm_iteratedFDeriv_one]
    exact (hK y).trans (Real.le_coe_toNNReal K)
  have hlip : ∀ τ : ℝ, 0 ≤ τ → LipschitzWith K.toNNReal ((fun _ => F) τ) := fun τ _ =>
    lipschitzWith_of_nnnorm_fderiv_le
      (fun y => (h.hasFDerivAt_field 0 le_rfl y).differentiableAt) fun y => by
        rw [← hDF, ← NNReal.coe_le_coe, coe_nnnorm]
        exact hK' y
  set R := Real.exp (K.toNNReal * (T - s)) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hDb : ∀ τ ∈ Icc s T, ∀ x, ‖D τ s x‖ ≤ R := fun τ hτ x =>
    (h.norm_fderiv_le_exp hlip hs hτ.1 x).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) (NNReal.coe_nonneg _)))
  -- the cut-off in the derivative variable
  let ρ : ContDiffBump (0 : E →L[ℝ] E) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  set ψ : (E →L[ℝ] E) → (E →L[ℝ] E) := fun M => ρ M • M with hψ
  have hψc : ContDiff ℝ ∞ ψ := ρ.contDiff.smul contDiff_id
  have hψs : HasCompactSupport ψ := ρ.hasCompactSupport.smul_right (f' := id)
  have hψb : ∀ i, ∃ C, ∀ M, ‖iteratedFDeriv ℝ i ψ M‖ ≤ C :=
    exists_bound_iteratedFDeriv_of_hasCompactSupport hψc hψs
  have hψid : ∀ M : E →L[ℝ] E, ‖M‖ ≤ R → ψ M = M := fun M hM => by
    have hmem : M ∈ Metric.closedBall (0 : E →L[ℝ] E) ρ.rIn := by
      rw [mem_closedBall_zero_iff]
      show ‖M‖ ≤ R + 1
      linarith
    simp only [hψ, ρ.one_of_mem_closedBall hmem, one_smul]
  -- the cut-off augmented field
  set G : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
    fun p => (F p.1, ContinuousLinearMap.compL ℝ E E E (fderiv ℝ F p.1) (ψ p.2)) with hG
  have hF1 : ContDiff ℝ (m + 1 : ℕ) (fderiv ℝ F) := hF.fderiv_right (by push_cast; exact le_rfl)
  have hF0 : ContDiff ℝ (m + 1 : ℕ) F := hF.of_le (by exact_mod_cast Nat.le_succ _)
  have hψ' : ContDiff ℝ (m + 1 : ℕ) fun p : E × (E →L[ℝ] E) => ψ p.2 :=
    (hψc.of_le (mod_cast le_top)).comp contDiff_snd
  have hF1' : ContDiff ℝ (m + 1 : ℕ) fun p : E × (E →L[ℝ] E) => fderiv ℝ F p.1 :=
    hF1.comp contDiff_fst
  have hF0' : ContDiff ℝ (m + 1 : ℕ) fun p : E × (E →L[ℝ] E) => F p.1 := hF0.comp contDiff_fst
  have hB' : ContDiff ℝ (m + 1 : ℕ) fun p : E × (E →L[ℝ] E) =>
      ContinuousLinearMap.compL ℝ E E E (fderiv ℝ F p.1) (ψ p.2) :=
    (contDiff_const.clm_apply hF1').clm_apply hψ'
  have hGc : ContDiff ℝ (m + 1 : ℕ) G := hF0'.prodMk hB'
  have hGb : HasBoundedIteratedFDeriv 1 (m + 1) G := by
    intro j hj1 hj2
    have hjN : (j : ℕ∞ω) ≤ (m + 1 : ℕ) := by exact_mod_cast hj2
    obtain ⟨C₁, hC₁⟩ := hb j hj1 (by omega)
    have h1 : ∀ p, ‖iteratedFDeriv ℝ j (fun p : E × (E →L[ℝ] E) => F p.1) p‖ ≤ C₁ := fun p =>
      (norm_iteratedFDeriv_comp_clm_le hF0 (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
        (ContinuousLinearMap.norm_fst_le ℝ E (E →L[ℝ] E)) p hjN).trans (hC₁ _)
    obtain ⟨C₂, hC₂⟩ := exists_bound_iteratedFDeriv_bilinear (ContinuousLinearMap.compL ℝ E E E)
      hF1' hψ' hjN (fun i hi => by
        obtain ⟨C, hC⟩ := hb (i + 1) (by omega) (by omega)
        refine ⟨C, fun p => ?_⟩
        have hiN : (i : ℕ∞ω) ≤ (m + 1 : ℕ) := by exact_mod_cast hi.trans hj2
        refine (norm_iteratedFDeriv_comp_clm_le hF1 (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))
          (ContinuousLinearMap.norm_fst_le ℝ E (E →L[ℝ] E)) p hiN).trans ?_
        rw [norm_iteratedFDeriv_fderiv]
        exact hC _)
      (fun i _ => by
        obtain ⟨C, hC⟩ := hψb i
        exact ⟨C, fun p => (norm_iteratedFDeriv_comp_clm_le hψc
          (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))
          (ContinuousLinearMap.norm_snd_le ℝ E (E →L[ℝ] E)) p (mod_cast le_top)).trans (hC _)⟩)
    exact ⟨C₁ + C₂, fun p =>
      (norm_iteratedFDeriv_prodMk_le hF0' hB' hjN p).trans (add_le_add (h1 p) (hC₂ p))⟩
  -- the flow of the cut-off augmented field
  obtain ⟨K₂, hK₂⟩ := hGb 1 le_rfl (by omega)
  have hGd : ∀ p, HasFDerivAt G (fderiv ℝ G p) p := fun p =>
    ((hGc.differentiable (by simp)) p).hasFDerivAt
  have hGfc : Continuous (fderiv ℝ G) := hGc.continuous_fderiv (by simp)
  have hGK : ∀ p, ‖fderiv ℝ G p‖ ≤ K₂.toNNReal := fun p => by
    rw [norm_fderiv_eq_norm_iteratedFDeriv_one]
    exact (hK₂ p).trans (Real.le_coe_toNNReal _)
  obtain ⟨φG, DG, hGflow⟩ := exists_isDifferentiableFlow_autonomous hGd hGfc hGK
  -- the augmented flow carries `(x, 1)` to `(φ(τ, s, x), D(τ, s, x))` for `τ ∈ [s, T]`
  have hGlip : LipschitzWith K₂.toNNReal G :=
    lipschitzWith_of_nnnorm_fderiv_le (fun p => (hGd p).differentiableAt) fun p => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hGK p
  have hFc : Continuous F := hF0.continuous
  have hid : ∀ τ₀ ∈ Icc s T, ∀ x, φG τ₀ s (x, 1) = (φ τ₀ s x, D τ₀ s x) := by
    intro τ₀ hτ₀ x
    have hyc : ContinuousOn (fun τ => (φ τ s x, D τ s x)) (Icc s T) :=
      ((h.continuousOn_trajectory hs x).prodMk (h.continuousOn_fderiv hs x)).mono
        Icc_subset_Ici_self
    have hyd : ∀ τ ∈ Ico s T, HasDerivWithinAt (fun τ => (φ τ s x, D τ s x))
        (G (φ τ s x, D τ s x)) (Ici τ) τ := by
      intro τ hτ
      have h1 := IsSolution.hasDerivWithinAt_Ici_autonomous hFc (h.isSolution s hs x) hτ.1
      have h2 := (h.variational τ s hs hτ.1 x).mono (Ici_subset_Ici.2 hτ.1)
      have e : G (φ τ s x, D τ s x) = (F (φ τ s x), DF (φ τ s x) * D τ s x) := by
        simp only [hG, ContinuousLinearMap.compL_apply,
          hψid _ (hDb τ (Ico_subset_Icc_self hτ) x), hDF]
        rfl
      rw [e]
      exact h1.prodMk h2
    have hzc : ContinuousOn (fun τ => φG τ s (x, 1)) (Icc s T) :=
      (hGflow.continuousOn_trajectory hs _).mono Icc_subset_Ici_self
    have hzd : ∀ τ ∈ Ico s T, HasDerivWithinAt (fun τ => φG τ s (x, 1)) (G (φG τ s (x, 1)))
        (Ici τ) τ := fun τ hτ =>
      IsSolution.hasDerivWithinAt_Ici_autonomous hGc.continuous (hGflow.isSolution s hs (x, 1))
        hτ.1
    have hd := dist_le_of_trajectories_ODE (v := fun _ => G) (K := K₂.toNNReal) (δ := 0)
      (fun _ => hGlip) hzc hzd hyc hyd
      (by rw [hGflow.self_eq s hs, h.self_eq s hs, h.fderiv_self s hs, dist_self]) τ₀ hτ₀
    rw [zero_mul] at hd
    exact dist_le_zero.1 hd
  have hloc : ∀ τ ∈ Icc s T, ∀ x, G =ᶠ[𝓝 (φ τ s x, D τ s x)]
      fun q => (F q.1, ContinuousLinearMap.compL ℝ E E E (fderiv ℝ F q.1) q.2) := by
    intro τ hτ x
    have hM : D τ s x ∈ Metric.ball (0 : E →L[ℝ] E) ρ.rIn := by
      rw [mem_ball_zero_iff]
      show ‖D τ s x‖ < R + 1
      linarith [hDb τ hτ x]
    have h1 : ∀ᶠ q : E × (E →L[ℝ] E) in 𝓝 (φ τ s x, D τ s x), ρ q.2 = (1 : (E →L[ℝ] E) → ℝ) q.2 :=
      (continuous_snd.tendsto (φ τ s x, D τ s x)).eventually (ρ.eventuallyEq_one_of_mem_ball hM)
    filter_upwards [h1] with q hq
    simp only [hG, hψ, hq, Pi.one_apply, one_smul]
  exact ⟨G, φG, DG, hGc, hGb, hGflow, hloc, hid⟩

/-- The induction behind `contDiff_flow` (MLS pp. 322–323): for every finite-dimensional space
and every field of class `C^{m+1}` with bounded derivatives of orders `1` to `m + 1`, every flow
differentiable in the initial state is `C^{m+1}` in the initial state. -/
private theorem contDiff_flow_aux (m : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (F : E → E) (DF : E → E →L[ℝ] E) (φ : ℝ → ℝ → E → E) (D : ℝ → ℝ → E → E →L[ℝ] E),
      ContDiff ℝ (m + 1 : ℕ) F → HasBoundedIteratedFDeriv 1 (m + 1) F →
      IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ContDiff ℝ (m + 1 : ℕ) (φ t s) := by
  induction m with
  | zero =>
    intro E _ _ _ F DF φ D hF hb h s t hs hst
    obtain ⟨K, hK⟩ := hb 1 le_rfl le_rfl
    have hDF : ∀ y, DF y = fderiv ℝ F y := fun y => (h.hasFDerivAt_field 0 le_rfl y).fderiv.symm
    have hK' : ∀ y, ‖DF y‖ ≤ K.toNNReal := fun y => by
      rw [hDF, norm_fderiv_eq_norm_iteratedFDeriv_one]
      exact (hK y).trans (Real.le_coe_toNNReal K)
    have hDFc : Continuous DF := by
      rw [show DF = fderiv ℝ F from funext hDF]
      exact hF.continuous_fderiv (by norm_num)
    have hc := h.continuous_fderiv (K := K.toNNReal) (hDFc.comp continuous_snd).continuousOn
      (fun _ _ y => hK' y) hs hst
    have := contDiff_one_iff_hasFDerivAt.2 ⟨D t s, hc, fun x => h.hasFDerivAt t s hs hst x⟩
    simpa using this
  | succ m ih =>
    intro E _ _ _ F DF φ D hF hb h s t hs hst
    obtain ⟨G, φG, DG, hGc, hGb, hGflow, -, hid⟩ := h.exists_augmentedFlow hF hb hs t
    have hIH := ih (E × (E →L[ℝ] E)) G (fderiv ℝ G) φG DG hGc hGb hGflow s t hs hst
    have hDeq : D t s = fun x => (φG t s (x, 1)).2 :=
      funext fun x => by rw [hid t ⟨hst, le_rfl⟩]
    have hDc : ContDiff ℝ (m + 1 : ℕ) (D t s) := by
      rw [hDeq]
      exact contDiff_snd.comp (hIH.comp (contDiff_id.prodMk contDiff_const))
    have := contDiff_succ_iff_hasFDerivAt.2 ⟨D t s, hDc, fun x => h.hasFDerivAt t s hs hst x⟩
    push_cast at this ⊢
    exact this

end IsDifferentiableFlow

namespace IsDifferentiableFlow

variable {F : E → E} {DF : E → E →L[ℝ] E} {φ : ℝ → ℝ → E → E} {D : ℝ → ℝ → E → E →L[ℝ] E}

/-- **Flows of class `C^k` in the initial state (MLS pp. 322–323, `φ^f_t` a local diffeomorphism;
the standing assumption of p. 179):** on a finite-dimensional real space, if `F` is of class `C^k`,
`k ≥ 1`, with bounded derivatives of orders `1` to `k`, and `φ` is a flow of `ẋ = F(x)`
differentiable in the initial state (`IsDifferentiableFlow`, time first), then `x ↦ φ(t, s, x)` is
of class `C^k` for `0 ≤ s ≤ t`. -/
theorem contDiff_flow [FiniteDimensional ℝ E] {k : ℕ} (hk : 1 ≤ k) (hF : ContDiff ℝ k F)
    (hb : HasBoundedIteratedFDeriv 1 k F)
    (h : IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : ContDiff ℝ k (φ t s) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact contDiff_flow_aux m E F DF φ D hF hb h s t hs hst

/-- **The derivative of the flow in the initial state is of class `C^k` (MLS pp. 322–323; for
`k = 1` the second derivative of the flow exists and is continuous):** on a finite-dimensional
real space, if `F` is of class `C^{k+1}` with bounded derivatives of orders `1` to `k + 1` and `φ`
is a flow of `ẋ = F(x)` with derivative `D` in the initial state (`IsDifferentiableFlow`, time
first), then `x ↦ D(t, s, x)` is of class `C^k` for `0 ≤ s ≤ t`. -/
theorem contDiff_fderiv_flow [FiniteDimensional ℝ E] {k : ℕ} (hF : ContDiff ℝ (k + 1) F)
    (hb : HasBoundedIteratedFDeriv 1 (k + 1) F)
    (h : IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : ContDiff ℝ k (D t s) := by
  have hφ : ContDiff ℝ (k + 1 : ℕ) (φ t s) :=
    h.contDiff_flow (by omega) (by exact_mod_cast hF) hb hs hst
  have hD : D t s = fderiv ℝ (φ t s) := funext fun x => (h.hasFDerivAt t s hs hst x).fderiv.symm
  rw [hD]
  exact hφ.fderiv_right (by push_cast; exact le_rfl)

/-- **Smooth fields with bounded derivatives have flows smooth in the initial state (MLS
pp. 322–323):** on a finite-dimensional real space, if `F` is smooth with every derivative of
order at least `1` bounded and `φ` is a flow of `ẋ = F(x)` differentiable in the initial state
(`IsDifferentiableFlow`, time first), then `x ↦ φ(t, s, x)` is smooth for `0 ≤ s ≤ t`. -/
theorem contDiff_flow_infty [FiniteDimensional ℝ E] (hF : ContDiff ℝ ∞ F)
    (hb : ∀ k, HasBoundedIteratedFDeriv 1 k F)
    (h : IsDifferentiableFlow (fun _ => F) (fun _ => DF) φ D) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : ContDiff ℝ ∞ (φ t s) := by
  refine contDiff_infty.2 fun n => ?_
  have h1 : ContDiff ℝ (n + 1 : ℕ) (φ t s) :=
    h.contDiff_flow (by omega) (hF.of_le (mod_cast le_top)) (hb (n + 1)) hs hst
  exact h1.of_le (by exact_mod_cast Nat.le_succ n)

end IsDifferentiableFlow

/-- **Existence of a flow of class `C^k` in the initial state (MLS pp. 322–323 and p. 179):** on a
finite-dimensional real space, a field `F` of class `C^k`, `k ≥ 1`, with bounded derivatives of
orders `1` to `k` has a flow `φ` with derivative `D` in the initial state
(`IsDifferentiableFlow (fun _ => F) (fun _ => fderiv ℝ F) φ D`, time first) such that
`x ↦ φ(t, s, x)` is of class `C^k` for `0 ≤ s ≤ t`. -/
theorem exists_isDifferentiableFlow_contDiff [FiniteDimensional ℝ E] {F : E → E} {k : ℕ}
    (hk : 1 ≤ k) (hF : ContDiff ℝ k F) (hb : HasBoundedIteratedFDeriv 1 k F) :
    ∃ φ : ℝ → ℝ → E → E, ∃ D : ℝ → ℝ → E → E →L[ℝ] E,
      IsDifferentiableFlow (fun _ => F) (fun _ => fderiv ℝ F) φ D ∧
        ∀ s t, 0 ≤ s → s ≤ t → ContDiff ℝ k (φ t s) := by
  obtain ⟨K, hK⟩ := hb 1 le_rfl hk
  have hd : ∀ y, HasFDerivAt F (fderiv ℝ F y) y := fun y =>
    ((hF.differentiable (by norm_cast; omega)) y).hasFDerivAt
  have hK' : ∀ y, ‖fderiv ℝ F y‖ ≤ K.toNNReal := fun y => by
    rw [norm_fderiv_eq_norm_iteratedFDeriv_one]
    exact (hK y).trans (Real.le_coe_toNNReal K)
  obtain ⟨φ, D, h⟩ := exists_isDifferentiableFlow_autonomous hd
    (hF.continuous_fderiv (by norm_cast; omega)) hK'
  exact ⟨φ, D, h, fun s t hs hst => h.contDiff_flow hk hF hb hs hst⟩

end Stability
end RoboLean
