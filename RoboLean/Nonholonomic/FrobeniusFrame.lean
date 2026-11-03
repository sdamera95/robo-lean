import RoboLean.Nonholonomic.FrobeniusLocal
import RoboLean.Nonholonomic.LocalFrames
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Frobenius' theorem, sufficiency (MLS Theorem 7.2, p. 326, "if"), with `C¹` defining maps

**What MLS prints.** Theorem 7.2 (Frobenius, p. 326): "A regular distribution is integrable if and
only if it is involutive", stated without proof; integrability is eq. (7.9).

**Proved here.**

* The linear-algebra step of the classical proof (`exists_commutingFrame`): for a distribution
  `D` regular and involutive on an open set `U ∋ q` and spanned near `q` by `C¹` fields, there are
  `k = dim D_q` fields `Z₁, …, Z_k`, of class `C¹` with compact support, linearly independent at
  `q`, with `[Zᵢ, Zⱼ] = 0` near `q` and `span{Z₁, …, Z_k} = D` near `q`. Construction: a local
  frame `f₁, …, f_k` (`exists_localFrame`), a linear map `P` with `P fᵢ(q) = eᵢ`, the normalized
  fields `Yᵢ = Σⱼ (P F(y))⁻¹ᵢⱼ fⱼ` with `P Yᵢ = eᵢ`, cut off by a smooth bump; involutivity puts
  `[Zᵢ, Zⱼ]` in `D`, and `P [Zᵢ, Zⱼ] = 0` because `P Zⱼ` is constant near `q`.
* **Theorem 7.2, "if", with a `C¹` defining map** (`isIntegrableAtOfClass_one_of_isInvolutiveOn`):
  such a distribution is integrable at `q` with a defining map of class `C¹`; for distributions
  spanned by finitely many `C¹` fields (`isIntegrableAtOfClass_one_of_spanAt`), and the form of
  the named statement `FrobeniusSufficiency` with `C¹` in place of `C^∞`
  (`frobeniusSufficiency_classOne`).

**Not proved here, and why.** `FrobeniusSufficiency` asks a `C^∞` defining map; the chart is
built from flows, and the flows of this library are known to be `C¹` in the initial state only.

**Conventions.** Mathlib's bracket `lieBracket ℝ` (the book's sign); `IsInvolutiveOn` with sections
differentiable on the set; `IsIntegrableAtOfClass` (Chapter 7, `Integrability2`); coordinates of
`ℝᵏ` are `Pi.single i 1`.
-/

noncomputable section

open Set Filter Topology VectorField Metric

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **MLS eq. (7.9), p. 326: integrability at `q` depends only on the distribution near `q`:** if
`D = D'` on a neighbourhood of `q`, integrability of `D` at `q` with `C^n` defining maps gives that
of `D'`. -/
theorem IsIntegrableAtOfClass.congr_nhds {n : WithTop ℕ∞} {D D' : E → Submodule ℝ E} {q : E}
    (h : IsIntegrableAtOfClass n D q) (hDD : ∀ᶠ y in 𝓝 q, D y = D' y) :
    IsIntegrableAtOfClass n D' q := by
  obtain ⟨U, hU, hqU, p, f, hf, hker⟩ := h
  obtain ⟨O, hO, hOo, hqO⟩ := _root_.eventually_nhds_iff.1 hDD
  refine ⟨U ∩ O, hU.inter hOo, ⟨hqU, hqO⟩, p, f, fun y hy => hf y hy.1, fun y hy => ?_⟩
  rw [← hO y hy.2]
  exact hker y hy.1

variable [FiniteDimensional ℝ E] {k : ℕ}

/-- The frame map `a ↦ Σᵢ aᵢ fᵢ(y)` (for MLS p. 325). -/
private def frameMap (f : Fin k → E → E) (y : E) : (Fin k → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (f i y)

omit [FiniteDimensional ℝ E] in
private theorem frameMap_apply (f : Fin k → E → E) (y : E) (a : Fin k → ℝ) :
    frameMap f y a = ∑ i, a i • f i y := by
  simp [frameMap]

/-- **A commuting frame near a point (the linear-algebra step of the proof of MLS Theorem 7.2,
p. 326, with p. 324):** on a finite-dimensional real space, let `D` be regular and involutive on
an open set `U ∋ q` and equal near `q` to `span{g₁, …, g_m}` for fields `gⱼ` of class `C¹`. Then
for some `k` there are fields `Z₁, …, Z_k` of class `C¹` with compact support, linearly
independent at `q`, with `[Zᵢ, Zⱼ] = 0` near `q` (Mathlib's bracket, the book's sign) and
`span{Z₁, …, Z_k} = D` near `q`. -/
theorem exists_commutingFrame {D : E → Submodule ℝ E} {U : Set E} (hU : IsOpen U)
    (hreg : IsRegularOn D U) (hinv : IsInvolutiveOn D U) {q : E} (hq : q ∈ U) {m : ℕ}
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hspan : ∀ᶠ y in 𝓝 q, D y = spanAt (Set.range g) y) :
    ∃ (k : ℕ) (Z : Fin k → E → E), (∀ i, ContDiff ℝ 1 (Z i)) ∧ (∀ i, HasCompactSupport (Z i)) ∧
      LinearIndependent ℝ (fun i => Z i q) ∧
      (∀ᶠ y in 𝓝 q, ∀ i j, lieBracket ℝ (Z i) (Z j) y = 0) ∧
      (∀ᶠ y in 𝓝 q, spanAt (Set.range Z) y = D y) := by
  classical
  -- a local frame of `D`
  obtain ⟨O, hOD, hOo, hqO⟩ := _root_.eventually_nhds_iff.1 hspan
  obtain ⟨r₀, hr₀⟩ := hreg
  have hreg' : IsRegularOn (spanAt (Set.range g)) (U ∩ O) :=
    ⟨r₀, fun y hy => by rw [← hOD y hy.2]; exact hr₀ y hy.1⟩
  obtain ⟨k, σ, hk, V, hV, hVUO, hframe⟩ := exists_localFrame (hU.inter hOo) hreg' ⟨hq, hqO⟩
    fun j => (hg j).continuous.continuousAt
  set f : Fin k → E → E := fun i => g (σ i) with hfdef
  set G : E → (Fin k → ℝ) →L[ℝ] E := fun y => frameMap f y with hGdef
  have hGc : ContDiff ℝ 1 G := by
    have : G = fun y => ∑ i, (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) E
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i)) (f i y) := by
      funext y; simp [hGdef, frameMap]
    rw [this]
    exact ContDiff.sum fun i _ => (ContinuousLinearMap.contDiff _).comp (hg (σ i))
  -- a left inverse `P` of `G q`
  have hliq : LinearIndependent ℝ fun i => f i q := (hframe q (mem_of_mem_nhds hV)).1
  have hGq : LinearMap.ker (G q : (Fin k → ℝ) →ₗ[ℝ] E) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    have h0 : ∑ i, a i • f i q = 0 := by rw [← frameMap_apply]; exact ha
    exact funext fun i => Fintype.linearIndependent_iff.1 hliq a h0 i
  obtain ⟨P', hP'⟩ := LinearMap.exists_leftInverse_of_injective _ hGq
  set P : E →L[ℝ] (Fin k → ℝ) := LinearMap.toContinuousLinearMap P' with hPdef
  have hPG : ∀ a, P (G q a) = a := fun a => by
    have := congrArg (fun L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) => L a) hP'
    simpa [hPdef] using this
  -- the matrix `P G(y)` and its inverse
  set Mm : E → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) := fun y => P.comp (G y) with hMm
  have hMc : ContDiff ℝ 1 Mm :=
    ((ContinuousLinearMap.compL ℝ (Fin k → ℝ) E (Fin k → ℝ)) P).contDiff.comp hGc
  have hMq : Mm q = 1 := by ext1 a; simp [hMm, hPG]
  set W₀ : Set E := Mm ⁻¹' {x | IsUnit x} with hW₀
  have hW₀o : IsOpen W₀ := Units.isOpen.preimage hMc.continuous
  have hqW₀ : q ∈ W₀ := by simp [hW₀, hMq]
  set Y : Fin k → E → E := fun i y => G y (Ring.inverse (Mm y) (Pi.single i 1)) with hYdef
  have hYc : ∀ i, ∀ y ∈ W₀, ContDiffAt ℝ 1 (Y i) y := fun i y hy => by
    have hu : IsUnit (Mm y) := hy
    have hinvc : ContDiffAt ℝ 1 (fun y => Ring.inverse (Mm y)) y := by
      have h := contDiffAt_ringInverse ℝ (n := 1) hu.unit
      rw [hu.unit_spec] at h
      exact h.comp y hMc.contDiffAt
    exact hGc.contDiffAt.clm_apply (hinvc.clm_apply contDiffAt_const)
  have hPY : ∀ i, ∀ y ∈ W₀, P (Y i y) = Pi.single i 1 := fun i y hy => by
    have hu : IsUnit (Mm y) := hy
    have h := congrArg (fun L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) => L (Pi.single i 1))
      (Ring.mul_inverse_cancel (Mm y) hu)
    simpa [hMm, hYdef] using h
  have hYmem : ∀ i y, Y i y ∈ spanAt (Set.range g) y := fun i y => by
    simp only [hYdef, hGdef, frameMap_apply]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (mem_spanAt (Set.mem_range_self (σ j)) y)
  -- `P` is injective on `D y` near `q`
  have hPinj : ∀ y ∈ V ∩ W₀, ∀ v ∈ spanAt (Set.range g) y, P v = 0 → v = 0 := by
    intro y hy v hv hPv
    rw [(hframe y hy.1).2] at hv
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
    have hu : IsUnit (Mm y) := hy.2
    have hMa : Mm y a = 0 := by
      have : G y a = ∑ i, a i • g (σ i) y := frameMap_apply f y a
      simp only [hMm, ContinuousLinearMap.coe_comp, Function.comp_apply, this]
      exact hPv
    have ha : a = 0 := by
      have h := congrArg (fun L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) => L a)
        (Ring.inverse_mul_cancel (Mm y) hu)
      simp only [mul_apply_eq_comp, hMa, map_zero,
        one_apply_eq_self] at h
      exact h.symm
    simp [ha]
  -- the cut-off
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem (Filter.inter_mem hV (hW₀o.mem_nhds hqW₀))
      ((hU.inter hOo).mem_nhds ⟨hq, hqO⟩))
  set χ : ContDiffBump q := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩ with hχ
  have hχsupp : tsupport χ ⊆ ball q ε := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by simp [hχ]; linarith)
  have hχ1 : ∀ y ∈ ball q (ε / 3), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  set Z : Fin k → E → E := fun i y => χ y • Y i y with hZdef
  have hZc : ∀ i, ContDiff ℝ 1 (Z i) := fun i => by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball q ε
    · exact (χ.contDiff.contDiffAt).smul (hYc i y (hεsub hy).1.2)
    · have hy' : y ∉ tsupport χ := fun h => hy (hχsupp h)
      have hev : Z i =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy'] with z hz
        simp [hZdef, hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hZcs : ∀ i, HasCompactSupport (Z i) := fun i => by
    have : Z i = (fun y => χ y) • Y i := rfl
    rw [this]
    exact χ.hasCompactSupport.smul_right
  have hZmem : ∀ i y, Z i y ∈ D y := fun i y => by
    by_cases hy : y ∈ tsupport χ
    · have hyO : y ∈ O := (hεsub (hχsupp hy)).2.2
      rw [hOD y hyO]
      exact Submodule.smul_mem _ _ (hYmem i y)
    · have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hZdef, this]
  have hZY : ∀ i, ∀ y ∈ ball q (ε / 3), Z i =ᶠ[𝓝 y] Y i := fun i y hy => by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp [hZdef, hχ1 z hz]
  have hsmall : ∀ y ∈ ball q (ε / 3), y ∈ ball q ε := fun y hy =>
    ball_subset_ball (by linarith) hy
  refine ⟨k, Z, hZc, hZcs, ?_, ?_, ?_⟩
  · -- independence at `q`
    have hPZ : (fun i => P (Z i q)) = fun i => (Pi.single i 1 : Fin k → ℝ) := by
      funext i
      rw [show Z i q = Y i q by simp [hZdef, hχ1 q (mem_ball_self (by positivity))]]
      exact hPY i q hqW₀
    have hli : LinearIndependent ℝ fun i => (Pi.single i 1 : Fin k → ℝ) := by
      convert (Pi.basisFun ℝ (Fin k)).linearIndependent using 1
      ext i : 1
      exact (Pi.basisFun_apply ℝ (Fin k) i).symm
    rw [← hPZ] at hli
    exact LinearIndependent.of_comp (P : E →ₗ[ℝ] Fin k → ℝ) hli
  · -- brackets vanish near `q`
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < ε / 3))] with y hy i j
    have hyU : y ∈ U := (hεsub (hsmall y hy)).2.1
    have hmem := hinv (Z i) (Z j) (fun z _ => ((hZc i).differentiable one_ne_zero) z)
      (fun z _ => ((hZc j).differentiable one_ne_zero) z) (fun z _ => hZmem i z)
      (fun z _ => hZmem j z) y hyU
    have hyO : y ∈ O := (hεsub (hsmall y hy)).2.2
    rw [hOD y hyO] at hmem
    have hPd : ∀ a, P.comp (fderiv ℝ (Z a) y) = 0 := fun a => by
      have h1 := P.hasFDerivAt.comp y (((hZc a).differentiable one_ne_zero) y).hasFDerivAt
      have hconst : (P ∘ Z a) =ᶠ[𝓝 y] fun _ => (Pi.single a 1 : Fin k → ℝ) := by
        filter_upwards [hZY a y hy, isOpen_ball.mem_nhds hy] with z hz hz'
        simp only [Function.comp_apply, hz]
        exact hPY a z (hεsub (hsmall z hz')).1.2
      have h2 := (hasFDerivAt_const (𝕜 := ℝ) (Pi.single a 1 : Fin k → ℝ) y).congr_of_eventuallyEq
        hconst
      exact h1.unique h2
    refine hPinj y ⟨(hεsub (hsmall y hy)).1.1, (hεsub (hsmall y hy)).1.2⟩ _ hmem ?_
    rw [lieBracket, map_sub]
    have e1 := congrArg (fun L : E →L[ℝ] (Fin k → ℝ) => L (Z i y)) (hPd j)
    have e2 := congrArg (fun L : E →L[ℝ] (Fin k → ℝ) => L (Z j y)) (hPd i)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      zero_apply] at e1 e2
    rw [e1, e2, sub_zero]
  · -- the span is `D` near `q`
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < ε / 3))] with y hy
    have hyb := hεsub (hsmall y hy)
    have hZYy : ∀ i, Z i y = Y i y := fun i => by simp [hZdef, hχ1 y hy]
    have hliy : LinearIndependent ℝ fun i => Z i y := by
      have hPZ : (fun i => P (Z i y)) = fun i => (Pi.single i 1 : Fin k → ℝ) := by
        funext i; rw [hZYy]; exact hPY i y hyb.1.2
      have hli : LinearIndependent ℝ fun i => (Pi.single i 1 : Fin k → ℝ) := by
        convert (Pi.basisFun ℝ (Fin k)).linearIndependent using 1
        ext i : 1
        exact (Pi.basisFun_apply ℝ (Fin k) i).symm
      rw [← hPZ] at hli
      exact LinearIndependent.of_comp (P : E →ₗ[ℝ] Fin k → ℝ) hli
    have hle : spanAt (Set.range Z) y ≤ D y := by
      rw [spanAt_range, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hZmem i y
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [spanAt_range, finrank_span_eq_card hliy, Fintype.card_fin, hr₀ y hyb.2.1, ← hr₀ q hq,
      hOD q hqO, hk]

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", with a `C¹` defining map:** on a
finite-dimensional real space, a distribution `D` regular and involutive on an open set `U ∋ q`
and spanned near `q` by finitely many `C¹` fields is integrable at `q` with a defining map of
class `C¹` (`IsIntegrableAtOfClass 1`; MLS asks smooth functions). -/
theorem isIntegrableAtOfClass_one_of_isInvolutiveOn {D : E → Submodule ℝ E} {U : Set E}
    (hU : IsOpen U) (hreg : IsRegularOn D U) (hinv : IsInvolutiveOn D U) {q : E} (hq : q ∈ U)
    {m : ℕ} {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hspan : ∀ᶠ y in 𝓝 q, D y = spanAt (Set.range g) y) :
    IsIntegrableAtOfClass 1 D q := by
  obtain ⟨k, Z, hZc, hZcs, hli, hbr, hZD⟩ := exists_commutingFrame hU hreg hinv hq hg hspan
  have hdc : ∀ i, Continuous (fderiv ℝ (Z i)) := fun i => (hZc i).continuous_fderiv one_ne_zero
  choose C hC using fun i => (hdc i).bounded_above_of_compact_support ((hZcs i).fderiv (𝕜 := ℝ))
  choose C' hC' using fun i => (hZc i).continuous.bounded_above_of_compact_support (hZcs i)
  have hsum : ∀ (c : Fin k → ℝ) (i : Fin k), c i ≤ ∑ j, |c j| := fun c i =>
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))
  set K : NNReal := ⟨∑ j, |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _⟩
  set M : NNReal := ⟨∑ j, |C' j|, Finset.sum_nonneg fun j _ => abs_nonneg _⟩
  have h := isIntegrableAtOfClass_one_of_lieBracket_eq_zero_nhds (X := Z)
    (DX := fun i y => fderiv ℝ (Z i) y) (K := K) (M := M)
    (fun i y => (((hZc i).differentiable one_ne_zero) y).hasFDerivAt) hdc
    (fun i y => (hC i y).trans (hsum C i)) (fun i y => (hC' i y).trans (hsum C' i)) hbr hli
  exact h.congr_nhds hZD

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", for distributions spanned by finitely many `C¹`
fields, with a `C¹` defining map:** on a finite-dimensional real space, if `span{g₁, …, g_m}` is
regular and involutive on an open set `U ∋ q`, it is integrable at `q` with a defining map of
class `C¹`. -/
theorem isIntegrableAtOfClass_one_of_spanAt {U : Set E} (hU : IsOpen U) {m : ℕ}
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ 1 (g j))
    (hreg : IsRegularOn (spanAt (Set.range g)) U)
    (hinv : IsInvolutiveOn (spanAt (Set.range g)) U) {q : E} (hq : q ∈ U) :
    IsIntegrableAtOfClass 1 (spanAt (Set.range g)) q :=
  isIntegrableAtOfClass_one_of_isInvolutiveOn hU hreg hinv hq hg (Eventually.of_forall fun _ => rfl)

open scoped ContDiff in
/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", in the form of the named statement
`FrobeniusSufficiency` with `C¹` defining maps in place of `C^∞`:** on a finite-dimensional real
space, every regular involutive distribution spanned by finitely many smooth fields is integrable
near every point with a defining map of class `C¹`. -/
theorem frobeniusSufficiency_classOne (m : ℕ) (g : Fin m → E → E) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hreg : IsRegularOn (spanAt (Set.range g)) Set.univ)
    (hinv : IsInvolutiveOn (spanAt (Set.range g)) Set.univ) (q : E) :
    IsIntegrableAtOfClass 1 (spanAt (Set.range g)) q :=
  isIntegrableAtOfClass_one_of_spanAt isOpen_univ (fun j => (hg j).of_le (by simp)) hreg hinv
    (mem_univ q)

end Nonholonomic
end RoboLean
