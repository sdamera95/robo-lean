import RoboLean.Nonholonomic.FrobeniusFrame
import RoboLean.Nonholonomic.FlowBoxSmooth

/-!
# Frobenius' theorem with smooth defining functions (MLS Theorem 7.2, p. 326)

**What MLS prints.** Theorem 7.2 (Frobenius, p. 326): "A regular distribution is integrable if and
only if it is involutive", stated without proof; integrability is eq. (7.9): near every point,
smooth `h₁, …, h_{n−k}` with independent rows `∂hᵢ/∂q` whose level sets are the integral manifolds.

**Proved here.**

* The chart criterion with defining maps of class `C^n` (`isIntegrableAtOfClass_of_chart`) and
  composed flows of class `C^n` (`contDiff_composedFlow_of_contDiff`).
* **Frobenius for a smooth frame commuting near `q`** (`isIntegrableAt_of_lieBracket_eq_zero_nhds`):
  smooth fields with compact support, brackets vanishing near `q`, independent at `q`, span a
  distribution integrable at `q` with smooth defining functions. The flow box is built from the
  two-sided flows, smooth in the time and the state together
  (`contDiff_twoSidedFlow_of_hasCompactSupport`, `Nonholonomic/FlowBoxSmooth`).
* A smooth commuting frame near a point of a regular involutive distribution spanned by smooth
  fields (`exists_commutingFrame_smooth`).
* **Theorem 7.2, "if", with smooth defining functions** (`isIntegrableAt_of_isInvolutiveOn`,
  `isIntegrableAt_of_spanAt`), so that the named statement holds on every finite-dimensional space
  (`frobeniusSufficiency : FrobeniusSufficiency E`) and Theorem 7.2 is an equivalence with no
  named hypothesis (`frobenius_iff`).

**Route.** As in `Nonholonomic/Frobenius`, `Nonholonomic/FrobeniusLocal` and
`Nonholonomic/FrobeniusFrame`, which give `C¹` defining maps; the only change is the regularity of
the flows: the flows of smooth fields with compact support are smooth in the time and the state
(`Control/FlowCk`, `Nonholonomic/FlowBoxSmooth`), so the composed flow `Ψ` is smooth, and the
inverse function theorem gives a smooth local inverse.

**Hypotheses against MLS.** MLS works on `ℝⁿ`; here any finite-dimensional real space (the named
statement's setting). The distribution is spanned by finitely many smooth fields, regular and
involutive on the whole space (the named statement) or on an open set (`isIntegrableAt_of_spanAt`).

**Conventions.** Mathlib's bracket `lieBracket ℝ` (the book's sign); `IsIntegrableAt` (smooth
defining maps, Chapter 7, `Integrability`) and `IsIntegrableAtOfClass` (`Integrability2`); flows
`IsDifferentiableFlow` (time first) and two-sided flows `twoSidedFlow`; `composedFlow Φ t x`
applies `Φ_k` first; the coordinates of `ℝᵏ` are `Pi.single i 1`.
-/

noncomputable section

open Set Filter Topology VectorField Metric
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {k : ℕ}

/-! ### The chart criterion and composed flows of class `C^n` -/

/-- **A chart whose coordinate lines are integral curves gives an integral manifold (MLS eq. (7.9)
and Theorem 7.2, p. 326):** on a finite-dimensional real space, let `C` be a subspace and
`Ψ : ℝᵏ × C → E` a map of class `C^n`, `n ≠ 0`, whose derivative at `z₀` is a linear
isomorphism, and suppose that near `z₀` the partial derivative of `Ψ` along the `i`-th coordinate of
`ℝᵏ` is `Xᵢ(Ψ(z))`. Then `span{X₁, …, X_k}` is integrable at `Ψ(z₀)` with a defining map of class
`C^n` (`IsIntegrableAtOfClass n`; for `n = ∞` this is `IsIntegrableAt`). -/
theorem isIntegrableAtOfClass_of_chart [FiniteDimensional ℝ E] {n : WithTop ℕ∞} (hn : n ≠ 0)
    {C : Submodule ℝ E}
    {Ψ : (Fin k → ℝ) × C → E} {X : Fin k → E → E} (hΨ : ContDiff ℝ n Ψ)
    {z₀ : (Fin k → ℝ) × C}
    (hinv : ∃ A : ((Fin k → ℝ) × C) ≃L[ℝ] E, HasFDerivAt Ψ (A : (Fin k → ℝ) × C →L[ℝ] E) z₀)
    (htan : ∀ᶠ z in 𝓝 z₀, ∀ i, fderiv ℝ Ψ z ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i (Ψ z)) :
    IsIntegrableAtOfClass n (spanAt (Set.range X)) (Ψ z₀) := by
  classical
  obtain ⟨A₀, hA₀⟩ := hinv
  have hca : ContDiffAt ℝ n Ψ z₀ := hΨ.contDiffAt
  set e := hca.toOpenPartialHomeomorph Ψ hA₀ hn with he
  have hcoe : (e : (Fin k → ℝ) × C → E) = Ψ := rfl
  -- the derivative stays invertible near `z₀`
  have hinvev : ∀ᶠ z in 𝓝 z₀, fderiv ℝ Ψ z ∈
      range ((↑) : (((Fin k → ℝ) × C) ≃L[ℝ] E) → (Fin k → ℝ) × C →L[ℝ] E) :=
    (hΨ.continuous_fderiv hn).continuousAt.eventually_mem
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨A₀, hA₀.fderiv.symm⟩)
  obtain ⟨O, hOP, hO, hz₀O⟩ := _root_.eventually_nhds_iff.1 (hinvev.and htan)
  set U := e '' (e.source ∩ O) with hUdef
  have hUo : IsOpen U := e.isOpen_image_source_inter hO
  have hqU : Ψ z₀ ∈ U :=
    ⟨z₀, ⟨hca.mem_toOpenPartialHomeomorph_source hA₀ hn, hz₀O⟩, rfl⟩
  set L : C ≃L[ℝ] (Fin (Module.finrank ℝ C) → ℝ) :=
    (Module.finBasis ℝ C).equivFun.toContinuousLinearEquiv with hL
  set h : E → Fin (Module.finrank ℝ C) → ℝ := fun y => L (e.symm y).2 with hh
  -- the data at a point of `U`
  have key : ∀ y ∈ U, ∃ A : ((Fin k → ℝ) × C) ≃L[ℝ] E, y ∈ e.target ∧
      HasFDerivAt e (A : (Fin k → ℝ) × C →L[ℝ] E) (e.symm y) ∧
        ∀ i, A ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i y := by
    rintro y ⟨z, ⟨hzs, hzO⟩, rfl⟩
    obtain ⟨⟨A, hA⟩, htz⟩ := hOP z hzO
    have hsy : e.symm (e z) = z := e.left_inv hzs
    refine ⟨A, e.map_source hzs, ?_, fun i => ?_⟩
    · rw [hsy, hcoe, hA]
      exact (hΨ.differentiable hn z).hasFDerivAt
    · have h1 := htz i
      rw [← hA, ContinuousLinearEquiv.coe_coe] at h1
      rw [hcoe]
      exact h1
  have hderiv : ∀ y ∈ U, ∃ A : ((Fin k → ℝ) × C) ≃L[ℝ] E,
      (∀ i, A ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i y) ∧
      HasFDerivAt h ((L : C →L[ℝ] Fin (Module.finrank ℝ C) → ℝ).comp
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) C).comp
          (A.symm : E →L[ℝ] (Fin k → ℝ) × C))) y ∧ ContDiffAt ℝ n h y := by
    intro y hy
    obtain ⟨A, hyt, hA, hAi⟩ := key y hy
    have hs := e.hasFDerivAt_symm hyt hA
    have hsc : ContDiffAt ℝ n e.symm y := e.contDiffAt_symm hyt hA hΨ.contDiffAt
    refine ⟨A, hAi, ?_, ?_⟩
    · exact (L : C →L[ℝ] Fin (Module.finrank ℝ C) → ℝ).hasFDerivAt.comp y
        (hasFDerivAt_snd.comp y hs)
    · exact (L : C →L[ℝ] Fin (Module.finrank ℝ C) → ℝ).contDiff.contDiffAt.comp y
        (contDiffAt_snd.comp y hsc)
  refine ⟨U, hUo, hqU, Module.finrank ℝ C, h, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨-, -, -, h3⟩ := hderiv y hy
    exact h3
  obtain ⟨A, hAi, hd, -⟩ := hderiv y hy
  rw [hd.fderiv]
  constructor
  · intro w
    refine ⟨A ((0 : Fin k → ℝ), L.symm w), ?_⟩
    simp
  · rw [spanAt_range]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [← hAi i]
      simp
    · intro v hv
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
        Function.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe] at hv
      have h2 : (A.symm v).2 = 0 := L.injective (by rw [hv, map_zero])
      have hv' : v = ∑ i, (A.symm v).1 i • X i y := by
        have hw : A.symm v = ∑ i, (A.symm v).1 i • ((Pi.single i 1 : Fin k → ℝ), (0 : C)) := by
          refine Prod.ext ?_ ?_
          · ext j
            simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
          · simp [Prod.snd_sum, h2]
        calc v = A (A.symm v) := (A.apply_symm_apply v).symm
          _ = A (∑ i, (A.symm v).1 i • ((Pi.single i 1 : Fin k → ℝ), (0 : C))) := congrArg A hw
          _ = ∑ i, (A.symm v).1 i • X i y := by simp only [map_sum, map_smul, hAi]
      rw [hv']
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The composition along a list of indices is `C^n` (for MLS pp. 330–331). -/
private theorem contDiff_foldr_of_contDiff {n : WithTop ℕ∞} {Φ : Fin k → ℝ → E → E}
    (hΦ : ∀ i, ContDiff ℝ n fun p : ℝ × E => Φ i p.1 p.2) (l : List (Fin k)) :
    ContDiff ℝ n fun p : (Fin k → ℝ) × E => l.foldr (fun i y => Φ i (p.1 i) y) p.2 := by
  induction l with
  | nil => simpa using contDiff_snd
  | cons i l ih =>
    simp only [List.foldr_cons]
    exact (hΦ i).comp (((contDiff_apply ℝ _ i).comp contDiff_fst).prodMk ih)

/-- **The composed flow is `C^n` in the times and the initial point (MLS pp. 330–331, for
Propositions 7.6–7.7 and Theorem 7.2, p. 326):** if every `(t, x) ↦ Φᵢ(t, x)` is of class `C^n`
on `ℝ × E`, so is `(t, x) ↦ composedFlow Φ t x` on `ℝᵏ × E` (`Φ_k` applied first). -/
theorem contDiff_composedFlow_of_contDiff {n : WithTop ℕ∞} {Φ : Fin k → ℝ → E → E}
    (hΦ : ∀ i, ContDiff ℝ n fun p : ℝ × E => Φ i p.1 p.2) :
    ContDiff ℝ n fun p : (Fin k → ℝ) × E => composedFlow Φ p.1 p.2 :=
  contDiff_foldr_of_contDiff hΦ _

omit [NormedSpace ℝ E] in
/-- Points along a composition of maps that move points by at most `M δ` (for MLS
pp. 330–331). -/
private theorem norm_foldr_sub_le {Φ : Fin k → ℝ → E → E} {M δ : ℝ}
    (hdisp : ∀ a τ y, ‖Φ a τ y - y‖ ≤ M * |τ|) (hM : 0 ≤ M) {t : Fin k → ℝ}
    (ht : ∀ i, |t i| ≤ δ) (l : List (Fin k)) (x : E) :
    ‖l.foldr (fun i y => Φ i (t i) y) x - x‖ ≤ l.length * (M * δ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc ‖Φ a (t a) (l.foldr (fun i y => Φ i (t i) y) x) - x‖
        ≤ ‖Φ a (t a) (l.foldr (fun i y => Φ i (t i) y) x) - l.foldr (fun i y => Φ i (t i) y) x‖ +
          ‖l.foldr (fun i y => Φ i (t i) y) x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M * δ + l.length * (M * δ) :=
          add_le_add ((hdisp _ _ _).trans (mul_le_mul_of_nonneg_left (ht a) hM)) ih
      _ = (l.length + 1) * (M * δ) := by ring

omit [NormedSpace ℝ E] in
/-- Moving one time out of a composition of maps that commute near the base point (for MLS
p. 324 and pp. 330–331). -/
private theorem foldr_add_single_on {Φ : Fin k → ℝ → E → E} {j : Fin k} {s M δ : ℝ} {x : E}
    (hdisp : ∀ a τ y, ‖Φ a τ y - y‖ ≤ M * |τ|) (hM : 0 ≤ M)
    (hcomm : ∀ a τ y, |τ| ≤ δ → ‖y - x‖ ≤ k * (M * δ) → Φ j s (Φ a τ y) = Φ a τ (Φ j s y))
    (hadd : ∀ τ y, Φ j (τ + s) y = Φ j s (Φ j τ y)) {t : Fin k → ℝ} (ht : ∀ i, |t i| ≤ δ)
    (l : List (Fin k)) (hl : l.Nodup) (hlen : l.length ≤ k) :
    l.foldr (fun i y => Φ i ((t + Pi.single j s : Fin k → ℝ) i) y) x =
      if j ∈ l then Φ j s (l.foldr (fun i y => Φ i (t i) y) x)
        else l.foldr (fun i y => Φ i (t i) y) x := by
  have hMδ : 0 ≤ M * δ := mul_nonneg hM ((abs_nonneg _).trans (ht j))
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hlen' : l.length ≤ k := by simp at hlen; omega
    have hF : ‖l.foldr (fun i y => Φ i (t i) y) x - x‖ ≤ k * (M * δ) :=
      (norm_foldr_sub_le hdisp hM ht l x).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen') hMδ)
    simp only [List.foldr_cons, List.mem_cons]
    rw [ih hl.2 hlen']
    by_cases haj : a = j
    · subst haj
      simp only [hl.1, ↓reduceIte, true_or, Pi.add_apply, Pi.single_eq_same]
      exact hadd _ _
    · have hja : ¬ j = a := fun h => haj h.symm
      simp only [hja, false_or, Pi.add_apply, Pi.single_eq_of_ne haj, add_zero]
      split_ifs with hj
      · exact (hcomm a (t a) _ (ht a) hF).symm
      · rfl

/-! ### Frobenius for a smooth frame commuting near a point -/

/-- **Frobenius for a smooth frame commuting near `q`, with a smooth defining map (MLS Theorem
7.2, p. 326, "if", with p. 324):** on a finite-dimensional real space, let `X₁, …, X_k` be smooth
with compact support, let `[Xᵢ, Xⱼ] = 0` on a neighbourhood of `q` (Mathlib's bracket, the book's
sign), and let `X₁(q), …, X_k(q)` be linearly independent. Then `Δ = span{X₁, …, X_k}` is
integrable at `q` (`IsIntegrableAt`, smooth defining functions as in MLS eq. (7.9)). -/
theorem isIntegrableAt_of_lieBracket_eq_zero_nhds [FiniteDimensional ℝ E]
    {X : Fin k → E → E} (hXc : ∀ i, ContDiff ℝ ∞ (X i)) (hXs : ∀ i, HasCompactSupport (X i))
    {q : E} (hbr : ∀ᶠ y in 𝓝 q, ∀ i j, lieBracket ℝ (X i) (X j) y = 0)
    (hli : LinearIndependent ℝ fun i => X i q) :
    IsIntegrableAt (spanAt (Set.range X)) q := by
  have hdc : ∀ i, Continuous (fderiv ℝ (X i)) := fun i => (hXc i).continuous_fderiv (by simp)
  choose C hC using fun i => (hdc i).bounded_above_of_compact_support ((hXs i).fderiv (𝕜 := ℝ))
  choose C' hC' using fun i => (hXc i).continuous.bounded_above_of_compact_support (hXs i)
  have hsum : ∀ (c : Fin k → ℝ) (i : Fin k), c i ≤ ∑ j, |c j| := fun c i =>
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))
  set K : NNReal := ⟨∑ j, |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _⟩
  set M : NNReal := ⟨∑ j, |C' j|, Finset.sum_nonneg fun j _ => abs_nonneg _⟩
  have hK : ∀ i y, ‖fderiv ℝ (X i) y‖ ≤ K := fun i y => (hC i y).trans (hsum C i)
  have hM : ∀ i y, ‖X i y‖ ≤ M := fun i y => (hC' i y).trans (hsum C' i)
  choose φ φ' D D' hφ hφ' hΦc using fun i => contDiff_twoSidedFlow_of_hasCompactSupport (hXc i)
    (hXs i)
  set Φ : Fin k → ℝ → E → E := fun i => twoSidedFlow (φ i) (φ' i) with hΦdef
  have h0 : ∀ i x, Φ i 0 x = x := fun i x => twoSidedFlow_zero (hφ i) x
  have hX0 : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0 := fun i x => by
    have h : HasDerivAt (fun t => Φ i t x) (X i (Φ i 0 x)) 0 :=
      isIntegralCurve_twoSidedFlow (hφ i) (hφ' i) x 0
    rwa [h0 i x] at h
  have hdisp : ∀ a τ y, ‖Φ a τ y - y‖ ≤ (M : ℝ) * |τ| := fun a τ y =>
    norm_twoSidedFlow_sub_le (hφ a) (hφ' a) (hM a) τ y
  have hadd : ∀ j s τ y, Φ j (τ + s) y = Φ j s (Φ j τ y) := fun j s τ y => by
    rw [add_comm]; exact (twoSidedFlow_add (hφ j) (hφ' j) s τ y).symm
  -- the radius where the brackets vanish, and the small times
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hbr
  set δ : ℝ := ρ / (4 * ((k : ℝ) + 2) * ((M : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hMδ : ((k : ℝ) + 2) * ((M : ℝ) * δ) ≤ ρ / 4 := by
    rw [hδdef]
    have hM0 : (0 : ℝ) ≤ M := M.coe_nonneg
    have hk0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [show ((k : ℝ) + 2) * ((M : ℝ) * (ρ / (4 * ((k : ℝ) + 2) * ((M : ℝ) + 1)))) =
      ρ / 4 * ((M : ℝ) / ((M : ℝ) + 1)) by field_simp]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  -- local commutation of the two-sided flows
  have hcomm : ∀ x : E, ‖x - q‖ < ρ / 2 → ∀ j a : Fin k, ∀ s τ y, |s| ≤ δ → |τ| ≤ δ →
      ‖y - x‖ ≤ k * (M * δ) → Φ j s (Φ a τ y) = Φ a τ (Φ j s y) := by
    intro x hx j a s τ y hs hτ hy
    refine twoSidedFlow_comm_of_lieBracket_eq_zero_on (hφ j) (hφ' j) (hφ a) (hφ' a) (hK j) (hK a)
      (W := ball q ρ) (fun z hz => hball z hz j a) fun σ τ' hσ hτ' => ?_
    rw [mem_ball, dist_eq_norm]
    have h1 := hdisp j τ' (Φ a σ y)
    have h2 := hdisp a σ y
    have hM0 : (0 : ℝ) ≤ M := M.coe_nonneg
    have e1 : (M : ℝ) * |τ'| ≤ M * δ := mul_le_mul_of_nonneg_left (hτ'.trans hs) hM0
    have e2 : (M : ℝ) * |σ| ≤ M * δ := mul_le_mul_of_nonneg_left (hσ.trans hτ) hM0
    calc ‖Φ j τ' (Φ a σ y) - q‖
        ≤ ‖Φ j τ' (Φ a σ y) - Φ a σ y‖ + ‖Φ a σ y - y‖ + ‖y - x‖ + ‖x - q‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (Φ j τ' (Φ a σ y)) (Φ a σ y) q
          have := norm_sub_le_norm_sub_add_norm_sub (Φ a σ y) y q
          have := norm_sub_le_norm_sub_add_norm_sub y x q
          linarith
      _ < ρ := by nlinarith [hMδ]
  -- the flow box and its coordinate lines near `(0, 0)`
  obtain ⟨C, -, A, -, hA⟩ := exists_flowBox_fderiv (fun i => (hΦc i).of_le (by simp)) h0 hX0 hli
  set Ψ : (Fin k → ℝ) × C → E := fun p => composedFlow Φ p.1 (q + (p.2 : E)) with hΨ
  have hin : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E)) :=
    contDiff_fst.prodMk (contDiff_const.add (C.subtypeL.contDiff.comp contDiff_snd))
  have hΨc : ContDiff ℝ ∞ Ψ := (contDiff_composedFlow_of_contDiff hΦc).comp hin
  have hmove : ∀ z : (Fin k → ℝ) × C, ‖z‖ < min (δ / 2) (ρ / 2) → ∀ i, ∀ s, |s| ≤ δ →
      composedFlow Φ (z.1 + Pi.single i s) (q + (z.2 : E)) =
        Φ i s (composedFlow Φ z.1 (q + (z.2 : E))) := by
    intro z hz i s hs
    have hz1 : ∀ a, |z.1 a| ≤ δ := fun a =>
      ((norm_le_pi_norm z.1 a).trans ((norm_fst_le z).trans (hz.le.trans
        ((min_le_left _ _).trans (by linarith))))).trans' (le_of_eq (Real.norm_eq_abs _).symm)
    have hx : ‖q + (z.2 : E) - q‖ < ρ / 2 := by
      rw [add_sub_cancel_left]
      calc ‖(z.2 : E)‖ = ‖z.2‖ := rfl
        _ ≤ ‖z‖ := norm_snd_le z
        _ < ρ / 2 := hz.trans_le (min_le_right _ _)
    have h := foldr_add_single_on (hdisp) M.coe_nonneg
      (fun a τ y hτ hy => hcomm _ hx i a s τ y hs hτ hy) (hadd i s) hz1 (List.finRange k)
      (List.nodup_finRange k) (by simp)
    simp only [List.mem_finRange, ↓reduceIte] at h
    exact h
  have htan : ∀ᶠ z in 𝓝 ((0 : Fin k → ℝ), (0 : C)), ∀ i,
      fderiv ℝ Ψ z ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i (Ψ z) := by
    filter_upwards [ball_mem_nhds _ (lt_min (half_pos hδ) (half_pos hρ))] with z hz i
    rw [mem_ball, Prod.mk_zero_zero, dist_zero_right] at hz
    have hline : HasDerivAt (fun s : ℝ => z + s • ((Pi.single i 1 : Fin k → ℝ), (0 : C)))
        ((Pi.single i 1 : Fin k → ℝ), (0 : C)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        ((Pi.single i 1 : Fin k → ℝ), (0 : C))).const_add z
    have hcomp := ((hΨc.differentiable (by simp)) z).hasFDerivAt.comp_hasDerivAt_of_eq
      (0 : ℝ) hline (by simp)
    have hfun : (Ψ ∘ fun s : ℝ => z + s • ((Pi.single i 1 : Fin k → ℝ), (0 : C))) =
        fun s => composedFlow Φ (z.1 + Pi.single i s) (q + (z.2 : E)) := by
      funext s
      simp only [Function.comp_apply, hΨ, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
        Prod.smul_snd, smul_zero, add_zero]
      congr 2
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hfun] at hcomp
    have hloc : (fun s => composedFlow Φ (z.1 + Pi.single i s) (q + (z.2 : E))) =ᶠ[𝓝 0]
        fun s => Φ i s (composedFlow Φ z.1 (q + (z.2 : E))) := by
      filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with s hs
      exact hmove z hz i s (abs_le.2 ⟨hs.1.le, hs.2.le⟩)
    have hd : HasDerivAt (fun s => Φ i s (composedFlow Φ z.1 (q + (z.2 : E))))
        (X i (composedFlow Φ z.1 (q + (z.2 : E)))) 0 := hX0 i _
    exact hcomp.unique (hd.congr_of_eventuallyEq hloc)
  have hres := isIntegrableAtOfClass_of_chart (n := ∞) (by simp) hΨc ⟨A, hA⟩ htan
  have hΨ0 : Ψ ((0 : Fin k → ℝ), (0 : C)) = q := by
    simp only [hΨ, ZeroMemClass.coe_zero, add_zero]
    exact composedFlow_zero h0 q
  rwa [hΨ0] at hres

variable [FiniteDimensional ℝ E]

/-! ### A smooth commuting frame -/

/-- The frame map `a ↦ Σᵢ aᵢ fᵢ(y)` (for MLS p. 325). -/
private def frameMap (f : Fin k → E → E) (y : E) : (Fin k → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).smulRight (f i y)

omit [FiniteDimensional ℝ E] in
private theorem frameMap_apply (f : Fin k → E → E) (y : E) (a : Fin k → ℝ) :
    frameMap f y a = ∑ i, a i • f i y := by
  simp [frameMap]

/-- **A smooth commuting frame near a point (the linear-algebra step of the proof of MLS Theorem 7.2,
p. 326, with p. 324):** on a finite-dimensional real space, let `D` be regular and involutive on
an open set `U ∋ q` and equal near `q` to `span{g₁, …, g_m}` for smooth fields `gⱼ`. Then for
some `k` there are smooth fields `Z₁, …, Z_k` with compact support, linearly independent at `q`, with `[Zᵢ, Zⱼ] = 0` near `q` (Mathlib's bracket, the book's sign) and
`span{Z₁, …, Z_k} = D` near `q`. -/
theorem exists_commutingFrame_smooth {D : E → Submodule ℝ E} {U : Set E} (hU : IsOpen U)
    (hreg : IsRegularOn D U) (hinv : IsInvolutiveOn D U) {q : E} (hq : q ∈ U) {m : ℕ}
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hspan : ∀ᶠ y in 𝓝 q, D y = spanAt (Set.range g) y) :
    ∃ (k : ℕ) (Z : Fin k → E → E), (∀ i, ContDiff ℝ ∞ (Z i)) ∧ (∀ i, HasCompactSupport (Z i)) ∧
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
  have hGc : ContDiff ℝ ∞ G := by
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
  have hMc : ContDiff ℝ ∞ Mm :=
    ((ContinuousLinearMap.compL ℝ (Fin k → ℝ) E (Fin k → ℝ)) P).contDiff.comp hGc
  have hMq : Mm q = 1 := by ext1 a; simp [hMm, hPG]
  set W₀ : Set E := Mm ⁻¹' {x | IsUnit x} with hW₀
  have hW₀o : IsOpen W₀ := Units.isOpen.preimage hMc.continuous
  have hqW₀ : q ∈ W₀ := by simp [hW₀, hMq]
  set Y : Fin k → E → E := fun i y => G y (Ring.inverse (Mm y) (Pi.single i 1)) with hYdef
  have hYc : ∀ i, ∀ y ∈ W₀, ContDiffAt ℝ ∞ (Y i) y := fun i y hy => by
    have hu : IsUnit (Mm y) := hy
    have hinvc : ContDiffAt ℝ ∞ (fun y => Ring.inverse (Mm y)) y := by
      have h := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
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
  have hZc : ∀ i, ContDiff ℝ ∞ (Z i) := fun i => by
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
    have hmem := hinv (Z i) (Z j) (fun z _ => ((hZc i).differentiable (by simp)) z)
      (fun z _ => ((hZc j).differentiable (by simp)) z) (fun z _ => hZmem i z)
      (fun z _ => hZmem j z) y hyU
    have hyO : y ∈ O := (hεsub (hsmall y hy)).2.2
    rw [hOD y hyO] at hmem
    have hPd : ∀ a, P.comp (fderiv ℝ (Z a) y) = 0 := fun a => by
      have h1 := P.hasFDerivAt.comp y (((hZc a).differentiable (by simp)) y).hasFDerivAt
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

/-! ### Theorem 7.2 with smooth defining functions -/

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", with smooth defining functions:** on a
finite-dimensional real space, a distribution `D` regular and involutive on an open set `U ∋ q`
and equal near `q` to the span of finitely many smooth fields is integrable at `q`
(`IsIntegrableAt`, MLS eq. (7.9)). -/
theorem isIntegrableAt_of_isInvolutiveOn {D : E → Submodule ℝ E} {U : Set E}
    (hU : IsOpen U) (hreg : IsRegularOn D U) (hinv : IsInvolutiveOn D U) {q : E} (hq : q ∈ U)
    {m : ℕ} {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hspan : ∀ᶠ y in 𝓝 q, D y = spanAt (Set.range g) y) :
    IsIntegrableAt D q := by
  obtain ⟨k, Z, hZc, hZcs, hli, hbr, hZD⟩ := exists_commutingFrame_smooth hU hreg hinv hq hg hspan
  exact IsIntegrableAtOfClass.congr_nhds (n := ∞)
    (isIntegrableAt_of_lieBracket_eq_zero_nhds hZc hZcs hbr hli) hZD

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", for distributions spanned by finitely many smooth
fields:** on a finite-dimensional real space, if `span{g₁, …, g_m}` is regular and involutive on an
open set `U ∋ q`, it is integrable at `q` with smooth defining functions (`IsIntegrableAt`). -/
theorem isIntegrableAt_of_spanAt {U : Set E} (hU : IsOpen U) {m : ℕ}
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hreg : IsRegularOn (spanAt (Set.range g)) U)
    (hinv : IsInvolutiveOn (spanAt (Set.range g)) U) {q : E} (hq : q ∈ U) :
    IsIntegrableAt (spanAt (Set.range g)) q :=
  isIntegrableAt_of_isInvolutiveOn hU hreg hinv hq hg (Eventually.of_forall fun _ => rfl)

/-- **MLS Theorem 7.2 (Frobenius), p. 326, "if", the named statement proved:** on every
finite-dimensional real space (MLS: `ℝⁿ`), every regular involutive distribution spanned by
finitely many smooth fields is integrable near every point with smooth defining functions
(`FrobeniusSufficiency E`). -/
theorem frobeniusSufficiency : FrobeniusSufficiency E :=
  fun _ _ hg hreg hinv q => isIntegrableAt_of_spanAt isOpen_univ hg hreg hinv (mem_univ q)

/-- **MLS Theorem 7.2 (Frobenius), p. 326: "A regular distribution is integrable if and only if it
is involutive",** for distributions spanned by finitely many smooth fields on a finite-dimensional
real space, with smooth defining functions (`IsIntegrableAt`, eq. (7.9)) and no named
hypothesis. -/
theorem frobenius_iff {m : ℕ} {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hreg : IsRegularOn (spanAt (Set.range g)) Set.univ) :
    (∀ q, IsIntegrableAt (spanAt (Set.range g)) q) ↔
      IsInvolutiveOn (spanAt (Set.range g)) Set.univ :=
  frobenius frobeniusSufficiency hg hreg

end Nonholonomic
end RoboLean
