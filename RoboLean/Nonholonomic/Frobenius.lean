import RoboLean.Nonholonomic.FlowBox
import RoboLean.Nonholonomic.CommutingFlows
import RoboLean.Nonholonomic.Integrability2
import RoboLean.Nonholonomic.VectorField

/-!
# Frobenius' theorem for a frame of commuting fields (MLS Theorem 7.2, p. 326, "if")

**What MLS prints.** Theorem 7.2 (Frobenius, p. 326): "A regular distribution is integrable if and
only if it is involutive", stated without proof; integrability is eq. (7.9): near every point,
smooth `h₁, …, h_{n−k}` with independent rows `∂hᵢ/∂q` and `L_f hᵢ = 0` for `f ∈ Δ`. Fields with
`[f, g] = 0` "commute": their flows commute and the square (7.8) closes (p. 324).

**Proved here.**

* A chart criterion (`isIntegrableAtOfClass_one_of_chart`): if a `C¹` map `Ψ : ℝᵏ × C → E` has an
  invertible derivative at `z₀` and its partial derivatives in the first `k` variables are
  `X₁ ∘ Ψ, …, X_k ∘ Ψ` near `z₀`, then `span{X₁, …, X_k}` is integrable at `Ψ(z₀)` with a `C¹`
  defining map: `h` is the `C` component of `Ψ⁻¹`, in coordinates.
* Two-sided flows of fields with vanishing bracket commute for all real times
  (`twoSidedFlow_comm`), so a time of the composed flow `Φ₁(t₁, ⋯ Φ_k(t_k, x))` can be moved to
  the outside (`composedFlow_add_single`), and the partial derivative in `tᵢ` is `Xᵢ` at the image
  point (`fderiv_composedFlow_single`).
* **Frobenius for a commuting frame** (`isIntegrableAtOfClass_one_of_lieBracket_eq_zero`): on a
  finite-dimensional space, if `X₁, …, X_k` have continuous bounded derivatives, pairwise vanishing
  brackets everywhere, and are linearly independent at `q`, then `Δ = span{X₁, …, X_k}` is
  integrable at `q` with a `C¹` defining map (`IsIntegrableAtOfClass 1`).

**Continued elsewhere.** Brackets vanishing only near `q` are treated in
`Nonholonomic/FrobeniusLocal`, and the passage from a regular involutive distribution to a frame
commuting near `q` in
`Nonholonomic/FrobeniusFrame`, which proves Theorem 7.2's "if" with `C¹` defining maps. The named
`FrobeniusSufficiency` asks a `C^∞` defining map, which needs flows of class `C^∞` in the initial
state; the flows of this library are `C¹`.

**Conventions.** Mathlib's bracket `lieBracket ℝ X Y` (the book's sign); flows
`IsDifferentiableFlow`
(time first) and two-sided flows `twoSidedFlow`; `composedFlow Φ t x` applies `Φ_k` first; the
coordinates of `ℝᵏ` are `Pi.single i 1`.
-/

noncomputable section

open Set Filter Topology VectorField

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {k : ℕ}

/-! ### The chart criterion -/

/-- **A chart whose coordinate lines are integral curves gives an integral manifold (MLS eq. (7.9)
and Theorem 7.2, p. 326):** on a finite-dimensional real space, let `C` be a subspace and
`Ψ : ℝᵏ × C → E` a `C¹` map whose derivative at `z₀` is a linear isomorphism, and suppose that
near `z₀` the partial derivative of `Ψ` along the `i`-th coordinate of `ℝᵏ` is `Xᵢ(Ψ(z))`. Then
`span{X₁, …, X_k}` is integrable at `Ψ(z₀)` with a defining map of class `C¹`. -/
theorem isIntegrableAtOfClass_one_of_chart [FiniteDimensional ℝ E] {C : Submodule ℝ E}
    {Ψ : (Fin k → ℝ) × C → E} {X : Fin k → E → E} (hΨ : ContDiff ℝ 1 Ψ)
    {z₀ : (Fin k → ℝ) × C}
    (hinv : ∃ A : ((Fin k → ℝ) × C) ≃L[ℝ] E, HasFDerivAt Ψ (A : (Fin k → ℝ) × C →L[ℝ] E) z₀)
    (htan : ∀ᶠ z in 𝓝 z₀, ∀ i, fderiv ℝ Ψ z ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i (Ψ z)) :
    IsIntegrableAtOfClass 1 (spanAt (Set.range X)) (Ψ z₀) := by
  classical
  obtain ⟨A₀, hA₀⟩ := hinv
  have hca : ContDiffAt ℝ 1 Ψ z₀ := hΨ.contDiffAt
  set e := hca.toOpenPartialHomeomorph Ψ hA₀ one_ne_zero with he
  have hcoe : (e : (Fin k → ℝ) × C → E) = Ψ := rfl
  -- the derivative stays invertible near `z₀`
  have hinvev : ∀ᶠ z in 𝓝 z₀, fderiv ℝ Ψ z ∈
      range ((↑) : (((Fin k → ℝ) × C) ≃L[ℝ] E) → (Fin k → ℝ) × C →L[ℝ] E) :=
    (hΨ.continuous_fderiv one_ne_zero).continuousAt.eventually_mem
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨A₀, hA₀.fderiv.symm⟩)
  obtain ⟨O, hOP, hO, hz₀O⟩ := eventually_nhds_iff.1 (hinvev.and htan)
  set U := e '' (e.source ∩ O) with hUdef
  have hUo : IsOpen U := e.isOpen_image_source_inter hO
  have hqU : Ψ z₀ ∈ U :=
    ⟨z₀, ⟨hca.mem_toOpenPartialHomeomorph_source hA₀ one_ne_zero, hz₀O⟩, rfl⟩
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
      exact (hΨ.differentiable one_ne_zero z).hasFDerivAt
    · have h1 := htz i
      rw [← hA, ContinuousLinearEquiv.coe_coe] at h1
      rw [hcoe]
      exact h1
  have hderiv : ∀ y ∈ U, ∃ A : ((Fin k → ℝ) × C) ≃L[ℝ] E,
      (∀ i, A ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i y) ∧
      HasFDerivAt h ((L : C →L[ℝ] Fin (Module.finrank ℝ C) → ℝ).comp
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) C).comp
          (A.symm : E →L[ℝ] (Fin k → ℝ) × C))) y ∧ ContDiffAt ℝ 1 h y := by
    intro y hy
    obtain ⟨A, hyt, hA, hAi⟩ := key y hy
    have hs := e.hasFDerivAt_symm hyt hA
    have hsc : ContDiffAt ℝ 1 e.symm y := e.contDiffAt_symm hyt hA hΨ.contDiffAt
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

/-! ### Commuting two-sided flows -/

/-- The derivative of the flow of `−X` is `−DX` (MLS pp. 322–323, the reversed flow). -/
private theorem fderiv_neg_eq' {X : E → E} {DX DX' : E → E →L[ℝ] E} {φ φ' : ℝ → ℝ → E → E}
    {D D' : ℝ → ℝ → E → E →L[ℝ] E}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D') (y : E) :
    DX' y = -DX y :=
  (hX'.hasFDerivAt_field 0 le_rfl y).unique (hX.hasFDerivAt_field 0 le_rfl y).neg

/-- The bracket of `−X` and `Y` (MLS Proposition 7.1, p. 325, with bilinearity). -/
private theorem lieBracket_neg_left' (X Y : E → E) :
    lieBracket ℝ (-X) Y = -lieBracket ℝ X Y := by
  rw [lieBracket_antisymm, lieBracket_neg_right, neg_neg, ← lieBracket_antisymm]

/-- **Two-sided flows of fields with vanishing bracket commute for all real times (MLS p. 324:
"if `[f, g] = 0` … `f` and `g` are said to commute"):** with flows `φ, φ'` of `X, −X` and `ψ, ψ'`
of `Y, −Y` (`IsDifferentiableFlow`, time first), `‖DX y‖ ≤ K` and `[X, Y] = 0` everywhere
(Mathlib's bracket, the book's sign), `φ^X_t ∘ φ^Y_s = φ^Y_s ∘ φ^X_t` for all real `t`, `s`. -/
theorem twoSidedFlow_comm {X Y : E → E} {DX DX' DY DY' : E → E →L[ℝ] E}
    {φ φ' ψ ψ' : ℝ → ℝ → E → E} {D₁ D₂ D₃ D₄ : ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ}
    (hX : Stability.IsDifferentiableFlow (fun _ => X) (fun _ => DX) φ D₁)
    (hX' : Stability.IsDifferentiableFlow (fun _ => -X) (fun _ => DX') φ' D₂)
    (hY : Stability.IsDifferentiableFlow (fun _ => Y) (fun _ => DY) ψ D₃)
    (hY' : Stability.IsDifferentiableFlow (fun _ => -Y) (fun _ => DY') ψ' D₄)
    (hXK : ∀ y, ‖DX y‖ ≤ K) (hXY : ∀ q, lieBracket ℝ X Y q = 0) (t s : ℝ) (x : E) :
    twoSidedFlow φ φ' t (twoSidedFlow ψ ψ' s x) = twoSidedFlow ψ ψ' s (twoSidedFlow φ φ' t x) := by
  have hXK' : ∀ y, ‖DX' y‖ ≤ K := fun y => by rw [fderiv_neg_eq' hX hX', norm_neg]; exact hXK y
  have h1 : ∀ q, lieBracket ℝ (-X) Y q = 0 := fun q => by
    rw [lieBracket_neg_left', Pi.neg_apply, hXY, neg_zero]
  have h2 : ∀ q, lieBracket ℝ X (-Y) q = 0 := fun q => by
    rw [lieBracket_neg_right, Pi.neg_apply, hXY, neg_zero]
  have h3 : ∀ q, lieBracket ℝ (-X) (-Y) q = 0 := fun q => by
    rw [lieBracket_neg_right, lieBracket_neg_left', neg_neg, hXY]
  by_cases ht : 0 ≤ t <;> by_cases hs : 0 ≤ s <;> simp only [twoSidedFlow, ht, hs, ↓reduceIte]
  · exact flow_comm_of_lieBracket_eq_zero hX hY hXK hXY ht hs x
  · exact flow_comm_of_lieBracket_eq_zero hX hY' hXK h2 ht (by linarith) x
  · exact flow_comm_of_lieBracket_eq_zero hX' hY hXK' h1 (by linarith) hs x
  · exact flow_comm_of_lieBracket_eq_zero hX' hY' hXK' h3 (by linarith) (by linarith) x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Moving one time out of a composition of commuting maps (for MLS p. 324 and
pp. 330–331). -/
private theorem foldr_add_single {Φ : Fin k → ℝ → E → E} {j : Fin k} {s : ℝ}
    (hcomm : ∀ a t y, Φ j s (Φ a t y) = Φ a t (Φ j s y))
    (hadd : ∀ t y, Φ j (t + s) y = Φ j s (Φ j t y)) (t : Fin k → ℝ) (l : List (Fin k))
    (x : E) :
    l.foldr (fun i y => Φ i ((t + Pi.single j s : Fin k → ℝ) i) y) x =
      (Φ j s)^[l.count j] (l.foldr (fun i y => Φ i (t i) y) x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    by_cases haj : a = j
    · subst haj
      rw [List.count_cons_self, Function.iterate_succ_apply', Pi.add_apply, Pi.single_eq_same,
        hadd, (show Function.Commute (Φ a s) (Φ a (t a)) from
          fun y => hcomm a (t a) y).iterate_left _ |>.eq]
    · rw [List.count_cons_of_ne haj, Pi.add_apply, Pi.single_eq_of_ne haj, add_zero,
        ((show Function.Commute (Φ j s) (Φ a (t a)) from
          fun y => hcomm a (t a) y).iterate_left _).eq]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Moving a time to the outside of the composed flow (MLS p. 324, commuting flows, for
pp. 330–331):** if `Φ_j(s, ·)` commutes with every `Φ_a(t, ·)` and
`Φ_j(t + s, ·) = Φ_j(s, Φ_j(t, ·))`,
then `composedFlow Φ (t + s eⱼ) x = Φ_j(s, composedFlow Φ t x)`. -/
theorem composedFlow_add_single {Φ : Fin k → ℝ → E → E} {j : Fin k} {s : ℝ}
    (hcomm : ∀ a t y, Φ j s (Φ a t y) = Φ a t (Φ j s y))
    (hadd : ∀ t y, Φ j (t + s) y = Φ j s (Φ j t y)) (t : Fin k → ℝ) (x : E) :
    composedFlow Φ (t + Pi.single j s) x = Φ j s (composedFlow Φ t x) := by
  have h := foldr_add_single hcomm hadd t (List.finRange k) x
  rw [List.count_finRange, Function.iterate_one] at h
  exact h

/-- **The coordinate lines of the composed flow of commuting fields are integral curves (MLS
p. 324 and pp. 330–331):** let `X₁, …, X_k` have flows `φᵢ` and reversed flows `φ'ᵢ`
(`IsDifferentiableFlow`, time first) with `‖DXᵢ y‖ ≤ K` and `[Xᵢ, Xⱼ] = 0` everywhere, and
`Φᵢ = twoSidedFlow φᵢ φ'ᵢ`. Then `s ↦ composedFlow Φ (t + s eⱼ) x` has at `s = 0` the derivative
`Xⱼ(composedFlow Φ t x)`. -/
theorem hasDerivAt_composedFlow_single {X : Fin k → E → E} {DX DX' : Fin k → E → E →L[ℝ] E}
    {φ φ' : Fin k → ℝ → ℝ → E → E} {D D' : Fin k → ℝ → ℝ → E → E →L[ℝ] E} {K : ℝ}
    (hX : ∀ i, Stability.IsDifferentiableFlow (fun _ => X i) (fun _ => DX i) (φ i) (D i))
    (hX' : ∀ i, Stability.IsDifferentiableFlow (fun _ => -X i) (fun _ => DX' i) (φ' i) (D' i))
    (hK : ∀ i y, ‖DX i y‖ ≤ K) (hbr : ∀ i j y, lieBracket ℝ (X i) (X j) y = 0) (j : Fin k)
    (t : Fin k → ℝ) (x : E) :
    HasDerivAt (fun s => composedFlow (fun i => twoSidedFlow (φ i) (φ' i)) (t + Pi.single j s) x)
      (X j (composedFlow (fun i => twoSidedFlow (φ i) (φ' i)) t x)) 0 := by
  set Φ : Fin k → ℝ → E → E := fun i => twoSidedFlow (φ i) (φ' i)
  have he : (fun s => composedFlow Φ (t + Pi.single j s) x) =
      fun s => Φ j s (composedFlow Φ t x) := by
    funext s
    refine composedFlow_add_single (fun a t' y => ?_) (fun t' y => ?_) t x
    · exact twoSidedFlow_comm (hX j) (hX' j) (hX a) (hX' a) (hK j) (hbr j a) s t' y
    · rw [add_comm]
      exact (twoSidedFlow_add (hX j) (hX' j) s t' y).symm
  rw [he]
  have h : HasDerivAt (fun s => Φ j s (composedFlow Φ t x)) (X j (Φ j 0 (composedFlow Φ t x))) 0 :=
    isIntegralCurve_twoSidedFlow (hX j) (hX' j) (composedFlow Φ t x) 0
  rwa [show Φ j 0 (composedFlow Φ t x) = composedFlow Φ t x from
    twoSidedFlow_zero (hX j) _] at h

/-! ### Frobenius for a commuting frame -/

/-- **Frobenius' theorem for a frame of commuting fields (MLS Theorem 7.2, p. 326, "if", with
p. 324), with a `C¹` defining map:** on a finite-dimensional real space, let `X₁, …, X_k` have
Fréchet derivatives `DXᵢ` that are continuous and bounded by `K`, let `[Xᵢ, Xⱼ] = 0` everywhere
(Mathlib's bracket, the book's sign), and let `X₁(q), …, X_k(q)` be linearly independent. Then
`Δ = span{X₁, …, X_k}` is integrable at `q` with a defining map of class `C¹`
(`IsIntegrableAtOfClass 1`; MLS asks smooth functions). The chart is the flow box
`(t, c) ↦ φ^{X₁}_{t₁} ∘ ⋯ ∘ φ^{X_k}_{t_k}(q + c)`. -/
theorem isIntegrableAtOfClass_one_of_lieBracket_eq_zero [FiniteDimensional ℝ E]
    {X : Fin k → E → E} {DX : Fin k → E → E →L[ℝ] E} {K : NNReal}
    (hDX : ∀ i y, HasFDerivAt (X i) (DX i y) y) (hDXc : ∀ i, Continuous (DX i))
    (hK : ∀ i y, ‖DX i y‖ ≤ K) (hbr : ∀ i j y, lieBracket ℝ (X i) (X j) y = 0) {q : E}
    (hli : LinearIndependent ℝ fun i => X i q) :
    IsIntegrableAtOfClass 1 (spanAt (Set.range X)) q := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  choose φ D hφ using fun i => Stability.exists_isDifferentiableFlow_autonomous (hDX i) (hDXc i)
    (hK i)
  choose φ' D' hφ' using fun i => Stability.exists_isDifferentiableFlow_autonomous
    (F := -X i) (DF := fun y => -DX i y) (fun y => (hDX i y).neg) (hDXc i).neg
    (fun y => by rw [norm_neg]; exact hK i y)
  set Φ : Fin k → ℝ → E → E := fun i => twoSidedFlow (φ i) (φ' i) with hΦdef
  have hΦc : ∀ i, ContDiff ℝ 1 fun p : ℝ × E => Φ i p.1 p.2 := fun i =>
    contDiff_twoSidedFlow (hφ i) (hφ' i) (hDXc i) (hK i)
  have h0 : ∀ i x, Φ i 0 x = x := fun i x => twoSidedFlow_zero (hφ i) x
  have hX0 : ∀ i x, HasDerivAt (fun t => Φ i t x) (X i x) 0 := fun i x => by
    have h : HasDerivAt (fun t => Φ i t x) (X i (Φ i 0 x)) 0 :=
      isIntegralCurve_twoSidedFlow (hφ i) (hφ' i) x 0
    rwa [h0 i x] at h
  obtain ⟨C, -, A, -, hA⟩ := exists_flowBox_fderiv hΦc h0 hX0 hli
  set Ψ : (Fin k → ℝ) × C → E := fun p => composedFlow Φ p.1 (q + (p.2 : E)) with hΨ
  have hin : ContDiff ℝ 1 fun p : (Fin k → ℝ) × C => (p.1, q + (p.2 : E)) :=
    contDiff_fst.prodMk (contDiff_const.add (C.subtypeL.contDiff.comp contDiff_snd))
  have hΨc : ContDiff ℝ 1 Ψ := (contDiff_composedFlow hΦc).comp hin
  have htan : ∀ z : (Fin k → ℝ) × C, ∀ i,
      fderiv ℝ Ψ z ((Pi.single i 1 : Fin k → ℝ), (0 : C)) = X i (Ψ z) := by
    intro z i
    have hline : HasDerivAt (fun s : ℝ => z + s • ((Pi.single i 1 : Fin k → ℝ), (0 : C)))
        ((Pi.single i 1 : Fin k → ℝ), (0 : C)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        ((Pi.single i 1 : Fin k → ℝ), (0 : C))).const_add z
    have hcomp := ((hΨc.differentiable one_ne_zero) z).hasFDerivAt.comp_hasDerivAt_of_eq
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
    exact hcomp.unique (hasDerivAt_composedFlow_single hφ hφ' hK hbr i z.1 (q + (z.2 : E)))
  have hres := isIntegrableAtOfClass_one_of_chart hΨc ⟨A, hA⟩ (Eventually.of_forall htan)
  have hΨ0 : Ψ ((0 : Fin k → ℝ), (0 : C)) = q := by
    simp only [hΨ, ZeroMemClass.coe_zero, add_zero]
    exact composedFlow_zero h0 q
  rwa [hΨ0] at hres

end Nonholonomic
end RoboLean
