import RoboLean.Nonholonomic.FrobeniusFrame

/-!
# Fields annihilating Pfaffian constraints (MLS Proposition 7.3, pp. 327–328) and Proposition 7.4,
"if" (p. 328)

**What MLS prints.** Proposition 7.3 (p. 327): "Given a set of one-forms `ωᵢ(q)`, `i = 1, …, k`,
there exist smooth, linearly independent vector fields `gⱼ(q)`, `j = 1, …, n − k` such that
`ωᵢ(q) · gⱼ(q) = 0` for all `i` and `j`", for one-forms "smooth and linearly independent"
(p. 327). The proof chooses local coordinates in which `ω̃ᵢ = (0 ⋯ 1 ⋯ 0 αᵢ,ₖ₊₁ ⋯ αᵢₙ)` and sets
`gⱼ = (−α₁,ⱼ₊ₖ, …, −αₖ,ⱼ₊ₖ, 0, …, 1, …, 0)` (p. 328): a local construction. Proposition 7.4
(p. 328): "A set of smooth Pfaffian constraints is integrable if and only if the distribution
which annihilates the constraints is involutive."

**Proved here.**

* Proposition 7.3 near a point (`exists_annihilatingFields`): for `A : E → (E →L F)` of class `C¹`
  with `A(q)` onto, there are `C¹` fields `g₁, …, g_p` (`p = dim ker A(q)`) that near `q` are
  linearly independent, satisfy `A(y) gⱼ(y) = 0`, and span `ker A(y)`. The book's normalization is
  replaced by a coordinate-free one: with a right inverse `S` of `A(q)`,
  `gⱼ(y) = (I − S (A(y) S)⁻¹ A(y)) bⱼ` for a basis `bⱼ` of `ker A(q)`, cut off away from `q`.
* Proposition 7.4, "if", near each point and with a `C¹` defining map
  (`isIntegrableAtOfClass_one_annihilator`): for Pfaffian constraints `A(q) q̇ = 0` of class `C¹`
  with independent rows on an open set `U`, if the annihilating distribution is involutive on `U`
  it is integrable at every point of `U` with a defining map of class `C¹`.

**Conventions.** Pfaffian constraints are the library's `A : ℝⁿ → ℝ^{k×n}` and their annihilating
distribution `annihilator A` (Chapter 7, `Integrability`); linearly independent rows are stated as
`A(y)` onto `ℝᵏ`. The library's `IsC2IntegrableOn` (one `C²` map on a whole set) is not the
conclusion: Frobenius gives defining maps near each point.
-/

noncomputable section

open Set Filter Topology Metric

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **MLS Proposition 7.3, pp. 327–328, near a point:** on finite-dimensional real spaces, let
`A : E → (E →L F)` be of class `C¹` with `A(q)` onto (the one-forms `ωᵢ` independent at `q`). Then
there are fields `g₁, …, g_p` of class `C¹`, `p = dim ker A(q)`, such that near `q`: `A(y)` is onto,
`g₁(y), …, g_p(y)` are linearly independent, `A(y) gⱼ(y) = 0`, and they span `ker A(y)`. -/
theorem exists_annihilatingFields {A : E → E →L[ℝ] F} (hA : ContDiff ℝ 1 A) {q : E}
    (hq : Function.Surjective (A q)) :
    ∃ (p : ℕ) (g : Fin p → E → E), (∀ j, ContDiff ℝ 1 (g j)) ∧
      p = Module.finrank ℝ (LinearMap.ker (A q : E →ₗ[ℝ] F)) ∧
      ∀ᶠ y in 𝓝 q, Function.Surjective (A y) ∧ LinearIndependent ℝ (fun j => g j y) ∧
        (∀ j, A y (g j y) = 0) ∧
          LinearMap.ker (A y : E →ₗ[ℝ] F) = Submodule.span ℝ (Set.range fun j => g j y) := by
  classical
  -- a right inverse `S` of `A q`
  obtain ⟨S', hS'⟩ := LinearMap.exists_rightInverse_of_surjective (A q : E →ₗ[ℝ] F)
    (LinearMap.range_eq_top.2 hq)
  set S : F →L[ℝ] E := LinearMap.toContinuousLinearMap S' with hSdef
  have hAS : ∀ w, A q (S w) = w := fun w => by
    have := congrArg (fun L : F →ₗ[ℝ] F => L w) hS'
    simpa [hSdef] using this
  set N : E → F →L[ℝ] F := fun y => (A y).comp S with hNdef
  have hNc : ContDiff ℝ 1 N := ((ContinuousLinearMap.compL ℝ F E F).flip S).contDiff.comp hA
  have hNq : N q = 1 := by ext1 w; simp [hNdef, hAS]
  set W₀ : Set E := N ⁻¹' {x | IsUnit x} with hW₀
  have hW₀o : IsOpen W₀ := Units.isOpen.preimage hNc.continuous
  have hqW₀ : q ∈ W₀ := by simp [hW₀, hNq]
  -- the projection onto `ker A(y)` and a basis of `ker A(q)`
  set K₀ := LinearMap.ker (A q : E →ₗ[ℝ] F) with hK₀
  set p := Module.finrank ℝ K₀ with hp
  set b := Module.finBasis ℝ K₀
  set Y : Fin p → E → E := fun j y => (b j : E) - S (Ring.inverse (N y) (A y (b j : E)))
    with hYdef
  have hYc : ∀ j, ∀ y ∈ W₀, ContDiffAt ℝ 1 (Y j) y := fun j y hy => by
    have hu : IsUnit (N y) := hy
    have hinvc : ContDiffAt ℝ 1 (fun y => Ring.inverse (N y)) y := by
      have h := contDiffAt_ringInverse ℝ (n := 1) hu.unit
      rw [hu.unit_spec] at h
      exact h.comp y hNc.contDiffAt
    exact contDiffAt_const.sub (S.contDiff.contDiffAt.comp y
      (hinvc.clm_apply (hA.contDiffAt.clm_apply contDiffAt_const)))
  have hAY : ∀ j, ∀ y ∈ W₀, A y (Y j y) = 0 := fun j y hy => by
    have hu : IsUnit (N y) := hy
    have h : N y (Ring.inverse (N y) (A y (b j : E))) = A y (b j : E) := by
      have := congrArg (fun L : F →L[ℝ] F => L (A y (b j : E))) (Ring.mul_inverse_cancel (N y) hu)
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using this
    have h' : A y (S (Ring.inverse (N y) (A y (b j : E)))) = A y (b j : E) := h
    simp only [hYdef, map_sub, h', sub_self]
  have hYq : ∀ j, Y j q = b j := fun j => by
    have h0 : A q (b j : E) = 0 := (b j).2
    simp [hYdef, h0]
  have hsurj : ∀ y ∈ W₀, Function.Surjective (A y) := fun y hy w => by
    have hu : IsUnit (N y) := hy
    refine ⟨S (Ring.inverse (N y) w), ?_⟩
    have h := congrArg (fun L : F →L[ℝ] F => L w) (Ring.mul_inverse_cancel (N y) hu)
    simpa [mul_apply_eq_comp, hNdef] using h
  -- the cut-off
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (hW₀o.mem_nhds hqW₀)
  set χ : ContDiffBump q := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩ with hχ
  have hχsupp : tsupport χ ⊆ ball q ε := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by simp [hχ]; linarith)
  have hχ1 : ∀ y ∈ ball q (ε / 3), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  set g : Fin p → E → E := fun j y => χ y • Y j y with hgdef
  have hgc : ∀ j, ContDiff ℝ 1 (g j) := fun j => by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball q ε
    · exact (χ.contDiff.contDiffAt).smul (hYc j y (hεsub hy))
    · have hy' : y ∉ tsupport χ := fun h => hy (hχsupp h)
      have hev : g j =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy'] with z hz
        simp [hgdef, hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  -- independence near `q`
  have hYcq : ContinuousAt (fun y => fun j => Y j y) q :=
    continuousAt_pi.2 fun j => (hYc j q hqW₀).continuousAt
  have hliq : LinearIndependent ℝ (fun j => Y j q) := by
    have : (fun j => Y j q) = fun j => (b j : E) := funext hYq
    rw [this]
    exact b.linearIndependent.map' K₀.subtype (Submodule.ker_subtype K₀)
  have hev : ∀ᶠ y in 𝓝 q, LinearIndependent ℝ (fun j => Y j y) :=
    hYcq.eventually hliq.eventually
  refine ⟨p, g, hgc, rfl, ?_⟩
  filter_upwards [hev, isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < ε / 3))]
    with y hli hy
  have hyW : y ∈ W₀ := hεsub (ball_subset_ball (by linarith) hy)
  have hgY : ∀ j, g j y = Y j y := fun j => by simp [hgdef, hχ1 y hy]
  have hli' : LinearIndependent ℝ (fun j => g j y) := by
    have : (fun j => g j y) = fun j => Y j y := funext hgY
    rw [this]; exact hli
  have hAg : ∀ j, A y (g j y) = 0 := fun j => by rw [hgY]; exact hAY j y hyW
  refine ⟨hsurj y hyW, hli', hAg, ?_⟩
  have hle : Submodule.span ℝ (Set.range fun j => g j y) ≤ LinearMap.ker (A y : E →ₗ[ℝ] F) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hAg j
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h1 := LinearMap.finrank_range_add_finrank_ker (A y : E →ₗ[ℝ] F)
  have h2 := LinearMap.finrank_range_add_finrank_ker (A q : E →ₗ[ℝ] F)
  rw [LinearMap.range_eq_top.2 (hsurj y hyW), finrank_top] at h1
  rw [LinearMap.range_eq_top.2 hq, finrank_top, ← hK₀] at h2
  rw [finrank_span_eq_card hli', Fintype.card_fin, hp]
  omega

variable {n k : ℕ}

/-- **MLS Proposition 7.4, p. 328, "if", near each point, with a `C¹` defining map:** let the
Pfaffian constraints `A(q) q̇ = 0` (`A : ℝⁿ → ℝ^{k×n}`) be of class `C¹` with linearly independent
rows (`A(y)` onto `ℝᵏ`) at every point of an open set `U`. If the annihilating distribution
`Δ_y = ker A(y)` is involutive on `U`, then it is integrable at every point of `U` with a defining
map of class `C¹` (`IsIntegrableAtOfClass 1`; MLS asks smooth functions). -/
theorem isIntegrableAtOfClass_one_annihilator {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 fun y => A y i j) {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hrank : ∀ y ∈ U, Function.Surjective (A y).mulVec)
    (hinv : IsInvolutiveOn (annihilator A) U) {q : Fin n → ℝ} (hq : q ∈ U) :
    IsIntegrableAtOfClass 1 (annihilator A) q := by
  -- the constraints as continuous linear maps, entry by entry
  set Ac : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := fun y => ∑ i, ∑ j, A y i j •
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).smulRight
      (Pi.single i 1 : Fin k → ℝ) with hAc
  have hAcv : ∀ y v, Ac y v = (A y).mulVec v := fun y v => by
    ext i'
    simp [hAc, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  have hAcc : ContDiff ℝ 1 Ac :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hA i j).smul contDiff_const
  have hker : ∀ y, annihilator A y = LinearMap.ker (Ac y : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) :=
    fun y => by ext v; simp [mem_annihilator, hAcv]
  have hsurj : ∀ y ∈ U, Function.Surjective (Ac y) := fun y hy w => by
    obtain ⟨v, hv⟩ := hrank y hy w
    exact ⟨v, by rw [hAcv]; exact hv⟩
  have hreg : IsRegularOn (annihilator A) U := by
    refine ⟨n - k, fun y hy => ?_⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (Ac y : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    rw [LinearMap.range_eq_top.2 (hsurj y hy), finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    rw [hker y]
    omega
  obtain ⟨p, g, hgc, -, hev⟩ := exists_annihilatingFields hAcc (hsurj q hq)
  refine isIntegrableAtOfClass_one_of_isInvolutiveOn hU hreg hinv hq hgc ?_
  filter_upwards [hev] with y hy
  rw [hker y, hy.2.2.2, spanAt_range]

end Nonholonomic
end RoboLean
