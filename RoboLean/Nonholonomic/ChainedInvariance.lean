import RoboLean.Examples.NilpotentEightState
import RoboLean.Nonholonomic.ChainedForm
import RoboLean.Nonholonomic.FiltrationBrackets

/-!
# Chapter 8, Exercise 1: no change of coordinates to a one-chained form (MLS p. 391)

MLS Chapter 8, Exercise 1, printed p. 391: the eight-state system "is controllable and nilpotent of
degree four. Can you find a nonlinear change of coordinates to transform this system into a
one-chained form?" As printed the system is not controllable (the library's
`eightPrinted_not_isControllable`); corrected (`q̇₆ = ⅙q₁³u₂`) it has growth vector `(2, 3, 5, 8)`
(the library's `eight_growthVector`).

**What is formalized.**
* Invariance of the filtration under a change of coordinates: if `ψ` is smooth, the fields
  `ψ^*Gⱼ = (Dψ)⁻¹ Gⱼ ∘ ψ` (Mathlib's `pullback`) have as filtration fields the pullbacks of the
  filtration fields of `G` (naturality of the bracket, Mathlib's `pullback_lieBracket`), and where
  `Dψ(q)` is invertible the ranks agree, `rank Δᵢ(ψ^*G)(q) = rank Δᵢ(G)(ψ(q))`.
* The one-chain system (8.7) has `rank Δ₃ ≤ 4` at every point (its third stage is spanned by
  `g₁`, `e₂`, `e₃`, `e₄`).
* Hence the answer for the corrected system is no: there is no smooth map `ψ : ℝ⁸ → ℝ⁸` with
  invertible derivative at some point `z` such that the one-chain fields in `z`-coordinates are the
  pullbacks of the corrected fields (`Dψ(z) gᵢ^{chain}(z) = gᵢ(ψ(z))` for all `z`), since that would
  give `rank Δ₃ = 5` for the chain at `z`. The corrected system is not one-chained in any
  coordinates of this kind.

**Recorded reading.** "Nonlinear change of coordinates" is read as a smooth map `ψ` from the new
coordinates to the old with the pulled-back fields equal to the one-chain fields everywhere and
`Dψ` invertible at one point (a diffeomorphism is a special case); input transformations
(feedback, as allowed in the conversion of §3.2) are not included. For the printed system the answer
is also no, since the one-chain system is controllable and the printed one is not; that statement
needs the invariance of controllability and is not formalized here.

**Conventions.** The bracket is Mathlib's `lieBracket` (the book's sign, p. 323); the filtration and
its rank are the library's `filtrationFields`, `filtrationAt`, `growth` (p. 340); smooth means
`C^∞`.
-/

noncomputable section

open Set VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}

/-- **MLS p. 340 with the naturality of the bracket: the filtration of pulled-back fields.** For a
smooth `ψ` and smooth generators `G`, the fields spanning `Δᵢ` for `ψ^*G` are the pullbacks of the
fields spanning `Δᵢ` for `G` (convention for MLS Chapter 8, Exercise 1, p. 391). -/
theorem filtrationFields_pullback {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) {G : Fin m → F → F}
    (hG : ∀ j, ContDiff ℝ ∞ (G j)) (k : ℕ) :
    filtrationFields (fun j => pullback ℝ ψ (G j)) k = pullback ℝ ψ '' filtrationFields G k := by
  have hbr : ∀ j {w : F → F}, ContDiff ℝ ∞ w →
      lieBracket ℝ (pullback ℝ ψ (G j)) (pullback ℝ ψ w) = pullback ℝ ψ (lieBracket ℝ (G j) w) := by
    intro j w hw
    funext x
    exact (pullback_lieBracket (by simp [minSmoothness_of_isRCLikeNormedField]) hψ.contDiffAt
      ((hG j).differentiable (by simp) _) (hw.differentiable (by simp) _)).symm
  induction k with
  | zero => simp [filtrationFields]
  | succ k ih =>
    ext f
    simp only [filtrationFields, mem_union, mem_range, mem_ofPred_eq, mem_image]
    constructor
    · rintro (⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩)
      · exact ⟨G j, Or.inl ⟨j, rfl⟩, rfl⟩
      · rw [ih] at hw
        obtain ⟨w', hw', rfl⟩ := hw
        exact ⟨lieBracket ℝ (G j) w', Or.inr ⟨j, w', hw', rfl⟩,
          (hbr j (contDiff_of_mem_filtrationFields hG hw')).symm⟩
    · rintro ⟨f', (⟨j, rfl⟩ | ⟨j, w', hw', rfl⟩), rfl⟩
      · exact Or.inl ⟨j, rfl⟩
      · refine Or.inr ⟨j, pullback ℝ ψ w', by rw [ih]; exact ⟨w', hw', rfl⟩, ?_⟩
        exact (hbr j (contDiff_of_mem_filtrationFields hG hw')).symm

omit [CompleteSpace E] in
/-- **MLS p. 340: the distribution of pulled-back fields** is the image of the distribution at
`ψ(q)` under `Dψ(q)⁻¹` (convention for MLS Chapter 8, Exercise 1, p. 391). -/
theorem spanAt_image_pullback (ψ : E → F) (S : Set (F → F)) (q : E) :
    spanAt (pullback ℝ ψ '' S) q =
      (spanAt S (ψ q)).map ((fderiv ℝ ψ q).inverse : F →ₗ[ℝ] E) := by
  rw [spanAt, spanAt, Submodule.map_span, ← Set.image_comp, ← Set.image_comp]
  rfl

/-- **MLS p. 340: the rank of the filtration is invariant under a change of coordinates.** For a
smooth `ψ`, smooth generators `G` and `Dψ(q)` invertible, `rank Δᵢ(ψ^*G)(q) = rank Δᵢ(G)(ψ(q))`
(convention for MLS Chapter 8, Exercise 1, p. 391). -/
theorem growth_pullback {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) {G : Fin m → F → F}
    (hG : ∀ j, ContDiff ℝ ∞ (G j)) {q : E} {e : E ≃L[ℝ] F} (he : fderiv ℝ ψ q = e) (k : ℕ) :
    growth (fun j => pullback ℝ ψ (G j)) k q = growth G k (ψ q) := by
  rw [growth, growth, filtrationAt, filtrationAt, filtrationFields_pullback hψ hG,
    spanAt_image_pullback, he, ContinuousLinearMap.inverse_equiv]
  exact LinearEquiv.finrank_map_eq e.symm.toLinearEquiv _

/-- The shift of the one-chain field on the unit vectors (supporting lemma for MLS p. 391). -/
private theorem chainShift_basis (n j : ℕ) (hj : 1 ≤ j) :
    chainShift n (chainBasis n j) = chainBasis n (j + 1) := by
  funext i
  show (if h : 2 ≤ i.val then chainBasis n j ⟨i.val - 1, by omega⟩ else 0) = chainBasis n (j + 1) i
  simp only [chainBasis]
  by_cases h : 2 ≤ i.val
  · by_cases h' : i.val = j + 1
    · simp [h']
      omega
    · simp [h, h', show i.val - 1 ≠ j by omega]
  · simp [h, show i.val ≠ j + 1 by omega]

/-- **MLS eq. (8.7), p. 364: the third stage of the one-chain filtration has rank at most four,**
spanned by `g₁(q)` and `e₂, e₃, e₄` (convention for MLS Chapter 8, Exercise 1, p. 391). -/
theorem chain_growth_three_le (n : ℕ) (q : Fin n → ℝ) : growth (chainFields n) 3 q ≤ 4 := by
  have hD : ∀ x, HasFDerivAt (chainG1 n) (chainShift n) x := fun x =>
    (chainShift n).hasFDerivAt.const_add (chainBasis n 0)
  set P : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (Set.range ![chainBasis n 1, chainBasis n 2]) with hP
  set Q : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (Set.range ![chainBasis n 1, chainBasis n 2, chainBasis n 3]) with hQ
  have hQ1 : chainBasis n 1 ∈ Q := Submodule.subset_span ⟨0, rfl⟩
  have hQ2 : chainBasis n 2 ∈ Q := Submodule.subset_span ⟨1, rfl⟩
  have hQ3 : chainBasis n 3 ∈ Q := Submodule.subset_span ⟨2, rfl⟩
  have hP1 : chainBasis n 1 ∈ P := Submodule.subset_span ⟨0, rfl⟩
  have hP2 : chainBasis n 2 ∈ P := Submodule.subset_span ⟨1, rfl⟩
  have hshift : ∀ c ∈ P, chainShift n c ∈ Q := by
    intro c hc
    have : P.map (chainShift n : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ Q := by
      rw [hP, Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · simpa [chainShift_basis n 1 le_rfl] using hQ2
      · simpa [chainShift_basis n 2 (by norm_num)] using hQ3
    exact this ⟨c, hc, rfl⟩
  have hbr1 : ∀ c : Fin n → ℝ, lieBracket ℝ (chainG1 n) (fun _ => c) = fun _ => -chainShift n c := by
    intro c
    funext x
    rw [lieBracket, (hasFDerivAt_const _ x).fderiv, (hD x).fderiv]
    simp
  have hbr2 : ∀ c : Fin n → ℝ, lieBracket ℝ (chainG2 n) (fun _ => c) = 0 := by
    intro c
    funext x
    rw [lieBracket, (hasFDerivAt_const _ x).fderiv,
      show chainG2 n = fun _ => chainBasis n 1 from rfl, (hasFDerivAt_const _ x).fderiv]
    simp
  have hbr21 : lieBracket ℝ (chainG2 n) (chainG1 n) = fun _ => chainBasis n 2 := by
    funext x
    rw [lieBracket, (hD x).fderiv,
      show chainG2 n = fun _ => chainBasis n 1 from rfl, (hasFDerivAt_const _ x).fderiv]
    simp [chainShift_basis n 1 le_rfl]
  have hg2 : chainG2 n = fun _ => chainBasis n 1 := rfl
  -- the fields spanning the second stage
  have h2 : ∀ f ∈ filtrationFields (chainFields n) 2, f = chainG1 n ∨ ∃ c ∈ P, f = fun _ => c := by
    intro f hf
    simp only [filtrationFields, mem_union, mem_range, mem_ofPred_eq] at hf
    have hgen : ∀ j : Fin 2, chainFields n j = chainG1 n ∨ ∃ c ∈ P, chainFields n j = fun _ => c := by
      intro j
      fin_cases j
      · exact Or.inl rfl
      · exact Or.inr ⟨chainBasis n 1, hP1, rfl⟩
    rcases hf with ⟨j, rfl⟩ | ⟨j, w, hw, rfl⟩
    · exact hgen j
    · simp only [mem_empty_iff_false, false_and, exists_false, or_false] at hw
      obtain ⟨i, rfl⟩ := hw
      fin_cases j <;> fin_cases i
      · exact Or.inr ⟨0, P.zero_mem, by simp [chainFields]; rfl⟩
      · refine Or.inr ⟨-chainBasis n 2, P.neg_mem hP2, ?_⟩
        simp only [chainFields, Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one,
          Matrix.cons_val_one]
        rw [hg2, hbr1, chainShift_basis n 1 le_rfl]
      · exact Or.inr ⟨chainBasis n 2, hP2, hbr21⟩
      · exact Or.inr ⟨0, P.zero_mem, by simp [chainFields]; rfl⟩
  -- the fields spanning the third stage take values in `span {g₁(q), e₂, e₃, e₄}`
  have h3 : ∀ f ∈ filtrationFields (chainFields n) 3,
      f q ∈ Submodule.span ℝ {chainG1 n q} ⊔ Q := by
    intro f hf
    have hconst : ∀ c ∈ Q, c ∈ Submodule.span ℝ {chainG1 n q} ⊔ Q := fun c hc =>
      Submodule.mem_sup_right hc
    simp only [filtrationFields] at hf
    rcases hf with hf | ⟨j, w, hw, rfl⟩
    · obtain ⟨j, rfl⟩ := hf
      fin_cases j
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · exact hconst _ hQ1
    · rcases h2 w hw with rfl | ⟨c, hc, rfl⟩
      · fin_cases j
        · simp [chainFields]
        · simp only [chainFields, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [hbr21]
          exact hconst _ hQ2
      · fin_cases j
        · simp only [chainFields, Fin.zero_eta, Matrix.cons_val_zero]
          rw [hbr1]
          exact hconst _ (Q.neg_mem (hshift c hc))
        · simp only [chainFields, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [hbr2]
          exact Submodule.zero_mem _
  have hle : filtrationAt (chainFields n) 3 q ≤ Submodule.span ℝ {chainG1 n q} ⊔ Q := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact h3 f hf
  calc growth (chainFields n) 3 q ≤ Module.finrank ℝ ↥(Submodule.span ℝ {chainG1 n q} ⊔ Q) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℝ ↥(Submodule.span ℝ {chainG1 n q}) + Module.finrank ℝ ↥Q :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ 1 + 3 := by
        gcongr
        · exact (finrank_span_le_card ({chainG1 n q} : Set (Fin n → ℝ))).trans (by simp)
        · exact (finrank_range_le_card _).trans (by simp)
    _ = 4 := by norm_num

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: the input fields are smooth**
(polynomial in `q₁, q₂`). -/
theorem eightFields_contDiff (j : Fin 2) : ContDiff ℝ ∞ (RoboLean.Examples.eightFields j) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases j <;> fin_cases i <;>
    simp [RoboLean.Examples.eightFields, baseField, RoboLean.Examples.eightG1,
      RoboLean.Examples.eightG2] <;> fun_prop

/-- **MLS Chapter 8, Exercise 1, p. 391, corrected printing: no change of coordinates to a
one-chained form.** There is no smooth `ψ : ℝ⁸ → ℝ⁸` with invertible derivative at some point `z`
such that the one-chain fields (8.7) with `n = 8` are the pullbacks under `ψ` of the corrected
fields: the rank of the third stage would be `5` (corrected system) and at most `4` (chain). -/
theorem not_exists_pullback_eightFields_eq_chainFields :
    ¬ ∃ (ψ : (Fin 8 → ℝ) → Fin 8 → ℝ) (z : Fin 8 → ℝ) (e : (Fin 8 → ℝ) ≃L[ℝ] (Fin 8 → ℝ)),
      ContDiff ℝ ∞ ψ ∧ fderiv ℝ ψ z = e ∧
        ∀ j, chainFields 8 j = pullback ℝ ψ (RoboLean.Examples.eightFields j) := by
  rintro ⟨ψ, z, e, hψ, he, hfields⟩
  have hc : chainFields 8 = fun j => pullback ℝ ψ (RoboLean.Examples.eightFields j) :=
    funext hfields
  have h1 := growth_pullback hψ eightFields_contDiff he 3
  rw [← hc] at h1
  have h2 := chain_growth_three_le 8 z
  have h3 : growth RoboLean.Examples.eightFields 3 (ψ z) = 5 := by
    have := congrFun (RoboLean.Examples.eight_growthVector (ψ z)).1 2
    simpa [growthVector] using this
  omega

end Nonholonomic
end RoboLean
