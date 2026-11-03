import RoboLean.Nonholonomic.Distribution
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local frames of regular distributions (MLS p. 325, for Theorem 7.2, p. 326)

**What MLS prints.** A distribution `Δ = span{g₁, …, g_m}` assigns `Δ_q = span{g₁(q), …, g_m(q)}`
to each point; it is regular on a set if its dimension is constant there (p. 325). The proof of
Frobenius' theorem (Theorem 7.2, p. 326, stated without proof) and the remark after Exercise 11
(p. 351, with p. 340) work with `k` of the generators that form a basis of `Δ_q` near a point.

**Proved here.** On a finite-dimensional real space, for generators `g₁, …, g_m` continuous at
`q` and a distribution regular on an open set `U ∋ q`: some `k = dim Δ_q` of the generators are
linearly independent at every point of a neighbourhood of `q` and span `Δ` there
(`exists_localFrame`). Independence is an open condition, and at a point where the rank is still
`k`, `k` independent vectors of `Δ_y` span it.

**Conventions.** `spanAt (Set.range g) q` is the library's `Δ_q` (Chapter 7, `Distribution`);
regularity is `IsRegularOn` (constant `finrank`).
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A local frame of a regular distribution (MLS p. 325, for Theorem 7.2, p. 326):** on a
finite-dimensional real space, let `g₁, …, g_m` be continuous at `q` and let
`Δ = span{g₁, …, g_m}` be regular on an open set `U ∋ q`. Then for `k = dim Δ_q` there are indices
`σ(1), …, σ(k)` and a neighbourhood `V ⊆ U` of `q` such that at every `y ∈ V` the vectors
`g_{σ(1)}(y), …, g_{σ(k)}(y)` are linearly independent and span `Δ_y`. -/
theorem exists_localFrame {m : ℕ} {g : Fin m → E → E} {U : Set E} (hU : IsOpen U)
    (hreg : IsRegularOn (spanAt (Set.range g)) U) {q : E} (hq : q ∈ U)
    (hg : ∀ j, ContinuousAt (g j) q) :
    ∃ (k : ℕ) (σ : Fin k → Fin m), Module.finrank ℝ (spanAt (Set.range g) q) = k ∧
      ∃ V ∈ 𝓝 q, V ⊆ U ∧ ∀ y ∈ V, LinearIndependent ℝ (fun i => g (σ i) y) ∧
        spanAt (Set.range g) y = Submodule.span ℝ (Set.range fun i => g (σ i) y) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ (fun j => g j q)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  set e := Fintype.equivFin κ
  set σ : Fin (Fintype.card κ) → Fin m := a ∘ e.symm with hσ
  have hliσ : LinearIndependent ℝ (fun i => g (σ i) q) :=
    hli.comp e.symm e.symm.injective
  have hspσ : Submodule.span ℝ (Set.range fun i => g (σ i) q) = spanAt (Set.range g) q := by
    rw [spanAt_range, ← hsp]
    have hr : (Set.range fun i => g (σ i) q) = Set.range ((fun j => g j q) ∘ a) := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨e c, by simp [hσ]⟩
    rw [hr]
  have hk : Module.finrank ℝ (spanAt (Set.range g) q) = Fintype.card κ := by
    rw [← hspσ, finrank_span_eq_card hliσ, Fintype.card_fin]
  -- independence persists near `q`
  have hcont : ContinuousAt (fun y => fun i => g (σ i) y) q :=
    continuousAt_pi.2 fun i => hg (σ i)
  have hev : ∀ᶠ y in 𝓝 q, LinearIndependent ℝ (fun i => g (σ i) y) :=
    hcont.eventually hliσ.eventually
  obtain ⟨r, hr⟩ := hreg
  refine ⟨Fintype.card κ, σ, hk, {y | LinearIndependent ℝ (fun i => g (σ i) y)} ∩ U,
    Filter.inter_mem hev (hU.mem_nhds hq), inter_subset_right, fun y hy => ⟨hy.1, ?_⟩⟩
  have hle : Submodule.span ℝ (Set.range fun i => g (σ i) y) ≤ spanAt (Set.range g) y :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact mem_spanAt (Set.mem_range_self (σ i)) y)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hy.1, Fintype.card_fin, hr y hy.2, ← hr q hq, hk]

end Nonholonomic
end RoboLean
