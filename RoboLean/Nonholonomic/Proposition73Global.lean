import RoboLean.Nonholonomic.Proposition73

/-!
# Proposition 7.3 on the whole space in the book's normal form (MLS pp. 327–328)

**What MLS prints.** Proposition 7.3 (p. 327): "Given a set of one-forms `ωᵢ(q)`, `i = 1, …, k`,
there exist smooth, linearly independent vector fields `gⱼ(q)`, `j = 1, …, n − k` such that
`ωᵢ(q) · gⱼ(q) = 0` for all `i` and `j`." The proof (pp. 327–328) chooses coordinates in which
`ω̃ᵢ = (0 ⋯ 1 ⋯ 0 αᵢ,ₖ₊₁ ⋯ αᵢₙ)`, the `1` in the `i`-th entry, and sets
`gⱼ = (−α₁,ⱼ₊ₖ, …, −αₖ,ⱼ₊ₖ, 0, …, 1, …, 0)`.

**Proved here.** The book's construction is global exactly when its normal form holds at every
point: when one fixed `k`-dimensional block of the constraint matrix stays invertible. In
coordinate-free form: if `A : E → (E →L F)` is of class `C¹` and some fixed `S : F →L E` makes
`A(y) ∘ S` invertible for every `y` (for the book's normal form, `S` is the inclusion of the first
`k` coordinates and `A(y) ∘ S = I`), there are fields `g₁, …, g_{n−k}` of class `C¹` on all of `E`
that are linearly independent at every point, annihilate the constraints and span `ker A(y)`
(`exists_annihilatingFields_global`): `gⱼ(y) = P(y) bⱼ` with the projection
`P(y) = I − S (A(y) S)⁻¹ A(y)` onto `ker A(y)` along the range of `S` and a basis `bⱼ` of
`ker A(0)`.

**Not proved: the statement for arbitrary independent one-forms on all of `ℝⁿ`.** Frames given near
each point (`exists_annihilatingFields`) do not glue: a partition of unity preserves the equations
`ωᵢ · gⱼ = 0` but not linear independence, and a finite cover of a compact set gives no single
frame. The global statement asks that the subbundle `ker A` of the trivial bundle be trivial, which
holds over `ℝⁿ` because `ℝⁿ` is contractible (for example by parallel transport of a basis of
`ker A(0)` along rays for the connection `P dP`), a route that needs smooth dependence of solutions
of linear equations on a parameter; it fails over open sets that are not contractible (the kernel of
`q · dq` on `ℝ³ ∖ {0}` is the tangent bundle of the spheres, which has no nonvanishing section).
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **MLS Proposition 7.3, pp. 327–328, on the whole space in the book's normal form:** let
`A : E → (E →L F)` be of class `C¹` and let a fixed `S : F →L E` make `A(y) ∘ S` invertible at every
`y` (the book's coordinates `ω̃ᵢ = (0 ⋯ 1 ⋯ 0 αᵢ,ₖ₊₁ ⋯ αᵢₙ)` at every point, with `S` the inclusion
of the first `k` coordinates). Then there are fields `g₁, …, g_p` of class `C¹`,
`p = n − k = dim E − dim F`, such that at every `y`: `A(y)` is onto, `g₁(y), …, g_p(y)` are
linearly independent, `A(y) gⱼ(y) = 0`, and they span `ker A(y)`. -/
theorem exists_annihilatingFields_global {A : E → E →L[ℝ] F} (hA : ContDiff ℝ 1 A)
    {S : F →L[ℝ] E} (hS : ∀ y, IsUnit ((A y).comp S)) :
    ∃ (p : ℕ) (g : Fin p → E → E), (∀ j, ContDiff ℝ 1 (g j)) ∧
      p = Module.finrank ℝ E - Module.finrank ℝ F ∧
      ∀ y, Function.Surjective (A y) ∧ LinearIndependent ℝ (fun j => g j y) ∧
        (∀ j, A y (g j y) = 0) ∧
          LinearMap.ker (A y : E →ₗ[ℝ] F) = Submodule.span ℝ (Set.range fun j => g j y) := by
  classical
  set N : E → F →L[ℝ] F := fun y => (A y).comp S with hNdef
  have hNc : ContDiff ℝ 1 N := ((ContinuousLinearMap.compL ℝ F E F).flip S).contDiff.comp hA
  have hsurj : ∀ y, Function.Surjective (A y) := fun y w => by
    refine ⟨S (Ring.inverse (N y) w), ?_⟩
    have h := congrArg (fun L : F →L[ℝ] F => L w) (Ring.mul_inverse_cancel (N y) (hS y))
    simpa [mul_apply_eq_comp, hNdef] using h
  set K₀ := LinearMap.ker (A 0 : E →ₗ[ℝ] F) with hK₀
  set p := Module.finrank ℝ K₀ with hp
  set b := Module.finBasis ℝ K₀
  set P : E → E →L[ℝ] E := fun y => 1 - S.comp ((Ring.inverse (N y)).comp (A y)) with hPdef
  set g : Fin p → E → E := fun j y => P y (b j : E) with hgdef
  have hinvc : ∀ y, ContDiffAt ℝ 1 (fun y => Ring.inverse (N y)) y := fun y => by
    have h := contDiffAt_ringInverse ℝ (n := 1) (hS y).unit
    rw [(hS y).unit_spec] at h
    exact h.comp y hNc.contDiffAt
  have hgc : ∀ j, ContDiff ℝ 1 (g j) := fun j => by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    have : g j = fun y => (b j : E) - S (Ring.inverse (N y) (A y (b j : E))) := by
      funext y; simp [hgdef, hPdef]
    rw [this]
    exact contDiffAt_const.sub (S.contDiff.contDiffAt.comp y
      ((hinvc y).clm_apply (hA.contDiffAt.clm_apply contDiffAt_const)))
  have hNinv : ∀ y w, N y (Ring.inverse (N y) w) = w := fun y w => by
    have := congrArg (fun L : F →L[ℝ] F => L w) (Ring.mul_inverse_cancel (N y) (hS y))
    simpa only [mul_apply_eq_comp, one_apply_eq_self]
      using this
  have hAP : ∀ y v, A y (P y v) = 0 := fun y v => by
    have h' : A y (S (Ring.inverse (N y) (A y v))) = A y v := hNinv y (A y v)
    simp [hPdef, h']
  have hAg : ∀ j y, A y (g j y) = 0 := fun j y => hAP y _
  have hli : ∀ y, LinearIndependent ℝ (fun j => g j y) := fun y => by
    have hb : LinearIndependent ℝ (fun j => (b j : E)) :=
      b.linearIndependent.map' K₀.subtype (Submodule.ker_subtype K₀)
    have hdisj : Disjoint (Submodule.span ℝ (Set.range fun j => (b j : E)))
        (LinearMap.ker (P y : E →ₗ[ℝ] E)) := by
      rw [Submodule.disjoint_def]
      intro v hv hPv
      have hvK : v ∈ K₀ := by
        have hle : Submodule.span ℝ (Set.range fun j => (b j : E)) ≤ K₀ := by
          rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          exact (b j).2
        exact hle hv
      have hPv' : v - S (Ring.inverse (N y) (A y v)) = 0 := by
        simpa [hPdef] using hPv
      set w := Ring.inverse (N y) (A y v)
      have hvS : v = S w := sub_eq_zero.1 hPv'
      have hA0 : A 0 v = 0 := hvK
      have hN0w : N 0 w = 0 := by simpa [hNdef, hvS] using hA0
      have hw : w = 0 := by
        have := congrArg (fun z => Ring.inverse (N 0) z) hN0w
        have hcanc := congrArg (fun L : F →L[ℝ] F => L w) (Ring.inverse_mul_cancel (N 0) (hS 0))
        simp only [mul_apply_eq_comp, one_apply_eq_self]
          at hcanc
        simp only [map_zero] at this
        rw [← hcanc]
        exact this
      rw [hvS, hw, map_zero]
    exact hb.map hdisj
  refine ⟨p, g, hgc, ?_, fun y => ⟨hsurj y, hli y, fun j => hAg j y, ?_⟩⟩
  · have h2 := LinearMap.finrank_range_add_finrank_ker (A 0 : E →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.2 (hsurj 0), finrank_top, ← hK₀] at h2
    omega
  · have hle : Submodule.span ℝ (Set.range fun j => g j y) ≤
        LinearMap.ker (A y : E →ₗ[ℝ] F) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hAg j y
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker (A y : E →ₗ[ℝ] F)
    have h2 := LinearMap.finrank_range_add_finrank_ker (A 0 : E →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.2 (hsurj y), finrank_top] at h1
    rw [LinearMap.range_eq_top.2 (hsurj 0), finrank_top, ← hK₀] at h2
    rw [finrank_span_eq_card (hli y), Fintype.card_fin, hp]
    omega

end Nonholonomic
end RoboLean
