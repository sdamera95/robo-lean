import RoboLean.Nonholonomic.IntegralsOfClosure

/-!
# The integrals of the involutive closure on a concrete system (MLS pp. 339–341)

A convention check for the integrals of the involutive closure (MLS pp. 339–341): on `ℝ²` with the
single constant input field `g₁ = e₁` (the constraint `q̇₂ = 0`), every field of `L(g₁)` is a
constant multiple of `e₁`, so `Δ̄_y = span{e₁}` has rank `1` at every point; the general theorem
then gives `2 − 1 = 1` integral near every point, and the second coordinate `h(q) = q₂` is one,
derived independently: its differential vanishes on `Δ̄` and is not zero. A concrete system says
nothing about a physical one.

**Conventions.** Points of `ℝ²` are `Fin 2 → ℝ`, `e₁ = Pi.single 0 1`, `q₂ = q 1`.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Examples

open Nonholonomic

/-- **The constant input field `g₁ = e₁` on `ℝ²` (for MLS pp. 339–341):** the control system
`q̇ = e₁ u₁`, dual to the constraint `q̇₂ = 0`. -/
def unitField : Fin 1 → (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ _ => Pi.single 0 1

/-- **MLS Definition 7.1, p. 326, for `g₁ = e₁`:** every field of `L(g₁)` is a constant multiple
of `e₁` (brackets of constant fields vanish). -/
theorem eq_smul_of_inLieAlgebra_unitField {f : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hf : InLieAlgebra unitField f) : ∃ c : ℝ, f = fun _ => c • (Pi.single 0 1 : Fin 2 → ℝ) := by
  induction hf with
  | gen j => exact ⟨1, by funext x; simp [unitField]⟩
  | add _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨c + d, by funext x; simp [add_smul]⟩
  | smul a _ ih =>
    obtain ⟨c, rfl⟩ := ih
    exact ⟨a * c, by funext x; simp [mul_smul]⟩
  | bracket _ _ ihf ihh =>
    obtain ⟨c, rfl⟩ := ihf
    obtain ⟨d, rfl⟩ := ihh
    exact ⟨0, by funext x; simp [lieBracket]⟩

/-- **MLS pp. 325–326 for `g₁ = e₁`:** `Δ̄_y = L(g₁)(y) = span{e₁}` at every point. -/
theorem lieAlgebraAt_unitField (y : Fin 2 → ℝ) :
    lieAlgebraAt unitField y = Submodule.span ℝ {(Pi.single 0 1 : Fin 2 → ℝ)} := by
  apply le_antisymm
  · unfold lieAlgebraAt spanAt
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨c, rfl⟩ := eq_smul_of_inLieAlgebra_unitField hf
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact mem_spanAt (InLieAlgebra.gen (g := unitField) 0) y

/-- **MLS p. 339 ("`Δ̄_q` has a constant rank") for `g₁ = e₁`:** the rank of `Δ̄` is `1` at every
point. -/
theorem finrank_lieAlgebraAt_unitField (y : Fin 2 → ℝ) :
    Module.finrank ℝ (lieAlgebraAt unitField y) = 1 := by
  rw [lieAlgebraAt_unitField]
  exact finrank_span_singleton (by simp)

/-- **MLS pp. 339–341 for `g₁ = e₁`: one integral near every point,** from the general theorem with
`n = 2` and `r = 1`. -/
theorem unitField_integrals (q : Fin 2 → ℝ) :
    ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ q ∈ V ∧
      ∃ h : Fin 1 → (Fin 2 → ℝ) → ℝ, (∀ i, ∀ y ∈ V, ContDiffAt ℝ 1 (h i) y) ∧
        (∀ y ∈ V, LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ (Fin 2 → ℝ))) ∧
        ∀ y ∈ V, Submodule.span ℝ (Set.range fun i =>
          (fderiv ℝ (h i) y : Module.Dual ℝ (Fin 2 → ℝ))) =
            (lieAlgebraAt unitField y).dualAnnihilator := by
  obtain ⟨V, hV, hqV, -, h, hC, hli, hspan⟩ := exists_integrals_of_involutiveClosure
    (g := unitField) (fun _ => contDiff_const) isOpen_univ (r := 1)
    (fun y _ => finrank_lieAlgebraAt_unitField y) (mem_univ q)
  have hn : Module.finrank ℝ (Fin 2 → ℝ) - 1 = 1 := by simp
  have hs : Function.Surjective (Fin.cast hn.symm) := (finCongr hn.symm).surjective
  refine ⟨V, hV, hqV, fun i => h (Fin.cast hn.symm i), fun i y hy => hC _ y hy,
    fun y hy => (hli y hy).comp _ (Fin.cast_injective _), fun y hy => ?_⟩
  rw [← hspan y hy]
  exact congrArg _ (hs.range_comp fun j => (fderiv ℝ (h j) y : Module.Dual ℝ (Fin 2 → ℝ)))

/-- **MLS p. 339 for `g₁ = e₁`, an integral derived independently:** the second coordinate
`h(q) = q₂` has differential vanishing on `Δ̄_y` and different from zero at every point. -/
theorem secondCoordinate_integral (y : Fin 2 → ℝ) :
    (∀ v ∈ lieAlgebraAt unitField y, fderiv ℝ (fun x : Fin 2 → ℝ => x 1) y v = 0) ∧
      fderiv ℝ (fun x : Fin 2 → ℝ => x 1) y ≠ 0 := by
  have hd : fderiv ℝ (fun x : Fin 2 → ℝ => x 1) y =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).fderiv
  refine ⟨fun v hv => ?_, fun h0 => ?_⟩
  · rw [lieAlgebraAt_unitField, Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    simp [hd]
  · have := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (Pi.single 1 1)) h0
    simp [hd] at this

end Examples
end RoboLean
