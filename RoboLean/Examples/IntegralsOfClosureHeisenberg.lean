import RoboLean.Nonholonomic.IntegralsOfClosure

/-!
# A system whose involutive closure is larger than its distribution (MLS pp. 339–341)

A convention check for the integrals of the involutive closure (MLS pp. 339–341) in the case the
book's count is about, `Δ̄ ≠ Δ`: on `ℝ⁴` the input fields `g₁ = e₁` and `g₂ = e₂ + q₁ e₃` (the
constraints `q̇₃ = q₁ q̇₂` and `q̇₄ = 0`, so `k = 2`) span a distribution `Δ` of rank `2` that does not
contain `[g₁, g₂] = e₃`; every field of `L(g₁, g₂)` is `a e₁ + b(e₂ + q₁ e₃) + c e₃` with constants
`a, b, c`, so `Δ̄_y = {v : v₄ = 0}` has rank `3` at every point. The general theorem gives
`n − rank Δ̄ = 4 − 3 = 1` integral near every point, fewer than `k = 2` (p. 339: "`p ≤ k`"), and the
fourth coordinate `h(q) = q₄` is one, derived independently. A concrete system says nothing about a
physical one.

**Conventions.** Points of `ℝ⁴` are `Fin 4 → ℝ`; `eᵢ₊₁ = Pi.single i 1`, `qᵢ₊₁ = q i`; Mathlib's
`lieBracket`, the convention of MLS p. 323.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Examples

open Nonholonomic

/-- **The input fields `g₁ = e₁`, `g₂ = e₂ + q₁ e₃` on `ℝ⁴` (for MLS pp. 339–341).** -/
def heisField : Fin 2 → (Fin 4 → ℝ) → Fin 4 → ℝ :=
  ![fun _ => Pi.single 0 1, fun x => Pi.single 1 1 + x 0 • Pi.single 2 1]

/-- The affine field `a e₁ + b (e₂ + q₁ e₃) + c e₃` (for MLS p. 326). -/
private def aff (a b c : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  a • Pi.single 0 1 + b • (Pi.single 1 1 + x 0 • Pi.single 2 1) + c • Pi.single 2 1

private lemma hasFDerivAt_aff (a b c : ℝ) (y : Fin 4 → ℝ) :
    HasFDerivAt (aff a b c)
      (b • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).smulRight
        (Pi.single 2 1 : Fin 4 → ℝ)) y := by
  have e : aff a b c = fun x => (a • Pi.single 0 1 + b • Pi.single 1 1 + c • Pi.single 2 1 :
      Fin 4 → ℝ) + (b • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).smulRight
        (Pi.single 2 1 : Fin 4 → ℝ)) x := by
    funext x
    simp only [aff, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_add]
    abel
  rw [e]
  exact (ContinuousLinearMap.hasFDerivAt _).const_add _

private lemma lieBracket_aff (a b c a' b' c' : ℝ) :
    lieBracket ℝ (aff a b c) (aff a' b' c') = aff 0 0 (b' * a - b * a') := by
  funext y
  rw [lieBracket, (hasFDerivAt_aff a b c y).fderiv, (hasFDerivAt_aff a' b' c' y).fderiv]
  funext i
  fin_cases i <;> simp [aff]

/-- **MLS Definition 7.1, p. 326, for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`:** every field of `L(g₁, g₂)` is
`a e₁ + b (e₂ + q₁ e₃) + c e₃` for constants `a, b, c`. -/
theorem exists_eq_of_inLieAlgebra_heisField {f : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hf : InLieAlgebra heisField f) : ∃ a b c : ℝ, ∀ x, f x =
      a • Pi.single 0 1 + b • (Pi.single 1 1 + x 0 • Pi.single 2 1) + c • Pi.single 2 1 := by
  suffices h : ∃ a b c : ℝ, f = aff a b c by
    obtain ⟨a, b, c, rfl⟩ := h
    exact ⟨a, b, c, fun x => rfl⟩
  induction hf with
  | gen j =>
    fin_cases j
    · exact ⟨1, 0, 0, by funext x; simp [heisField, aff]⟩
    · exact ⟨0, 1, 0, by funext x; simp [heisField, aff]⟩
  | add _ _ ihf ihh =>
    obtain ⟨a, b, c, rfl⟩ := ihf
    obtain ⟨a', b', c', rfl⟩ := ihh
    refine ⟨a + a', b + b', c + c', ?_⟩
    funext x
    simp only [aff, Pi.add_apply, add_smul]
    abel
  | smul r _ ih =>
    obtain ⟨a, b, c, rfl⟩ := ih
    refine ⟨r * a, r * b, r * c, ?_⟩
    funext x
    simp only [aff, Pi.smul_apply, smul_add, mul_smul]
  | bracket _ _ ihf ihh =>
    obtain ⟨a, b, c, rfl⟩ := ihf
    obtain ⟨a', b', c', rfl⟩ := ihh
    exact ⟨0, 0, b' * a - b * a', lieBracket_aff a b c a' b' c'⟩

/-- **MLS p. 339 for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`: `[g₁, g₂] = e₃`.** -/
theorem lieBracket_heisField : lieBracket ℝ (heisField 0) (heisField 1) = fun _ => Pi.single 2 1 := by
  have h0 : heisField 0 = aff 1 0 0 := by funext x; simp [heisField, aff]
  have h1 : heisField 1 = aff 0 1 0 := by funext x; simp [heisField, aff]
  rw [h0, h1, lieBracket_aff]
  funext x
  simp [aff]

/-- **MLS pp. 325–326 for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`:** `Δ̄_y = L(g₁, g₂)(y)` is the hyperplane
`{v : v₄ = 0}` at every point. -/
theorem lieAlgebraAt_heisField (y : Fin 4 → ℝ) :
    lieAlgebraAt heisField y =
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3) := by
  apply le_antisymm
  · unfold lieAlgebraAt spanAt
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, b, c, hfx⟩ := exists_eq_of_inLieAlgebra_heisField hf
    simp [hfx]
  · intro v hv
    have hv3 : v 3 = 0 := hv
    have hg0 : (Pi.single 0 1 : Fin 4 → ℝ) ∈ lieAlgebraAt heisField y :=
      mem_spanAt (InLieAlgebra.gen (g := heisField) 0) y
    have hg1 : Pi.single 1 1 + y 0 • (Pi.single 2 1 : Fin 4 → ℝ) ∈ lieAlgebraAt heisField y :=
      mem_spanAt (InLieAlgebra.gen (g := heisField) 1) y
    have hg2 : (Pi.single 2 1 : Fin 4 → ℝ) ∈ lieAlgebraAt heisField y := by
      have := mem_spanAt (InLieAlgebra.bracket (InLieAlgebra.gen (g := heisField) 0)
        (InLieAlgebra.gen (g := heisField) 1)) y
      rwa [lieBracket_heisField] at this
    have e : v = v 0 • (Pi.single 0 1 : Fin 4 → ℝ) +
        v 1 • (Pi.single 1 1 + y 0 • (Pi.single 2 1 : Fin 4 → ℝ)) +
        (v 2 - v 1 * y 0) • (Pi.single 2 1 : Fin 4 → ℝ) := by
      funext i
      fin_cases i <;> simp [hv3]
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hg0)
      (Submodule.smul_mem _ _ hg1)) (Submodule.smul_mem _ _ hg2)

/-- **MLS p. 339 ("`Δ̄_q` has a constant rank") for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`:** the rank of
`Δ̄` is `3` at every point. -/
theorem finrank_lieAlgebraAt_heisField (y : Fin 4 → ℝ) :
    Module.finrank ℝ (lieAlgebraAt heisField y) = 3 := by
  rw [lieAlgebraAt_heisField]
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3)
  have hr : LinearMap.range (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun r => ⟨Pi.single 3 r, by simp⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- **MLS p. 339 for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`: `Δ̄ ≠ Δ`:** the bracket direction `e₃` is not in
`Δ_y = span{g₁(y), g₂(y)}` at any point, while it lies in `Δ̄_y`. -/
theorem single_two_not_mem_spanAt_heisField (y : Fin 4 → ℝ) :
    (Pi.single 2 1 : Fin 4 → ℝ) ∉ spanAt (Set.range heisField) y ∧
      (Pi.single 2 1 : Fin 4 → ℝ) ∈ lieAlgebraAt heisField y := by
  refine ⟨fun h => ?_, by rw [lieAlgebraAt_heisField]; simp⟩
  rw [spanAt_range, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_two, heisField] at h1 h2
  rw [h1] at h2
  simp at h2

/-- **MLS pp. 339–341 for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`: one integral near every point,** from the
general theorem with `n = 4` and `r = 3`; the system has `k = 2` constraints, so `p = 1 < k`. -/
theorem heisField_integrals (q : Fin 4 → ℝ) :
    ∃ V : Set (Fin 4 → ℝ), IsOpen V ∧ q ∈ V ∧
      ∃ h : Fin (Module.finrank ℝ (Fin 4 → ℝ) - 3) → (Fin 4 → ℝ) → ℝ,
        (∀ i, ∀ y ∈ V, ContDiffAt ℝ 1 (h i) y) ∧
        (∀ y ∈ V, LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ (Fin 4 → ℝ))) ∧
        ∀ y ∈ V, Submodule.span ℝ (Set.range fun i =>
          (fderiv ℝ (h i) y : Module.Dual ℝ (Fin 4 → ℝ))) =
            (lieAlgebraAt heisField y).dualAnnihilator := by
  have hg : ∀ j, ContDiff ℝ ∞ (heisField j) := by
    intro j
    fin_cases j
    · exact contDiff_const
    · exact contDiff_const.add (contDiff_apply ℝ ℝ (0 : Fin 4) |>.smul contDiff_const)
  obtain ⟨V, hV, hqV, -, h, hC, hli, hspan⟩ := exists_integrals_of_involutiveClosure hg
    isOpen_univ (fun y _ => finrank_lieAlgebraAt_heisField y) (mem_univ q)
  exact ⟨V, hV, hqV, h, hC, hli, hspan⟩

/-- **MLS p. 339 for `g₁ = e₁`, `g₂ = e₂ + q₁ e₃`, an integral derived independently:** the fourth
coordinate `h(q) = q₄` has differential vanishing on `Δ̄_y` and different from zero at every
point. -/
theorem fourthCoordinate_integral (y : Fin 4 → ℝ) :
    (∀ v ∈ lieAlgebraAt heisField y, fderiv ℝ (fun x : Fin 4 → ℝ => x 3) y v = 0) ∧
      fderiv ℝ (fun x : Fin 4 → ℝ => x 3) y ≠ 0 := by
  have hd : fderiv ℝ (fun x : Fin 4 → ℝ => x 3) y =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3 :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3).fderiv
  refine ⟨fun v hv => ?_, fun h0 => ?_⟩
  · rw [lieAlgebraAt_heisField] at hv
    have hv3 : v 3 = 0 := hv
    simp [hd, hv3]
  · have := congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single 3 1)) h0
    simp [hd] at this

end Examples
end RoboLean
