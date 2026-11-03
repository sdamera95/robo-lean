import RoboLean.Nonholonomic.NilpotencyBridge
import RoboLean.Examples.NilpotentFiveState

/-!
# A nonabelian instance of Example 7.12's hypothesis: the five-state system of Chapter 8

MLS Example 7.12, p. 345, concerns three generators nilpotent of order 3 (p. 344). The five-state
system of Chapter 8, Exercise 2 (p. 391), `g₁ = (1, 0, −q₂, 0, q₂²)`, `g₂ = (0, 1, q₁, q₁², 0)`, is
nilpotent of order 3 (in the library's example of that exercise). With the third field
`g₃ = [g₁, g₂] = (0, 0, 2, 2q₁, −2q₂)` the three smooth fields `g₁, g₂, g₃`:

* are nilpotent of order 3, every Lie product of `g₁, g₂, g₃` being a Lie product of `g₁, g₂` at
  least as long (`isNilpotentOfOrder_fiveHallFields`), so they satisfy the hypothesis of the spanning
  half of Example 7.12 in both of its forms;
* do not commute: `[g₁, g₂] ≠ 0` and `[g₁, g₃] = (0, 0, 0, 2, 0) ≠ 0`
  (`fiveHallFields_not_abelian`);
* have `L(g₁, g₂, g₃)(q) = ℝ⁵` at every point, so the values of the fourteen Hall fields span `ℝ⁵`
  (`span_hallUpToThree_fiveHallFields`); fourteen vectors of `ℝ⁵` are not independent, as the reading
  of p. 345 for fields says.

A concrete system is a convention check for the general theorems; it says nothing about a physical
system.

**Conventions.** Coordinates `q 0 = q₁`, …, `q 4 = q₅`; the fields of the library's example of
Chapter 8, Exercise 2; Mathlib's `lieBracket`, the convention of MLS p. 323.
-/

noncomputable section

open scoped ContDiff
open VectorField RoboLean.Examples

namespace RoboLean
namespace Nonholonomic

/-- **Three generators for MLS Example 7.12, p. 345, from Chapter 8, Exercise 2, p. 391:**
`g₁ = (1, 0, −q₂, 0, q₂²)`, `g₂ = (0, 1, q₁, q₁², 0)` and `g₃ = [g₁, g₂]`. -/
def fiveHallFields : Fin 3 → (Fin 5 → ℝ) → Fin 5 → ℝ :=
  ![fiveFields 0, fiveFields 1, lieBracket ℝ (fiveFields 0) (fiveFields 1)]

/-- **MLS p. 391:** the three fields are smooth (polynomial in `q₁, q₂`). -/
theorem contDiff_fiveHallFields (j : Fin 3) : ContDiff ℝ ∞ (fiveHallFields j) := by
  fin_cases j
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveHallFields, fiveFields, baseField, fiveG1] <;> fun_prop
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [fiveHallFields, fiveFields, baseField, fiveG2] <;> fun_prop
  · change ContDiff ℝ ∞ (lieBracket ℝ (fiveFields 0) (fiveFields 1))
    rw [five_lieBracket]
    refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [baseField, fiveC] <;> fun_prop

/-- **MLS p. 344 with p. 391: `g₁, g₂, [g₁, g₂]` are nilpotent of order 3,** since `g₁, g₂` are and
each of the three is a Lie product of `g₁, g₂`. -/
theorem isNilpotentOfOrder_fiveHallFields : IsNilpotentOfOrder fiveHallFields 3 := by
  refine five_isNilpotencyOrder.1.of_isLieProduct fun j => ?_
  fin_cases j
  · exact ⟨1, IsLieProduct.gen 0⟩
  · exact ⟨1, IsLieProduct.gen 1⟩
  · exact ⟨2, IsLieProduct.bracket (IsLieProduct.gen 0) (IsLieProduct.gen 1)⟩

/-- **MLS Example 7.12's hypothesis on formal products (p. 344) for the five-state fields:** every
formal Lie product of length greater than 3 evaluates to zero on `g₁, g₂, [g₁, g₂]`. -/
theorem eval_fiveHallFields_eq_zero (A : LieProduct 3) (hA : 3 < A.length) :
    LieProduct.eval fiveHallFields A = 0 :=
  isNilpotentOfOrder_iff_eval.1 isNilpotentOfOrder_fiveHallFields A hA

/-- **The instance is not abelian (MLS p. 391):** `[g₁, g₂] ≠ 0` and `[g₁, g₃] ≠ 0`, with
`[g₁, g₃] = [g₁, [g₁, g₂]] = (0, 0, 0, 2, 0)`. -/
theorem fiveHallFields_not_abelian :
    lieBracket ℝ (fiveHallFields 0) (fiveHallFields 1) ≠ 0 ∧
      lieBracket ℝ (fiveHallFields 0) (fiveHallFields 2) ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := congrFun (congrFun h 0) 2
    change lieBracket ℝ (fiveFields 0) (fiveFields 1) 0 2 = 0 at h1
    rw [five_lieBracket] at h1
    simp [baseField, fiveC] at h1
  · have h1 := congrFun (congrFun h 0) 3
    change lieBracket ℝ (fiveFields 0) (lieBracket ℝ (fiveFields 0) (fiveFields 1)) 0 3 = 0 at h1
    rw [five_lieBracket_g1_lieBracket] at h1
    simp [fiveD1] at h1

/-- **MLS Example 7.12, p. 345, for the five-state fields:** the values at every `q` of the fourteen
Hall fields of `g₁, g₂, [g₁, g₂]` span `ℝ⁵`, through the spanning half restated with
`IsNilpotentOfOrder` and the rank condition of p. 391. -/
theorem span_hallUpToThree_fiveHallFields (q : Fin 5 → ℝ) :
    Submodule.span ℝ ((fun B => LieProduct.eval fiveHallFields B q) ''
      {B | B ∈ LieProduct.hallUpToThree}) = ⊤ := by
  rw [← lieAlgebraAt_eq_span_hallUpToThree_of_isNilpotentOfOrder contDiff_fiveHallFields
    isNilpotentOfOrder_fiveHallFields q]
  refine eq_top_iff.2 ?_
  rw [← five_lieAlgebraAt q]
  refine lieAlgebraAt_le_of_inLieAlgebra (fun i => ?_) q
  fin_cases i
  · exact InLieAlgebra.gen (g := fiveHallFields) 0
  · exact InLieAlgebra.gen (g := fiveHallFields) 1

end Nonholonomic
end RoboLean
