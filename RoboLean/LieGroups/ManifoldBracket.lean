import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import RoboLean.LieGroups.Manifold

/-!
# The bracket (A.1) on the Lie algebra of `GL(n, ℝ)` in Mathlib's sense

MLS Appendix A, printed p. 410: the Lie algebra of a Lie group is `T_eG` with the bracket
`[ξ₁, ξ₂] = [X_{ξ₁}, X_{ξ₂}](e)` (A.1) of the left invariant fields `X_ξ(g) = T_eL_g ξ`; Example A.6:
for `GL(n, ℝ)` this bracket is `[A, B] = AB − BA` ("see [108, pp. 509–511] for the details of this
calculation").

Statements. Mathlib's `GroupLieAlgebra I G` is `T_eG` with the bracket `mlieBracket` of
`mulInvariantVectorField`s at the identity, which is (A.1) with the sign of p. 407. For the units
`Rˣ` of any complete normed real algebra `R` (charted by `Rˣ → R`): the inclusion has derivative the
identity in charts, `X_A(u) = uA`, and the bracket of `A, B ∈ T_eRˣ = R` is `AB − BA`. The proof pulls
the fields `x ↦ xA` of the model space back along the inclusion (naturality of the bracket,
Mathlib's `mpullback_mlieBracket`) and computes their bracket in `R`. For `GL(n, ℝ)` as the units of
the endomorphisms of `ℝⁿ` (`RoboLean.LieGroup.EuclideanGL`), transported to matrices by
`groupLieAlgebraEquiv`, this is Example A.6 as printed.
-/

noncomputable section

open scoped Manifold ContDiff
open VectorField

namespace RoboLean

namespace LieGroup

section Units

variable {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra ℝ R]

/-- MLS Example A.2, p. 409 (the group as an open subset of its algebra): a map `f : Rˣ → Rˣ` with
`f(x) = F(x)` in `R` has, in the chart `Rˣ → R`, the derivative of `F`. -/
theorem hasMFDerivAt_units_of_val {f : Rˣ → Rˣ} {F : R → R} {F' : R →L[ℝ] R} (u : Rˣ)
    (hf : ∀ x, ((f x : Rˣ) : R) = F x) (hF : HasFDerivAt F F' (u : R)) :
    HasMFDerivAt 𝓘(ℝ, R) 𝓘(ℝ, R) f u F' := by
  refine ⟨?_, ?_⟩
  · rw [Units.isOpenEmbedding_val.isEmbedding.continuousAt_iff]
    have : (Units.val ∘ f) = F ∘ Units.val := funext hf
    rw [this]
    exact hF.continuousAt.comp Units.continuous_val.continuousAt
  · have hT : (chartAt R u).target ∈ nhds (u : R) :=
      (chartAt R u).open_target.mem_nhds (mem_chart_target R u)
    have key : writtenInExtChartAt 𝓘(ℝ, R) 𝓘(ℝ, R) u f =ᶠ[nhds (u : R)] F := by
      filter_upwards [hT] with y hy
      have hr : (((chartAt R u).symm y : Rˣ) : R) = y := (chartAt R u).right_inv hy
      simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_apply, id, Units.chartAt_apply]
      rw [hf, hr]
    have hu : (extChartAt 𝓘(ℝ, R) u) u = (u : R) := rfl
    rw [hu, modelWithCornersSelf_coe, Set.range_id]
    exact (hF.congr_of_eventuallyEq key).hasFDerivWithinAt

/-- MLS Example A.2, p. 409: the inclusion `Rˣ → R` of the units as an open subset has, at every
point, the identity as derivative. -/
theorem hasMFDerivAt_units_val (u : Rˣ) :
    HasMFDerivAt 𝓘(ℝ, R) 𝓘(ℝ, R) (Units.val : Rˣ → R) u (ContinuousLinearMap.id ℝ R) := by
  refine ⟨Units.continuous_val.continuousAt, ?_⟩
  have hT : (chartAt R u).target ∈ nhds (u : R) :=
    (chartAt R u).open_target.mem_nhds (mem_chart_target R u)
  have key : writtenInExtChartAt 𝓘(ℝ, R) 𝓘(ℝ, R) u (Units.val : Rˣ → R) =ᶠ[nhds (u : R)] id := by
    filter_upwards [hT] with y hy
    have hr : (((chartAt R u).symm y : Rˣ) : R) = y := (chartAt R u).right_inv hy
    simp only [writtenInExtChartAt, extChartAt_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id, extChartAt_model_space_eq_id, PartialEquiv.refl_coe]
    exact hr
  have hu : (extChartAt 𝓘(ℝ, R) u) u = (u : R) := rfl
  rw [hu, modelWithCornersSelf_coe, Set.range_id]
  exact ((hasFDerivAt_id (u : R)).congr_of_eventuallyEq key).hasFDerivWithinAt

/-- An element of `R` as a tangent vector at the identity of `Rˣ`, an element of the Lie algebra
`T_eRˣ = R` (MLS p. 410, Example A.6). -/
abbrev unitsLieAlgebraOf (A : R) : GroupLieAlgebra 𝓘(ℝ, R) Rˣ := A

/-- The field `x ↦ xA` on `R` (MLS Example A.5–A.6, p. 410: left invariant fields written on the
ambient algebra). -/
def rightMulField (A : R) : (x : R) → TangentSpace 𝓘(ℝ, R) x := fun x => x * A

/-- **MLS p. 410 with Example A.6: the left invariant field of `A ∈ T_eRˣ` is `X_A(u) = uA`**
(Mathlib's `mulInvariantVectorField`, `X_ξ(g) = T_eL_g ξ`). -/
theorem mulInvariantVectorField_units (A : R) (u : Rˣ) :
    (mulInvariantVectorField (unitsLieAlgebraOf A) u : R) = (u : R) * A := by
  have h := hasMFDerivAt_units_of_val (f := fun x : Rˣ => u * x) (F := fun y : R => (u : R) * y)
    (F' := ContinuousLinearMap.mul ℝ R u) 1 (fun x => by simp)
    ((ContinuousLinearMap.mul ℝ R u).hasFDerivAt)
  simp only [mulInvariantVectorField, h.mfderiv]
  rfl

omit [CompleteSpace R] in
/-- MLS Example A.6, p. 410: the field `x ↦ xA` on `R` is differentiable as a section of the tangent
bundle. -/
theorem mdifferentiableAt_rightMulField (A : R) (y : R) :
    MDifferentiableAt 𝓘(ℝ, R) 𝓘(ℝ, R).tangent
      (fun x : R => (⟨x, rightMulField A x⟩ : TangentBundle 𝓘(ℝ, R) R)) y := by
  rw [mdifferentiableAt_section]
  simp only [trivializationAt_model_space_apply]
  show MDifferentiableAt 𝓘(ℝ, R) 𝓘(ℝ, R) (fun b : R => b * A) y
  rw [mdifferentiableAt_iff_differentiableAt]
  exact ((ContinuousLinearMap.mul ℝ R).flip A).differentiableAt

/-- MLS Example A.6, p. 410: the field `x ↦ xA` on `R`, pulled back along the inclusion `Rˣ → R`, is
the left invariant field `X_A` of `Rˣ`. -/
theorem mpullback_val_rightMulField (A : R) :
    mpullback 𝓘(ℝ, R) 𝓘(ℝ, R) (Units.val : Rˣ → R) (rightMulField A) =
      mulInvariantVectorField (unitsLieAlgebraOf A) := by
  funext u
  simp only [mpullback, (hasMFDerivAt_units_val u).mfderiv]
  erw [ContinuousLinearMap.inverse_id]
  rw [mulInvariantVectorField_units]
  rfl

/-- **MLS (A.1), p. 410, and Example A.6: the bracket of the Lie algebra of `Rˣ` is the commutator**,
`[A, B] = [X_A, X_B](e) = AB − BA`, with Mathlib's bracket of left invariant fields. -/
theorem bracket_unitsLieAlgebraOf (A B : R) :
    ⁅unitsLieAlgebraOf A, unitsLieAlgebraOf B⁆ = unitsLieAlgebraOf (A * B - B * A) := by
  rw [GroupLieAlgebra.bracket_def, ← mpullback_val_rightMulField, ← mpullback_val_rightMulField,
    ← mpullback_mlieBracket (mdifferentiableAt_rightMulField A _)
      (mdifferentiableAt_rightMulField B _) Units.contMDiff_val.contMDiffAt le_rfl]
  simp only [mpullback, (hasMFDerivAt_units_val 1).mfderiv]
  erw [ContinuousLinearMap.inverse_id]
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  change lieBracketWithin ℝ ⇑((ContinuousLinearMap.mul ℝ R).flip A)
    ⇑((ContinuousLinearMap.mul ℝ R).flip B) Set.univ (1 : R) = A * B - B * A
  rw [lieBracketWithin_univ, lieBracket, ((ContinuousLinearMap.mul ℝ R).flip A).fderiv,
    ((ContinuousLinearMap.mul ℝ R).flip B).fderiv]
  simp

end Units

/-- **MLS Example A.6, p. 410: the Lie algebra of `GL(n, ℝ)` is `gl(n, ℝ)` with the bracket
`[A, B] = AB − BA`**, for Mathlib's Lie group `GL(n, ℝ)` and its bracket (A.1) of left invariant
fields, transported to matrices by `groupLieAlgebraEquiv`. -/
theorem groupLieAlgebraEquiv_bracket (n : ℕ)
    (A B : GroupLieAlgebra 𝓘(ℝ, EuclideanEnd n) (EuclideanGL n)) :
    groupLieAlgebraEquiv n ⁅A, B⁆ =
      groupLieAlgebraEquiv n A * groupLieAlgebraEquiv n B -
        groupLieAlgebraEquiv n B * groupLieAlgebraEquiv n A := by
  have h := bracket_unitsLieAlgebraOf (R := EuclideanEnd n) A B
  simp only [unitsLieAlgebraOf] at h
  rw [h]
  have key : ∀ X Y : EuclideanEnd n,
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (X * Y - Y * X) =
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm X *
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm Y -
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm Y *
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm X := fun X Y => by
    rw [map_sub, map_mul, map_mul]
  exact key A B

end LieGroup

end RoboLean
