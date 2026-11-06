import RoboLean.Surfaces.OrthogonalChartProof

/-!
# Theorem 5.9 on the saddle chart (MLS p. 244)

**What MLS prints.** Printed p. 244: "**Theorem 5.9.** Locally, there exists an orthogonal chart for
all regular surfaces."

**Checked here.** The saddle chart `c(u, v) = (u, v, uv)` is smooth on `ℝ²` with injective
differential at every point (`contDiff_saddleChart`, `injective_fderiv_saddleChart`; the projection
to the first two coordinates is a left inverse), so Theorem 5.9 (`exists_orthogonal_reparametrization`)
gives near every parameter a smooth injective reparametrization onto a neighbourhood after which
the chart is orthogonal (`exists_orthogonal_reparametrization_saddle`). The saddle chart itself is
not orthogonal away from the coordinate axes (`c_u · c_v = uv`), which is what makes the example
more than a convention check of the identity reparametrization: `c_u = (1, 0, v)`,
`c_v = (0, 1, u)` (`partialU_saddleChart`, `partialV_saddleChart`) and the chart is not orthogonal
at `(1, 1)` (`not_isOrthogonalAt_saddleChart`).

**Conventions.** Charts `(Fin 2 → ℝ) → Vec3` with `Vec3 = EuclideanSpace ℝ (Fin 3)`, points written
`WithLp.toLp 2 ![x, y, z]`; orthogonal charts `IsOrthogonalChartOn` (MLS pp. 243–244).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace RoboLean
namespace Examples

open Surface

/-- **The saddle chart `c(u, v) = (u, v, uv)` (for MLS Theorem 5.9, p. 244):** a regular chart of
the saddle surface `z = xy`, coordinates `α = (u, v)` indexed `0, 1`. -/
def saddleChart (α : Fin 2 → ℝ) : Vec3 := WithLp.toLp 2 ![α 0, α 1, α 0 * α 1]

/-- **The projection `(x, y, z) ↦ (x, y)` (for MLS Theorem 5.9, p. 244),** a left inverse of the
saddle chart. -/
def saddleProj : Vec3 →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin 2 => EuclideanSpace.proj (Fin.castSucc i)

/-- **The saddle chart is smooth (MLS p. 243, condition 1 of a regular surface, for Theorem 5.9,
p. 244).** -/
theorem contDiff_saddleChart : ContDiff ℝ ∞ saddleChart := by
  refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp ?_
  refine contDiff_pi.2 fun i => ?_
  have hx : ∀ i : Fin 2, ContDiff ℝ ∞ fun x : Fin 2 → ℝ => x i := fun i => contDiff_apply ℝ _ i
  fin_cases i
  · simpa using hx 0
  · simpa using hx 1
  · simpa using (hx 0).mul (hx 1)

/-- **The projection to the first two coordinates inverts the saddle chart (for MLS Theorem 5.9,
p. 244).** -/
theorem saddleProj_comp_saddleChart : saddleProj ∘ saddleChart = id := by
  funext α i
  fin_cases i <;> simp [saddleProj, saddleChart]

/-- **The saddle chart has injective differential everywhere (MLS p. 243, condition 3 of a regular
surface, for Theorem 5.9, p. 244).** -/
theorem injective_fderiv_saddleChart (α : Fin 2 → ℝ) :
    Function.Injective (fderiv ℝ saddleChart α) := by
  have hd : HasFDerivAt (saddleProj ∘ saddleChart) (saddleProj.comp (fderiv ℝ saddleChart α)) α :=
    saddleProj.hasFDerivAt.comp α ((contDiff_saddleChart.differentiable (by simp)) α).hasFDerivAt
  rw [saddleProj_comp_saddleChart] at hd
  have h1 := hd.unique (hasFDerivAt_id α)
  intro a b hab
  have ha := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T a) h1
  have hb := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T b) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
  rw [← ha, ← hb, hab]

/-- **The partial `c_u` of the saddle chart (MLS p. 243, `c_u = ∂c/∂u`):** `c_u = (1, 0, v)`. -/
theorem partialU_saddleChart (α : Fin 2 → ℝ) :
    partialU saddleChart α = WithLp.toLp 2 ![1, 0, α 1] := by
  refine partialU_eq_of_hasDerivAt ((contDiff_saddleChart.differentiable (by simp)) α) ?_
  have hv : HasDerivAt (fun s : ℝ => ![(α + s • (Pi.single 0 1 : Fin 2 → ℝ)) 0, (α + s • (Pi.single 0 1 : Fin 2 → ℝ)) 1,
      (α + s • (Pi.single 0 1 : Fin 2 → ℝ)) 0 * (α + s • (Pi.single 0 1 : Fin 2 → ℝ)) 1]) ![1, 0, α 1] 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using (hasDerivAt_id (0 : ℝ)).const_add (α 0)
    · simpa using hasDerivAt_const (0 : ℝ) (α 1)
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (α 0)).mul_const (α 1)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt 0 hv

/-- **The partial `c_v` of the saddle chart (MLS p. 243, `c_v = ∂c/∂v`):** `c_v = (0, 1, u)`. -/
theorem partialV_saddleChart (α : Fin 2 → ℝ) :
    partialV saddleChart α = WithLp.toLp 2 ![0, 1, α 0] := by
  refine partialV_eq_of_hasDerivAt ((contDiff_saddleChart.differentiable (by simp)) α) ?_
  have hv : HasDerivAt (fun s : ℝ => ![(α + s • (Pi.single 1 1 : Fin 2 → ℝ)) 0, (α + s • (Pi.single 1 1 : Fin 2 → ℝ)) 1,
      (α + s • (Pi.single 1 1 : Fin 2 → ℝ)) 0 * (α + s • (Pi.single 1 1 : Fin 2 → ℝ)) 1]) ![0, 1, α 0] 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) (α 0)
    · simpa using (hasDerivAt_id (0 : ℝ)).const_add (α 1)
    · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (α 1)).const_mul (α 0)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt 0 hv

/-- **The saddle chart is not orthogonal at `(1, 1)` (MLS p. 244, orthogonal charts):**
`c_u · c_v = uv = 1` there, so Theorem 5.9 is needed to make it orthogonal. -/
theorem not_isOrthogonalAt_saddleChart : ¬ IsOrthogonalAt saddleChart ![1, 1] := by
  rw [IsOrthogonalAt, partialU_saddleChart, partialV_saddleChart]
  simp [PiLp.inner_apply, Fin.sum_univ_three]

/-- **Theorem 5.9 on the saddle (MLS p. 244):** near every parameter `α₀` the saddle chart has a
smooth reparametrization `θ`, injective on an open `V ∋ β₀` with `θ(β₀) = α₀` and `θ(V)` a
neighbourhood of `α₀`, after which it is an orthogonal chart on `V`. -/
theorem exists_orthogonal_reparametrization_saddle (α₀ : Fin 2 → ℝ) :
    ∃ (V : Set (Fin 2 → ℝ)) (θ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (β₀ : Fin 2 → ℝ),
      β₀ ∈ V ∧ θ β₀ = α₀ ∧ ContDiffOn ℝ ∞ θ V ∧ Set.InjOn θ V ∧ θ '' V ∈ 𝓝 α₀ ∧
        IsOrthogonalChartOn (saddleChart ∘ θ) V := by
  obtain ⟨V, θ, β₀, h1, h2, h3, h4, -, h6, h7⟩ := exists_orthogonal_reparametrization isOpen_univ
    contDiff_saddleChart.contDiffOn (fun α _ => injective_fderiv_saddleChart α) (mem_univ α₀)
  exact ⟨V, θ, β₀, h1, h2, h3, h4, h6, h7⟩

end Examples
end RoboLean
