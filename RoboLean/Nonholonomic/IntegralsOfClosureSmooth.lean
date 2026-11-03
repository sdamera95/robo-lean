import RoboLean.Nonholonomic.IntegralsOfClosure
import RoboLean.Nonholonomic.FrobeniusSmooth

/-!
# Smooth integrals of the involutive closure (MLS pp. 339–341)

**What MLS prints.** p. 339: "If `Δ̄_q ≠ T_q ℝⁿ` and in addition `Δ̄_q` has a constant rank `n − p`
which is less than `n`, then it follows from Frobenius' theorem that there exist functions
`hᵢ(q) = cᵢ`, `i = 1, …, p`"; p. 339: "it follows that `p ≤ k`"; pp. 340–341: "The maximum number of
functions `hᵢ` such that `span{∂h₁/∂q, …, ∂h_p/∂q} ⊂ span{ω₁, …, ω_k}` is given to be the set of
functions such that `span{∂h₁/∂q, …, ∂h_p/∂q} = (Δ̄)^⊥` by Frobenius' theorem."

**Proved here**, with the library's smooth Frobenius theorem (finite-dimensional real space `E` of
dimension `n`, smooth input fields, `Δ̄_y = L(g₁, …, g_m)(y)` of constant rank `r` on an open set
`U`):

* `Δ̄` is integrable at every point of `U` with a smooth defining map (`isIntegrableAt_lieAlgebraAt`).
* Near every `q ∈ U` there are `n − r` smooth functions with independent differentials spanning
  `(Δ̄_y)^⊥` (`exists_smooth_integrals_of_involutiveClosure`), the smooth functions MLS asks for; they
  are smooth integrals of the constraints, `L_{gⱼ} hᵢ = 0`.
* **The landed bound is attained** (`isGreatest_card_smooth_integrals`): among smooth integrals of the
  constraints on an open neighbourhood of `q` (functions of class `C^∞` there with `L_{gⱼ} h = 0`,
  the functions of the library's bound `p + rank Δ̄_q ≤ n`, `card_add_finrank_lieAlgebraAt_le`), the
  largest number with independent differentials at `q` is `n − r`.

The functions of class `C¹` of the companion module (`exists_integrals_of_involutiveClosure`) are
not superseded there: that module states the count for any functions whose differentials vanish on
`Δ̄`.

**Conventions.** As the companion module: `lieAlgebraAt g y` is `Δ̄_y`; differentials are `fderiv`
in `Module.Dual ℝ E`; `IsIntegrableAt` is eq. (7.9) with smooth defining functions.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ}

/-- **MLS pp. 339–341 with Theorem 7.2 (Frobenius), p. 326: the involutive closure is integrable with
a smooth defining map:** on a finite-dimensional real space, for smooth input fields and an open set
`U` on which `Δ̄` has constant rank, `Δ̄` is integrable at every `q ∈ U` (`IsIntegrableAt`, eq.
(7.9) with smooth functions). -/
theorem isIntegrableAt_lieAlgebraAt {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {U : Set E} (hU : IsOpen U) (hreg : IsRegularOn (lieAlgebraAt g) U) {q : E} (hq : q ∈ U) :
    IsIntegrableAt (lieAlgebraAt g) q := by
  obtain ⟨k, v, hvS, -, V, hV, -, hframe⟩ :=
    exists_localFrame_of_set (S := {f | InLieAlgebra g f}) hU hreg hq
      fun f hf => (InLieAlgebra.contDiff hg hf).continuous.continuousAt
  refine isIntegrableAt_of_isInvolutiveOn hU hreg (isInvolutiveOn_lieAlgebraAt hg hU hreg) hq
    (g := v) (fun i => InLieAlgebra.contDiff hg (hvS i)) ?_
  filter_upwards [hV] with y hy
  rw [lieAlgebraAt, (hframe y hy).2, spanAt_range]

/-- **MLS p. 339 ("there exist functions `hᵢ(q) = cᵢ`, `i = 1, …, p`"), with smooth functions, and
p. 341 (`span{∂h₁/∂q, …, ∂h_p/∂q} = (Δ̄)^⊥`).** On a finite-dimensional real space of dimension `n`,
for smooth input fields and an open set `U` on which `Δ̄_y = L(g₁, …, g_m)(y)` has constant rank `r`,
every `q ∈ U` has an open neighbourhood `V ⊆ U` carrying `n − r` smooth functions (class `C^∞` at
every point of `V`) whose differentials are linearly independent and span `(Δ̄_y)^⊥` at every
`y ∈ V`, and which satisfy `L_{gⱼ} hᵢ = 0` on `V`. -/
theorem exists_smooth_integrals_of_involutiveClosure {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {r : ℕ}
    (hreg : ∀ y ∈ U, Module.finrank ℝ (lieAlgebraAt g y) = r) {q : E} (hq : q ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∃ h : Fin (Module.finrank ℝ E - r) → E → ℝ,
        (∀ i, ∀ y ∈ V, ContDiffAt ℝ ∞ (h i) y) ∧
        (∀ y ∈ V, LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) ∧
        (∀ y ∈ V, Submodule.span ℝ (Set.range fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) =
          (lieAlgebraAt g y).dualAnnihilator) ∧
        ∀ i, ∀ y ∈ V, ∀ j, fderiv ℝ (h i) y (g j y) = 0 := by
  obtain ⟨W, hW, hqW, p, H, hH, hker⟩ := isIntegrableAt_lieAlgebraAt hg hU ⟨r, hreg⟩ hq
  have hcount : ∀ y ∈ W ∩ U, p + r = Module.finrank ℝ E := by
    intro y hy
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ H y : E →ₗ[ℝ] Fin p → ℝ)
    have h2 : LinearMap.range (fderiv ℝ H y : E →ₗ[ℝ] Fin p → ℝ) = ⊤ :=
      LinearMap.range_eq_top.2 (hker y hy.1).1
    rw [h2, finrank_top, Module.finrank_fin_fun, ← (hker y hy.1).2, hreg y hy.2] at h1
    exact h1
  have hp : p = Module.finrank ℝ E - r := by
    have := hcount q ⟨hqW, hq⟩
    omega
  subst hp
  have hdiff : ∀ y ∈ W, DifferentiableAt ℝ H y := fun y hy =>
    (hH y hy).differentiableAt (by simp)
  have hcomp : ∀ y ∈ W, ∀ i, fderiv ℝ (fun z => H z i) y =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E - r) => ℝ) i).comp
        (fderiv ℝ H y) := fun y hy i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E - r) => ℝ) i).hasFDerivAt.comp
      y (hdiff y hy).hasFDerivAt).fderiv
  have hli : ∀ y ∈ W ∩ U,
      LinearIndependent ℝ fun i => (fderiv ℝ (fun z => H z i) y : Module.Dual ℝ E) := by
    intro y hy
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    obtain ⟨w, hw⟩ := (hker y hy.1).1 (Pi.single j 1)
    have := congrArg (fun φ : Module.Dual ℝ E => φ w) hc
    simpa [hcomp y hy.1, hw, Pi.single_apply] using this
  have hspan : ∀ y ∈ W ∩ U, Submodule.span ℝ (Set.range fun i =>
      (fderiv ℝ (fun z => H z i) y : Module.Dual ℝ E)) = (lieAlgebraAt g y).dualAnnihilator := by
    intro y hy
    have hle : Submodule.span ℝ (Set.range fun i => (fderiv ℝ (fun z => H z i) y :
        Module.Dual ℝ E)) ≤ (lieAlgebraAt g y).dualAnnihilator := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      intro v hv
      rw [(hker y hy.1).2] at hv
      have hv' : fderiv ℝ H y v = 0 := hv
      simp [hcomp y hy.1, hv']
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (lieAlgebraAt g y)
    rw [hreg y hy.2] at h2
    rw [finrank_span_eq_card (hli y hy), Fintype.card_fin]
    exact (Nat.eq_sub_of_add_eq' h2).symm
  refine ⟨W ∩ U, hW.inter hU, ⟨hqW, hq⟩, inter_subset_right, fun i z => H z i,
    fun i y hy => contDiffAt_pi.1 (hH y hy.1) i, hli, hspan, fun i y hy j => ?_⟩
  have hmem : (fderiv ℝ (fun z => H z i) y : Module.Dual ℝ E) ∈
      (lieAlgebraAt g y).dualAnnihilator := by
    rw [← hspan y hy]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact (Submodule.mem_dualAnnihilator _).1 hmem _ (mem_spanAt (InLieAlgebra.gen j) y)

/-- **MLS pp. 339–341: the bound on the number of integrals is attained by smooth integrals.** On a
finite-dimensional real space of dimension `n`, for smooth input fields and an open set `U` on which
`Δ̄` has constant rank `r`, at every `q ∈ U` the largest `p` for which there are an open
neighbourhood `V` of `q` and `p` functions of class `C^∞` on `V` with `L_{gⱼ} hᵢ = 0` on `V` (smooth
integrals of the constraints) and linearly independent differentials at `q` is `n − r`: the
library's bound `p + rank Δ̄_q ≤ n` is attained. -/
theorem isGreatest_card_smooth_integrals {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {U : Set E} (hU : IsOpen U) {r : ℕ} (hreg : ∀ y ∈ U, Module.finrank ℝ (lieAlgebraAt g y) = r)
    {q : E} (hq : q ∈ U) :
    IsGreatest {p : ℕ | ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ ∃ h : Fin p → E → ℝ,
        (∀ i, ContDiffOn ℝ ∞ (h i) V) ∧ (∀ i, ∀ y ∈ V, ∀ j, fderiv ℝ (h i) y (g j y) = 0) ∧
        LinearIndependent ℝ fun i => (fderiv ℝ (h i) q : Module.Dual ℝ E)}
      (Module.finrank ℝ E - r) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hqV, -, h, hC, hli, -, hL⟩ :=
      exists_smooth_integrals_of_involutiveClosure hg hU hreg hq
    exact ⟨V, hV, hqV, h, fun i y hy => (hC i y hy).contDiffWithinAt, hL, hli q hqV⟩
  · rintro p ⟨V, hV, hqV, h, hC, hL, hli⟩
    have := card_add_finrank_lieAlgebraAt_le hg hV hC hL hqV hli
    rw [hreg q hq] at this
    omega

end Nonholonomic
end RoboLean
