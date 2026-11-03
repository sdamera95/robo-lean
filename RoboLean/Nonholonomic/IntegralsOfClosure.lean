import RoboLean.Nonholonomic.SevenRemainder
import RoboLean.Nonholonomic.FrobeniusFrame
import RoboLean.Nonholonomic.LocalFramesFiltration

/-!
# The integrals of the involutive closure (MLS pp. 339–341)

**What MLS prints.** p. 339: "If `Δ̄_q ≠ T_q ℝⁿ` and in addition `Δ̄_q` has a constant rank `n − p`
which is less than `n`, then it follows from Frobenius' theorem that there exist functions
`hᵢ(q) = cᵢ`, `i = 1, …, p` such that `ωᵢ(q) q̇ = 0, i = 1, …, k ⟺ h_j(q) = c_j, j = 1, …, p`."
pp. 340–341: "The maximum number of functions `hᵢ` such that
`span{∂h₁/∂q, …, ∂h_p/∂q} ⊂ span{ω₁, …, ω_k}` is given to be the set of functions such that
`span{∂h₁/∂q, …, ∂h_p/∂q} = (Δ̄)^⊥` by Frobenius' theorem."

**Proved here** (finite-dimensional real space `E` of dimension `n`, smooth input fields
`g₁, …, g_m`, the rank of the involutive closure `Δ̄_y = L(g₁, …, g_m)(y)` equal to `r` at every
point of an open set `U`):

* `Δ̄` is involutive on `U` in the library's sense (sections differentiable on `U`), through a local
  frame of fields of `L(g₁, …, g_m)` and the bracket closure of the Lie algebra
  (`isInvolutiveOn_lieAlgebraAt`), and it is integrable at every point of `U` with a defining map of
  class `C¹` by the library's Frobenius theorem (`isIntegrableAtOfClass_one_lieAlgebraAt`).
* **The integrals of the involutive closure** (`exists_integrals_of_involutiveClosure`): near every
  `q ∈ U` there are `n − r` functions of class `C¹` whose differentials are linearly independent and
  span `(Δ̄_y)^⊥` at every nearby `y` (the display of p. 341).
* **For constraints** `A(q) q̇ = 0` whose null space is spanned by the input fields on `U`
  (`exists_integrals_of_constraints`): these functions satisfy `L_{gⱼ} hᵢ = 0`, their differentials
  lie in the codistribution `Ω_y = span{ω₁(y), …, ω_k(y)}` (p. 340), and every point reachable from
  `q₀` by trajectories staying near `q` lies on the level set `hᵢ = hᵢ(q₀)` (the direction "⟹" of
  p. 339).
* **The count is the maximum** (`card_add_finrank_le_of_annihilates`, `isGreatest_card_integrals`):
  `p` functions whose differentials at `y` are independent and vanish on `Δ̄_y` satisfy
  `p + rank Δ̄_y ≤ n`, and `n − r` is the largest such number near `q`.

**Readings.** The functions are of class `C¹` (the class the library's Frobenius theorem gives), not
smooth as MLS asks. The book's "`⟺`" of p. 339 is read in the direction that a feasible curve stays
in a level set; the converse (that every curve in a level set is feasible) fails when `Δ̄ ≠ Δ` and
is not claimed. The rank hypothesis is the book's "`Δ̄_q` has a constant rank".

**Conventions.** `lieAlgebraAt g y` is the library's `Δ̄_y` (equal to the values of the involutive
closure, `spanAt_involutiveClosure`); differentials are Mathlib's `fderiv`, viewed in
`Module.Dual ℝ E`; `(Δ̄_y)^⊥` is `Submodule.dualAnnihilator`; the codistribution is
`codistributionAt`; reachable sets are the library's `reachableSet`.
-/

noncomputable section

open Set Filter Topology VectorField
open scoped ContDiff

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {m : ℕ}

/-- **MLS p. 325 with pp. 339–341: the involutive closure `Δ̄` is involutive where its rank is
constant:** on a finite-dimensional real space, for smooth input fields and an open set `U` on which
`Δ̄_y = L(g₁, …, g_m)(y)` has constant rank, `Δ̄` is involutive on `U` (sections differentiable on
`U`). -/
theorem isInvolutiveOn_lieAlgebraAt {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j))
    {U : Set E} (hU : IsOpen U) (hreg : IsRegularOn (lieAlgebraAt g) U) :
    IsInvolutiveOn (lieAlgebraAt g) U := by
  have hsmooth : ∀ {f : E → E}, InLieAlgebra g f → ContDiff ℝ ∞ f :=
    fun hf => InLieAlgebra.contDiff hg hf
  intro f h hf hh hfD hhD y hy
  obtain ⟨k, v, hvS, -, V, hV, hVU, hframe⟩ :=
    exists_localFrame_of_set (S := {f | InLieAlgebra g f}) hU hreg hy
      fun f hf => (hsmooth hf).continuous.continuousAt
  have hvd : ∀ b, DifferentiableAt ℝ (v b) y := fun b =>
    ((hsmooth (hvS b)).differentiable (by simp)) y
  have hmemof : ∀ s : E → E, (∀ x ∈ U, s x ∈ lieAlgebraAt g x) →
      ∀ᶠ z in 𝓝 y, s z ∈ Submodule.span ℝ (Set.range fun b => v b z) := fun s hs => by
    filter_upwards [hV] with z hz
    have h1 := hs z (hVU hz)
    rw [lieAlgebraAt, (hframe z hz).2] at h1
    exact h1
  have hli := (hframe y (mem_of_mem_nhds hV)).1
  obtain ⟨α, hα, hfα⟩ := exists_coeffs_of_localFrame hvd hli (hf y hy) (hmemof f hfD)
  obtain ⟨β, hβ, hhβ⟩ := exists_coeffs_of_localFrame hvd hli (hh y hy) (hmemof h hhD)
  have hgen : GeneratorsInvolutiveOn (Set.range v) {y} := by
    rintro z hz _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [mem_singleton_iff.1 hz]
    have h1 : lieBracket ℝ (v a) (v b) y ∈ lieAlgebraAt g y :=
      mem_spanAt (InLieAlgebra.bracket (hvS a) (hvS b)) y
    rw [lieAlgebraAt, (hframe y (mem_of_mem_nhds hV)).2, ← spanAt_range] at h1
    exact h1
  have h := hgen.lieBracket_mem (mem_singleton y) hvd hα hβ hfα hhβ
  rw [spanAt_range, ← (hframe y (mem_of_mem_nhds hV)).2] at h
  exact h

/-- **MLS pp. 339–341 with Theorem 7.2 (Frobenius), p. 326, "if": the involutive closure is
integrable with a `C¹` defining map:** on a finite-dimensional real space, for smooth input fields
and an open set `U` on which `Δ̄` has constant rank, `Δ̄` is integrable at every `q ∈ U` with a
defining map of class `C¹` (`IsIntegrableAtOfClass 1`; MLS asks smooth functions). -/
theorem isIntegrableAtOfClass_one_lieAlgebraAt {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U)
    (hreg : IsRegularOn (lieAlgebraAt g) U) {q : E} (hq : q ∈ U) :
    IsIntegrableAtOfClass 1 (lieAlgebraAt g) q := by
  obtain ⟨k, v, hvS, -, V, hV, -, hframe⟩ :=
    exists_localFrame_of_set (S := {f | InLieAlgebra g f}) hU hreg hq
      fun f hf => (InLieAlgebra.contDiff hg hf).continuous.continuousAt
  refine isIntegrableAtOfClass_one_of_isInvolutiveOn hU hreg (isInvolutiveOn_lieAlgebraAt hg hU hreg)
    hq (g := v) (fun i => (InLieAlgebra.contDiff hg (hvS i)).of_le (by simp)) ?_
  filter_upwards [hV] with y hy
  rw [lieAlgebraAt, (hframe y hy).2, spanAt_range]

/-- **MLS pp. 339–341: the number of functions whose differentials annihilate `Δ̄`:** on a
finite-dimensional real space, `p` functions whose differentials at `y` are linearly independent
and vanish on `Δ̄_y = L(g₁, …, g_m)(y)` satisfy `p + rank Δ̄_y ≤ n` (no smoothness is needed; for
smooth integrals of the constraints the vanishing on `Δ̄_y` is `fderiv_apply_eq_zero_of_mem_lieAlgebraAt`). -/
theorem card_add_finrank_le_of_annihilates {g : Fin m → E → E} {p : ℕ} {h : Fin p → E → ℝ}
    {y : E} (h0 : ∀ i, ∀ v ∈ lieAlgebraAt g y, fderiv ℝ (h i) y v = 0)
    (hli : LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) :
    p + Module.finrank ℝ (lieAlgebraAt g y) ≤ Module.finrank ℝ E := by
  have hsub : Submodule.span ℝ (Set.range fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) ≤
      (lieAlgebraAt g y).dualAnnihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    exact h0 i
  have h1 := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (lieAlgebraAt g y)
  have h3 := Nat.add_le_add_left h1 (Module.finrank ℝ (lieAlgebraAt g y))
  rw [add_comm]
  exact h3.trans h2.le

/-- **MLS p. 339 ("it follows from Frobenius' theorem that there exist functions `hᵢ(q) = cᵢ`,
`i = 1, …, p`") and p. 341 (`span{∂h₁/∂q, …, ∂h_p/∂q} = (Δ̄)^⊥`): the integrals of the involutive
closure.** On a finite-dimensional real space of dimension `n`, for smooth input fields and an open
set `U` on which `Δ̄_y = L(g₁, …, g_m)(y)` has constant rank `r`, every `q ∈ U` has an open
neighbourhood `V ⊆ U` carrying `n − r` functions `h₁, …, h_{n−r}` of class `C¹` (MLS: smooth) whose
differentials are linearly independent and span the annihilator `(Δ̄_y)^⊥` at every `y ∈ V`. -/
theorem exists_integrals_of_involutiveClosure {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U) {r : ℕ}
    (hreg : ∀ y ∈ U, Module.finrank ℝ (lieAlgebraAt g y) = r) {q : E} (hq : q ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∃ h : Fin (Module.finrank ℝ E - r) → E → ℝ,
        (∀ i, ∀ y ∈ V, ContDiffAt ℝ 1 (h i) y) ∧
        (∀ y ∈ V, LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) ∧
        ∀ y ∈ V, Submodule.span ℝ (Set.range fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) =
          (lieAlgebraAt g y).dualAnnihilator := by
  obtain ⟨W, hW, hqW, p, H, hH, hker⟩ :=
    isIntegrableAtOfClass_one_lieAlgebraAt hg hU ⟨r, hreg⟩ hq
  -- the count `p = n − r`
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
  -- the components and their differentials
  have hdiff : ∀ y ∈ W, DifferentiableAt ℝ H y := fun y hy =>
    (hH y hy).differentiableAt one_ne_zero
  have hcomp : ∀ y ∈ W, ∀ i, fderiv ℝ (fun z => H z i) y =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E - r) => ℝ) i).comp
        (fderiv ℝ H y) := fun y hy i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E - r) => ℝ) i).hasFDerivAt.comp y
      (hdiff y hy).hasFDerivAt).fderiv
  refine ⟨W ∩ U, hW.inter hU, ⟨hqW, hq⟩, inter_subset_right, fun i z => H z i,
    fun i y hy => contDiffAt_pi.1 (hH y hy.1) i, ?_, ?_⟩
  · -- independence, from the onto derivative
    intro y hy
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    obtain ⟨w, hw⟩ := (hker y hy.1).1 (Pi.single j 1)
    have := congrArg (fun φ : Module.Dual ℝ E => φ w) hc
    simpa [hcomp y hy.1, hw, Pi.single_apply] using this
  · -- the span is the annihilator, by inclusion and dimension
    intro y hy
    have hli : LinearIndependent ℝ fun i => (fderiv ℝ (fun z => H z i) y : Module.Dual ℝ E) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc j
      obtain ⟨w, hw⟩ := (hker y hy.1).1 (Pi.single j 1)
      have := congrArg (fun φ : Module.Dual ℝ E => φ w) hc
      simpa [hcomp y hy.1, hw, Pi.single_apply] using this
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
    rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact (Nat.eq_sub_of_add_eq' h2).symm

/-- **MLS pp. 339–341 for constraints `ωᵢ(q) q̇ = 0`: the integrals of the constraints.** On a
finite-dimensional real space of dimension `n`, let the constraints `A(y) q̇ = 0` have null space
`ker A(y) = span{g₁(y), …, g_m(y)}` on an open set `U`, for smooth `gⱼ` (the dual control system
(7.20)), and let `Δ̄_y = L(g₁, …, g_m)(y)` have constant rank `r` on `U`. Then every `q ∈ U` has an
open neighbourhood `V ⊆ U` carrying `n − r` functions `hᵢ` of class `C¹` (MLS: smooth) such that on
`V`: the differentials are independent and span `(Δ̄_y)^⊥` (p. 341); `L_{gⱼ} hᵢ = 0` (the integrals
of the constraints of the library's bounds, here without smoothness of `hᵢ`); each differential
lies in the codistribution `Ω_y = span{ω₁(y), …, ω_k(y)}` (p. 340); and every point reachable from
`q₀` in time `T ≥ 0` by a trajectory of (7.20) staying in `V` lies on the level set
`hᵢ = hᵢ(q₀)` (p. 339, "`⟹`"). -/
theorem exists_integrals_of_constraints {A : E → E →L[ℝ] F} {g : Fin m → E → E}
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E} (hU : IsOpen U)
    (hker : ∀ y ∈ U, LinearMap.ker (A y : E →ₗ[ℝ] F) = spanAt (Set.range g) y) {r : ℕ}
    (hreg : ∀ y ∈ U, Module.finrank ℝ (lieAlgebraAt g y) = r) {q : E} (hq : q ∈ U) :
    ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∃ h : Fin (Module.finrank ℝ E - r) → E → ℝ,
        (∀ i, ∀ y ∈ V, ContDiffAt ℝ 1 (h i) y) ∧
        (∀ y ∈ V, LinearIndependent ℝ fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) ∧
        (∀ y ∈ V, Submodule.span ℝ (Set.range fun i => (fderiv ℝ (h i) y : Module.Dual ℝ E)) =
          (lieAlgebraAt g y).dualAnnihilator) ∧
        (∀ i, ∀ y ∈ V, ∀ j, fderiv ℝ (h i) y (g j y) = 0) ∧
        (∀ i, ∀ y ∈ V, (fderiv ℝ (h i) y : Module.Dual ℝ E) ∈ codistributionAt A y) ∧
        ∀ (Uin : Set (Fin m → ℝ)) (q₀ : E) (T : ℝ), 0 ≤ T → ∀ i,
          reachableSet g Uin V q₀ T ⊆ {x | h i x = h i q₀} := by
  obtain ⟨V, hV, hqV, hVU, h, hC, hli, hspan⟩ :=
    exists_integrals_of_involutiveClosure hg hU hreg hq
  have hann : ∀ i, ∀ y ∈ V, (fderiv ℝ (h i) y : Module.Dual ℝ E) ∈
      (lieAlgebraAt g y).dualAnnihilator := fun i y hy => by
    rw [← hspan y hy]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hL : ∀ i, ∀ y ∈ V, ∀ j, fderiv ℝ (h i) y (g j y) = 0 := fun i y hy j =>
    (Submodule.mem_dualAnnihilator _).1 (hann i y hy) _ (mem_spanAt (InLieAlgebra.gen j) y)
  refine ⟨V, hV, hqV, hVU, h, hC, hli, hspan, hL, fun i y hy => ?_, fun Uin q₀ T hT i => ?_⟩
  · have hle : spanAt (Set.range g) y ≤ lieAlgebraAt g y := by
      rw [← filtrationAt_one]
      exact filtrationAt_le_lieAlgebraAt g 1 y
    rw [codistributionAt, LinearMap.range_dualMap_eq_dualAnnihilator_ker, hker y (hVU hy)]
    exact Submodule.dualAnnihilator_anti hle (hann i y hy)
  · exact reachableSet_subset_levelSet hT (fun x hx => (hC i x hx).differentiableAt one_ne_zero)
      (fun x hx j => hL i x hx j)

/-- **MLS pp. 340–341: "the maximum number of functions `hᵢ`" is `n − rank Δ̄`.** On a
finite-dimensional real space of dimension `n`, for smooth input fields and an open set `U` on which
`Δ̄` has constant rank `r`, at every `q ∈ U` the largest `p` for which there are `p` functions of
class `C¹` near `q` whose differentials vanish on `Δ̄` near `q` and are linearly independent at `q`
is `n − r`: the bound `p + rank Δ̄_q ≤ n` is attained. -/
theorem isGreatest_card_integrals {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j)) {U : Set E}
    (hU : IsOpen U) {r : ℕ} (hreg : ∀ y ∈ U, Module.finrank ℝ (lieAlgebraAt g y) = r) {q : E}
    (hq : q ∈ U) :
    IsGreatest {p : ℕ | ∃ h : Fin p → E → ℝ,
        (∀ᶠ y in 𝓝 q, ∀ i, ContDiffAt ℝ 1 (h i) y ∧
          ∀ v ∈ lieAlgebraAt g y, fderiv ℝ (h i) y v = 0) ∧
        LinearIndependent ℝ fun i => (fderiv ℝ (h i) q : Module.Dual ℝ E)}
      (Module.finrank ℝ E - r) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hqV, -, h, hC, hli, hspan⟩ := exists_integrals_of_involutiveClosure hg hU hreg hq
    refine ⟨h, ?_, hli q hqV⟩
    filter_upwards [hV.mem_nhds hqV] with y hy i
    refine ⟨hC i y hy, fun v hv => ?_⟩
    have hmem : (fderiv ℝ (h i) y : Module.Dual ℝ E) ∈ (lieAlgebraAt g y).dualAnnihilator := by
      rw [← hspan y hy]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_dualAnnihilator _).1 hmem v hv
  · rintro p ⟨h, hev, hli⟩
    have h0 : ∀ i, ∀ v ∈ lieAlgebraAt g q, fderiv ℝ (h i) q v = 0 := fun i => (hev.self_of_nhds i).2
    have := card_add_finrank_le_of_annihilates h0 hli
    rw [hreg q hq] at this
    omega

end Nonholonomic
end RoboLean
