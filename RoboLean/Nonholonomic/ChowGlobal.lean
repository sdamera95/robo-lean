import RoboLean.Nonholonomic.Chow

/-!
# Controllability from the rank condition at every point (MLS pp. 329–331)

**What MLS prints.** After Theorem 7.5: "This result asserts that the drift-free system `Σ` is
controllable if the rank of the controllability Lie algebra is `n`" (p. 330). After
Proposition 7.7: "In principle, we now have a recipe for solving the motion planning problem …
find finitely many intermediate via points `q₁, …, q_p` and neighborhoods `Vᵢ` such that
`⋃ R^{Vᵢ}(qᵢ, ≤ T)` contains the straight line segment connecting `q₀` to `q_f` … Then there
exists a control law of `p` segments which steers from `q₀` to `q_f`" (pp. 331–332).

**Proved here.** For a symmetric input set containing `0`, local controllability at every point
gives controllability (`isControllable_of_forall_isLocallyControllableAt`): the points reachable
from `q₀` form an open and closed set (concatenation and reversal of trajectories), hence the whole
space, which is connected. With Chow's theorem: on a finite-dimensional space, smooth generators
with the rank condition at every point and unconstrained inputs give a controllable system
(`isControllable_of_forall_lieAlgebraAt_eq_top`).

**Conventions.** Those of `Nonholonomic/Controllability`; `IsControllable g U`: every `q_f` is
reachable from every `q₀` in some time `T > 0` (p. 329).
-/

noncomputable section

open Set Filter Topology

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- **MLS pp. 331–332 (the recipe after Proposition 7.7) with p. 329: local controllability at
every point gives controllability.** For an input set with `U = −U` and `0 ∈ U`, if the system
(7.10) is locally controllable at every point, it is controllable. -/
theorem isControllable_of_forall_isLocallyControllableAt {g : Fin m → E → E}
    {U : Set (Fin m → ℝ)} (hU : ∀ v ∈ U, -v ∈ U) (h0 : (0 : Fin m → ℝ) ∈ U)
    (hloc : ∀ q, IsLocallyControllableAt g U q) : IsControllable g U := by
  intro q₀ qf
  set A : Set E := {q | ∃ T, 0 < T ∧ q ∈ reachableSet g U univ q₀ T} with hA
  have hstep : ∀ q, ∀ p ∈ reachableSetLE g U univ q 1,
      ∃ τ, 0 < τ ∧ p ∈ reachableSet g U univ q τ := by
    intro q p hp
    obtain ⟨τ, hτ, hpτ⟩ := mem_iUnion₂.1 hp
    exact ⟨τ, hτ.1, hpτ⟩
  have hN : ∀ q, reachableSetLE g U univ q 1 ∈ 𝓝 q := fun q => hloc q univ univ_mem 1 one_pos
  have hopen : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 fun q hq => mem_of_superset (hN q) fun p hp => ?_
    obtain ⟨T, hT, hqT⟩ := hq
    obtain ⟨τ, hτ, hpτ⟩ := hstep q p hp
    exact ⟨T + τ, by linarith, mem_reachableSet_trans hqT hpτ hT.le hτ.le⟩
  have hclosed : IsClosed A := by
    refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun q hq =>
      mem_of_superset (hN q) fun p hp hpA => hq ?_)
    obtain ⟨τ, hτ, hpτ⟩ := hstep q p hp
    obtain ⟨T, hT, hpT⟩ := hpA
    exact ⟨T + τ, by linarith, mem_reachableSet_trans hpT (mem_reachableSet_reverse hU hpτ) hT.le
      hτ.le⟩
  have hq₀ : q₀ ∈ A := ⟨1, one_pos, self_mem_reachableSet h0 (mem_univ _)⟩
  have huniv : A = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨q₀, hq₀⟩
  have hqf : qf ∈ A := by rw [huniv]; exact mem_univ _
  obtain ⟨T, hT, h⟩ := hqf
  exact ⟨T, hT, h⟩

open scoped ContDiff in
/-- **MLS p. 330 ("the drift-free system `Σ` is controllable if the rank of the controllability
Lie algebra is `n`"), with Theorem 7.5, p. 329:** on a finite-dimensional space, if the generators
are smooth and the controllability Lie algebra has full rank at every point, the system (7.10)
with unconstrained inputs is controllable. -/
theorem isControllable_of_forall_lieAlgebraAt_eq_top [FiniteDimensional ℝ E]
    {g : Fin m → E → E} (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hq : ∀ q, lieAlgebraAt g q = ⊤) :
    IsControllable g univ :=
  isControllable_of_forall_isLocallyControllableAt (fun _ _ => mem_univ _) (mem_univ _)
    fun q => isLocallyControllableAt_of_lieAlgebraAt_eq_top hg (hq q)

end Nonholonomic
end RoboLean
