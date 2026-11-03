import RoboLean.Nonholonomic.ChowGlobal
import RoboLean.Nonholonomic.ChainedForm
import RoboLean.Examples.NonholonomicGrowth

/-!
# Chow's theorem applied: the one-chain system, the rolling disk and the hopper (MLS Theorem 7.5,
p. 329; Proposition 8.2, p. 365; Examples 7.7 and 7.9, p. 342)

**What MLS prints.** Proposition 8.2 (p. 365): "The one-chain system (8.7) is completely
nonholonomic (controllable)." Examples 7.7 and 7.9 (p. 342) compute the growth vectors of the
hopper and the rolling disk, whose controllability Lie algebras have full rank.

**Proved here.** The library's conditional results `chain_isLocallyControllableAt`,
`disk_isLocallyControllableAt` and `hopper_isLocallyControllableAt` (stated with Chow's theorem as
the hypothesis `ChowStatement`) hold unconditionally, by `chowStatement`; the one-chain system and
the rolling disk (`ρ ≠ 0`) are moreover controllable, since the rank condition holds at every
point (`isControllable_of_forall_lieAlgebraAt_eq_top`). These are satisfying instances of the
hypotheses of Chow's theorem on `ℝⁿ`, `ℝ⁴` and `ℝ³`; nothing here concerns physical fidelity.

**Conventions.** Those of `Nonholonomic/Controllability`, `Nonholonomic/ChainedForm` and
`Examples/NonholonomicGrowth`; unconstrained inputs `U = ℝ²`.
-/

open Set
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Proposition 8.2, p. 365, with Theorem 7.5, p. 329:** the one-chain system (8.7) with
unconstrained inputs is locally controllable at every point of `ℝⁿ`. -/
theorem isLocallyControllableAt_chainFields (n : ℕ) (q : Fin n → ℝ) :
    IsLocallyControllableAt (chainFields n) univ q :=
  chain_isLocallyControllableAt chowStatement q

/-- **MLS Proposition 8.2, p. 365 ("controllable"), with Theorem 7.5, p. 329:** the one-chain
system (8.7) with unconstrained inputs is controllable. -/
theorem isControllable_chainFields (n : ℕ) : IsControllable (chainFields n) univ :=
  isControllable_of_forall_isLocallyControllableAt (fun _ _ => mem_univ _) (mem_univ _)
    (isLocallyControllableAt_chainFields n)

/-- **MLS Theorem 7.5 (Chow), p. 329, for Example 7.9, p. 342:** the rolling disk with
unconstrained inputs is locally controllable at every `q ∈ ℝ⁴`, for `ρ ≠ 0`. -/
theorem isLocallyControllableAt_diskFields {ρ : ℝ} (hρ : ρ ≠ 0) (q : Fin 4 → ℝ) :
    IsLocallyControllableAt (diskFields ρ) univ q :=
  disk_isLocallyControllableAt chowStatement hρ q

/-- **MLS p. 330 ("controllable if the rank of the controllability Lie algebra is `n`") for
Example 7.9, p. 342:** the rolling disk with unconstrained inputs is controllable, for `ρ ≠ 0`. -/
theorem isControllable_diskFields {ρ : ℝ} (hρ : ρ ≠ 0) : IsControllable (diskFields ρ) univ :=
  isControllable_of_forall_isLocallyControllableAt (fun _ _ => mem_univ _) (mem_univ _)
    (isLocallyControllableAt_diskFields hρ)

/-- **MLS Theorem 7.5 (Chow), p. 329, for Example 7.7, p. 342:** the hopper with unconstrained
inputs is locally controllable at every `q` with `l + d ≠ 0` (`I, m > 0`). -/
theorem isLocallyControllableAt_hopperFields {I m : ℝ} (hI : 0 < I) (hm : 0 < m) (d : ℝ)
    {q : Fin 3 → ℝ} (hq : q ∈ hopperDomain d) :
    IsLocallyControllableAt (hopperFields I m d) univ q :=
  hopper_isLocallyControllableAt chowStatement hI hm d hq

end Examples
end RoboLean
