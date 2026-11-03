import RoboLean.Nonholonomic.PhilipHall
import RoboLean.Nonholonomic.ExercisesSeven

/-!
# Chapter 7, Exercise 14: a Philip Hall basis of order 5 for two generators (MLS p. 352)

MLS Chapter 7, Exercise 14, printed p. 352: "Write a computer program to write a Philip Hall basis
of given order for a set of `m` generators `g₁, …, g_m`. Use your program to generate a Philip Hall
basis of order 5 for a system with 2 generators."

**What is formalized.** The program is the library's `LieProduct.hallOfLength m n`, the Philip Hall
products of length `n` read from conditions 1–3 of pp. 344–345 (the order: by length, then
lexicographically, generators first). For two generators it returns, by evaluation in the kernel:
* length 1: `g₁, g₂`; length 2: `[g₁, g₂]`;
* length 3: `[g₁, [g₁, g₂]]`, `[g₂, [g₁, g₂]]`;
* length 4: `[g₁, [g₁, [g₁, g₂]]]`, `[g₂, [g₁, [g₁, g₂]]]`, `[g₂, [g₂, [g₁, g₂]]]`;
* length 5: `[g₁, [g₁, [g₁, [g₁, g₂]]]]`, `[g₂, [g₁, [g₁, [g₁, g₂]]]]`,
  `[g₂, [g₂, [g₁, [g₁, g₂]]]]`, `[g₂, [g₂, [g₂, [g₁, g₂]]]]`, `[[g₁, g₂], [g₁, [g₁, g₂]]]`,
  `[[g₁, g₂], [g₂, [g₁, g₂]]]`;
fourteen products in all, `2, 1, 2, 3, 6` by length. These counts equal the bounds `σ̄ᵢ` of
Exercise 17 (p. 353) for `σ̄₁ = 2` at the stages `i = 1, …, 5`. That these fourteen products form a
basis (of the free nilpotent Lie algebra of order 5) is the basis property the book cites without
proof (p. 345); it is not proved here.

**Conventions.** Generators `0, 1` for `g₁, g₂`; `br A B` is the formal bracket `[A, B]`.
-/

namespace RoboLean
namespace Examples

open RoboLean.Nonholonomic RoboLean.Nonholonomic.LieProduct

/-- **MLS Chapter 7, Exercise 14, p. 352: the Philip Hall products of lengths 1 and 2 for two
generators,** `g₁, g₂` and `[g₁, g₂]`. -/
theorem hallOfLength_two_one_two :
    hallOfLength 2 1 = [gen 0, gen 1] ∧ hallOfLength 2 2 = [br (gen 0) (gen 1)] := by
  decide

/-- **MLS Chapter 7, Exercise 14, p. 352: the Philip Hall products of length 3 for two
generators,** `[g₁, [g₁, g₂]]` and `[g₂, [g₁, g₂]]`. -/
theorem hallOfLength_two_three :
    hallOfLength 2 3 = [br (gen 0) (br (gen 0) (gen 1)), br (gen 1) (br (gen 0) (gen 1))] := by
  decide

/-- **MLS Chapter 7, Exercise 14, p. 352: the Philip Hall products of length 4 for two
generators.** -/
theorem hallOfLength_two_four :
    hallOfLength 2 4 = [br (gen 0) (br (gen 0) (br (gen 0) (gen 1))),
      br (gen 1) (br (gen 0) (br (gen 0) (gen 1))),
      br (gen 1) (br (gen 1) (br (gen 0) (gen 1)))] := by
  decide

/-- **MLS Chapter 7, Exercise 14, p. 352: the Philip Hall products of length 5 for two
generators.** -/
theorem hallOfLength_two_five :
    hallOfLength 2 5 = [br (gen 0) (br (gen 0) (br (gen 0) (br (gen 0) (gen 1)))),
      br (gen 1) (br (gen 0) (br (gen 0) (br (gen 0) (gen 1)))),
      br (gen 1) (br (gen 1) (br (gen 0) (br (gen 0) (gen 1)))),
      br (gen 1) (br (gen 1) (br (gen 1) (br (gen 0) (gen 1)))),
      br (br (gen 0) (gen 1)) (br (gen 0) (br (gen 0) (gen 1))),
      br (br (gen 0) (gen 1)) (br (gen 1) (br (gen 0) (gen 1)))] := by
  decide

/-- **MLS Chapter 7, Exercise 14, p. 352: the Philip Hall basis of order 5 for two generators has
fourteen products,** `2 + 1 + 2 + 3 + 6`. -/
theorem hallOfLength_two_upToFive_length :
    ((List.range 5).flatMap fun k => hallOfLength 2 (k + 1)).length = 14 := by
  decide

/-- **MLS Chapter 7, Exercises 14 and 17, pp. 352–353: the counts by length agree with the bound
`σ̄ᵢ` of Exercise 17 for `σ̄₁ = 2`** at the stages `i = 1, …, 5`. -/
theorem hallOfLength_two_length_eq_maxGrowth :
    ∀ i ∈ Finset.Icc 1 5, ((hallOfLength 2 i).length : ℚ) = maxGrowth 2 i := by
  have h4 : maxGrowth 2 4 = 3 := by
    have h : Nat.properDivisors 4 = {1, 2} := by decide
    rw [maxGrowth, Finset.sum_attach (Nat.properDivisors 4) (fun j => (j : ℚ) * maxGrowth 2 j), h,
      Finset.sum_pair (by norm_num), maxGrowth_one, maxGrowth_two]
    norm_num
  have h5 : maxGrowth 2 5 = 6 := by
    have h : Nat.properDivisors 5 = {1} := by decide
    rw [maxGrowth, Finset.sum_attach (Nat.properDivisors 5) (fun j => (j : ℚ) * maxGrowth 2 j), h,
      Finset.sum_singleton, maxGrowth_one]
    norm_num
  intro i hi
  rcases Finset.mem_Icc.1 hi with ⟨h1, h2⟩
  interval_cases i
  · rw [hallOfLength_two_one_two.1, maxGrowth_one]; norm_num
  · rw [hallOfLength_two_one_two.2, maxGrowth_two]; norm_num
  · rw [hallOfLength_two_three, maxGrowth_three]; norm_num
  · rw [hallOfLength_two_four, h4]; norm_num
  · rw [hallOfLength_two_five, h5]; norm_num

end Examples
end RoboLean
