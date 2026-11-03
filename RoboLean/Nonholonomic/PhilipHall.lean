import RoboLean.Nonholonomic.Filtration

/-!
# The Philip Hall basis (MLS §7.4.3, pp. 344–345, Example 7.12)

**What MLS prints.** The length of a Lie product, `l(gᵢ) = 1` and `l([A, B]) = l(A) + l(B)`
(p. 344). "A Philip Hall basis is an ordered set of Lie products `H = {Bᵢ}` satisfying: 1.
`gᵢ ∈ H`; 2. if `l(Bᵢ) < l(Bⱼ)` then `Bᵢ < Bⱼ`; 3. `[Bᵢ, Bⱼ] ∈ H` if and only if (a) `Bᵢ, Bⱼ ∈ H`
and `Bᵢ < Bⱼ` and (b) either `Bⱼ = g_k` for some `k` or `Bⱼ = [B_l, B_r]` with `B_l, B_r ∈ H` and
`B_l ≤ Bᵢ`" (pp. 344–345). That it is a basis of the Lie algebra "is beyond the scope of this
book" (p. 345). Example 7.12 (p. 345) lists the basis of order 3 for three generators: three
generators, three brackets and eight products of length 3.

**Formalized here.** Lie products of `m` generators as formal brackets (`LieProduct m`), their
length and their evaluation on fields (`LieProduct.eval`, a member of `L(g₁, …, g_m)`,
`LieProduct.inLieAlgebra_eval`); a total order refining the length (`LieProduct.cmp`: by length,
then generators by index and brackets lexicographically, a choice: MLS fixes only condition 2);
the Hall condition 3 read recursively (`LieProduct.IsHall`); the Hall products of each length
(`LieProduct.hallOfLength`). Example 7.12 is checked by evaluation: the counts `3, 3, 8`, the
fourteen products, and the exclusion of `[g₁, [g₂, g₃]]`.

**Corrected printing.** Example 7.12 lists `[g₃, g₁]` among the brackets. With `g₁ < g₃`,
condition 3(a) admits `[g₁, g₃]` and not `[g₃, g₁]` (`not_isHall_g3_g1`), and the products of
length 3 printed next to it, `[g₁, [g₁, g₃]]`, `[g₂, [g₁, g₃]]`, `[g₃, [g₁, g₃]]`, use `[g₁, g₃]`.
The two differ by a sign, so either spans the same line of the Lie algebra; the Hall element is
`[g₁, g₃]`.

**The basis property** (cited by MLS, not proved there) is in `HallBasis` (spanning by every product
of length at most three, the named statement for every length) and `HallBasisFree` (the independence
of the fourteen products of Example 7.12 in the free Lie algebra on three generators).
-/

namespace RoboLean
namespace Nonholonomic

/-- **MLS p. 344: the Lie products of the generators `g₁, …, g_m`** (indices `Fin m`), as formal
brackets: a generator `gᵢ` or a bracket `[A, B]` of two products. -/
inductive LieProduct (m : ℕ) : Type
  /-- The generator `gᵢ` (MLS p. 344). -/
  | gen : Fin m → LieProduct m
  /-- The bracket `[A, B]` of two Lie products (MLS p. 344). -/
  | br : LieProduct m → LieProduct m → LieProduct m
  deriving DecidableEq

namespace LieProduct

variable {m : ℕ}

/-- **MLS p. 344: the length of a Lie product,** `l(gᵢ) = 1`, `l([A, B]) = l(A) + l(B)` (the
number of generators in its expansion). -/
def length : LieProduct m → ℕ
  | gen _ => 1
  | br a b => a.length + b.length

/-- **MLS p. 344, condition 2: an order on Lie products refining the length:** a shorter product
comes first; generators are ordered by index and brackets of equal length lexicographically (MLS
asks only condition 2; this tie-break is a choice). -/
def cmp : LieProduct m → LieProduct m → Ordering
  | gen i, gen j => compare i j
  | gen _, br _ _ => .lt
  | br _ _, gen _ => .gt
  | br a b, br c d =>
    (compare (a.length + b.length) (c.length + d.length)).then ((cmp a c).then (cmp b d))

/-- **MLS pp. 344–345, condition 3: the Hall products,** read recursively: generators are Hall
(condition 1), and `[A, B]` is Hall exactly when `A` and `B` are Hall, `A < B`, and `B` is a
generator or `B = [B_l, B_r]` with `B_l ≤ A`. -/
def IsHall : LieProduct m → Bool
  | gen _ => true
  | br a b => IsHall a && IsHall b && (cmp a b == .lt) &&
      (match b with
        | gen _ => true
        | br l _ => cmp l a != .gt)

/-- The products of each length `0, 1, …, n` (for MLS p. 345: "construct all possible Lie products
with length less than `k`"). -/
def upTo (m : ℕ) : ℕ → List (List (LieProduct m))
  | 0 => [[]]
  | n + 1 =>
    let t := upTo m n
    t ++ [if n = 0 then List.ofFn gen else
      (List.range (n + 1)).flatMap fun i =>
        ((t.getD i []).flatMap fun a => (t.getD (n + 1 - i) []).map fun b => br a b)]

/-- **MLS p. 345: all Lie products of length `n`** (formal brackets of `m` generators). -/
def ofLength (m n : ℕ) : List (LieProduct m) :=
  (upTo m n).getD n []

/-- **MLS pp. 344–345: the Philip Hall products of length `n`,** in the order of `ofLength`. -/
def hallOfLength (m n : ℕ) : List (LieProduct m) :=
  (ofLength m n).filter IsHall

/-- **MLS p. 344 and Definition 7.1, p. 326: the field of a Lie product,** `gᵢ` for a generator
and `[eval A, eval B]` (Mathlib's bracket, the book's sign) for `[A, B]`. -/
noncomputable def eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Fin m → E → E) : LieProduct m → E → E
  | gen i => g i
  | br a b => VectorField.lieBracket ℝ (eval g a) (eval g b)

/-- **MLS Definition 7.1, p. 326, and p. 344: every Lie product of the generators lies in
`L(g₁, …, g_m)`.** -/
theorem inLieAlgebra_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Fin m → E → E) (A : LieProduct m) : InLieAlgebra g (eval g A) := by
  induction A with
  | gen i => exact InLieAlgebra.gen i
  | br a b iha ihb => exact InLieAlgebra.bracket iha ihb

/-! ### Example 7.12: the Philip Hall basis of order 3 for three generators -/

/-- **MLS Example 7.12, p. 345:** three Hall products of length 1, the generators. -/
theorem hallOfLength_three_one : (hallOfLength 3 1).length = 3 := by decide

/-- **MLS Example 7.12, p. 345:** three Hall products of length 2. -/
theorem hallOfLength_three_two : (hallOfLength 3 2).length = 3 := by decide

/-- **MLS Example 7.12, p. 345:** eight Hall products of length 3. -/
theorem hallOfLength_three_three : (hallOfLength 3 3).length = 8 := by decide

/-- **MLS Example 7.12, p. 345:** the Hall products of length 2 are `[g₁, g₂]`, `[g₁, g₃]`,
`[g₂, g₃]` (MLS prints `[g₃, g₁]` for the second; corrected printing). -/
theorem hallOfLength_three_two_eq :
    hallOfLength 3 2 = [br (gen 0) (gen 1), br (gen 0) (gen 2), br (gen 1) (gen 2)] := by decide

/-- **MLS Example 7.12, p. 345:** the Hall products of length 3 are the eight printed ones,
`[g₁, [g₁, g₂]]`, `[g₁, [g₁, g₃]]`, `[g₂, [g₁, g₂]]`, `[g₂, [g₁, g₃]]`, `[g₂, [g₂, g₃]]`,
`[g₃, [g₁, g₂]]`, `[g₃, [g₁, g₃]]`, `[g₃, [g₂, g₃]]` (in a different order). -/
theorem hallOfLength_three_three_perm :
    (hallOfLength 3 3).Perm
      [br (gen 0) (br (gen 0) (gen 1)), br (gen 0) (br (gen 0) (gen 2)),
        br (gen 1) (br (gen 0) (gen 1)), br (gen 1) (br (gen 0) (gen 2)),
        br (gen 1) (br (gen 1) (gen 2)), br (gen 2) (br (gen 0) (gen 1)),
        br (gen 2) (br (gen 0) (gen 2)), br (gen 2) (br (gen 1) (gen 2))] := by decide

/-- **MLS Example 7.12, p. 345:** `[g₁, [g₂, g₃]]` is not a Hall product ("does not appear since"
the Jacobi identity expresses it by the other two). -/
theorem not_isHall_g1_g2g3 : IsHall (br (gen 0) (br (gen 1) (gen 2)) : LieProduct 3) = false := by
  decide

/-- **MLS Example 7.12, p. 345, corrected printing:** the printed `[g₃, g₁]` is not a Hall product
(condition 3(a) asks `g₃ < g₁`); `[g₁, g₃]` is. -/
theorem not_isHall_g3_g1 : IsHall (br (gen 2) (gen 0) : LieProduct 3) = false ∧
    IsHall (br (gen 0) (gen 2) : LieProduct 3) = true := by
  decide

end LieProduct

end Nonholonomic
end RoboLean
