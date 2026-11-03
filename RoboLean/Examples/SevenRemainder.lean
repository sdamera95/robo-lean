import RoboLean.Nonholonomic.SevenRemainder

/-!
# One input on the line: the degree of nonholonomy equals `n` (MLS p. 340)

MLS p. 340: "if a filtration is regular, then there exists an integer `κ < n` such that `Δᵢ = Δ_κ`
for all `i ≥ κ`". For the single field `g₁ = 1` on `ℝ` (`n = 1`) the filtration is regular, its
degree of nonholonomy is `κ = 1 = n`, and no `κ < n` is a degree: the printed bound fails; the bound
that holds is `κ + rank Δ₁ ≤ n + 1` (`exists_isDegreeOfNonholonomy`).
-/

noncomputable section

open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **For MLS p. 340:** the single field `g₁ = 1` on `ℝ`. -/
def lineField : Fin 1 → ℝ → ℝ := fun _ _ => 1

/-- **MLS p. 340, corrected printing:** for `g₁ = 1` on `ℝ` the degree of nonholonomy is `1`, which
equals `n = dim ℝ = 1`, and no degree is smaller than `n` ("there exists an integer `κ < n`" fails);
the filtration is regular on `ℝ`. -/
theorem lineField_degree (q : ℝ) :
    IsDegreeOfNonholonomy lineField q 1 ∧ Module.finrank ℝ ℝ = 1 ∧
      IsRegularFiltrationOn lineField Set.univ q ∧
      ¬ ∃ κ, IsDegreeOfNonholonomy lineField q κ ∧ κ < Module.finrank ℝ ℝ := by
  have hpos : ∀ y : ℝ, ∀ i, 1 ≤ i → growth lineField i y = 1 := by
    intro y i hi
    have hle := growth_le_finrank lineField i y
    rw [Module.finrank_self] at hle
    have h1 : 1 ≤ growth lineField 1 y := by
      unfold growth
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hb
      have hmem : lineField 0 y ∈ filtrationAt lineField 1 y := by
        rw [filtrationAt_one]
        exact mem_spanAt (Set.mem_range_self 0) y
      rw [hb, Submodule.mem_bot] at hmem
      simp [lineField] at hmem
    have hm := growth_mono lineField hi y
    omega
  refine ⟨⟨le_rfl, by rw [hpos q 1 le_rfl, hpos q 2 (by norm_num)], fun i hi hi1 => by omega⟩,
    Module.finrank_self ℝ, fun i y _ => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [growth_zero]
    · rw [hpos y i hi, hpos q i hi]
  · rintro ⟨κ, ⟨h1, -, -⟩, hlt⟩
    rw [Module.finrank_self] at hlt
    omega

end Examples
end RoboLean
