import RoboLean.Nonholonomic.TwoInputs
import RoboLean.Nonholonomic.VectorField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The planar space robot: MLS Examples 7.3 and 7.8 (pp. 334–335 and 342)

**What MLS prints.** Example 7.3 (p. 335): the angular momentum constraint (7.12)
`a₁₃(ψ)ψ̇₁ + a₂₃(ψ)ψ̇₂ + a₃₃(ψ)θ̇ = 0`, `q = (ψ₁, ψ₂, θ)`, with `a₁₃ = ml² + mr cos ψ₁`,
`a₂₃ = ml² + mr cos ψ₂`, `a₃₃ = I + 2ml² + 2mr² + 2mrl cos ψ₁ + 2mrl cos ψ₂`, and the fields
`g₁ = (1, 0, −a₁₃/a₃₃)`, `g₂ = (0, 1, −a₂₃/a₃₃)`. Example 7.8 (p. 342): "the Lie bracket is
`g₃ = [g₁, g₂] = (0, 0, 2m²l²r(−l sin ψ₁ − r sin(ψ₁ − ψ₂) + l sin ψ₂)/a₃₃²)`. The vector field `g₃`
is zero when `ψ₁ = ψ₂` and hence the filtration `{Δᵢ}` is not regular."

**Corrected printing.** The printed `a₁₃ = ml² + mr cos ψ₁` and `a₂₃` are not consistent with
`a₃₃` (whose terms are `2mrl cos ψᵢ`, units of `ml²`); with `a₁₃ = ml² + mrl cos ψ₁`,
`a₂₃ = ml² + mrl cos ψ₂` the bracket is exactly the printed `g₃` (`spaceRobot_lieBracket`). (With the
printed entries it differs from the printed `g₃` by `2lm²r²(l − 1) sin(ψ₁ − ψ₂)/a₃₃²`, a computation
not repeated here.) Example 7.8 also writes `θ̇₁, θ̇₂` for `ψ̇₁, ψ̇₂` in (7.12).

**Formalized here.** The corrected fields, `a₃₃ ≥ I > 0`, the bracket, its vanishing on `ψ₁ = ψ₂`,
and that the filtration is regular on no neighbourhood of `q = 0`: there `rank Δ₂ = 2`, while at the
points `(ψ₁, 0, θ)` with `0 < ψ₁ < π`, arbitrarily close to `0`, the third entry of `g₃` is nonzero
and `rank Δ₂ = 3` (for `I, m, l, r > 0`); and "by computing higher order Lie brackets … it is
possible to show that `Δ̄_q = T_qℝ³`" at `q = 0`: `[g₁, g₃](0) = (0, 0, −2m²l²r(l + r)/a₃₃(0)²)`, so
`Δ₃(0) = ℝ³`, and full rank persists in a neighbourhood of `q = 0` (independence is an open
condition). That the system is then controllable is Chow's theorem, not used here.

**Conventions.** `q 0 = ψ₁`, `q 1 = ψ₂`, `q 2 = θ`; parameters `I > 0`, `m ≥ 0`, `l`, `r` real
(positivity of `m`, `l`, `r` where the rank is claimed).
-/

noncomputable section

open Real VectorField
open RoboLean.Nonholonomic

namespace RoboLean
namespace Examples

/-- **MLS Example 7.3, p. 335, corrected printing:** `a₁₃ = ml² + mrl cos ψ₁`. -/
def spaceA13 (m l r : ℝ) (q : Fin 3 → ℝ) : ℝ := m * l ^ 2 + m * r * l * cos (q 0)

/-- **MLS Example 7.3, p. 335, corrected printing:** `a₂₃ = ml² + mrl cos ψ₂`. -/
def spaceA23 (m l r : ℝ) (q : Fin 3 → ℝ) : ℝ := m * l ^ 2 + m * r * l * cos (q 1)

/-- **MLS Example 7.3, p. 335:** `a₃₃ = I + 2ml² + 2mr² + 2mrl cos ψ₁ + 2mrl cos ψ₂`. -/
def spaceA33 (I m l r : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  I + 2 * m * l ^ 2 + 2 * m * r ^ 2 + 2 * m * r * l * cos (q 0) + 2 * m * r * l * cos (q 1)

/-- **MLS Example 7.3, p. 335:** `g₁ = (1, 0, −a₁₃/a₃₃)`. -/
def spaceG1 (I m l r : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![1, 0, -(spaceA13 m l r q / spaceA33 I m l r q)]

/-- **MLS Example 7.3, p. 335:** `g₂ = (0, 1, −a₂₃/a₃₃)`. -/
def spaceG2 (I m l r : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0, 1, -(spaceA23 m l r q / spaceA33 I m l r q)]

/-- **MLS Example 7.8, p. 342:** the printed `g₃ = [g₁, g₂]`. -/
def spaceG3 (I m l r : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0, 0, 2 * m ^ 2 * l ^ 2 * r * (-l * sin (q 0) - r * sin (q 0 - q 1) + l * sin (q 1)) /
    spaceA33 I m l r q ^ 2]

/-- **MLS Example 7.3, p. 335:** `a₃₃ ≥ I`, so `a₃₃ > 0` for `I > 0` and `m ≥ 0`
(`a₃₃ = I + m|l + r e^{iψ₁}|² + m|l + r e^{iψ₂}|²`). -/
theorem spaceA33_ge {I m : ℝ} (hm : 0 ≤ m) (l r : ℝ) (q : Fin 3 → ℝ) : I ≤ spaceA33 I m l r q := by
  have h1 : 0 ≤ m * ((l + r * cos (q 0)) ^ 2 + (r * sin (q 0)) ^ 2) := by positivity
  have h2 : 0 ≤ m * ((l + r * cos (q 1)) ^ 2 + (r * sin (q 1)) ^ 2) := by positivity
  have e0 := sin_sq_add_cos_sq (q 0)
  have e1 := sin_sq_add_cos_sq (q 1)
  have key : spaceA33 I m l r q - I = m * ((l + r * cos (q 0)) ^ 2 + (r * sin (q 0)) ^ 2) +
      m * ((l + r * cos (q 1)) ^ 2 + (r * sin (q 1)) ^ 2) := by
    unfold spaceA33
    linear_combination (-(m * r ^ 2)) * e0 + (-(m * r ^ 2)) * e1
  linarith

private theorem deriv_line {n : ℕ} (G : (Fin n → ℝ) → Fin n → ℝ) (q v w : Fin n → ℝ)
    (h : ∀ i, HasDerivAt (fun t : ℝ => G (q + t • v) i) (w i) 0) :
    deriv (fun t : ℝ => G (q + t • v)) 0 = w := by
  have hd : HasDerivAt (fun t : ℝ => G (q + t • v)) w 0 := by
    rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_pi']
    intro i
    convert (h i).hasFDerivAt using 1
    ext
    simp
  exact hd.deriv

private theorem hasDerivAt_cos_line (a c : ℝ) :
    HasDerivAt (fun t : ℝ => cos (a + t * c)) (-sin a * c) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add a).cos
  simpa using h

/-- **MLS Example 7.3, p. 335:** `g₁` is smooth for `I > 0`, `m ≥ 0`. -/
theorem spaceG1_contDiff {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (l r : ℝ) :
    ContDiff ℝ ⊤ (spaceG1 I m l r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · have hD : ∀ q, spaceA33 I m l r q ≠ 0 := fun q => (hI.trans_le (spaceA33_ge hm l r q)).ne'
    simp only [spaceG1, spaceA13, spaceA33]
    simp only [Fin.reduceFinMk, Matrix.cons_val]
    refine ContDiff.neg (ContDiff.div ?_ ?_ fun q => hD q)
    · exact contDiff_const.add (contDiff_const.mul (contDiff_cos.comp (contDiff_apply ℝ ℝ 0)))
    · exact (((contDiff_const.add (contDiff_const.mul (contDiff_cos.comp
        (contDiff_apply ℝ ℝ 0))))).add (contDiff_const.mul (contDiff_cos.comp
        (contDiff_apply ℝ ℝ 1))))

/-- **MLS Example 7.3, p. 335:** `g₂` is smooth for `I > 0`, `m ≥ 0`. -/
theorem spaceG2_contDiff {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (l r : ℝ) :
    ContDiff ℝ ⊤ (spaceG2 I m l r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · have hD : ∀ q, spaceA33 I m l r q ≠ 0 := fun q => (hI.trans_le (spaceA33_ge hm l r q)).ne'
    simp only [spaceG2, spaceA23, spaceA33]
    simp only [Fin.reduceFinMk, Matrix.cons_val]
    refine ContDiff.neg (ContDiff.div ?_ ?_ fun q => hD q)
    · exact contDiff_const.add (contDiff_const.mul (contDiff_cos.comp (contDiff_apply ℝ ℝ 1)))
    · exact (((contDiff_const.add (contDiff_const.mul (contDiff_cos.comp
        (contDiff_apply ℝ ℝ 0))))).add (contDiff_const.mul (contDiff_cos.comp
        (contDiff_apply ℝ ℝ 1))))

/-- **MLS Example 7.8, p. 342, corrected printing:** `[g₁, g₂] = g₃`, the printed bracket, with the
corrected `a₁₃ = ml² + mrl cos ψ₁`, `a₂₃ = ml² + mrl cos ψ₂` (for `I > 0`, `m ≥ 0`). -/
theorem spaceRobot_lieBracket {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (l r : ℝ) (q : Fin 3 → ℝ) :
    lieBracket ℝ (spaceG1 I m l r) (spaceG2 I m l r) q = spaceG3 I m l r q := by
  have hpos : ∀ q, 0 < spaceA33 I m l r q := fun q => hI.trans_le (spaceA33_ge hm l r q)
  have h1 := ((spaceG1_contDiff hI hm l r).differentiable (by simp)) q
  have h2 := ((spaceG2_contDiff hI hm l r).differentiable (by simp)) q
  set D := spaceA33 I m l r q with hDdef
  have hD0 : D ≠ 0 := (hpos q).ne'
  -- the line along `g₁(q)` in the third entry of `g₂`
  have L2 : HasDerivAt (fun t : ℝ => spaceG2 I m l r (q + t • spaceG1 I m l r q) 2)
      (-(0 * D - spaceA23 m l r q * (2 * m * r * l * (-sin (q 0) * 1) +
        2 * m * r * l * (-sin (q 1) * 0))) / D ^ 2) 0 := by
    have hN : HasDerivAt (fun t : ℝ => m * l ^ 2 + m * r * l * cos (q 1 + t * 0))
        (m * r * l * (-sin (q 1) * 0)) 0 := (hasDerivAt_cos_line (q 1) 0).const_mul _ |>.const_add _
    have hDd : HasDerivAt (fun t : ℝ => I + 2 * m * l ^ 2 + 2 * m * r ^ 2 +
        2 * m * r * l * cos (q 0 + t * 1) + 2 * m * r * l * cos (q 1 + t * 0))
        (2 * m * r * l * (-sin (q 0) * 1) + 2 * m * r * l * (-sin (q 1) * 0)) 0 :=
      (((hasDerivAt_cos_line (q 0) 1).const_mul _).const_add _).add
        ((hasDerivAt_cos_line (q 1) 0).const_mul _)
    have hD0' : I + 2 * m * l ^ 2 + 2 * m * r ^ 2 + 2 * m * r * l * cos (q 0 + 0 * 1) +
        2 * m * r * l * cos (q 1 + 0 * 0) ≠ 0 := by simpa [hDdef, spaceA33] using hD0
    have h := (hN.div hDd hD0').neg
    convert h using 1
    · funext t
      simp [spaceG2, spaceG1, spaceA23, spaceA33]
    · simp [hDdef, spaceA23, spaceA33]
      ring
  -- the line along `g₂(q)` in the third entry of `g₁`
  have L1 : HasDerivAt (fun t : ℝ => spaceG1 I m l r (q + t • spaceG2 I m l r q) 2)
      (-(0 * D - spaceA13 m l r q * (2 * m * r * l * (-sin (q 0) * 0) +
        2 * m * r * l * (-sin (q 1) * 1))) / D ^ 2) 0 := by
    have hN : HasDerivAt (fun t : ℝ => m * l ^ 2 + m * r * l * cos (q 0 + t * 0))
        (m * r * l * (-sin (q 0) * 0)) 0 := (hasDerivAt_cos_line (q 0) 0).const_mul _ |>.const_add _
    have hDd : HasDerivAt (fun t : ℝ => I + 2 * m * l ^ 2 + 2 * m * r ^ 2 +
        2 * m * r * l * cos (q 0 + t * 0) + 2 * m * r * l * cos (q 1 + t * 1))
        (2 * m * r * l * (-sin (q 0) * 0) + 2 * m * r * l * (-sin (q 1) * 1)) 0 :=
      (((hasDerivAt_cos_line (q 0) 0).const_mul _).const_add _).add
        ((hasDerivAt_cos_line (q 1) 1).const_mul _)
    have hD0' : I + 2 * m * l ^ 2 + 2 * m * r ^ 2 + 2 * m * r * l * cos (q 0 + 0 * 0) +
        2 * m * r * l * cos (q 1 + 0 * 1) ≠ 0 := by simpa [hDdef, spaceA33] using hD0
    have h := (hN.div hDd hD0').neg
    convert h using 1
    · funext t
      simp [spaceG2, spaceG1, spaceA13, spaceA33]
    · simp [hDdef, spaceA13, spaceA33]
      ring
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h2,
    deriv_line (spaceG2 I m l r) q (spaceG1 I m l r q) ![0, 0, -(0 * D - spaceA23 m l r q *
      (2 * m * r * l * (-sin (q 0) * 1) + 2 * m * r * l * (-sin (q 1) * 0))) / D ^ 2] ?_,
    deriv_line (spaceG1 I m l r) q (spaceG2 I m l r q) ![0, 0, -(0 * D - spaceA13 m l r q *
      (2 * m * r * l * (-sin (q 0) * 0) + 2 * m * r * l * (-sin (q 1) * 1))) / D ^ 2] ?_]
  · ext i
    fin_cases i
    · simp [spaceG3]
    · simp [spaceG3]
    · simp only [spaceG3, spaceA13, spaceA23, Fin.reduceFinMk, Matrix.cons_val,
        Pi.sub_apply]
      rw [← hDdef, sin_sub]
      field_simp
      ring
  · intro i
    fin_cases i
    · simpa [spaceG1] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa [spaceG1] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact L1
  · intro i
    fin_cases i
    · simpa [spaceG2] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [spaceG2] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · exact L2

/-- **MLS Example 7.8, p. 342: "the vector field `g₃` is zero when `ψ₁ = ψ₂`".** -/
theorem spaceG3_eq_zero_of_eq (I m l r : ℝ) {q : Fin 3 → ℝ} (h : q 0 = q 1) :
    spaceG3 I m l r q = 0 := by
  ext i
  fin_cases i <;> simp [spaceG3, h]

/-- **MLS Examples 7.3 and 7.8, pp. 335 and 342: the input fields `(g₁, g₂)` of the planar space
robot.** -/
def spaceFields (I m l r : ℝ) : Fin 2 → (Fin 3 → ℝ) → Fin 3 → ℝ :=
  ![spaceG1 I m l r, spaceG2 I m l r]

private theorem linearIndependent_triangular (x y z : ℝ) (hz : z ≠ 0) :
    LinearIndependent ℝ ![(![1, 0, x] : Fin 3 → ℝ), ![0, 1, y], ![0, 0, z]] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_three] at h0 h1 h2
  have hc2 : c 2 = 0 := by
    rw [h0, h1] at h2
    simpa [hz] using h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact hc2

/-- **MLS Example 7.8, p. 342: "hence the filtration `{Δᵢ}` is not regular":** for `I, m, l, r > 0`,
`rank Δ₂ = 2` at `q = 0` (where `g₃ = 0`) and `rank Δ₂ = 3` at the points `(ψ₁, 0, θ)` with
`0 < ψ₁ < π`, so the filtration is regular on no neighbourhood of `q = 0`. -/
theorem spaceRobot_not_isRegularFiltrationOn {I m l r : ℝ} (hI : 0 < I) (hm : 0 < m)
    (hl : 0 < l) (hr : 0 < r) {U : Set (Fin 3 → ℝ)} (hU : U ∈ nhds (0 : Fin 3 → ℝ)) :
    growth (spaceFields I m l r) 2 0 = 2 ∧
      ¬ IsRegularFiltrationOn (spaceFields I m l r) U 0 := by
  have hbr : ∀ q, lieBracket ℝ (spaceFields I m l r 0) (spaceFields I m l r 1) q =
      spaceG3 I m l r q := fun q => spaceRobot_lieBracket hI hm.le l r q
  have hg1 : ∀ q, spaceFields I m l r 0 q = ![1, 0, -(spaceA13 m l r q / spaceA33 I m l r q)] :=
    fun q => rfl
  have hg2 : ∀ q, spaceFields I m l r 1 q = ![0, 1, -(spaceA23 m l r q / spaceA33 I m l r q)] :=
    fun q => rfl
  -- rank 2 at the origin
  have h0 : growth (spaceFields I m l r) 2 0 = 2 := by
    rw [growth, filtrationAt_two, hbr, spaceG3_eq_zero_of_eq I m l r (by simp)]
    have hs : ({spaceFields I m l r 0 0, spaceFields I m l r 1 0, 0} : Set (Fin 3 → ℝ)) =
        insert 0 (Set.range ![spaceFields I m l r 0 0, spaceFields I m l r 1 0]) := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]
      ext v
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    rw [hs, Submodule.span_insert_zero]
    have hli : LinearIndependent ℝ ![spaceFields I m l r 0 0, spaceFields I m l r 1 0] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have e0 := congrFun hst 0
      have e1 := congrFun hst 1
      simp [hg1, hg2] at e0 e1
      exact ⟨e0, e1⟩
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine ⟨h0, fun hreg => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  set ε : ℝ := min (δ / 2) 1 with hε
  have hεpos : 0 < ε := lt_min (by linarith) one_pos
  have hεπ : ε < π := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.two_le_pi])
  set q : Fin 3 → ℝ := Pi.single 0 ε with hq
  have hqU : q ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    rw [pi_norm_lt_iff hδ]
    intro i
    have hle : ‖q i‖ ≤ ε := by
      rw [hq, Pi.single_apply]
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_pos hεpos]
      · simp [hεpos.le]
    exact lt_of_le_of_lt hle (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hq0 : q 0 = ε := by simp [hq]
  have hq1 : q 1 = 0 := by simp [hq]
  have hA : 0 < spaceA33 I m l r q := hI.trans_le (spaceA33_ge hm.le l r q)
  have hz : 2 * m ^ 2 * l ^ 2 * r * (-l * sin (q 0) - r * sin (q 0 - q 1) + l * sin (q 1)) /
      spaceA33 I m l r q ^ 2 ≠ 0 := by
    rw [hq0, hq1]
    simp only [sub_zero, sin_zero, mul_zero, add_zero]
    have hs : 0 < sin ε := sin_pos_of_pos_of_lt_pi hεpos hεπ
    apply div_ne_zero _ (pow_ne_zero 2 hA.ne')
    have : -l * sin ε - r * sin ε = -((l + r) * sin ε) := by ring
    rw [this]
    have h5 : 0 < (l + r) * sin ε := mul_pos (by linarith) hs
    have h4 : 0 < 2 * m ^ 2 * l ^ 2 * r := by positivity
    exact mul_ne_zero h4.ne' (neg_ne_zero.2 h5.ne')
  have h3 : growth (spaceFields I m l r) 2 q = 3 := by
    apply growth_two_eq_three
    rw [hbr, hg1, hg2]
    exact linearIndependent_triangular _ _ _ hz
  have := hreg 2 q hqU
  omega

/-- **MLS Example 7.8, p. 342:** `g₃` is smooth for `I > 0`, `m ≥ 0`. -/
theorem spaceG3_contDiff {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (l r : ℝ) :
    ContDiff ℝ ⊤ (spaceG3 I m l r) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · have hD : ∀ q, spaceA33 I m l r q ^ 2 ≠ 0 := fun q =>
      pow_ne_zero 2 (hI.trans_le (spaceA33_ge hm l r q)).ne'
    simp only [spaceG3, spaceA33]
    simp only [Fin.reduceFinMk, Matrix.cons_val]
    refine ContDiff.div ?_ ?_ fun q => hD q
    · refine contDiff_const.mul (((contDiff_const.mul (contDiff_sin.comp (contDiff_apply ℝ ℝ 0))).sub
        (contDiff_const.mul (contDiff_sin.comp ((contDiff_apply ℝ ℝ 0).sub
          (contDiff_apply ℝ ℝ 1))))).add (contDiff_const.mul (contDiff_sin.comp
          (contDiff_apply ℝ ℝ 1))))
    · exact ((((contDiff_const.add (contDiff_const.mul (contDiff_cos.comp
        (contDiff_apply ℝ ℝ 0))))).add (contDiff_const.mul (contDiff_cos.comp
        (contDiff_apply ℝ ℝ 1))))).pow 2

/-- **MLS Example 7.8, p. 342:** at `q = 0`, `[g₁, g₃](0) = (0, 0, −2m²l²r(l + r)/a₃₃(0)²)`. -/
theorem spaceRobot_lieBracket_g1_g3_zero {I m : ℝ} (hI : 0 < I) (hm : 0 ≤ m) (l r : ℝ) :
    lieBracket ℝ (spaceG1 I m l r) (spaceG3 I m l r) 0 =
      ![0, 0, -(2 * m ^ 2 * l ^ 2 * r * (l + r)) / spaceA33 I m l r 0 ^ 2] := by
  have h1 := ((spaceG1_contDiff hI hm l r).differentiable (by simp)) 0
  have h3 := ((spaceG3_contDiff hI hm l r).differentiable (by simp)) 0
  set D := spaceA33 I m l r 0 with hDdef
  have hD0 : D ≠ 0 := (hI.trans_le (spaceA33_ge hm l r 0)).ne'
  have hg3 : spaceG3 I m l r 0 = 0 := spaceG3_eq_zero_of_eq I m l r rfl
  -- the line along `g₁(0)` in the third entry of `g₃`
  have L3 : HasDerivAt (fun t : ℝ => spaceG3 I m l r (0 + t • spaceG1 I m l r 0) 2)
      (-(2 * m ^ 2 * l ^ 2 * r * (l + r)) / D ^ 2) 0 := by
    have hN : HasDerivAt (fun t : ℝ => 2 * m ^ 2 * l ^ 2 * r *
        (-l * sin (t * 1) - r * sin (t * 1 - t * 0) + l * sin (t * 0)))
        (2 * m ^ 2 * l ^ 2 * r * (-l * (cos 0 * 1) - r * (cos 0 * (1 - 0)) + l * (cos 0 * 0))) 0 := by
      have a1 := ((hasDerivAt_id (0 : ℝ)).mul_const 1).sin
      have a2 := (((hasDerivAt_id (0 : ℝ)).mul_const 1).sub ((hasDerivAt_id (0 : ℝ)).mul_const 0)).sin
      have a3 := ((hasDerivAt_id (0 : ℝ)).mul_const 0).sin
      have := (((a1.const_mul (-l)).sub (a2.const_mul r)).add (a3.const_mul l)).const_mul
        (2 * m ^ 2 * l ^ 2 * r)
      convert this using 1
      · simp
      · simp
    have hDd : HasDerivAt (fun t : ℝ => (I + 2 * m * l ^ 2 + 2 * m * r ^ 2 +
        2 * m * r * l * cos (t * 1) + 2 * m * r * l * cos (t * 0)) ^ 2)
        (2 * (I + 2 * m * l ^ 2 + 2 * m * r ^ 2 + 2 * m * r * l * cos (0 * 1) +
          2 * m * r * l * cos (0 * 0)) * (2 * m * r * l * (-sin 0 * 1) +
            2 * m * r * l * (-sin 0 * 0))) 0 := by
      have b1 := hasDerivAt_cos_line 0 1
      have b2 := hasDerivAt_cos_line 0 0
      simp only [zero_add] at b1 b2
      have := ((((b1.const_mul (2 * m * r * l)).const_add (I + 2 * m * l ^ 2 + 2 * m * r ^ 2)).add
        (b2.const_mul (2 * m * r * l)))).pow 2
      convert this using 1
      · simp
    have hD0' : (I + 2 * m * l ^ 2 + 2 * m * r ^ 2 + 2 * m * r * l * cos (0 * 1) +
        2 * m * r * l * cos (0 * 0)) ^ 2 ≠ 0 := by
      simpa [hDdef, spaceA33] using pow_ne_zero 2 hD0
    have h := hN.div hDd hD0'
    convert h using 1
    · funext t
      simp [spaceG3, spaceG1, spaceA33]
    · simp [hDdef, spaceA33]
      field_simp
      ring
  rw [RoboLean.Nonholonomic.lieBracket_eq_deriv h1 h3,
    deriv_line (spaceG3 I m l r) 0 (spaceG1 I m l r 0) ![0, 0, -(2 * m ^ 2 * l ^ 2 * r * (l + r)) / D ^ 2] ?_,
    hg3]
  · simp
  · intro i
    fin_cases i
    · simpa [spaceG3] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [spaceG3] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact L3

/-- **MLS Example 7.8, p. 342: "by computing higher order Lie brackets, however, it is possible to
show that `Δ̄_q = T_qℝ³`" at `q = 0`:** for `I, m, l, r > 0`, `g₁(0)`, `g₂(0)` and
`[g₁, [g₁, g₂]](0)` are independent, so `Δ₃(0) = ℝ³` and the controllability Lie algebra has full
rank at `0`. -/
theorem spaceRobot_lieAlgebraAt_zero {I m l r : ℝ} (hI : 0 < I) (hm : 0 < m) (hl : 0 < l)
    (hr : 0 < r) : filtrationAt (spaceFields I m l r) 3 0 = ⊤ ∧
      lieAlgebraAt (spaceFields I m l r) 0 = ⊤ := by
  have hbr : lieBracket ℝ (spaceFields I m l r 0) (spaceFields I m l r 1) = spaceG3 I m l r :=
    funext fun q => spaceRobot_lieBracket hI hm.le l r q
  have hz : -(2 * m ^ 2 * l ^ 2 * r * (l + r)) / spaceA33 I m l r 0 ^ 2 ≠ 0 := by
    have hA : 0 < spaceA33 I m l r 0 := hI.trans_le (spaceA33_ge hm.le l r 0)
    have : 0 < 2 * m ^ 2 * l ^ 2 * r * (l + r) := by positivity
    exact div_ne_zero (neg_ne_zero.2 this.ne') (pow_ne_zero 2 hA.ne')
  have hli : LinearIndependent ℝ ![spaceFields I m l r 0 0, spaceFields I m l r 1 0,
      lieBracket ℝ (spaceFields I m l r 0) (lieBracket ℝ (spaceFields I m l r 0)
        (spaceFields I m l r 1)) 0] := by
    rw [hbr]
    have e : lieBracket ℝ (spaceFields I m l r 0) (spaceG3 I m l r) 0 =
        ![0, 0, -(2 * m ^ 2 * l ^ 2 * r * (l + r)) / spaceA33 I m l r 0 ^ 2] :=
      spaceRobot_lieBracket_g1_g3_zero hI hm.le l r
    rw [e]
    exact linearIndependent_triangular _ _ _ hz
  have htop : filtrationAt (spaceFields I m l r) 3 0 = ⊤ := by
    refine filtrationAt_eq_top_of_linearIndependent (spaceFields I m l r) (by simp) hli ?_
    intro k
    fin_cases k
    · exact generator_mem_filtrationAt _ 0 (by norm_num) 0
    · exact generator_mem_filtrationAt _ 1 (by norm_num) 0
    · exact lieBracket_lieBracket_mem_filtrationAt_three _ 0 le_rfl 0
  exact ⟨htop, lieAlgebraAt_eq_top_of_filtrationAt _ htop⟩

/-- **MLS Example 7.8, p. 342: "`Δ̄_q = T_qℝ³` in a neighborhood of `q = 0`":** for `I, m, l, r > 0`,
`g₁(q)`, `g₂(q)` and `[g₁, [g₁, g₂]](q)` stay independent near `0` (independence is an open
condition and the fields are continuous), so the controllability Lie algebra has full rank at every
point of a neighbourhood of `0`. -/
theorem spaceRobot_lieAlgebraAt_eventually {I m l r : ℝ} (hI : 0 < I) (hm : 0 < m) (hl : 0 < l)
    (hr : 0 < r) : ∀ᶠ q in nhds (0 : Fin 3 → ℝ), lieAlgebraAt (spaceFields I m l r) q = ⊤ := by
  set F : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ := fun q => ![spaceFields I m l r 0 q,
    spaceFields I m l r 1 q, lieBracket ℝ (spaceFields I m l r 0)
      (lieBracket ℝ (spaceFields I m l r 0) (spaceFields I m l r 1)) q] with hF
  have hbr : lieBracket ℝ (spaceFields I m l r 0) (spaceFields I m l r 1) = spaceG3 I m l r :=
    funext fun q => spaceRobot_lieBracket hI hm.le l r q
  have hc1 : Continuous (spaceFields I m l r 0) := (spaceG1_contDiff hI hm.le l r).continuous
  have hc2 : Continuous (spaceFields I m l r 1) := (spaceG2_contDiff hI hm.le l r).continuous
  have hc3 : Continuous (lieBracket ℝ (spaceFields I m l r 0)
      (lieBracket ℝ (spaceFields I m l r 0) (spaceFields I m l r 1))) := by
    rw [hbr]
    exact (ContDiff.lieBracket_vectorField (m := 0) (spaceG1_contDiff hI hm.le l r)
      (spaceG3_contDiff hI hm.le l r) (by simp)).continuous
  have hcont : ContinuousAt F 0 := by
    refine continuousAt_pi.2 fun i => ?_
    fin_cases i
    · exact hc1.continuousAt
    · exact hc2.continuousAt
    · exact hc3.continuousAt
  have hli0 : LinearIndependent ℝ (F 0) := by
    have hli : LinearIndependent ℝ ![spaceFields I m l r 0 0, spaceFields I m l r 1 0,
        lieBracket ℝ (spaceFields I m l r 0) (lieBracket ℝ (spaceFields I m l r 0)
          (spaceFields I m l r 1)) 0] := by
      have e : lieBracket ℝ (spaceFields I m l r 0) (spaceG3 I m l r) 0 =
          ![0, 0, -(2 * m ^ 2 * l ^ 2 * r * (l + r)) / spaceA33 I m l r 0 ^ 2] :=
        spaceRobot_lieBracket_g1_g3_zero hI hm.le l r
      rw [hbr, e]
      have hA : 0 < spaceA33 I m l r 0 := hI.trans_le (spaceA33_ge hm.le l r 0)
      have : 0 < 2 * m ^ 2 * l ^ 2 * r * (l + r) := by positivity
      exact linearIndependent_triangular _ _ _
        (div_ne_zero (neg_ne_zero.2 this.ne') (pow_ne_zero 2 hA.ne'))
    exact hli
  filter_upwards [hcont.eventually hli0.eventually] with q hq
  have htop : filtrationAt (spaceFields I m l r) 3 q = ⊤ := by
    refine filtrationAt_eq_top_of_linearIndependent (spaceFields I m l r) (by simp) hq ?_
    intro k
    fin_cases k
    · exact generator_mem_filtrationAt _ 0 (by norm_num) q
    · exact generator_mem_filtrationAt _ 1 (by norm_num) q
    · exact lieBracket_lieBracket_mem_filtrationAt_three _ 0 le_rfl q
  exact lieAlgebraAt_eq_top_of_filtrationAt _ htop

end Examples
end RoboLean
