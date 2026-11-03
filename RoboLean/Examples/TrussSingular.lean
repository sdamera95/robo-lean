import RoboLean.Examples.ParallelExerciseTruss
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The variable geometry truss with a leg of zero length is kinematically singular

MLS Chapter 3, Exercise 21(e), printed p. 153, with the kinematic singularity of p. 134 (a
configuration of `Q′` where the rank `ρ` of eq. (3.70) is smaller than at configurations of `Q′`
arbitrarily close to it, `ParallelMechanism.IsKinematicallySingular`). The truss, its legs and
coordinates are those of `RoboLean.Examples.ParallelExerciseTruss`: leg `i` has coordinates
`(αᵢ, dᵢ, βᵢ)`, `dᵢ` the signed leg length.

Contents:

* at a configuration with a leg of zero length the rank is at most two: that leg's first and third
  twists coincide (the revolute axes at both ends of the leg meet);
* the planar twists have dimension at least three, so a configuration whose three legs have nonzero
  length has rank at least three;
* `trussShift Θ i ε`, the configuration obtained from `Θ` by translating the platform by `ε` along
  the direction `(cos αᵢ, sin αᵢ)` of leg `i`, with leg `i` lengthened to `ε` and every other leg
  re-solved in polar coordinates near its length; it lies in `Q′` and tends to `Θ` as `ε → 0`;
* hence a configuration of `Q′` with exactly one leg of zero length is kinematically singular.

The case of two legs of zero length at once (possible only with the platform pivots on the base
pivots of legs `d₁` and `d₂`) is not treated. Statements about the coordinate model, not about a
physical truss.
-/

noncomputable section

open Real

namespace RoboLean

namespace Examples

/-! ### Private helpers -/

private theorem ts_cos {d : ℝ} (hd : d ≠ 0) (α αi ε : ℝ) {z : ℂ}
    (hre : z.re = 1 + ε / d * cos (αi - α)) (him : z.im = ε / d * sin (αi - α)) :
    d * ‖z‖ * cos (α + Complex.arg z) = d * cos α + ε * cos αi := by
  have hA := Complex.norm_mul_cos_arg z
  have hB := Complex.norm_mul_sin_arg z
  rw [hre] at hA
  rw [him] at hB
  have hdt : d * (ε / d) = ε := mul_div_cancel₀ ε hd
  have hψ : cos αi = cos (αi - α) * cos α - sin (αi - α) * sin α := by
    rw [← cos_add, sub_add_cancel]
  rw [cos_add]
  linear_combination (d * cos α) * hA - (d * sin α) * hB +
    (cos α * cos (αi - α) - sin α * sin (αi - α)) * hdt - ε * hψ

private theorem ts_sin {d : ℝ} (hd : d ≠ 0) (α αi ε : ℝ) {z : ℂ}
    (hre : z.re = 1 + ε / d * cos (αi - α)) (him : z.im = ε / d * sin (αi - α)) :
    d * ‖z‖ * sin (α + Complex.arg z) = d * sin α + ε * sin αi := by
  have hA := Complex.norm_mul_cos_arg z
  have hB := Complex.norm_mul_sin_arg z
  rw [hre] at hA
  rw [him] at hB
  have hdt : d * (ε / d) = ε := mul_div_cancel₀ ε hd
  have hψ : sin αi = sin (αi - α) * cos α + cos (αi - α) * sin α := by
    rw [← sin_add, sub_add_cancel]
  rw [sin_add]
  linear_combination (d * sin α) * hA + (d * cos α) * hB +
    (sin α * cos (αi - α) + cos α * sin (αi - α)) * hdt - ε * hψ

private theorem ts_chain (h : ℝ) (k : Fin 3) :
    ∃ a b : ℝ, (variableGeometryTruss h).chain k = trussLeg a b := by
  fin_cases k <;> exact ⟨_, _, rfl⟩

private theorem ts_re (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp

private theorem ts_im (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp

/-- **MLS Exercise 21(e), p. 153: a leg of zero length caps the rank at two** (eq. (3.70),
p. 134). If leg `i` of the truss has length `0`, its first and third instantaneous twists coincide,
so the admissible tool velocities lie in a span of two twists and `ρ ≤ 2`. -/
theorem variableGeometryTruss_structureRank_le_two (h : ℝ) (Θ : Fin 3 → Fin 3 → ℝ) {i : Fin 3}
    (hi : Θ i 1 = 0) : (variableGeometryTruss h).structureRank Θ ≤ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ((variableGeometryTruss h).chain i).spatialJacobian (Θ i) =
      ![⟨vec a 0 0, vec 0 0 1⟩, ⟨vec (cos (Θ i 0)) (sin (Θ i 0)) 0, vec 0 0 0⟩,
        ⟨vec (a + Θ i 1 * sin (Θ i 0)) (-(Θ i 1 * cos (Θ i 0))) 0, vec 0 0 1⟩] := by
    fin_cases i <;> exact ⟨_, trussLeg_spatialJacobian _ _ _⟩
  set v : Fin 2 → Twist := ![⟨vec a 0 0, vec 0 0 1⟩,
    ⟨vec (cos (Θ i 0)) (sin (Θ i 0)) 0, vec 0 0 0⟩] with hv
  have hle : (variableGeometryTruss h).admissibleVelocities Θ ≤
      Submodule.span ℝ (Set.range v) := by
    refine (iInf_le _ i).trans ?_
    rw [Submodule.span_le, ha]
    rintro _ ⟨l, rfl⟩
    apply Submodule.subset_span
    fin_cases l
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, by simp [hv, hi]⟩
  calc (variableGeometryTruss h).structureRank Θ
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin 2) := finrank_range_le_card v
    _ = 2 := Fintype.card_fin 2

/-- The planar twists `(v_x, v_y, 0, 0, 0, ω)` of MLS p. 136 form a space of dimension at least
three: `(e_x, 0)`, `(e_y, 0)` and `(0, e_z)` are linearly independent planar twists. -/
theorem three_le_finrank_planarTwistSubmodule :
    3 ≤ Module.finrank ℝ planarTwistSubmodule := by
  let e : Fin 3 → planarTwistSubmodule :=
    ![⟨⟨vec 1 0 0, vec 0 0 0⟩, ⟨by simp [vec], by simp [vec], by simp [vec]⟩⟩,
      ⟨⟨vec 0 1 0, vec 0 0 0⟩, ⟨by simp [vec], by simp [vec], by simp [vec]⟩⟩,
      ⟨⟨vec 0 0 0, vec 0 0 1⟩, ⟨by simp [vec], by simp [vec], by simp [vec]⟩⟩]
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h' := congrArg (fun V : planarTwistSubmodule => (V : Twist)) hg
    simp only [Fin.sum_univ_three, Submodule.coe_zero] at h'
    have h0 := congrArg (fun V : Twist => V.linear 0) h'
    have h1 := congrArg (fun V : Twist => V.linear 1) h'
    have h2 := congrArg (fun V : Twist => V.angular 2) h'
    simp [e, vec] at h0 h1 h2
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  simpa using hli.fintype_card_le_finrank

/-- **MLS Exercise 21(e), p. 153: three nonzero legs give rank at least three** (eq. (3.70),
p. 134): with every leg of nonzero length the admissible tool velocities are all the planar
twists. -/
theorem variableGeometryTruss_three_le_structureRank {h : ℝ} (Θ : Fin 3 → Fin 3 → ℝ)
    (hd : ∀ i, Θ i 1 ≠ 0) : 3 ≤ (variableGeometryTruss h).structureRank Θ := by
  rw [ParallelMechanism.structureRank, variableGeometryTruss_admissibleVelocities_eq Θ hd]
  exact three_le_finrank_planarTwistSubmodule

/-- The configuration of the truss of MLS Exercise 21, p. 152, obtained from `Θ` by translating
the platform by `ε` along the direction `(cos αᵢ, sin αᵢ)` of leg `i`, intended for `dᵢ = 0`:
every leg `k` gets angle `αₖ + arg zₖ`, length `dₖ ‖zₖ‖` (plus `ε` for `k = i`) and platform angle
`βₖ - arg zₖ`, with `zₖ = 1 + (ε / dₖ) e^{i(αᵢ - αₖ)}`, so that `dₖ ‖zₖ‖ e^{i(αₖ + arg zₖ)} =
dₖ e^{iαₖ} + ε e^{iαᵢ}` when `dₖ ≠ 0`. For `dᵢ = 0` Lean's division by zero gives `zᵢ = 1`, so leg
`i` keeps its angles and gets length `ε`; the statements about this configuration assume `dᵢ = 0`
and `dₖ ≠ 0` for `k ≠ i`. -/
def trussShift (Θ : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (ε : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun k =>
    let z : ℂ := ((1 + ε / Θ k 1 * cos (Θ i 0 - Θ k 0) : ℝ) : ℂ) +
      ((ε / Θ k 1 * sin (Θ i 0 - Θ k 0) : ℝ) : ℂ) * Complex.I
    ![Θ k 0 + Complex.arg z, Θ k 1 * ‖z‖ + if k = i then ε else 0, Θ k 2 - Complex.arg z]

/-- MLS Exercise 21, p. 152: the shifted configuration at `ε = 0` is `Θ` itself. -/
theorem trussShift_zero (Θ : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    trussShift Θ i 0 = Θ := by
  funext k l
  fin_cases l <;> simp [trussShift]

/-- MLS Exercise 21, p. 152: the shifted configuration depends continuously on `ε` at `ε = 0`
(the angles `arg zₖ` are continuous at `zₖ = 1`). -/
theorem continuousAt_trussShift (Θ : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    ContinuousAt (trussShift Θ i) 0 := by
  rw [continuousAt_pi]
  intro k
  rw [continuousAt_pi]
  intro l
  set z : ℝ → ℂ := fun ε => ((1 + ε / Θ k 1 * cos (Θ i 0 - Θ k 0) : ℝ) : ℂ) +
      ((ε / Θ k 1 * sin (Θ i 0 - Θ k 0) : ℝ) : ℂ) * Complex.I with hz
  have hzc : Continuous z := by
    rw [hz]
    fun_prop
  have hz0 : z 0 = 1 := by simp [hz]
  have harg : ContinuousAt (fun ε => Complex.arg (z ε)) 0 := by
    refine ContinuousAt.comp (g := Complex.arg) ?_ hzc.continuousAt
    rw [hz0]
    exact Complex.continuousAt_arg Complex.one_mem_slitPlane
  fin_cases l
  · exact continuousAt_const.add harg
  · have hite : Continuous fun ε : ℝ => if k = i then ε else 0 := by
      split_ifs
      · exact continuous_id
      · exact continuous_const
    exact ((continuous_const.mul hzc.norm).add hite).continuousAt
  · exact continuousAt_const.sub harg

/-- **MLS Exercise 21(b), p. 152, for the shifted configuration: it closes the loop.** If `Θ`
lies in `Q′` with leg `i` of length `0` and every other leg of nonzero length, then for every `ε`
the configuration `trussShift Θ i ε` lies in `Q′`: its three legs reach the platform pose of `Θ`
translated by `ε (cos αᵢ, sin αᵢ)`. -/
theorem trussShift_mem_admissible {h : ℝ} {Θ : Fin 3 → Fin 3 → ℝ}
    (hΘ : Θ ∈ (variableGeometryTruss h).admissible) {i : Fin 3} (hi : Θ i 1 = 0)
    (hk : ∀ k, k ≠ i → Θ k 1 ≠ 0) (ε : ℝ) :
    trussShift Θ i ε ∈ (variableGeometryTruss h).admissible := by
  obtain ⟨x, y, φ, H⟩ := (variableGeometryTruss_mem_admissible_iff h Θ).1 hΘ
  rw [variableGeometryTruss_mem_admissible_iff]
  refine ⟨x + ε * cos (Θ i 0), y + ε * sin (Θ i 0), φ, fun k => ?_⟩
  obtain ⟨a, b, hab⟩ := ts_chain h k
  have Hk := H k
  rw [hab, trussLeg_fk_eq_iff] at Hk
  obtain ⟨⟨m, hm⟩, hx, hy⟩ := Hk
  rw [hab, trussLeg_fk_eq_iff]
  have hc : (trussShift Θ i ε k 1) * cos (trussShift Θ i ε k 0) =
      Θ k 1 * cos (Θ k 0) + ε * cos (Θ i 0) ∧
      (trussShift Θ i ε k 1) * sin (trussShift Θ i ε k 0) =
      Θ k 1 * sin (Θ k 0) + ε * sin (Θ i 0) := by
    by_cases hki : k = i
    · subst hki
      simp [trussShift, hi]
    · simp only [trussShift, Matrix.cons_val_zero, Matrix.cons_val_one, hki, ↓reduceIte,
        add_zero]
      exact ⟨ts_cos (hk k hki) _ _ _ (ts_re _ _) (ts_im _ _),
        ts_sin (hk k hki) _ _ _ (ts_re _ _) (ts_im _ _)⟩
  refine ⟨⟨m, ?_⟩, ?_, ?_⟩
  · simp only [trussShift, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    linarith
  · linarith [hc.1]
  · linarith [hc.2]

/-- **MLS Exercise 21(e), p. 153, with p. 134: a leg of zero length is a kinematic singularity.**
If a configuration of `Q′` has leg `i` of length `0` and the other two legs of nonzero length, it
is kinematically singular in the convention of `ParallelMechanism.IsKinematicallySingular`: every
neighbourhood contains configurations of `Q′` (`trussShift Θ i ε`, `ε ≠ 0` small) whose three legs
have nonzero length, where `ρ ≥ 3 > 2 ≥ ρ(Θ)`. -/
theorem variableGeometryTruss_isKinematicallySingular_of_leg_eq_zero {h : ℝ}
    {Θ : Fin 3 → Fin 3 → ℝ} (hΘ : Θ ∈ (variableGeometryTruss h).admissible) {i : Fin 3}
    (hi : Θ i 1 = 0) (hk : ∀ k, k ≠ i → Θ k 1 ≠ 0) :
    (variableGeometryTruss h).IsKinematicallySingular Θ := by
  intro U hU
  have hc := continuousAt_trussShift Θ i
  rw [ContinuousAt, trussShift_zero Θ i] at hc
  have h1 : ∀ᶠ ε in nhds (0 : ℝ), trussShift Θ i ε ∈ U := hc hU
  have h2 : ∀ᶠ ε in nhds (0 : ℝ), ∀ k, k ≠ i → |ε| < |Θ k 1| := by
    rw [Filter.eventually_all]
    intro k
    by_cases hki : k = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hki h
    · have hpos : 0 < |Θ k 1| := abs_pos.mpr (hk k hki)
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with ε hε
      intro _
      rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
  obtain ⟨ε, ⟨hεU, hεk⟩, hε0⟩ :=
    (((h1.and h2).filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))).and
      (self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ nhdsWithin (0 : ℝ) {0}ᶜ)).exists
  refine ⟨trussShift Θ i ε, hεU, trussShift_mem_admissible hΘ hi hk ε, ?_⟩
  have hle := variableGeometryTruss_structureRank_le_two h Θ hi
  have hge : 3 ≤ (variableGeometryTruss h).structureRank (trussShift Θ i ε) := by
    refine variableGeometryTruss_three_le_structureRank _ fun k => ?_
    by_cases hki : k = i
    · subst hki
      simpa [trussShift, hi] using (Set.mem_compl_singleton_iff.mp hε0)
    · simp only [trussShift, Matrix.cons_val_one, hki, ↓reduceIte, add_zero]
      refine mul_ne_zero (hk k hki) (norm_ne_zero_iff.mpr fun h0 => ?_)
      have hre := congrArg Complex.re h0
      rw [ts_re, Complex.zero_re] at hre
      have hlt : |ε / Θ k 1 * cos (Θ i 0 - Θ k 0)| < 1 := by
        rw [abs_mul, abs_div]
        calc |ε| / |Θ k 1| * |cos (Θ i 0 - Θ k 0)| ≤ |ε| / |Θ k 1| * 1 :=
              mul_le_mul_of_nonneg_left (abs_cos_le_one _) (by positivity)
          _ < 1 := by
              rw [mul_one, div_lt_one (abs_pos.mpr (hk k hki))]
              exact hεk k hki
      have := (abs_lt.mp hlt).1
      linarith
  omega

end Examples

end RoboLean
