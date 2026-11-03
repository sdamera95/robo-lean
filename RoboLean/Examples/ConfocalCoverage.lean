import RoboLean.Examples.EllipsoidConfocal

/-!
# The confocal patch covers the ellipsoid minus two arcs (MLS Exercise 14, p. 262)

MLS p. 243: "In general, it may take several coordinate charts to completely describe the surface of
the object." For the confocal chart of the three-axis ellipsoid `x²/a² + y²/b² + z²/c² = 1`,
`a > b > c > 0` (the library's example for Exercises 14, 15 and 19, p. 262), on its patch
`{cos t > 0}`:

* **Coverage** (`confocalChart_image_confocalDomain`): the image of the patch is the ellipsoid
  without the set `confocalArcs` of its points with `y = 0` and `z² ≥ c²(b² − c²)/(a² − c²)`: the two
  closed arcs of the ellipse `x²/a² + z²/c² = 1` in the plane `y = 0` that join the four points
  `(±a √((a² − b²)/(a² − c²)), 0, ±c √((b² − c²)/(a² − c²)))` (the images of the excluded parameters)
  through the vertices `(0, 0, ±c)`.

**Derivation.** A point of the ellipsoid gives the confocal coordinates `μ ≥ ν`, the roots of
`λ² − Sλ + T` with `S = a² + b² + c² − x² − y² − z²` and
`T = a²b² + a²c² + b²c² − x²(b² + c²) − y²(a² + c²) − z²(a² + b²)` (the equation
`x²/(a² − λ) + y²/(b² − λ) + z²/(c² − λ) = 1` cleared of denominators, divided by `λ`). On the
ellipsoid, `a²(a² − μ)(a² − ν) = x²(a² − b²)(a² − c²)`, `b²(μ − b²)(b² − ν) = y²(a² − b²)(b² − c²)` and
`c²(μ − c²)(ν − c²) = z²(a² − c²)(b² − c²)`, so `c² ≤ ν ≤ b² ≤ μ ≤ a²`; and `ν = b²` forces `y = 0`
and `z² = c²(μ − c²)/(a² − c²)`, a point of the arcs. Away from the arcs `ν < b²`, and
`sin t = z √(a² − c²)/(c √(μ − c²))`, `cos t > 0`, `cos s = x √(a² − c²)/(a √(a² − ν))`,
`sin s = y/(b cos t)` define parameters with `c(s, t) = (x, y, z)`.

The parameters are not claimed unique (the chart is `2π`-periodic in both variables). Concrete
charts are convention checks; they say nothing about a physical fingertip.

**Conventions.** As the library's confocal example: `Vec3` coordinates `p 0 = x`, `p 1 = y`,
`p 2 = z`; the patch `confocalDomain = {α | cos (α 1) > 0}`.
-/

noncomputable section

open Real

namespace RoboLean
namespace Examples

variable {a b c : ℝ}

/-- **The part of the ellipsoid outside the confocal patch (MLS Exercise 14, p. 262; p. 243, several
charts per surface):** the points of `x²/a² + y²/b² + z²/c² = 1` with `y = 0` and
`z² ≥ c²(b² − c²)/(a² − c²)`, the two arcs of the ellipse `x²/a² + z²/c² = 1` in the plane `y = 0`
joining the four excluded points through `(0, 0, ±c)`. -/
def confocalArcs (a b c : ℝ) : Set Vec3 :=
  {p | ellipsoidFunction a b c p = 0 ∧ p 1 = 0 ∧ c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) ≤ p 2 ^ 2}

/-- A point of the unit circle has an angle (supporting lemma for MLS Exercise 14, p. 262). -/
private lemma exists_angle (C S : ℝ) (h : C ^ 2 + S ^ 2 = 1) : ∃ θ : ℝ, cos θ = C ∧ sin θ = S := by
  let w : ℂ := ⟨C, S⟩
  have hn : ‖w‖ = 1 := by
    rw [Complex.norm_def]
    change √(C * C + S * S) = 1
    rw [show C * C + S * S = 1 by linear_combination h, sqrt_one]
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    norm_num at hn
  exact ⟨w.arg, by simpa [hn] using Complex.cos_arg hw, by simpa [hn] using Complex.sin_arg w⟩

/-- **The algebra of the coverage (MLS Exercise 14, p. 262):** a point `(x, y, z)` of the
ellipsoid that is not on the arcs is `c(s, t)` for some `s`, `t` with `cos t > 0`. -/
private lemma exists_params (hcb : c < b) (hba : b < a) (hc : 0 < c) {x y z : ℝ}
    (hE : x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 1)
    (hn : ¬(y = 0 ∧ c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) ≤ z ^ 2)) :
    ∃ s t : ℝ, 0 < cos t ∧ a / √(a ^ 2 - c ^ 2) * cos s * confocalX a b c t = x ∧
      b * sin s * cos t = y ∧ c / √(a ^ 2 - c ^ 2) * sin t * confocalZ a b c s = z := by
  have hb : 0 < b := by linarith
  have ha : 0 < a := by linarith
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have hE' : b ^ 2 * c ^ 2 * x ^ 2 + a ^ 2 * c ^ 2 * y ^ 2 + a ^ 2 * b ^ 2 * z ^ 2 =
      a ^ 2 * b ^ 2 * c ^ 2 := by
    field_simp at hE
    linear_combination hE
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = a ^ 2 + b ^ 2 + c ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 -
      x ^ 2 * (b ^ 2 + c ^ 2) - y ^ 2 * (a ^ 2 + c ^ 2) - z ^ 2 * (a ^ 2 + b ^ 2) := ⟨_, rfl⟩
  have Qa : a ^ 2 * (a ^ 4 - a ^ 2 * S + T) = x ^ 2 * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) := by
    rw [hS, hT]; linear_combination -hE'
  have Qb : b ^ 2 * (b ^ 4 - b ^ 2 * S + T) = -(y ^ 2 * (a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2)) := by
    rw [hS, hT]; linear_combination -hE'
  have Qc : c ^ 2 * (c ^ 4 - c ^ 2 * S + T) = z ^ 2 * (a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) := by
    rw [hS, hT]; linear_combination -hE'
  have hb2 : 0 < b ^ 2 := by positivity
  have hc2 : 0 < c ^ 2 := by positivity
  have ha2 : 0 < a ^ 2 := by positivity
  have hyX : 0 ≤ y ^ 2 * (a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg y) (by linarith)) (by linarith)
  have hxX : 0 ≤ x ^ 2 * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg x) (by linarith)) (by linarith)
  have hzX : 0 ≤ z ^ 2 * (a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg z) (by linarith)) (by linarith)
  -- the discriminant and the roots `μ ≥ ν`
  have hD : 0 ≤ S ^ 2 - 4 * T := by
    have e : b ^ 2 * (S ^ 2 - 4 * T) =
        b ^ 2 * (S - 2 * b ^ 2) ^ 2 + 4 * (y ^ 2 * (a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2)) := by
      linear_combination -4 * Qb
    have : 0 ≤ b ^ 2 * (S ^ 2 - 4 * T) := by rw [e]; positivity
    exact (mul_nonneg_iff_of_pos_left hb2).1 this
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √(S ^ 2 - 4 * T) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ sqrt_nonneg _
  have hr2 : r ^ 2 = S ^ 2 - 4 * T := hr ▸ sq_sqrt hD
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (S + r) / 2 := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = (S - r) / 2 := ⟨_, rfl⟩
  have hsum : μ + ν = S := by rw [hμ, hν]; ring
  have hprod : μ * ν = T := by rw [hμ, hν]; linear_combination -hr2 / 4
  have hνμ : ν ≤ μ := by rw [hμ, hν]; linarith
  have Pa : (a ^ 2 - μ) * (a ^ 2 - ν) = a ^ 4 - a ^ 2 * S + T := by rw [← hsum, ← hprod]; ring
  have Pb : (b ^ 2 - μ) * (b ^ 2 - ν) = b ^ 4 - b ^ 2 * S + T := by rw [← hsum, ← hprod]; ring
  have Pc : (c ^ 2 - μ) * (c ^ 2 - ν) = c ^ 4 - c ^ 2 * S + T := by rw [← hsum, ← hprod]; ring
  have Va : a ^ 2 * ((a ^ 2 - μ) * (a ^ 2 - ν)) = x ^ 2 * (a ^ 2 - b ^ 2) * (a ^ 2 - c ^ 2) := by
    rw [Pa]; exact Qa
  have Vb : b ^ 2 * ((μ - b ^ 2) * (b ^ 2 - ν)) = y ^ 2 * (a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) := by
    linear_combination -b ^ 2 * Pb - Qb
  have Vc : c ^ 2 * ((μ - c ^ 2) * (ν - c ^ 2)) = z ^ 2 * (a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) := by
    linear_combination c ^ 2 * Pc + Qc
  -- `c² ≤ ν ≤ b² ≤ μ ≤ a²`
  have hb' : 0 ≤ (μ - b ^ 2) * (b ^ 2 - ν) := (mul_nonneg_iff_of_pos_left hb2).1 (Vb ▸ hyX)
  have ha' : 0 ≤ (a ^ 2 - μ) * (a ^ 2 - ν) := (mul_nonneg_iff_of_pos_left ha2).1 (Va ▸ hxX)
  have hc' : 0 ≤ (μ - c ^ 2) * (ν - c ^ 2) := (mul_nonneg_iff_of_pos_left hc2).1 (Vc ▸ hzX)
  have hμb : b ^ 2 ≤ μ := by
    by_contra h
    push Not at h
    have : (μ - b ^ 2) * (b ^ 2 - ν) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  have hνb : ν ≤ b ^ 2 := by
    by_contra h
    push Not at h
    have : (μ - b ^ 2) * (b ^ 2 - ν) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have hμa : μ ≤ a ^ 2 := by
    by_contra h
    push Not at h
    have : (a ^ 2 - μ) * (a ^ 2 - ν) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  have hνc : c ^ 2 ≤ ν := by
    by_contra h
    push Not at h
    have : (μ - c ^ 2) * (ν - c ^ 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have hνb' : ν < b ^ 2 := by
    refine lt_of_le_of_ne hνb fun he => hn ⟨?_, ?_⟩
    · rw [he, sub_self, mul_zero, mul_zero] at Vb
      have h0 : y ^ 2 * (a ^ 2 - b ^ 2) * (b ^ 2 - c ^ 2) = 0 := Vb.symm
      have hy2 : y ^ 2 = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact h
          · exact absurd h (ne_of_gt (by linarith))
        · exact absurd h (ne_of_gt (by linarith))
      exact pow_eq_zero_iff two_ne_zero |>.1 hy2
    · rw [he] at Vc
      rw [div_le_iff₀ (by linarith)]
      have h3 : c ^ 2 * (b ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) ≤
          z ^ 2 * (a ^ 2 - c ^ 2) * (b ^ 2 - c ^ 2) := by
        rw [← Vc, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hc2.le
      exact le_of_mul_le_mul_right h3 (by linarith)
  -- the parameters
  have hbc : b ^ 2 - c ^ 2 ≠ 0 := by linarith
  have hab : a ^ 2 - b ^ 2 ≠ 0 := by linarith
  have hνb0 : b ^ 2 - ν ≠ 0 := by linarith
  have hμc : 0 < μ - c ^ 2 := by linarith
  have hνa : 0 < a ^ 2 - ν := by linarith
  have hk2 : √(a ^ 2 - c ^ 2) ^ 2 = a ^ 2 - c ^ 2 := sq_sqrt (by linarith)
  have hk0 : 0 < √(a ^ 2 - c ^ 2) := sqrt_pos.2 (by linarith)
  have hm2 : √(μ - c ^ 2) ^ 2 = μ - c ^ 2 := sq_sqrt hμc.le
  have hm0 : 0 < √(μ - c ^ 2) := sqrt_pos.2 hμc
  have hn2 : √(a ^ 2 - ν) ^ 2 = a ^ 2 - ν := sq_sqrt hνa.le
  have hn0 : 0 < √(a ^ 2 - ν) := sqrt_pos.2 hνa
  set P := z * √(a ^ 2 - c ^ 2) / (c * √(μ - c ^ 2)) with hPdef
  have hP2 : P ^ 2 = (ν - c ^ 2) / (b ^ 2 - c ^ 2) := by
    rw [hPdef, div_pow, mul_pow, mul_pow, hk2, hm2, div_eq_div_iff (by positivity) (by linarith)]
    linear_combination -Vc
  have hQ1 : 0 < 1 - P ^ 2 := by
    rw [hP2, sub_pos, div_lt_one (by linarith)]
    linarith
  set Q := √(1 - P ^ 2) with hQdef
  have hQ0 : 0 < Q := sqrt_pos.2 hQ1
  have hQ2 : Q ^ 2 = 1 - P ^ 2 := sq_sqrt hQ1.le
  have hQ2' : Q ^ 2 = (b ^ 2 - ν) / (b ^ 2 - c ^ 2) := by
    rw [hQ2, hP2]; field_simp; ring
  set C := x * √(a ^ 2 - c ^ 2) / (a * √(a ^ 2 - ν)) with hCdef
  set Sn := y / (b * Q) with hSndef
  have hC2 : C ^ 2 = (a ^ 2 - μ) / (a ^ 2 - b ^ 2) := by
    rw [hCdef, div_pow, mul_pow, mul_pow, hk2, hn2, div_eq_div_iff (by positivity) (by linarith)]
    linear_combination -Va
  have hSn2 : Sn ^ 2 = (μ - b ^ 2) / (a ^ 2 - b ^ 2) := by
    rw [hSndef, div_pow, mul_pow, hQ2', div_eq_div_iff (by positivity) hab]
    field_simp
    linear_combination -Vb
  obtain ⟨s, hcs, hss⟩ := exists_angle C Sn (by
    rw [hC2, hSn2, ← add_div, div_eq_one_iff_eq (by linarith)]; ring)
  obtain ⟨t, hct, hst⟩ := exists_angle Q P (by rw [hQ2]; ring)
  have hnu : confocalNu b c t = ν := by
    rw [confocalNu, hst, hP2]; field_simp; ring
  have hmu : confocalMu a b s = μ := by
    rw [confocalMu, hss, hSn2]; field_simp; ring
  refine ⟨s, t, hct ▸ hQ0, ?_, ?_, ?_⟩
  · rw [confocalX, hnu, hcs, hCdef]
    field_simp
  · rw [hss, hct, hSndef]
    field_simp
  · rw [confocalZ, hmu, hst, hPdef]
    field_simp

/-- **The confocal patch covers the ellipsoid minus two arcs (MLS Exercise 14, p. 262; p. 243):**
for `a > b > c > 0`, the image of the patch `{cos t > 0}` under the confocal chart is the ellipsoid
`x²/a² + y²/b² + z²/c² = 1` without `confocalArcs`, its points with `y = 0` and
`z² ≥ c²(b² − c²)/(a² − c²)`. -/
theorem confocalChart_image_confocalDomain (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    confocalChart a b c '' confocalDomain =
      {p | ellipsoidFunction a b c p = 0} \ confocalArcs a b c := by
  have hb : 0 < b := by linarith
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  ext p
  constructor
  · rintro ⟨α, hα, rfl⟩
    refine ⟨ellipsoidFunction_confocalChart hcb hba hc α, ?_⟩
    rintro ⟨-, hy, hz⟩
    have hα' : 0 < cos (α 1) := hα
    have hs : sin (α 0) = 0 := by
      have : b * sin (α 0) * cos (α 1) = 0 := by simpa [confocalChart] using hy
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · exact h
      · linarith
    have hZ : confocalZ a b c (α 0) ^ 2 = b ^ 2 - c ^ 2 := by
      rw [confocalZ, confocalMu, hs, sq_sqrt (by nlinarith)]
      ring
    have hz2 : confocalChart a b c α 2 ^ 2 =
        c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) * sin (α 1) ^ 2 := by
      simp only [confocalChart, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      rw [mul_pow, mul_pow, div_pow, sq_sqrt (by nlinarith), hZ]
      ring
    have hsin : sin (α 1) ^ 2 < 1 := by nlinarith [sin_sq_add_cos_sq (α 1)]
    have hpos : 0 < c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) :=
      div_pos (mul_pos (by positivity) (by linarith)) (by nlinarith)
    rw [hz2] at hz
    nlinarith
  · rintro ⟨hp, hnot⟩
    have hE : p 0 ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2 + p 2 ^ 2 / c ^ 2 = 1 := by
      simp only [Set.mem_ofPred_eq, ellipsoidFunction] at hp
      linarith
    have hn : ¬(p 1 = 0 ∧ c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) ≤ p 2 ^ 2) :=
      fun h => hnot ⟨hp, h.1, h.2⟩
    obtain ⟨s, t, ht, e0, e1, e2⟩ := exists_params hcb hba hc hE hn
    refine ⟨![s, t], ht, ?_⟩
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simpa [confocalChart] using e0
    · simpa [confocalChart] using e1
    · simpa [confocalChart] using e2

end Examples
end RoboLean
