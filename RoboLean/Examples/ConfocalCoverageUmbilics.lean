import RoboLean.Examples.ConfocalCoverage
import RoboLean.Surfaces.Umbilics

/-!
# The excluded points of the confocal chart are umbilics (MLS Exercise 14, p. 262)

The confocal chart of the three-axis ellipsoid `x²/a² + y²/b² + z²/c² = 1`, `a > b > c > 0` (the
library's example for MLS Exercises 14, 15 and 19, pp. 262–263), is singular at the parameters
`sin s = 0`, `cos t = 0`, whose images are the four points
`p = (x₀, 0, z₀)` with `x₀² = a²(a² − b²)/(a² − c²)`, `z₀² = c²(b² − c²)/(a² − c²)`. Its curvature
tensor `K = (abc/√(μν)) diag(1/μ, 1/ν)` on the patch has distinct diagonal entries there (`μ > ν`),
and both tend to `ac/b³` as `μ, ν → b²` at the excluded parameters.

**Proved here.**

* At each of the four points the derivative of the ellipsoid's normal field
  `G(x) = (x/a², y/b², z/c²)` is `1/b²` times the identity on the tangent plane:
  `wᵀ DG(p) w' = wᵀ w'/b²` for `w, w' ⟂ G(p)` (`inner_fderiv_ellipsoidField_of_umbilic`).
* The graph charts `c_σ(u, v) = (u, v, σ c √(1 − u²/a² − v²/b²))`, `σ = ±1` (`ellipsoidGraph`),
  are regular at `(x₀, 0)`, orthogonal there, and have Gauss normal `σ G/‖G‖` near it
  (`gaussNormal_ellipsoidGraph`); so `(x₀, 0)` is an umbilic of `c_σ` in the sense of `IsUmbilicAt`,
  with curvature tensor `σ (ac/b³) I`: the principal curvatures coincide and equal `ac/b³` in
  absolute value (`isUmbilicAt_ellipsoidGraph`).
* The image of every excluded parameter of the confocal chart is such a point `c_σ(x₀, 0)`
  (`confocalChart_excluded_eq_ellipsoidGraph`), hence an umbilic of a chart regular there
  (`isUmbilicAt_confocalChart_excluded`). The confocal chart itself is singular at these parameters
  (`partial_confocalChart_ne_zero_iff`), so its own `K` there carries no information; the umbilic is
  read in a chart that is regular at the point.

Not proved here: that the ellipsoid has no other umbilics. Concrete charts are convention checks;
they say nothing about a physical fingertip.

**Conventions.** `Vec3` coordinates `p 0 = x`, `p 1 = y`, `p 2 = z`; chart parameters
`α 0 = u`, `α 1 = v`; `IsUmbilicAt`, `curvatureTensor` and `gaussNormal` as in the library's
Chapter 5 modules.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Surface

variable {a b c : ℝ}

/-- **A graph chart of the ellipsoid (for MLS Exercise 14, p. 262, and p. 243, several charts per
surface):** `c_σ(u, v) = (u, v, σ c √(1 − u²/a² − v²/b²))`; for `σ = 1` the half `z > 0`, for
`σ = −1` the half `z < 0`. -/
def ellipsoidGraph (a b c σ : ℝ) (α : Fin 2 → ℝ) : Vec3 :=
  WithLp.toLp 2 ![α 0, α 1, σ * c * √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2)]

private lemma hasDerivAt_toLp3' {f g k : ℝ → ℝ} {p q d x : ℝ} (hf : HasDerivAt f p x)
    (hg : HasDerivAt g q x) (hk : HasDerivAt k d x) :
    HasDerivAt (fun s => (WithLp.toLp 2 ![f s, g s, k s] : Vec3)) (WithLp.toLp 2 ![p, q, d]) x := by
  have h := (hf.smul_const (WithLp.toLp 2 ![1, 0, 0] : Vec3)).add
    ((hg.smul_const (WithLp.toLp 2 ![0, 1, 0] : Vec3)).add
      (hk.smul_const (WithLp.toLp 2 ![0, 0, 1] : Vec3)))
  convert h using 1
  · funext s
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp
  · apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp

/-- **The graph chart is differentiable where it is defined (MLS p. 243, condition 1):** at every
`(u, v)` with `1 − u²/a² − v²/b² > 0`. -/
theorem differentiableAt_ellipsoidGraph (σ : ℝ) {α : Fin 2 → ℝ} (hR : 0 < 1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) :
    DifferentiableAt ℝ (ellipsoidGraph a b c σ) α := by
  have h : DifferentiableAt ℝ (fun α : Fin 2 → ℝ =>
      ![α 0, α 1, σ * c * √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2)]) α := by
    refine differentiableAt_pi.mpr fun i => ?_
    fin_cases i
    · simp; fun_prop
    · simp; fun_prop
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact DifferentiableAt.const_mul (DifferentiableAt.sqrt
        (f := fun α : Fin 2 → ℝ => 1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) (by fun_prop) hR.ne') _
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.differentiableAt.comp α h

private lemma partialU_ellipsoidGraph (σ : ℝ) {α : Fin 2 → ℝ} (hR : 0 < 1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) :
    partialU (ellipsoidGraph a b c σ) α =
      WithLp.toLp 2 ![1, 0, σ * c * (-(2 * α 0 / a ^ 2) /
        (2 * √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2)))] := by
  refine partialU_eq_of_hasDerivAt (differentiableAt_ellipsoidGraph σ hR) ?_
  have hr : HasDerivAt (fun s : ℝ => 1 - (α 0 + s) ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2)
      (-(2 * α 0 / a ^ 2)) 0 := by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add (α 0)).pow 2).div_const (a ^ 2)).const_sub 1
    convert h.sub_const (α 1 ^ 2 / b ^ 2) using 1
    simp
  have hr0 : (fun s : ℝ => 1 - (α 0 + s) ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) 0 ≠ 0 := by
    simpa using hR.ne'
  have h := hasDerivAt_toLp3' ((hasDerivAt_id' (0 : ℝ)).const_add (α 0))
    (hasDerivAt_const (0 : ℝ) (α 1)) ((hr.sqrt hr0).const_mul (σ * c))
  convert h using 1
  · funext s
    simp [ellipsoidGraph]
  · simp

private lemma partialV_ellipsoidGraph (σ : ℝ) {α : Fin 2 → ℝ} (hR : 0 < 1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) :
    partialV (ellipsoidGraph a b c σ) α =
      WithLp.toLp 2 ![0, 1, σ * c * (-(2 * α 1 / b ^ 2) /
        (2 * √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2)))] := by
  refine partialV_eq_of_hasDerivAt (differentiableAt_ellipsoidGraph σ hR) ?_
  have hr : HasDerivAt (fun s : ℝ => 1 - α 0 ^ 2 / a ^ 2 - (α 1 + s) ^ 2 / b ^ 2)
      (-(2 * α 1 / b ^ 2)) 0 := by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add (α 1)).pow 2).div_const (b ^ 2)).const_sub
      (1 - α 0 ^ 2 / a ^ 2)
    convert h using 1
    simp
  have hr0 : (fun s : ℝ => 1 - α 0 ^ 2 / a ^ 2 - (α 1 + s) ^ 2 / b ^ 2) 0 ≠ 0 := by
    simpa using hR.ne'
  have h := hasDerivAt_toLp3' (hasDerivAt_const (0 : ℝ) (α 0))
    ((hasDerivAt_id' (0 : ℝ)).const_add (α 1)) ((hr.sqrt hr0).const_mul (σ * c))
  convert h using 1
  · funext s
    simp [ellipsoidGraph]
  · simp

/-- **The Gauss normal of the graph chart (MLS eq. (5.19), p. 245):** for `σ = ±1`, `c > 0` and
`a, b ≠ 0`, where `1 − u²/a² − v²/b² > 0` the Gauss normal of `c_σ` is `σG/‖σG‖` at `c_σ(u, v)`,
`G(x) = (x/a², y/b², z/c²)` the ellipsoid's normal field. -/
theorem gaussNormal_ellipsoidGraph (ha : a ≠ 0) (hb : b ≠ 0) (hc : 0 < c) {σ : ℝ}
    (hσ : σ ^ 2 = 1) {α : Fin 2 → ℝ} (hR : 0 < 1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) :
    gaussNormal (ellipsoidGraph a b c σ) α =
      normalizedField (fun x => σ • ellipsoidField a b c x) (ellipsoidGraph a b c σ α) := by
  have hR' := hR
  have hs0 : 0 < √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) := sqrt_pos.2 hR'
  have hs2 : √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) ^ 2 = (1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) := sq_sqrt hR'.le
  set l := c / √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) with hl
  have hl0 : 0 < l := div_pos hc hs0
  have hX : Vec3.cross (partialU (ellipsoidGraph a b c σ) α)
      (partialV (ellipsoidGraph a b c σ) α) =
      l • (σ • ellipsoidField a b c (ellipsoidGraph a b c σ α)) := by
    rw [partialU_ellipsoidGraph σ hR', partialV_ellipsoidGraph σ hR']
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · simp [Vec3.cross, cross_apply, ellipsoidField, ellipsoidGraph, hl]
      field_simp
    · simp [Vec3.cross, cross_apply, ellipsoidField, ellipsoidGraph, hl]
      field_simp
    · simp [Vec3.cross, cross_apply, ellipsoidField, ellipsoidGraph, hl]
      generalize √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) = q at hs0 ⊢
      field_simp
      linear_combination -hσ
  rw [gaussNormal, hX, normalizedField, norm_smul, Real.norm_of_nonneg hl0.le, smul_smul]
  congr 1
  field_simp

/-- **At the four excluded points the normal field's derivative is `1/b²` on the tangent plane
(MLS Exercise 14, p. 262; Exercise 19, p. 263):** for `a > b > c > 0` and `p = (x₀, 0, z₀)` with
`x₀²(a² − c²) = a²(a² − b²)` and `z₀²(a² − c²) = c²(b² − c²)`, every `w, w'` orthogonal to
`G(p) = (x₀/a², 0, z₀/c²)` satisfy `wᵀ DG(p) w' = wᵀ w'/b²`. -/
theorem inner_fderiv_ellipsoidField_of_umbilic (hcb : c < b) (hba : b < a) (hc : 0 < c)
    {p : Vec3} (hp1 : p 1 = 0) (hp0 : p 0 ^ 2 * (a ^ 2 - c ^ 2) = a ^ 2 * (a ^ 2 - b ^ 2))
    (hp2 : p 2 ^ 2 * (a ^ 2 - c ^ 2) = c ^ 2 * (b ^ 2 - c ^ 2)) {w w' : Vec3}
    (hw : inner ℝ w (ellipsoidField a b c p) = 0) (hw' : inner ℝ w' (ellipsoidField a b c p) = 0) :
    inner ℝ w (fderiv ℝ (ellipsoidField a b c) p w') = 1 / b ^ 2 * inner ℝ w w' := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have hx0 : p 0 ≠ 0 := by
    intro h
    rw [h] at hp0
    nlinarith
  have hinner : ∀ u v : Vec3, inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := fun u v => by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    ring
  have hG : ∀ v : Vec3, ellipsoidField a b c v 0 = v 0 / a ^ 2 ∧
      ellipsoidField a b c v 1 = v 1 / b ^ 2 ∧ ellipsoidField a b c v 2 = v 2 / c ^ 2 :=
    fun v => ⟨by simp [ellipsoidField], by simp [ellipsoidField], by simp [ellipsoidField]⟩
  rw [fderiv_ellipsoidField, hinner, hinner, (hG w').1, (hG w').2.1, (hG w').2.2]
  rw [hinner, (hG p).1, (hG p).2.1, (hG p).2.2, hp1] at hw hw'
  have hb2 : b ^ 2 ≠ 0 := by positivity
  have H1 : w 0 * p 0 * c ^ 2 + w 2 * p 2 * a ^ 2 = 0 := by
    refine (mul_eq_zero.1 (?_ : b ^ 2 * (w 0 * p 0 * c ^ 2 + w 2 * p 2 * a ^ 2) = 0)).resolve_left hb2
    field_simp at hw
    linear_combination hw
  have H1' : w' 0 * p 0 * c ^ 2 + w' 2 * p 2 * a ^ 2 = 0 := by
    refine (mul_eq_zero.1 (?_ : b ^ 2 * (w' 0 * p 0 * c ^ 2 + w' 2 * p 2 * a ^ 2) = 0)).resolve_left hb2
    field_simp at hw'
    linear_combination hw'
  have E : p 0 ^ 2 * c ^ 4 * (w 0 * w' 0) = p 2 ^ 2 * a ^ 4 * (w 2 * w' 2) := by
    have e1 : w 0 * p 0 * c ^ 2 = -(w 2 * p 2 * a ^ 2) := by linear_combination H1
    have e2 : w' 0 * p 0 * c ^ 2 = -(w' 2 * p 2 * a ^ 2) := by linear_combination H1'
    calc p 0 ^ 2 * c ^ 4 * (w 0 * w' 0) = (w 0 * p 0 * c ^ 2) * (w' 0 * p 0 * c ^ 2) := by ring
      _ = (-(w 2 * p 2 * a ^ 2)) * (-(w' 2 * p 2 * a ^ 2)) := by rw [e1, e2]
      _ = p 2 ^ 2 * a ^ 4 * (w 2 * w' 2) := by ring
  have hK : (a ^ 2 - c ^ 2) * (p 0 ^ 2 * c ^ 4) *
      ((b ^ 2 - a ^ 2) * c ^ 2 * (w 0 * w' 0) + (b ^ 2 - c ^ 2) * a ^ 2 * (w 2 * w' 2)) = 0 := by
    linear_combination (b ^ 2 - a ^ 2) * c ^ 2 * (a ^ 2 - c ^ 2) * E +
      (b ^ 2 - a ^ 2) * c ^ 2 * a ^ 4 * (w 2 * w' 2) * hp2 +
      (b ^ 2 - c ^ 2) * a ^ 2 * c ^ 4 * (w 2 * w' 2) * hp0
  have hne : (a ^ 2 - c ^ 2) * (p 0 ^ 2 * c ^ 4) ≠ 0 :=
    mul_ne_zero (by linarith) (by positivity)
  have K0 := (mul_eq_zero.1 hK).resolve_left hne
  field_simp
  linear_combination K0

private lemma rad_pos_of_sq (hcb : c < b) (hba : b < a) (hc : 0 < c) {x₀ : ℝ}
    (hx : x₀ ^ 2 * (a ^ 2 - c ^ 2) = a ^ 2 * (a ^ 2 - b ^ 2)) :
    1 - (![x₀, 0] : Fin 2 → ℝ) 0 ^ 2 / a ^ 2 - (![x₀, 0] : Fin 2 → ℝ) 1 ^ 2 / b ^ 2 =
      (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) ∧
    0 < 1 - (![x₀, 0] : Fin 2 → ℝ) 0 ^ 2 / a ^ 2 - (![x₀, 0] : Fin 2 → ℝ) 1 ^ 2 / b ^ 2 := by
  have ha : 0 < a := by linarith
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have e : 1 - (![x₀, 0] : Fin 2 → ℝ) 0 ^ 2 / a ^ 2 - (![x₀, 0] : Fin 2 → ℝ) 1 ^ 2 / b ^ 2 =
      (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hac : a ^ 2 - c ^ 2 ≠ 0 := by linarith
    field_simp
    linear_combination -hx
  exact ⟨e, by rw [e]; exact div_pos (by linarith) (by linarith)⟩

/-- **The graph chart is regular where it is defined (MLS p. 243, condition 3):** where
`1 − u²/a² − v²/b² > 0`, `c_u ≠ 0` and `c_v ≠ 0` (their first and second coordinates are `1`). -/
theorem partial_ellipsoidGraph_ne_zero (σ : ℝ) {α : Fin 2 → ℝ}
    (hR : 0 < 1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) :
    partialU (ellipsoidGraph a b c σ) α ≠ 0 ∧ partialV (ellipsoidGraph a b c σ) α ≠ 0 := by
  rw [partialU_ellipsoidGraph σ hR, partialV_ellipsoidGraph σ hR]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun v : Vec3 => v 0) h
    simp at this
  · have := congrArg (fun v : Vec3 => v 1) h
    simp at this

/-- **The four excluded points are umbilics of the graph charts (MLS eq. (5.21), p. 245, and
Exercise 14, p. 262):** for `a > b > c > 0`, `σ = ±1` and `x₀²(a² − c²) = a²(a² − b²)`, the chart
`c_σ` is orthogonal at `(x₀, 0)`, the point is an umbilic of `c_σ` (`IsUmbilicAt`), and the
curvature tensor there is `σ (ac/b³) I`: both principal curvatures equal `σ ac/b³`. -/
theorem isUmbilicAt_ellipsoidGraph (hcb : c < b) (hba : b < a) (hc : 0 < c) {σ : ℝ}
    (hσ : σ ^ 2 = 1) {x₀ : ℝ} (hx : x₀ ^ 2 * (a ^ 2 - c ^ 2) = a ^ 2 * (a ^ 2 - b ^ 2)) :
    IsOrthogonalAt (ellipsoidGraph a b c σ) ![x₀, 0] ∧
      IsUmbilicAt (ellipsoidGraph a b c σ) ![x₀, 0] ∧
      curvatureTensor (ellipsoidGraph a b c σ) ![x₀, 0] =
        (σ * (a * c / b ^ 3)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have hac : a ^ 2 - c ^ 2 ≠ 0 := by linarith
  obtain ⟨hRv, hR⟩ := rad_pos_of_sq hcb hba hc hx
  set α : Fin 2 → ℝ := ![x₀, 0] with hα
  set p := ellipsoidGraph a b c σ α with hp
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    norm_num at hσ
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    have : 0 < a ^ 2 * (a ^ 2 - b ^ 2) := mul_pos (by positivity) (by linarith)
    rw [← hx] at this
    simp at this
  have hp0 : p 0 = x₀ := by simp [hp, ellipsoidGraph, hα]
  have hp1 : p 1 = 0 := by simp [hp, ellipsoidGraph, hα]
  have hp2 : p 2 = σ * c * √(1 - α 0 ^ 2 / a ^ 2 - α 1 ^ 2 / b ^ 2) := by
    simp [hp, ellipsoidGraph]
  have hp2sq : p 2 ^ 2 * (a ^ 2 - c ^ 2) = c ^ 2 * (b ^ 2 - c ^ 2) := by
    rw [hp2, mul_pow, mul_pow, hσ, sq_sqrt hR.le, hRv]
    field_simp
  have hp0sq : p 0 ^ 2 * (a ^ 2 - c ^ 2) = a ^ 2 * (a ^ 2 - b ^ 2) := by rw [hp0]; exact hx
  have hopen : IsOpen {β : Fin 2 → ℝ | 0 < 1 - β 0 ^ 2 / a ^ 2 - β 1 ^ 2 / b ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have hn : gaussNormal (ellipsoidGraph a b c σ) =ᶠ[𝓝 α]
      fun β => normalizedField (fun x => σ • ellipsoidField a b c x) (ellipsoidGraph a b c σ β) := by
    filter_upwards [hopen.mem_nhds hR] with β hβ
    exact gaussNormal_ellipsoidGraph ha.ne' hb.ne' hc hσ hβ
  have hGd : DifferentiableAt ℝ (fun x => σ • ellipsoidField a b c x) p :=
    (differentiable_ellipsoidField.const_smul σ) p
  have hG0 : σ • ellipsoidField a b c p ≠ 0 := by
    intro h
    have := congrArg (fun v : Vec3 => v 0) h
    simp [ellipsoidField, hp0, hσ0, hx0, ha.ne'] at this
  have horth : IsOrthogonalAt (ellipsoidGraph a b c σ) α := by
    rw [IsOrthogonalAt, partialU_ellipsoidGraph σ hR, partialV_ellipsoidGraph σ hR]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, hα]
  obtain ⟨hu, hv⟩ := partial_ellipsoidGraph_ne_zero (c := c) σ hR
  have hκ : ∀ w w' : Vec3, inner ℝ w (σ • ellipsoidField a b c p) = 0 →
      inner ℝ w' (σ • ellipsoidField a b c p) = 0 →
      inner ℝ w (fderiv ℝ (fun x => σ • ellipsoidField a b c x) p w') =
        σ / b ^ 2 * inner ℝ w w' := by
    intro w w' hw hw'
    rw [inner_smul_right] at hw hw'
    have e := inner_fderiv_ellipsoidField_of_umbilic hcb hba hc hp1 hp0sq hp2sq
      ((mul_eq_zero.1 hw).resolve_left hσ0) ((mul_eq_zero.1 hw').resolve_left hσ0)
    rw [fderiv_fun_const_smul (differentiable_ellipsoidField p), _root_.smul_apply,
      inner_smul_right, e]
    ring
  have hK := curvatureTensor_eq_smul_one_of_form
    (differentiableAt_ellipsoidGraph σ hR) hGd hG0 hn horth hu hv hκ
  have hnorm : ‖σ • ellipsoidField a b c p‖ = b / (a * c) := by
    have hsq : ‖σ • ellipsoidField a b c p‖ ^ 2 = (b / (a * c)) ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hσ, one_mul, EuclideanSpace.norm_eq,
        sq_sqrt (by positivity)]
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, ellipsoidField, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, hp1]
      have hp0v : p 0 ^ 2 = a ^ 2 * (a ^ 2 - b ^ 2) / (a ^ 2 - c ^ 2) := by
        rw [eq_div_iff hac]; exact hp0sq
      have hp2v : p 2 ^ 2 = c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) := by
        rw [eq_div_iff hac]; exact hp2sq
      rw [div_pow, div_pow, div_pow, hp0v, hp2v]
      field_simp
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  refine ⟨horth, isUmbilicAt_of_form (differentiableAt_ellipsoidGraph σ hR) hGd hG0 hn horth hu hv
    hκ, ?_⟩
  rw [hK, hnorm]
  congr 1
  field_simp

/-- **The images of the excluded parameters of the confocal chart lie on the graph charts (MLS
Exercise 14, p. 262):** where `sin s = 0` and `cos t = 0`, the confocal chart point is
`c_σ(x₀, 0)` with `σ = sin t = ±1`, `x₀` its first coordinate and `x₀²(a² − c²) = a²(a² − b²)`. -/
theorem confocalChart_excluded_eq_ellipsoidGraph (hcb : c < b) (hba : b < a) (hc : 0 < c)
    {α : Fin 2 → ℝ} (hs : sin (α 0) = 0) (ht : cos (α 1) = 0) :
    sin (α 1) ^ 2 = 1 ∧
      confocalChart a b c α 0 ^ 2 * (a ^ 2 - c ^ 2) = a ^ 2 * (a ^ 2 - b ^ 2) ∧
      ellipsoidGraph a b c (sin (α 1)) ![confocalChart a b c α 0, 0] = confocalChart a b c α := by
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  obtain ⟨hy, hx2, hz2⟩ := confocalChart_of_sin_eq_zero_of_cos_eq_zero hcb hba hc hs ht
  have hs2 : sin (α 1) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (α 1)]
  have hx : confocalChart a b c α 0 ^ 2 * (a ^ 2 - c ^ 2) = a ^ 2 * (a ^ 2 - b ^ 2) := by
    rw [hx2]
    have hac : a ^ 2 - c ^ 2 ≠ 0 := by linarith
    field_simp
  obtain ⟨hRv, -⟩ := rad_pos_of_sq hcb hba hc hx
  refine ⟨hs2, hx, ?_⟩
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [ellipsoidGraph]
  · simp [ellipsoidGraph, hy]
  · have e : ellipsoidGraph a b c (sin (α 1)) ![confocalChart a b c α 0, 0] 2 =
        sin (α 1) * c * √((b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2)) := by
      rw [← hRv]
      simp [ellipsoidGraph]
    have e2 : confocalChart a b c α 2 =
        c / √(a ^ 2 - c ^ 2) * sin (α 1) * √(b ^ 2 - c ^ 2) := by
      simp [confocalChart, confocalZ, confocalMu, hs]
    change ellipsoidGraph a b c (sin (α 1)) ![confocalChart a b c α 0, 0] 2 =
      confocalChart a b c α 2
    rw [e, e2, Real.sqrt_div (by linarith)]
    ring

/-- **The excluded parameters of the confocal chart map to umbilics (MLS Exercise 14, p. 262, with
eq. (5.21), p. 245):** for `a > b > c > 0`, where `sin s = 0` and `cos t = 0` the confocal chart
point is the point `(x₀, 0)` of the graph chart `c_σ`, `σ = sin t`, which is regular and orthogonal
there, and the point is an umbilic of `c_σ` with both principal curvatures `σ ac/b³`. -/
theorem isUmbilicAt_confocalChart_excluded (hcb : c < b) (hba : b < a) (hc : 0 < c)
    {α : Fin 2 → ℝ} (hs : sin (α 0) = 0) (ht : cos (α 1) = 0) :
    ellipsoidGraph a b c (sin (α 1)) ![confocalChart a b c α 0, 0] = confocalChart a b c α ∧
      partialU (ellipsoidGraph a b c (sin (α 1))) ![confocalChart a b c α 0, 0] ≠ 0 ∧
      partialV (ellipsoidGraph a b c (sin (α 1))) ![confocalChart a b c α 0, 0] ≠ 0 ∧
      IsOrthogonalAt (ellipsoidGraph a b c (sin (α 1))) ![confocalChart a b c α 0, 0] ∧
      IsUmbilicAt (ellipsoidGraph a b c (sin (α 1))) ![confocalChart a b c α 0, 0] ∧
      curvatureTensor (ellipsoidGraph a b c (sin (α 1))) ![confocalChart a b c α 0, 0] =
        (sin (α 1) * (a * c / b ^ 3)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨hσ, hx, heq⟩ := confocalChart_excluded_eq_ellipsoidGraph hcb hba hc hs ht
  obtain ⟨ho, hU, hK⟩ := isUmbilicAt_ellipsoidGraph hcb hba hc hσ hx
  obtain ⟨-, hR⟩ := rad_pos_of_sq hcb hba hc hx
  obtain ⟨hu, hv⟩ := partial_ellipsoidGraph_ne_zero (c := c) (sin (α 1)) hR
  exact ⟨heq, hu, hv, ho, hU, hK⟩

end Examples
end RoboLean
