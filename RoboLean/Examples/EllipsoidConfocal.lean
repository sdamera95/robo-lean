import RoboLean.Surfaces.LevelSet
import RoboLean.Examples.SphereChart
import RoboLean.Grasp.RollingContact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A three-axis ellipsoid in confocal coordinates: MLS Exercises 14, 15 and 19

MLS Chapter 5, Exercise 14, printed p. 262: "Calculate the geometric parameters for an ellipsoid".
Exercise 15, p. 262: an elliptic fingertip whose principal axes "have length `a`, `b`, and `c`" in
contact with a flat object: "(a) Give an orthonormal coordinate chart for the fingertip around the
point of contact as shown in the figure. (b) Assume the fingertip is in rolling contact with the
object. Derive the equations of contact. (c) Compute the velocity of the fingertip relative to the
object which satisfies rolling constraint and produces a contact velocity of `α̇_o = (0, v)`."
Exercise 19, p. 263: "Test your solution using an ellipsoid rolling on a plane."

**The chart.** For semi-axes `a > b > c > 0` the ellipsoid `x²/a² + y²/b² + z²/c² = 1` carries the
confocal (ellipsoidal) coordinates `μ ∈ [b², a²]`, `ν ∈ [c², b²]`, the two roots other than `0` of
`x²/(a² − λ) + y²/(b² − λ) + z²/(c² − λ) = 1`; their coordinate lines are the lines of curvature.
They are singular at the four vertices on the `x`- and `z`-axes. The substitution
`μ = b² + (a² − b²) sin² s`, `ν = c² + (b² − c²) sin² t` removes that singularity at the vertices
`(±a, 0, 0)` and gives the chart (`confocalChart`)
`c(s, t) = ((a/k) cos s √(a² − ν), b sin s cos t, (c/k) sin t √(μ − c²))`, `k = √(a² − c²)`,
twice continuously differentiable on all of `ℝ²` and orthogonal at every point. It is regular
exactly where `sin s ≠ 0` or `cos t ≠ 0`, and an orthogonal chart there
(`isOrthogonalChartOn_confocalChart_regular`); the excluded parameters `sin s = 0`, `cos t = 0` map
to the points `(±a √((a² − b²)/(a² − c²)), 0, ±c √((b² − c²)/(a² − c²)))`
(`confocalChart_of_sin_eq_zero_of_cos_eq_zero`), the four umbilics of the ellipsoid (a classical fact,
not proved here). The patch used for the geometric parameters is `{cos t > 0}` (`confocalDomain`).
Not proved here: that on `(−π, π] × (−π/2, π/2)` the patch is mapped injectively onto the ellipsoid
without the two arcs of the ellipse `x²/a² + z²/c² = 1` in the plane `y = 0` that join the umbilics
through the vertices `(0, 0, ±c)` (a derivation from the signs of `x`, `y`, `z` and the values of
`μ`, `ν`).

**Geometric parameters** (`exercise14_confocal`): with `μ = b² + (a² − b²) sin² s` and
`ν = c² + (b² − c²) sin² t`, the normal (5.19) is outward,
`n = (x/a², y/b², z/c²)/‖(x/a², y/b², z/c²)‖`, and
`M = diag(√(μ(μ − ν)/(μ − c²)), √(ν(μ − ν)/(a² − ν)))`,
`K = (abc/√(μν)) diag(1/μ, 1/ν)` (the principal curvatures, `K` diagonal because the coordinate
lines are lines of curvature),
`T = [(b² − c²) sin t cos t/((μ − ν) ‖c_t‖), (a² − b²) sin s cos s/((μ − ν) ‖c_s‖)]`.
The curvature is computed from the normal field `(x/a², y/b², z/c²)`, one half of the gradient of
`x²/a² + y²/b² + z²/c² − 1`, by `Surface.curvatureTensor_eq_of_gaussNormal`: this is the level-set
computation of Exercise 19.

**Exercise 15.** The contact point of the figure is the vertex `(−a, 0, 0) = c(π, 0)`, outward
normal `(−1, 0, 0)`; there `M = diag(b, c √((b² − c²)/(a² − c²)))`, `K = diag(a/b², a/c²)`,
`T = 0`. Against the plane chart of MLS Example 5.7 the equations of contact under rolling are
those of Corollary 5.11.1 (p. 252) with `K_f + K̃_o = K_f` (`exercise15b_confocal`), and the
rolling velocities producing `α̇_o = (0, v)` are read off (`exercise15c_confocal`). "Orthonormal
coordinate chart" is read as orthogonal chart, as for the two-equal-axes case. Concrete charts are
convention checks for the general theorems; they say nothing about a physical fingertip.
-/

noncomputable section

open Matrix Filter Topology Real

namespace RoboLean
namespace Examples

open Surface Rolling

/-- **The confocal coordinate `μ` along the chart (MLS Exercise 14, p. 262):**
`μ(s) = b² + (a² − b²) sin² s ∈ [b², a²]`. -/
def confocalMu (a b s : ℝ) : ℝ := b ^ 2 + (a ^ 2 - b ^ 2) * sin s ^ 2

/-- **The confocal coordinate `ν` along the chart (MLS Exercise 14, p. 262):**
`ν(t) = c² + (b² − c²) sin² t ∈ [c², b²]`. -/
def confocalNu (b c t : ℝ) : ℝ := c ^ 2 + (b ^ 2 - c ^ 2) * sin t ^ 2

/-- **The factor `√(a² − ν(t))` of the first coordinate of the confocal chart (MLS Exercise 14,
p. 262).** -/
def confocalX (a b c t : ℝ) : ℝ := √(a ^ 2 - confocalNu b c t)

/-- **The factor `√(μ(s) − c²)` of the third coordinate of the confocal chart (MLS Exercise 14,
p. 262).** -/
def confocalZ (a b c s : ℝ) : ℝ := √(confocalMu a b s - c ^ 2)

/-- **The confocal chart of the ellipsoid `x²/a² + y²/b² + z²/c² = 1` (MLS Exercises 14–15,
p. 262):** `c(s, t) = ((a/k) cos s √(a² − ν), b sin s cos t, (c/k) sin t √(μ − c²))` with
`k = √(a² − c²)`, `μ = b² + (a² − b²) sin² s` and `ν = c² + (b² − c²) sin² t` the confocal
coordinates; for `a > b > c > 0` its coordinate lines are the lines of curvature. -/
def confocalChart (a b c : ℝ) (α : Fin 2 → ℝ) : Vec3 :=
  WithLp.toLp 2 ![a / √(a ^ 2 - c ^ 2) * cos (α 0) * confocalX a b c (α 1),
    b * sin (α 0) * cos (α 1), c / √(a ^ 2 - c ^ 2) * sin (α 1) * confocalZ a b c (α 0)]

/-- **The patch of the confocal chart (MLS pp. 243–244, an open chart domain):** the parameters
with `cos t > 0`, which excludes the preimages of the four umbilics. -/
def confocalDomain : Set (Fin 2 → ℝ) := {α | 0 < cos (α 1)}

/-- **The defining function of the ellipsoid (MLS Exercise 19, p. 263, a surface as a level set):**
`h(x) = x₁²/a² + x₂²/b² + x₃²/c² − 1`, the solid being `{h ≤ 0}`. -/
def ellipsoidFunction (a b c : ℝ) (x : Vec3) : ℝ :=
  x 0 ^ 2 / a ^ 2 + x 1 ^ 2 / b ^ 2 + x 2 ^ 2 / c ^ 2 - 1

/-- **A normal field of the ellipsoid (MLS Exercise 19, p. 263):** `G(x) = (x₁/a², x₂/b², x₃/c²)`,
one half of the gradient of `ellipsoidFunction`. -/
def ellipsoidField (a b c : ℝ) (x : Vec3) : Vec3 :=
  WithLp.toLp 2 ![x 0 / a ^ 2, x 1 / b ^ 2, x 2 / c ^ 2]

variable {a b c : ℝ} {α : Fin 2 → ℝ}

/-! ### Supporting facts on the factors -/

private lemma sin_sq_le (x : ℝ) : sin x ^ 2 ≤ 1 := sin_sq_le_one x

private lemma confocalX_arg_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (t : ℝ) :
    0 < a ^ 2 - confocalNu b c t := by
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have := sin_sq_le t
  have := sq_nonneg (sin t)
  unfold confocalNu
  nlinarith

private lemma confocalZ_arg_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (s : ℝ) :
    0 < confocalMu a b s - c ^ 2 := by
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have := sq_nonneg (sin s)
  unfold confocalMu
  nlinarith

private lemma confocalX_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (t : ℝ) :
    0 < confocalX a b c t := Real.sqrt_pos.mpr (confocalX_arg_pos hcb hba hc t)

private lemma confocalZ_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (s : ℝ) :
    0 < confocalZ a b c s := Real.sqrt_pos.mpr (confocalZ_arg_pos hcb hba hc s)

private lemma confocalX_sq (hcb : c < b) (hba : b < a) (hc : 0 < c) (t : ℝ) :
    confocalX a b c t ^ 2 = a ^ 2 - c ^ 2 - (b ^ 2 - c ^ 2) * sin t ^ 2 := by
  rw [confocalX, sq_sqrt (confocalX_arg_pos hcb hba hc t).le, confocalNu]
  ring

private lemma confocalZ_sq (hcb : c < b) (hba : b < a) (hc : 0 < c) (s : ℝ) :
    confocalZ a b c s ^ 2 = b ^ 2 - c ^ 2 + (a ^ 2 - b ^ 2) * sin s ^ 2 := by
  rw [confocalZ, sq_sqrt (confocalZ_arg_pos hcb hba hc s).le, confocalMu]
  ring

private lemma k_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) : 0 < √(a ^ 2 - c ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith)

private lemma k_sq (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    √(a ^ 2 - c ^ 2) ^ 2 = a ^ 2 - c ^ 2 := sq_sqrt (by nlinarith)

private lemma hasDerivAt_confocalX (hcb : c < b) (hba : b < a) (hc : 0 < c) (t : ℝ) :
    HasDerivAt (confocalX a b c)
      (-(b ^ 2 - c ^ 2) * sin t * cos t / confocalX a b c t) t := by
  have hf : HasDerivAt (fun t => a ^ 2 - confocalNu b c t)
      (-((b ^ 2 - c ^ 2) * (2 * sin t * cos t))) t := by
    have h := (((hasDerivAt_sin t).pow 2).const_mul (b ^ 2 - c ^ 2)).const_add (c ^ 2)
    convert h.const_sub (a ^ 2) using 1
    · funext x
      simp [confocalNu]
    · norm_num
  have h := hf.sqrt (confocalX_arg_pos hcb hba hc t).ne'
  convert h using 1
  · funext y
    rfl
  · have hX : √(a ^ 2 - confocalNu b c t) ≠ 0 := (confocalX_pos hcb hba hc t).ne'
    change _ / √(a ^ 2 - confocalNu b c t) = _
    field_simp

private lemma hasDerivAt_confocalZ (hcb : c < b) (hba : b < a) (hc : 0 < c) (s : ℝ) :
    HasDerivAt (confocalZ a b c)
      ((a ^ 2 - b ^ 2) * sin s * cos s / confocalZ a b c s) s := by
  have hf : HasDerivAt (fun s => confocalMu a b s - c ^ 2)
      ((a ^ 2 - b ^ 2) * (2 * sin s * cos s)) s := by
    have h := ((((hasDerivAt_sin s).pow 2).const_mul (a ^ 2 - b ^ 2)).const_add (b ^ 2)).sub_const
      (c ^ 2)
    convert h using 1
    · funext x
      simp [confocalMu]
    · norm_num
  have h := hf.sqrt (confocalZ_arg_pos hcb hba hc s).ne'
  convert h using 1
  · funext y
    rfl
  · have hZ : √(confocalMu a b s - c ^ 2) ≠ 0 := (confocalZ_pos hcb hba hc s).ne'
    change _ / √(confocalMu a b s - c ^ 2) = _
    field_simp

private lemma contDiff_confocalX (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    ContDiff ℝ 2 (confocalX a b c) :=
  ContDiff.sqrt (by unfold confocalNu; fun_prop) fun t => (confocalX_arg_pos hcb hba hc t).ne'

private lemma contDiff_confocalZ (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    ContDiff ℝ 2 (confocalZ a b c) :=
  ContDiff.sqrt (by unfold confocalMu; fun_prop) fun s => (confocalZ_arg_pos hcb hba hc s).ne'

/-! ### Supporting lemmas on curves in `Vec3` (as for the surfaces of revolution) -/

private lemma contDiff_toLp {F : (Fin 2 → ℝ) → Fin 3 → ℝ} (h : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (fun α => (WithLp.toLp 2 (F α) : Vec3)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp h

private lemma hasDerivAt_toLp3 {f g k : ℝ → ℝ} {p q d x : ℝ} (hf : HasDerivAt f p x)
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

private lemma norm_toLp3 (p q d : ℝ) :
    ‖(WithLp.toLp 2 ![p, q, d] : Vec3)‖ = √(p ^ 2 + q ^ 2 + d ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

private lemma hasDerivAt_cos_add (x : ℝ) : HasDerivAt (fun s => cos (x + s)) (-sin x) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add x).cos

private lemma hasDerivAt_sin_add (x : ℝ) : HasDerivAt (fun s => sin (x + s)) (cos x) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add x).sin

private lemma hasDerivAt_add_of {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun s => f (x + s)) f' 0 :=
  HasDerivAt.comp_const_add x 0 (by simpa using hf)

/-! ### The chart and its partials -/

private lemma contDiff_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    ContDiff ℝ 2 (confocalChart a b c) := by
  have hX := contDiff_confocalX hcb hba hc
  have hZ := contDiff_confocalZ hcb hba hc
  refine contDiff_toLp (contDiff_pi.mpr fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

private lemma partialU_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    partialU (confocalChart a b c) α = WithLp.toLp 2
      ![a / √(a ^ 2 - c ^ 2) * -sin (α 0) * confocalX a b c (α 1), b * cos (α 0) * cos (α 1),
        c / √(a ^ 2 - c ^ 2) * sin (α 1) *
          ((a ^ 2 - b ^ 2) * sin (α 0) * cos (α 0) / confocalZ a b c (α 0))] := by
  refine partialU_eq_of_hasDerivAt ((contDiff_confocalChart hcb hba hc).differentiable
    (by simp) α) ?_
  have h := hasDerivAt_toLp3
    (((hasDerivAt_cos_add (α 0)).const_mul (a / √(a ^ 2 - c ^ 2))).mul_const
      (confocalX a b c (α 1)))
    (((hasDerivAt_sin_add (α 0)).const_mul b).mul_const (cos (α 1)))
    ((hasDerivAt_add_of (hasDerivAt_confocalZ hcb hba hc (α 0))).const_mul
      (c / √(a ^ 2 - c ^ 2) * sin (α 1)))
  convert h using 1
  funext s
  simp [confocalChart]

private lemma partialV_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    partialV (confocalChart a b c) α = WithLp.toLp 2
      ![a / √(a ^ 2 - c ^ 2) * cos (α 0) *
          (-(b ^ 2 - c ^ 2) * sin (α 1) * cos (α 1) / confocalX a b c (α 1)),
        b * sin (α 0) * -sin (α 1), c / √(a ^ 2 - c ^ 2) * cos (α 1) * confocalZ a b c (α 0)] := by
  refine partialV_eq_of_hasDerivAt ((contDiff_confocalChart hcb hba hc).differentiable
    (by simp) α) ?_
  have h := hasDerivAt_toLp3
    ((hasDerivAt_add_of (hasDerivAt_confocalX hcb hba hc (α 1))).const_mul
      (a / √(a ^ 2 - c ^ 2) * cos (α 0)))
    ((hasDerivAt_cos_add (α 1)).const_mul (b * sin (α 0)))
    (((hasDerivAt_sin_add (α 1)).const_mul (c / √(a ^ 2 - c ^ 2))).mul_const
      (confocalZ a b c (α 0)))
  convert h using 1
  funext s
  simp [confocalChart]

private lemma partialV_partialU_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (α : Fin 2 → ℝ) : partialV (partialU (confocalChart a b c)) α = WithLp.toLp 2
      ![a / √(a ^ 2 - c ^ 2) * -sin (α 0) *
          (-(b ^ 2 - c ^ 2) * sin (α 1) * cos (α 1) / confocalX a b c (α 1)),
        b * cos (α 0) * -sin (α 1),
        c / √(a ^ 2 - c ^ 2) * cos (α 1) *
          ((a ^ 2 - b ^ 2) * sin (α 0) * cos (α 0) / confocalZ a b c (α 0))] := by
  have hd := differentiableAt_partialU ((contDiff_confocalChart hcb hba hc).contDiffAt (x := α))
  rw [funext (partialU_confocalChart hcb hba hc)] at hd ⊢
  refine partialV_eq_of_hasDerivAt hd ?_
  have h := hasDerivAt_toLp3
    ((hasDerivAt_add_of (hasDerivAt_confocalX hcb hba hc (α 1))).const_mul
      (a / √(a ^ 2 - c ^ 2) * -sin (α 0)))
    ((hasDerivAt_cos_add (α 1)).const_mul (b * cos (α 0)))
    (((hasDerivAt_sin_add (α 1)).const_mul (c / √(a ^ 2 - c ^ 2))).mul_const
      ((a ^ 2 - b ^ 2) * sin (α 0) * cos (α 0) / confocalZ a b c (α 0)))
  convert h using 1
  funext s
  simp

/-! ### Algebraic identities of the chart -/

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_orth {a b c k X Z S C P Q : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) :
    (a / k * -S * X) * (a / k * C * (-(b^2-c^2) * P * Q / X)) + (b * C * Q) * (b * S * -P) +
      (c / k * P * ((a^2-b^2) * S * C / Z)) * (c / k * Q * Z) = 0 := by
  field_simp
  linear_combination (-C*P*Q*S*b^2) * hk2

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_normU {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hZ : Z ≠ 0) (hm0 : m - c ^ 2 ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * -S * X) ^ 2 + (b * C * Q) ^ 2 + (c / k * P * ((a^2-b^2) * S * C / Z)) ^ 2 =
      m * (m - n) / (m - c ^ 2) := by
  field_simp
  linear_combination (-S^2*Z^2*a^2*(c^2 - m)) * hX2 + (-C^2*Q^2*b^2*c^2*k^2 + C^2*Q^2*b^2*k^2*m - S^2*a^4*c^2 + S^2*a^4*m + S^2*a^2*c^2*n - S^2*a^2*m*n - k^2*m^2 + k^2*m*n) * hZ2 + ((c^2 - m)*(C^2*Q^2*b^2*c^2 - C^2*Q^2*b^2*m + m^2 - m*n)) * hk2 + (C^2*P^2*S^2*a^4*c^2 - 2*C^2*P^2*S^2*a^2*b^2*c^2 + C^2*P^2*S^2*b^4*c^2 + C^2*Q^2*S^2*a^4*b^2 - C^2*Q^2*S^2*a^2*b^4 - C^2*Q^2*S^2*a^2*b^2*c^2 + C^2*Q^2*S^2*b^4*c^2 + C^2*Q^2*a^2*b^4 - 2*C^2*Q^2*a^2*b^2*c^2 + C^2*Q^2*a^2*b^2*m - C^2*Q^2*b^4*c^2 + 2*C^2*Q^2*b^2*c^4 - C^2*Q^2*b^2*c^2*m + S^4*a^4*b^2 + S^4*a^4*c^2 - S^4*a^4*n - S^4*a^2*b^4 - 2*S^4*a^2*b^2*c^2 + S^4*a^2*b^2*n + S^4*b^4*c^2 - S^2*a^4*b^2 - S^2*a^4*c^2 + S^2*a^4*n + 2*S^2*a^2*b^4 + S^2*a^2*b^2*c^2 + S^2*a^2*b^2*m - 2*S^2*a^2*b^2*n - S^2*a^2*c^4 + S^2*a^2*c^2*m + S^2*a^2*c^2*n - S^2*a^2*m*n - 2*S^2*b^4*c^2 + S^2*b^2*c^4 - S^2*b^2*c^2*m + S^2*b^2*c^2*n - a^2*b^4 + a^2*b^2*c^2 - a^2*b^2*m + a^2*b^2*n + a^2*c^2*m - a^2*c^2*n - a^2*m^2 + a^2*m*n + b^4*c^2 - b^2*c^4 + b^2*c^2*m - b^2*c^2*n - c^4*m + c^4*n + c^2*m^2 - c^2*m*n) * hm + (-(S - 1)*(S + 1)*(S^2*a^2 - S^2*b^2 + b^2 - c^2)*(S^2*a^4 - S^2*a^2*b^2 + a^2*b^2 - b^2*c^2)) * hn + ((S^2*a^2 - S^2*b^2 + b^2 - c^2)*(P^2*S^2*a^4*c^2 - 2*P^2*S^2*a^2*b^2*c^2 + P^2*S^2*b^4*c^2 + Q^2*S^2*a^4*b^2 - Q^2*S^2*a^2*b^4 - Q^2*S^2*a^2*b^2*c^2 + Q^2*S^2*b^4*c^2 + Q^2*a^2*b^4 - Q^2*a^2*b^2*c^2 - Q^2*b^4*c^2 + Q^2*b^2*c^4)) * hS + (-b^2*(S - 1)*(S + 1)*(a - c)*(a + c)*(S^2*a^2 - S^2*b^2 + b^2 - c^2)^2) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_normV {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hn0 : a ^ 2 - n ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * C * (-(b^2-c^2) * P * Q / X)) ^ 2 + (b * S * -P) ^ 2 + (c / k * Q * Z) ^ 2 =
      n * (m - n) / (a ^ 2 - n) := by
  field_simp
  linear_combination (P^2*S^2*a^2*b^2*k^2 - P^2*S^2*b^2*k^2*n + Q^2*Z^2*a^2*c^2 - Q^2*Z^2*c^2*n - k^2*m*n + k^2*n^2) * hX2 + (Q^2*c^2*(a^2 - n)^2) * hZ2 + ((a^2 - n)*(P^2*S^2*a^2*b^2 - P^2*S^2*b^2*n - m*n + n^2)) * hk2 + ((a^2 - n)*(Q^2*a^2*c^2 - Q^2*c^2*n - a^2*n + c^2*n)) * hm + (-C^2*P^2*Q^2*a^2*b^4 + 2*C^2*P^2*Q^2*a^2*b^2*c^2 - C^2*P^2*Q^2*a^2*c^4 + P^4*S^2*a^2*b^4 - P^4*S^2*a^2*b^2*c^2 - P^4*S^2*b^4*c^2 + P^4*S^2*b^2*c^4 - P^4*a^2*b^4 + 2*P^4*a^2*b^2*c^2 - P^4*a^2*c^4 + P^4*b^4*c^2 - 2*P^4*b^2*c^4 + P^4*c^6 + P^2*Q^2*S^2*a^2*b^2*c^2 - P^2*Q^2*S^2*a^2*c^4 - P^2*Q^2*S^2*b^4*c^2 + P^2*Q^2*S^2*b^2*c^4 + P^2*Q^2*b^4*c^2 - 2*P^2*Q^2*b^2*c^4 + P^2*Q^2*c^6 - P^2*S^2*a^4*b^2 - P^2*S^2*a^4*c^2 - P^2*S^2*a^2*b^4 + 3*P^2*S^2*a^2*b^2*c^2 + P^2*S^2*a^2*b^2*n + P^2*S^2*a^2*c^4 + P^2*S^2*b^4*c^2 - 2*P^2*S^2*b^2*c^4 - P^2*S^2*b^2*c^2*n + P^2*a^4*b^2 - P^2*a^4*c^2 + P^2*a^2*b^4 - 4*P^2*a^2*b^2*c^2 - P^2*a^2*b^2*n + 3*P^2*a^2*c^4 + P^2*a^2*c^2*n - P^2*b^4*c^2 + 3*P^2*b^2*c^4 + P^2*b^2*c^2*n - 2*P^2*c^6 - P^2*c^4*n - 2*Q^2*S^2*a^4*c^2 + 2*Q^2*S^2*a^2*b^2*c^2 + Q^2*S^2*a^2*c^4 + Q^2*S^2*a^2*c^2*n - Q^2*S^2*b^2*c^4 - Q^2*S^2*b^2*c^2*n - 2*Q^2*a^2*b^2*c^2 + 2*Q^2*a^2*c^4 + Q^2*b^2*c^4 + Q^2*b^2*c^2*n - Q^2*c^6 - Q^2*c^4*n - S^2*a^6 + S^2*a^4*b^2 + 2*S^2*a^4*c^2 + S^2*a^4*n - 2*S^2*a^2*b^2*c^2 - S^2*a^2*b^2*n - S^2*a^2*c^4 - S^2*a^2*c^2*n + S^2*b^2*c^4 + S^2*b^2*c^2*n - a^4*b^2 + a^4*c^2 + a^4*n + 2*a^2*b^2*c^2 + a^2*b^2*n - 2*a^2*c^4 - 2*a^2*c^2*n - a^2*n^2 - b^2*c^4 - b^2*c^2*n + c^6 + c^4*n + c^2*n^2) * hn + (P^2*Q^2*a^2*(b - c)^2*(b + c)^2*(-P^2*b^2 + P^2*c^2 + a^2 - c^2)) * hS + ((a - c)*(a + c)*(-P^2*b^2 + P^2*c^2 + a^2 - c^2)*(-P^2*S^2*b^4 + P^2*S^2*b^2*c^2 + P^2*b^4 - 2*P^2*b^2*c^2 + P^2*c^4 + S^2*a^2*c^2 - S^2*b^2*c^2 + b^2*c^2 - c^4)) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_surface {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * C * X) ^ 2 / a ^ 2 + (b * S * Q) ^ 2 / b ^ 2 + (c / k * P * Z) ^ 2 / c ^ 2 - 1 = 0 := by
  field_simp
  linear_combination (C^2) * hX2 + (P^2) * hZ2 + ((Q*S - 1)*(Q*S + 1)) * hk2 + (P^2) * hm + (-C^2) * hn + (-P^2*b^2 + P^2*c^2 + a^2 - c^2) * hS + (S^2*(a - c)*(a + c)) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_field_sq {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * C * X / a ^ 2) ^ 2 + (b * S * Q / b ^ 2) ^ 2 + (c / k * P * Z / c ^ 2) ^ 2 =
      m * n / (a ^ 2 * b ^ 2 * c ^ 2) := by
  field_simp
  linear_combination (C^2*b^2*c^2) * hX2 + (P^2*a^2*b^2) * hZ2 + (Q^2*S^2*a^2*c^2 - m*n) * hk2 + (P^2*a^2*b^2 - a^2*n + c^2*n) * hm + (-C^2*b^2*c^2 - S^2*a^4 + S^2*a^2*b^2 + S^2*a^2*c^2 - S^2*b^2*c^2 - a^2*b^2 + b^2*c^2) * hn + (b^2*c^2*(-P^2*b^2 + P^2*c^2 + a^2 - c^2)) * hS + (S^2*a^2*c^2*(a - c)*(a + c)) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_cross0 {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hZ2 : Z ^ 2 = m - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hP : P ^ 2 + Q ^ 2 = 1) :
    (b * C * Q) * (c / k * Q * Z) - (c / k * P * ((a^2-b^2) * S * C / Z)) * (b * S * -P) =
      a * b * c * (m - n) / (X * Z) * (a / k * C * X / a ^ 2) := by
  field_simp
  linear_combination (C*Q^2) * hZ2 + (C*(Q - 1)*(Q + 1)) * hm + (C) * hn + (C*(S^2*a^2 - S^2*b^2 + b^2 - c^2)) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_cross1 {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) :
    (c / k * P * ((a^2-b^2) * S * C / Z)) * (a / k * C * (-(b^2-c^2) * P * Q / X)) -
      (a / k * -S * X) * (c / k * Q * Z) =
      a * b * c * (m - n) / (X * Z) * (b * S * Q / b ^ 2) := by
  field_simp
  linear_combination (Q*S*Z^2) * hX2 + (Q*S*(a^2 - n)) * hZ2 + (-Q*S*(m - n)) * hk2 + (Q*S*(c^2 - n)) * hm + (-Q*S*(S - 1)*(S + 1)*(a - b)*(a + b)) * hn + (-P^2*Q*S*(a - b)*(a + b)*(b - c)*(b + c)) * hS

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_cross2 {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * -S * X) * (b * S * -P) - (b * C * Q) * (a / k * C * (-(b^2-c^2) * P * Q / X)) =
      a * b * c * (m - n) / (X * Z) * (c / k * P * Z / c ^ 2) := by
  field_simp
  linear_combination (P*S^2) * hX2 + (-P) * hm + (-P*(S - 1)*(S + 1)) * hn + (P*Q^2*(b - c)*(b + c)) * hS + (-P*(S - 1)*(S + 1)*(b - c)*(b + c)) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_qUU {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hZ : Z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hm0 : m - c ^ 2 ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * -S * X) * ((a / k * -S * X) / a ^ 2) + (b * C * Q) * ((b * C * Q) / b ^ 2) +
      (c / k * P * ((a^2-b^2) * S * C / Z)) * ((c / k * P * ((a^2-b^2) * S * C / Z)) / c ^ 2) =
      (m - n) / (m - c ^ 2) := by
  field_simp
  linear_combination (-S^2*Z^2*(c^2 - m)) * hX2 + (-C^2*Q^2*c^2*k^2 + C^2*Q^2*k^2*m - S^2*a^2*c^2 + S^2*a^2*m + S^2*c^2*n - S^2*m*n - k^2*m + k^2*n) * hZ2 + ((c^2 - m)*(C^2*Q^2*c^2 - C^2*Q^2*m + m - n)) * hk2 + (C^2*P^2*S^2*a^4 - 2*C^2*P^2*S^2*a^2*b^2 + C^2*P^2*S^2*b^4 + C^2*Q^2*S^2*a^4 - C^2*Q^2*S^2*a^2*b^2 - C^2*Q^2*S^2*a^2*c^2 + C^2*Q^2*S^2*b^2*c^2 + C^2*Q^2*a^2*b^2 - 2*C^2*Q^2*a^2*c^2 + C^2*Q^2*a^2*m - C^2*Q^2*b^2*c^2 + 2*C^2*Q^2*c^4 - C^2*Q^2*c^2*m + S^4*a^4 - S^4*a^2*b^2 - S^4*a^2*n + S^4*b^2*n - S^2*a^4 + 2*S^2*a^2*b^2 - S^2*a^2*c^2 + S^2*a^2*m - S^2*b^2*c^2 - S^2*b^2*n + 2*S^2*c^2*n - S^2*m*n - a^2*b^2 + a^2*c^2 - a^2*m + a^2*n + b^2*c^2 - c^4 + c^2*m - c^2*n) * hm + (-(S - 1)*(S + 1)*(S^2*a^2 - S^2*b^2 + a^2 - c^2)*(S^2*a^2 - S^2*b^2 + b^2 - c^2)) * hn + ((S^2*a^2 - S^2*b^2 + b^2 - c^2)*(P^2*S^2*a^4 - 2*P^2*S^2*a^2*b^2 + P^2*S^2*b^4 + Q^2*S^2*a^4 - Q^2*S^2*a^2*b^2 - Q^2*S^2*a^2*c^2 + Q^2*S^2*b^2*c^2 + Q^2*a^2*b^2 - Q^2*a^2*c^2 - Q^2*b^2*c^2 + Q^2*c^4)) * hS + (-(S - 1)*(S + 1)*(a - c)*(a + c)*(S^2*a^2 - S^2*b^2 + b^2 - c^2)^2) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_qVV {a b c k X Z S C P Q m n : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hn0 : a ^ 2 - n ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hS : S ^ 2 + C ^ 2 = 1) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * C * (-(b^2-c^2) * P * Q / X)) * ((a / k * C * (-(b^2-c^2) * P * Q / X)) / a ^ 2) +
      (b * S * -P) * ((b * S * -P) / b ^ 2) + (c / k * Q * Z) * ((c / k * Q * Z) / c ^ 2) =
      (m - n) / (a ^ 2 - n) := by
  field_simp
  linear_combination (P^2*S^2*a^2*k^2 - P^2*S^2*k^2*n + Q^2*Z^2*a^2 - Q^2*Z^2*n - k^2*m + k^2*n) * hX2 + (Q^2*(a^2 - n)^2) * hZ2 + ((a^2 - n)*(P^2*S^2*a^2 - P^2*S^2*n - m + n)) * hk2 + ((a^2 - n)*(Q^2*a^2 - Q^2*n - a^2 + c^2)) * hm + (-C^2*P^2*Q^2*b^4 + 2*C^2*P^2*Q^2*b^2*c^2 - C^2*P^2*Q^2*c^4 + P^4*S^2*a^2*b^2 - P^4*S^2*a^2*c^2 - P^4*S^2*b^2*c^2 + P^4*S^2*c^4 + P^2*Q^2*S^2*a^2*b^2 - P^2*Q^2*S^2*a^2*c^2 - P^2*Q^2*S^2*b^4 + P^2*Q^2*S^2*b^2*c^2 + P^2*Q^2*b^4 - 2*P^2*Q^2*b^2*c^2 + P^2*Q^2*c^4 - 2*P^2*S^2*a^4 + 3*P^2*S^2*a^2*c^2 + P^2*S^2*a^2*n - P^2*S^2*c^4 - P^2*S^2*c^2*n - P^2*a^2*b^2 + P^2*a^2*c^2 + P^2*b^2*c^2 - P^2*c^4 - 2*Q^2*S^2*a^4 + 2*Q^2*S^2*a^2*b^2 + Q^2*S^2*a^2*c^2 + Q^2*S^2*a^2*n - Q^2*S^2*b^2*c^2 - Q^2*S^2*b^2*n - 2*Q^2*a^2*b^2 + 2*Q^2*a^2*c^2 + Q^2*b^2*c^2 + Q^2*b^2*n - Q^2*c^4 - Q^2*c^2*n + S^2*a^4 - S^2*a^2*b^2 - S^2*a^2*c^2 + S^2*b^2*c^2 + a^4 + a^2*b^2 - 2*a^2*c^2 - a^2*n - b^2*c^2 + c^4 + c^2*n) * hn + (P^2*Q^2*(b - c)^2*(b + c)^2*(-P^2*b^2 + P^2*c^2 + a^2 - c^2)) * hS + ((a - c)*(a + c)*(-P^2*b^2 + P^2*c^2 + a^2 - c^2)*(-P^2*S^2*b^2 + P^2*S^2*c^2 + S^2*a^2 - S^2*b^2 + b^2 - c^2)) * hP

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_qUV {a b c k X Z S C P Q : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) :
    (a / k * -S * X) * ((a / k * C * (-(b^2-c^2) * P * Q / X)) / a ^ 2) +
      (b * C * Q) * ((b * S * -P) / b ^ 2) +
      (c / k * P * ((a^2-b^2) * S * C / Z)) * ((c / k * Q * Z) / c ^ 2) = 0 := by
  field_simp
  linear_combination (-C*P*Q*S) * hk2

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_uUV {a b c k X Z S C P Q m : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (hm0 : m - c ^ 2 ≠ 0) (hZ2 : Z ^ 2 = m - c ^ 2) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hm : m = b ^ 2 + (a ^ 2 - b ^ 2) * S ^ 2) (hS : S ^ 2 + C ^ 2 = 1) :
    (a / k * -S * X) * (a / k * -S * (-(b^2-c^2) * P * Q / X)) + (b * C * Q) * (b * C * -P) +
      (c / k * P * ((a^2-b^2) * S * C / Z)) * (c / k * Q * ((a^2-b^2) * S * C / Z)) =
      -(P * Q * (b ^ 2 - c ^ 2) * m / (m - c ^ 2)) := by
  field_simp
  linear_combination (P*Q*(C^2*b^2*c^2*k^2 - C^2*b^2*k^2*m + S^2*a^2*b^2*c^2 - S^2*a^2*b^2*m - S^2*a^2*c^4 + S^2*a^2*c^2*m + b^2*k^2*m - c^2*k^2*m)) * hZ2 + (-P*Q*(c^2 - m)*(C^2*b^2*c^2 - C^2*b^2*m + b^2*m - c^2*m)) * hk2 + (-P*Q*(C^2*S^2*a^4*b^2 - C^2*S^2*a^4*c^2 - C^2*S^2*a^2*b^4 + C^2*S^2*a^2*b^2*c^2 + C^2*a^2*b^4 - 2*C^2*a^2*b^2*c^2 + C^2*a^2*b^2*m - C^2*b^4*c^2 + 2*C^2*b^2*c^4 - C^2*b^2*c^2*m + S^4*a^4*b^2 - S^4*a^4*c^2 - S^4*a^2*b^4 + S^4*a^2*b^2*c^2 - S^2*a^4*b^2 + S^2*a^4*c^2 + 2*S^2*a^2*b^4 - 3*S^2*a^2*b^2*c^2 + S^2*a^2*b^2*m + S^2*a^2*c^4 - S^2*a^2*c^2*m - S^2*b^4*c^2 + S^2*b^2*c^4 - a^2*b^4 + 2*a^2*b^2*c^2 - a^2*b^2*m - a^2*c^4 + a^2*c^2*m + b^4*c^2 - 2*b^2*c^4 + b^2*c^2*m + c^6 - c^4*m)) * hm + (-P*Q*(b - c)*(b + c)*(S^2*a^2 - S^2*b^2 + b^2 - c^2)*(S^2*a^4 - S^2*a^2*b^2 + a^2*b^2 - b^2*c^2)) * hS

/-- Supporting algebraic identity for the confocal chart of MLS Exercises 14–15, p. 262. -/
private lemma alg_vUV {a b c k X Z S C P Q n : ℝ} (hk0 : k ≠ 0) (hX : X ≠ 0) (hZ : Z ≠ 0) (hn0 : a ^ 2 - n ≠ 0) (hX2 : X ^ 2 = a ^ 2 - n) (hk2 : k ^ 2 = a ^ 2 - c ^ 2) (hn : n = c ^ 2 + (b ^ 2 - c ^ 2) * P ^ 2) (hP : P ^ 2 + Q ^ 2 = 1) :
    (a / k * C * (-(b^2-c^2) * P * Q / X)) * (a / k * -S * (-(b^2-c^2) * P * Q / X)) +
      (b * S * -P) * (b * C * -P) + (c / k * Q * Z) * (c / k * Q * ((a^2-b^2) * S * C / Z)) =
      S * C * (a ^ 2 - b ^ 2) * n / (a ^ 2 - n) := by
  field_simp
  linear_combination (C*S*(P^2*a^2*b^2*k^2 - P^2*b^2*k^2*n + Q^2*a^4*c^2 - Q^2*a^2*b^2*c^2 - Q^2*a^2*c^2*n + Q^2*b^2*c^2*n - a^2*k^2*n + b^2*k^2*n)) * hX2 + (C*S*(a^2 - n)*(P^2*a^2*b^2 - P^2*b^2*n - a^2*n + b^2*n)) * hk2 + (-C*S*(-P^4*a^2*b^4 + P^4*a^2*b^2*c^2 + P^4*b^4*c^2 - P^4*b^2*c^4 - P^2*Q^2*a^2*b^4 + P^2*Q^2*a^2*b^2*c^2 + P^2*Q^2*b^4*c^2 - P^2*Q^2*b^2*c^4 + P^2*a^4*b^2 + P^2*a^4*c^2 + P^2*a^2*b^4 - 3*P^2*a^2*b^2*c^2 - P^2*a^2*b^2*n - P^2*a^2*c^4 - P^2*b^4*c^2 + 2*P^2*b^2*c^4 + P^2*b^2*c^2*n + 2*Q^2*a^4*c^2 - 2*Q^2*a^2*b^2*c^2 - Q^2*a^2*c^4 - Q^2*a^2*c^2*n + Q^2*b^2*c^4 + Q^2*b^2*c^2*n + a^6 - a^4*b^2 - 2*a^4*c^2 - a^4*n + 2*a^2*b^2*c^2 + a^2*b^2*n + a^2*c^4 + a^2*c^2*n - b^2*c^4 - b^2*c^2*n)) * hn + (C*S*(a - c)*(a + c)*(-P^2*b^2 + P^2*c^2 + a^2 - c^2)*(-P^2*b^4 + P^2*b^2*c^2 + a^2*c^2 - b^2*c^2)) * hP

/-! ### Orthogonality, the metric tensor and the normal -/

private lemma confocal_rels (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    confocalX a b c (α 1) ^ 2 = a ^ 2 - confocalNu b c (α 1) ∧
      confocalZ a b c (α 0) ^ 2 = confocalMu a b (α 0) - c ^ 2 :=
  ⟨sq_sqrt (confocalX_arg_pos hcb hba hc _).le, sq_sqrt (confocalZ_arg_pos hcb hba hc _).le⟩

private lemma mu_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (s : ℝ) : 0 < confocalMu a b s := by
  have h2 : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  have hb : 0 < b ^ 2 := by nlinarith
  unfold confocalMu
  nlinarith [mul_nonneg h2 (sq_nonneg (sin s))]

private lemma nu_pos (hc : 0 < c) (hcb : c < b) (t : ℝ) : 0 < confocalNu b c t := by
  have h2 : 0 ≤ b ^ 2 - c ^ 2 := by nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  unfold confocalNu
  nlinarith [mul_nonneg h2 (sq_nonneg (sin t))]

private lemma mu_sub_nu_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (hα : 0 < cos (α 1)) :
    0 < confocalMu a b (α 0) - confocalNu b c (α 1) := by
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have e : confocalMu a b (α 0) - confocalNu b c (α 1) =
      (b ^ 2 - c ^ 2) * cos (α 1) ^ 2 + (a ^ 2 - b ^ 2) * sin (α 0) ^ 2 := by
    unfold confocalMu confocalNu
    linear_combination -(b ^ 2 - c ^ 2) * sin_sq_add_cos_sq (α 1)
  rw [e]
  have := pow_pos hα 2
  nlinarith [sq_nonneg (sin (α 0))]

/-- **The confocal chart is orthogonal at every point (MLS p. 244, "A coordinate chart is an
orthogonal coordinate chart if `c_u` and `c_v` are orthogonal"; Exercise 15(a), p. 262):** for
`a > b > c > 0`, `c_sᵀ c_t = 0` on all of `ℝ²`. -/
theorem isOrthogonalAt_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    IsOrthogonalAt (confocalChart a b c) α := by
  rw [IsOrthogonalAt, partialU_confocalChart hcb hba hc, partialV_confocalChart hcb hba hc,
    EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, star_trivial]
  linear_combination alg_orth (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1))
      (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne'
    (confocalZ_pos hcb hba hc (α 0)).ne' (k_sq hcb hba hc)

private lemma norm_partialU_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (α : Fin 2 → ℝ) : ‖partialU (confocalChart a b c) α‖ =
      √(confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
        (confocalMu a b (α 0) - c ^ 2)) := by
  rw [partialU_confocalChart hcb hba hc, norm_toLp3]
  congr 1
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  linear_combination alg_normU (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
      (k_pos hcb hba hc).ne' (confocalZ_pos hcb hba hc (α 0)).ne'
    (confocalZ_arg_pos hcb hba hc (α 0)).ne' hX2 hZ2 (k_sq hcb hba hc) rfl rfl
    (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1))

private lemma norm_partialV_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (α : Fin 2 → ℝ) : ‖partialV (confocalChart a b c) α‖ =
      √(confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
        (a ^ 2 - confocalNu b c (α 1))) := by
  rw [partialV_confocalChart hcb hba hc, norm_toLp3]
  congr 1
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  linear_combination alg_normV (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
      (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne'
    (confocalX_arg_pos hcb hba hc (α 1)).ne' hX2 hZ2 (k_sq hcb hba hc) rfl rfl
    (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1))

private lemma normU_arg_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (hα : 0 < cos (α 1)) :
    0 < confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
      (confocalMu a b (α 0) - c ^ 2) :=
  div_pos (mul_pos (mu_pos hcb hba hc _) (mu_sub_nu_pos hcb hba hc hα)) (confocalZ_arg_pos hcb hba hc _)

private lemma normV_arg_pos (hcb : c < b) (hba : b < a) (hc : 0 < c) (hα : 0 < cos (α 1)) :
    0 < confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
      (a ^ 2 - confocalNu b c (α 1)) :=
  div_pos (mul_pos (nu_pos hc hcb _) (mu_sub_nu_pos hcb hba hc hα)) (confocalX_arg_pos hcb hba hc _)

/-- **The patch of the confocal chart is open (MLS p. 243, an open chart domain).** -/
theorem isOpen_confocalDomain : IsOpen confocalDomain :=
  isOpen_lt continuous_const (continuous_cos.comp (continuous_apply 1))

/-- **The confocal chart is an orthogonal chart on its patch (MLS pp. 243–244; Exercise 15(a),
p. 262):** for `a > b > c > 0`, `IsOrthogonalChartOn (confocalChart a b c) {cos t > 0}`. -/
theorem isOrthogonalChartOn_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    IsOrthogonalChartOn (confocalChart a b c) confocalDomain := by
  refine IsOrthogonalChartOn.of_ne_zero isOpen_confocalDomain
    (contDiff_confocalChart hcb hba hc).contDiffOn
    (fun α _ => isOrthogonalAt_confocalChart hcb hba hc α) (fun α hα => ?_) (fun α hα => ?_)
  · rw [← norm_ne_zero_iff, norm_partialU_confocalChart hcb hba hc]
    exact (Real.sqrt_pos.mpr (normU_arg_pos hcb hba hc hα)).ne'
  · rw [← norm_ne_zero_iff, norm_partialV_confocalChart hcb hba hc]
    exact (Real.sqrt_pos.mpr (normV_arg_pos hcb hba hc hα)).ne'

private lemma ellipsoidField_confocalChart (α : Fin 2 → ℝ) :
    ellipsoidField a b c (confocalChart a b c α) = WithLp.toLp 2
      ![a / √(a ^ 2 - c ^ 2) * cos (α 0) * confocalX a b c (α 1) / a ^ 2,
        b * sin (α 0) * cos (α 1) / b ^ 2,
        c / √(a ^ 2 - c ^ 2) * sin (α 1) * confocalZ a b c (α 0) / c ^ 2] := by
  simp [ellipsoidField, confocalChart]

private lemma norm_ellipsoidField_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (α : Fin 2 → ℝ) : ‖ellipsoidField a b c (confocalChart a b c α)‖ =
      √(confocalMu a b (α 0) * confocalNu b c (α 1)) / (a * b * c) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  rw [ellipsoidField_confocalChart, norm_toLp3]
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  rw [alg_field_sq (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
      (k_pos hcb hba hc).ne' ha.ne' hb.ne' hc.ne' hX2 hZ2 (k_sq hcb hba hc) rfl rfl
    (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1)), Real.sqrt_div' _ (by positivity),
    show a ^ 2 * b ^ 2 * c ^ 2 = (a * b * c) ^ 2 by ring, Real.sqrt_sq (by positivity)]

private lemma cross_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    Vec3.cross (partialU (confocalChart a b c) α) (partialV (confocalChart a b c) α) =
      (a * b * c * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
        (confocalX a b c (α 1) * confocalZ a b c (α 0))) •
        ellipsoidField a b c (confocalChart a b c α) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hk0 := (k_pos hcb hba hc).ne'
  have hX0 := (confocalX_pos hcb hba hc (α 1)).ne'
  have hZ0 := (confocalZ_pos hcb hba hc (α 0)).ne'
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  rw [partialU_confocalChart hcb hba hc, partialV_confocalChart hcb hba hc,
    ellipsoidField_confocalChart]
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [Vec3.cross, cross_apply]
    linear_combination alg_cross0 (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
      hk0 hX0 hZ0 ha.ne' hb.ne' hc.ne' hZ2 rfl rfl
      (sin_sq_add_cos_sq (α 1))
  · simp [Vec3.cross, cross_apply]
    linear_combination alg_cross1 (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
      hk0 hX0 hZ0 ha.ne' hb.ne' hc.ne' hX2 hZ2 (k_sq hcb hba hc) rfl
      rfl (sin_sq_add_cos_sq (α 0))
  · simp [Vec3.cross, cross_apply]
    linear_combination alg_cross2 (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2)) (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0)) (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
      hk0 hX0 hZ0 ha.ne' hb.ne' hc.ne' hX2 rfl rfl
      (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1))

/-- **The Gauss normal of the confocal chart is the normalized field `(x/a², y/b², z/c²)` (MLS eq.
(5.19), p. 245; Exercise 19, p. 263):** on the patch `{cos t > 0}`, `c_s × c_t` is a positive
multiple of `G(c) = (x/a², y/b², z/c²)`, so `n = G(c)/‖G(c)‖`, the outward unit normal of the
level set. -/
theorem gaussNormal_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (hα : α ∈ confocalDomain) :
    gaussNormal (confocalChart a b c) α =
      normalizedField (ellipsoidField a b c) (confocalChart a b c α) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hl : 0 < a * b * c * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
      (confocalX a b c (α 1) * confocalZ a b c (α 0)) :=
    div_pos (mul_pos (by positivity) (mu_sub_nu_pos hcb hba hc hα))
      (mul_pos (confocalX_pos hcb hba hc _) (confocalZ_pos hcb hba hc _))
  have hG : 0 < ‖ellipsoidField a b c (confocalChart a b c α)‖ := by
    rw [norm_ellipsoidField_confocalChart hcb hba hc]
    exact div_pos (Real.sqrt_pos.mpr (mul_pos (mu_pos hcb hba hc _) (nu_pos hc hcb _)))
      (by positivity)
  rw [gaussNormal, cross_confocalChart hcb hba hc, norm_smul, Real.norm_of_nonneg hl.le,
    smul_smul, normalizedField]
  congr 1
  rw [mul_inv, mul_right_comm, inv_mul_cancel₀ hl.ne', one_mul]

/-! ### The regular set and the excluded parameters -/

private lemma mu_sub_nu_pos_iff (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    0 < confocalMu a b (α 0) - confocalNu b c (α 1) ↔ sin (α 0) ≠ 0 ∨ cos (α 1) ≠ 0 := by
  have h1 : c ^ 2 < b ^ 2 := by nlinarith
  have h2 : b ^ 2 < a ^ 2 := by nlinarith
  have e : confocalMu a b (α 0) - confocalNu b c (α 1) =
      (b ^ 2 - c ^ 2) * cos (α 1) ^ 2 + (a ^ 2 - b ^ 2) * sin (α 0) ^ 2 := by
    unfold confocalMu confocalNu
    linear_combination -(b ^ 2 - c ^ 2) * sin_sq_add_cos_sq (α 1)
  rw [e]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    rw [hn.1, hn.2] at h
    norm_num at h
  · rintro (h | h)
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (cos (α 1))]
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (sin (α 0))]

/-- **Where the confocal chart is regular (MLS p. 243, condition 3 of a regular surface):** for
`a > b > c > 0`, `c_s ≠ 0` and `c_t ≠ 0` exactly when `sin s ≠ 0` or `cos t ≠ 0`; the excluded
parameters `sin s = 0`, `cos t = 0` are where `μ = ν = b²`. -/
theorem partial_confocalChart_ne_zero_iff (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (α : Fin 2 → ℝ) :
    (partialU (confocalChart a b c) α ≠ 0 ∧ partialV (confocalChart a b c) α ≠ 0) ↔
      (sin (α 0) ≠ 0 ∨ cos (α 1) ≠ 0) := by
  have hu : partialU (confocalChart a b c) α ≠ 0 ↔
      0 < confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
        (confocalMu a b (α 0) - c ^ 2) := by
    rw [← norm_ne_zero_iff, norm_partialU_confocalChart hcb hba hc, Real.sqrt_ne_zero']
  have hv : partialV (confocalChart a b c) α ≠ 0 ↔
      0 < confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
        (a ^ 2 - confocalNu b c (α 1)) := by
    rw [← norm_ne_zero_iff, norm_partialV_confocalChart hcb hba hc, Real.sqrt_ne_zero']
  rw [← mu_sub_nu_pos_iff hcb hba hc α, hu, hv]
  have hm := mu_pos hcb hba hc (α 0)
  have hn := nu_pos hc hcb (α 1)
  have hmc := confocalZ_arg_pos hcb hba hc (α 0)
  have hac := confocalX_arg_pos hcb hba hc (α 1)
  constructor
  · intro h
    have := h.1
    rw [div_pos_iff_of_pos_right hmc] at this
    exact pos_of_mul_pos_right this hm.le
  · intro h
    exact ⟨div_pos (mul_pos hm h) hmc, div_pos (mul_pos hn h) hac⟩

/-- **The confocal chart is an orthogonal chart on its whole regular set (MLS pp. 243–244):** for
`a > b > c > 0`, `IsOrthogonalChartOn (confocalChart a b c) {sin s ≠ 0 ∨ cos t ≠ 0}`; the
complement is the set of parameters `sin s = 0`, `cos t = 0`. -/
theorem isOrthogonalChartOn_confocalChart_regular (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    IsOrthogonalChartOn (confocalChart a b c) {α | sin (α 0) ≠ 0 ∨ cos (α 1) ≠ 0} := by
  have hU : IsOpen {α : Fin 2 → ℝ | sin (α 0) ≠ 0 ∨ cos (α 1) ≠ 0} :=
    (isOpen_ne_fun (continuous_sin.comp (continuous_apply 0)) continuous_const).union
      (isOpen_ne_fun (continuous_cos.comp (continuous_apply 1)) continuous_const)
  exact IsOrthogonalChartOn.of_ne_zero hU (contDiff_confocalChart hcb hba hc).contDiffOn
    (fun α _ => isOrthogonalAt_confocalChart hcb hba hc α)
    (fun α hα => ((partial_confocalChart_ne_zero_iff hcb hba hc α).mpr hα).1)
    (fun α hα => ((partial_confocalChart_ne_zero_iff hcb hba hc α).mpr hα).2)

/-- **The images of the excluded parameters (MLS Exercise 14, p. 262):** where `sin s = 0` and
`cos t = 0`, the chart point is `(x, 0, z)` with `x² = a² (a² − b²)/(a² − c²)` and
`z² = c² (b² − c²)/(a² − c²)`: the four umbilics of the ellipsoid in the plane `y = 0` (that these
points are umbilics is the classical fact, not proved here, since the chart is singular there). -/
theorem confocalChart_of_sin_eq_zero_of_cos_eq_zero (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (hs : sin (α 0) = 0) (ht : cos (α 1) = 0) :
    confocalChart a b c α 1 = 0 ∧
      confocalChart a b c α 0 ^ 2 = a ^ 2 * (a ^ 2 - b ^ 2) / (a ^ 2 - c ^ 2) ∧
      confocalChart a b c α 2 ^ 2 = c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) := by
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  have hk := k_sq hcb hba hc
  have hk0 := (k_pos hcb hba hc).ne'
  have hc2 : cos (α 0) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (α 0)]
  have hs2 : sin (α 1) ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq (α 1)]
  refine ⟨by simp [confocalChart, hs], ?_, ?_⟩
  · simp only [confocalChart, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [mul_pow, mul_pow, div_pow, hX2, hk, hc2]
    simp only [confocalNu, hs2]
    ring
  · simp only [confocalChart, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [mul_pow, mul_pow, div_pow, hZ2, hk, hs2]
    simp only [confocalMu, hs]
    ring

/-! ### The level set, the outward normal, the curvature tensor and the torsion form -/

private lemma fderiv_apply_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : Vec3 → F} {p w : Vec3} {d : F} (hd : DifferentiableAt ℝ h p)
    (hl : HasDerivAt (fun t : ℝ => h (p + t • w)) d 0) : fderiv ℝ h p w = d := by
  have hline : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
  have h' : HasFDerivAt h (fderiv ℝ h p) (p + (0 : ℝ) • w) := by simpa using hd.hasFDerivAt
  exact (h'.comp_hasDerivAt (0 : ℝ) hline).unique hl

private lemma hasDerivAt_coord (p w : Vec3) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => p i + t * w i) (w i) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w i)).const_add (p i)

/-- **The normal field of the ellipsoid is differentiable (MLS Exercise 19, p. 263).** -/
theorem differentiable_ellipsoidField : Differentiable ℝ (ellipsoidField a b c) := by
  have h : Differentiable ℝ (fun x : Vec3 => ![x 0 / a ^ 2, x 1 / b ^ 2, x 2 / c ^ 2]) := by
    refine differentiable_pi.mpr fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.differentiable.comp h

/-- **The derivative of the normal field of the ellipsoid (MLS Exercise 19, p. 263):** `G` is
linear, `DG(p) w = G(w)`; it is one half of the Hessian of `ellipsoidFunction`. -/
theorem fderiv_ellipsoidField (p w : Vec3) :
    fderiv ℝ (ellipsoidField a b c) p w = ellipsoidField a b c w := by
  refine fderiv_apply_of_hasDerivAt (differentiable_ellipsoidField p) ?_
  have h := hasDerivAt_toLp3 ((hasDerivAt_coord p w 0).div_const (a ^ 2))
    ((hasDerivAt_coord p w 1).div_const (b ^ 2)) ((hasDerivAt_coord p w 2).div_const (c ^ 2))
  convert h using 1
  · funext t
    simp [ellipsoidField]
  · rfl

/-- **The gradient of the ellipsoid function (MLS Exercise 19, p. 263):**
`Dh(p) w = 2 ⟨G(p), w⟩` with `G(p) = (p₁/a², p₂/b², p₃/c²)`. -/
theorem fderiv_ellipsoidFunction (p w : Vec3) :
    fderiv ℝ (ellipsoidFunction a b c) p w = 2 * inner ℝ (ellipsoidField a b c p) w := by
  have hd : DifferentiableAt ℝ (ellipsoidFunction a b c) p := by
    unfold ellipsoidFunction
    fun_prop
  refine fderiv_apply_of_hasDerivAt hd ?_
  have h := (((((hasDerivAt_coord p w 0).pow 2).div_const (a ^ 2)).add
    (((hasDerivAt_coord p w 1).pow 2).div_const (b ^ 2))).add
    (((hasDerivAt_coord p w 2).pow 2).div_const (c ^ 2))).sub_const 1
  convert h using 1
  · funext t
    simp [ellipsoidFunction]
  · simp [ellipsoidField, PiLp.inner_apply, Fin.sum_univ_three]
    ring

private lemma qUU (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    inner ℝ (partialU (confocalChart a b c) α)
      (ellipsoidField a b c (partialU (confocalChart a b c) α)) =
      (confocalMu a b (α 0) - confocalNu b c (α 1)) / (confocalMu a b (α 0) - c ^ 2) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  rw [partialU_confocalChart hcb hba hc]
  simp only [ellipsoidField, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, star_trivial]
  linear_combination alg_qUU (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
    (k_pos hcb hba hc).ne' (confocalZ_pos hcb hba hc (α 0)).ne' ha.ne' hb.ne' hc.ne'
    (confocalZ_arg_pos hcb hba hc (α 0)).ne' hX2 hZ2 (k_sq hcb hba hc) rfl rfl
    (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1))

private lemma qVV (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    inner ℝ (partialV (confocalChart a b c) α)
      (ellipsoidField a b c (partialV (confocalChart a b c) α)) =
      (confocalMu a b (α 0) - confocalNu b c (α 1)) / (a ^ 2 - confocalNu b c (α 1)) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  rw [partialV_confocalChart hcb hba hc]
  simp only [ellipsoidField, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, star_trivial]
  linear_combination alg_qVV (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
    (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne' ha.ne' hb.ne' hc.ne'
    (confocalX_arg_pos hcb hba hc (α 1)).ne' hX2 hZ2 (k_sq hcb hba hc) rfl rfl
    (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1))

private lemma qUV (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    inner ℝ (partialU (confocalChart a b c) α)
      (ellipsoidField a b c (partialV (confocalChart a b c) α)) = 0 := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  rw [partialU_confocalChart hcb hba hc, partialV_confocalChart hcb hba hc]
  simp only [ellipsoidField, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, star_trivial]
  linear_combination alg_qUV (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1))
    (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne'
    (confocalZ_pos hcb hba hc (α 0)).ne' ha.ne' hb.ne' hc.ne' (k_sq hcb hba hc)

private lemma qVU (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    inner ℝ (partialV (confocalChart a b c) α)
      (ellipsoidField a b c (partialU (confocalChart a b c) α)) = 0 := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  rw [partialU_confocalChart hcb hba hc, partialV_confocalChart hcb hba hc]
  simp only [ellipsoidField, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, star_trivial]
  linear_combination alg_qUV (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1))
    (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne'
    (confocalZ_pos hcb hba hc (α 0)).ne' ha.ne' hb.ne' hc.ne' (k_sq hcb hba hc)

private lemma uUV (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    inner ℝ (partialU (confocalChart a b c) α) (partialV (partialU (confocalChart a b c)) α) =
      -(sin (α 1) * cos (α 1) * (b ^ 2 - c ^ 2) * confocalMu a b (α 0) /
        (confocalMu a b (α 0) - c ^ 2)) := by
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  rw [partialU_confocalChart hcb hba hc, partialV_partialU_confocalChart hcb hba hc]
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, star_trivial]
  linear_combination alg_uUV (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0))
    (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne'
    (confocalZ_pos hcb hba hc (α 0)).ne' (confocalZ_arg_pos hcb hba hc (α 0)).ne' hZ2
    (k_sq hcb hba hc) rfl (sin_sq_add_cos_sq (α 0))

private lemma vUV (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    inner ℝ (partialV (confocalChart a b c) α) (partialV (partialU (confocalChart a b c)) α) =
      sin (α 0) * cos (α 0) * (a ^ 2 - b ^ 2) * confocalNu b c (α 1) /
        (a ^ 2 - confocalNu b c (α 1)) := by
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  rw [partialV_confocalChart hcb hba hc, partialV_partialU_confocalChart hcb hba hc]
  simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, star_trivial]
  linear_combination alg_vUV (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1)) (n := confocalNu b c (α 1))
    (k_pos hcb hba hc).ne' (confocalX_pos hcb hba hc (α 1)).ne'
    (confocalZ_pos hcb hba hc (α 0)).ne' (confocalX_arg_pos hcb hba hc (α 1)).ne' hX2
    (k_sq hcb hba hc) rfl (sin_sq_add_cos_sq (α 1))

/-- **The confocal chart lies on the ellipsoid (MLS Exercise 14, p. 262; Exercise 19, p. 263):**
`x²/a² + y²/b² + z²/c² = 1` at every chart point, for `a > b > c > 0`. -/
theorem ellipsoidFunction_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (α : Fin 2 → ℝ) : ellipsoidFunction a b c (confocalChart a b c α) = 0 := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  obtain ⟨hX2, hZ2⟩ := confocal_rels hcb hba hc α
  simp only [ellipsoidFunction, confocalChart, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  linear_combination alg_surface (a := a) (b := b) (c := c) (k := √(a ^ 2 - c ^ 2))
    (X := confocalX a b c (α 1)) (Z := confocalZ a b c (α 0)) (S := sin (α 0)) (C := cos (α 0))
    (P := sin (α 1)) (Q := cos (α 1)) (m := confocalMu a b (α 0)) (n := confocalNu b c (α 1))
    (k_pos hcb hba hc).ne' ha.ne' hb.ne' hc.ne' hX2 hZ2 (k_sq hcb hba hc) rfl rfl
    (sin_sq_add_cos_sq (α 0)) (sin_sq_add_cos_sq (α 1))

private lemma ellipsoidField_ne_zero (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    0 < ‖ellipsoidField a b c (confocalChart a b c α)‖ := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  rw [norm_ellipsoidField_confocalChart hcb hba hc]
  exact div_pos (Real.sqrt_pos.mpr (mul_pos (mu_pos hcb hba hc _) (nu_pos hc hcb _)))
    (by positivity)

/-- **The normal of the confocal chart points out of the solid ellipsoid (MLS p. 244, "outward
pointing unit normal"):** on the patch, `IsOutwardNormal` for the body `{h ≤ 0}`,
`h = x²/a² + y²/b² + z²/c² − 1`. -/
theorem isOutwardNormal_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (hα : α ∈ confocalDomain) :
    IsOutwardNormal (ellipsoidFunction a b c) (confocalChart a b c) α := by
  have hG := ellipsoidField_ne_zero hcb hba hc α
  rw [IsOutwardNormal, fderiv_ellipsoidFunction, gaussNormal_confocalChart hcb hba hc hα,
    normalizedField, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖ellipsoidField a b c (confocalChart a b c α)‖⁻¹ *
      ‖ellipsoidField a b c (confocalChart a b c α)‖ ^ 2 =
      ‖ellipsoidField a b c (confocalChart a b c α)‖ := by
    field_simp
  rw [this]
  linarith

/-- **The curvature tensor of the confocal chart (MLS eq. (5.21), p. 245; Exercise 14, p. 262),
computed from the normal field as in Exercise 19, p. 263:** on the patch,
`K = diag(abc/(μ √(μν)), abc/(ν √(μν)))`, the principal curvatures of the ellipsoid along the
lines of curvature `t = const` and `s = const`. -/
theorem curvatureTensor_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (hα : α ∈ confocalDomain) :
    curvatureTensor (confocalChart a b c) α =
      !![a * b * c / (confocalMu a b (α 0) * √(confocalMu a b (α 0) * confocalNu b c (α 1))), 0;
        0, a * b * c / (confocalNu b c (α 1) * √(confocalMu a b (α 0) * confocalNu b c (α 1)))] := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hG := ellipsoidField_ne_zero hcb hba hc α
  have hn : gaussNormal (confocalChart a b c) =ᶠ[𝓝 α]
      fun β => normalizedField (ellipsoidField a b c) (confocalChart a b c β) :=
    Filter.eventually_of_mem (isOpen_confocalDomain.mem_nhds hα)
      fun β hβ => gaussNormal_confocalChart hcb hba hc hβ
  have hm := mu_pos hcb hba hc (α 0)
  have hnu := nu_pos hc hcb (α 1)
  have hmn := mu_sub_nu_pos hcb hba hc hα
  have hmc := confocalZ_arg_pos hcb hba hc (α 0)
  have hac := confocalX_arg_pos hcb hba hc (α 1)
  have hs : 0 < √(confocalMu a b (α 0) * confocalNu b c (α 1)) := Real.sqrt_pos.mpr (by positivity)
  rw [curvatureTensor_eq_of_gaussNormal
    ((contDiff_confocalChart hcb hba hc).differentiable (by simp) α)
    (differentiable_ellipsoidField _) (norm_pos_iff.mp hG) hn, fderiv_ellipsoidField,
    fderiv_ellipsoidField, qUU hcb hba hc, qUV hcb hba hc, qVU hcb hba hc, qVV hcb hba hc,
    norm_partialU_confocalChart hcb hba hc, norm_partialV_confocalChart hcb hba hc,
    norm_ellipsoidField_confocalChart hcb hba hc, Real.sq_sqrt (normU_arg_pos hcb hba hc hα).le,
    Real.sq_sqrt (normV_arg_pos hcb hba hc hα).le]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- **The torsion form of the confocal chart (MLS eq. (5.24), p. 246; Exercise 14, p. 262):** on
the patch,
`T = [(b² − c²) sin t cos t/((μ − ν) ‖c_t‖), (a² − b²) sin s cos s/((μ − ν) ‖c_s‖)]` with
`‖c_s‖ = √(μ(μ − ν)/(μ − c²))`, `‖c_t‖ = √(ν(μ − ν)/(a² − ν))`. -/
theorem torsionForm_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c)
    (hα : α ∈ confocalDomain) :
    torsionForm (confocalChart a b c) α =
      ![(b ^ 2 - c ^ 2) * sin (α 1) * cos (α 1) /
          ((confocalMu a b (α 0) - confocalNu b c (α 1)) *
            √(confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
              (a ^ 2 - confocalNu b c (α 1)))),
        (a ^ 2 - b ^ 2) * sin (α 0) * cos (α 0) /
          ((confocalMu a b (α 0) - confocalNu b c (α 1)) *
            √(confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
              (confocalMu a b (α 0) - c ^ 2)))] := by
  have hO := isOrthogonalChartOn_confocalChart hcb hba hc
  have hm := mu_pos hcb hba hc (α 0)
  have hnu := nu_pos hc hcb (α 1)
  have hmn := mu_sub_nu_pos hcb hba hc hα
  have hmc := confocalZ_arg_pos hcb hba hc (α 0)
  have hac := confocalX_arg_pos hcb hba hc (α 1)
  have hu := Real.sqrt_pos.mpr (normU_arg_pos hcb hba hc hα)
  have hv := Real.sqrt_pos.mpr (normV_arg_pos hcb hba hc hα)
  rw [torsionForm_eq_of_orthogonal ((contDiff_confocalChart hcb hba hc).contDiffAt)
    (Filter.Eventually.of_forall fun β => isOrthogonalAt_confocalChart hcb hba hc β)
    (hO.partialU_ne_zero hα) (hO.partialV_ne_zero hα), uUV hcb hba hc, vUV hcb hba hc,
    norm_partialU_confocalChart hcb hba hc, norm_partialV_confocalChart hcb hba hc]
  have eU := Real.sq_sqrt (normU_arg_pos hcb hba hc hα).le
  have eV := Real.sq_sqrt (normV_arg_pos hcb hba hc hα).le
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [eU]
    field_simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [eV]
    field_simp

/-- **The metric tensor of the confocal chart (MLS eq. (5.18), p. 244; Exercise 14, p. 262):**
`M = diag(√(μ(μ − ν)/(μ − c²)), √(ν(μ − ν)/(a² − ν)))` at every point. -/
theorem metricTensor_confocalChart (hcb : c < b) (hba : b < a) (hc : 0 < c) (α : Fin 2 → ℝ) :
    metricTensor (confocalChart a b c) α =
      !![√(confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
          (confocalMu a b (α 0) - c ^ 2)), 0;
        0, √(confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
          (a ^ 2 - confocalNu b c (α 1)))] := by
  rw [metricTensor, norm_partialU_confocalChart hcb hba hc, norm_partialV_confocalChart hcb hba hc]

/-- **MLS Exercise 14, p. 262, for an ellipsoid with three different axes `a > b > c > 0`:** on the
patch `{cos t > 0}` of the confocal chart, the chart point lies on the ellipsoid, the normal (5.19)
is the outward normal `G/‖G‖`, `G = (x/a², y/b², z/c²)`, and the geometric parameters are
`M = diag(√(μ(μ − ν)/(μ − c²)), √(ν(μ − ν)/(a² − ν)))`, `K = diag(abc/(μ √(μν)), abc/(ν √(μν)))`,
`T = [(b² − c²) sin t cos t/((μ − ν) ‖c_t‖), (a² − b²) sin s cos s/((μ − ν) ‖c_s‖)]`, with
`μ = b² + (a² − b²) sin² s` and `ν = c² + (b² − c²) sin² t`. -/
theorem exercise14_confocal (hcb : c < b) (hba : b < a) (hc : 0 < c) (hα : α ∈ confocalDomain) :
    ellipsoidFunction a b c (confocalChart a b c α) = 0 ∧
      IsOutwardNormal (ellipsoidFunction a b c) (confocalChart a b c) α ∧
      gaussNormal (confocalChart a b c) α =
        normalizedField (ellipsoidField a b c) (confocalChart a b c α) ∧
      metricTensor (confocalChart a b c) α =
        !![√(confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
            (confocalMu a b (α 0) - c ^ 2)), 0;
          0, √(confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
            (a ^ 2 - confocalNu b c (α 1)))] ∧
      curvatureTensor (confocalChart a b c) α =
        !![a * b * c / (confocalMu a b (α 0) * √(confocalMu a b (α 0) * confocalNu b c (α 1))), 0;
          0, a * b * c /
            (confocalNu b c (α 1) * √(confocalMu a b (α 0) * confocalNu b c (α 1)))] ∧
      torsionForm (confocalChart a b c) α =
        ![(b ^ 2 - c ^ 2) * sin (α 1) * cos (α 1) /
            ((confocalMu a b (α 0) - confocalNu b c (α 1)) *
              √(confocalNu b c (α 1) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
                (a ^ 2 - confocalNu b c (α 1)))),
          (a ^ 2 - b ^ 2) * sin (α 0) * cos (α 0) /
            ((confocalMu a b (α 0) - confocalNu b c (α 1)) *
              √(confocalMu a b (α 0) * (confocalMu a b (α 0) - confocalNu b c (α 1)) /
                (confocalMu a b (α 0) - c ^ 2)))] :=
  ⟨ellipsoidFunction_confocalChart hcb hba hc α, isOutwardNormal_confocalChart hcb hba hc hα,
    gaussNormal_confocalChart hcb hba hc hα, metricTensor_confocalChart hcb hba hc α,
    curvatureTensor_confocalChart hcb hba hc hα, torsionForm_confocalChart hcb hba hc hα⟩

/-! ### Exercise 15: the elliptic fingertip at the vertex `(−a, 0, 0)` rolling on a plane -/

/-- **MLS Exercise 15(a), p. 262, for three different axes `a > b > c > 0`:** the confocal chart is
an orthogonal chart on a patch containing `(s, t) = (π, 0)`, whose image is the contact point
`(−a, 0, 0)` of the figure (the end of the `x`-axis facing the object) with outward normal
`(−1, 0, 0)`; there `M = diag(b, c √((b² − c²)/(a² − c²)))`, `K = diag(a/b², a/c²)` and `T = 0`. -/
theorem exercise15a_confocal (hcb : c < b) (hba : b < a) (hc : 0 < c) :
    confocalChart a b c ![π, 0] = WithLp.toLp 2 ![-a, 0, 0] ∧
      gaussNormal (confocalChart a b c) ![π, 0] = WithLp.toLp 2 ![-1, 0, 0] ∧
      IsOrthogonalChartOn (confocalChart a b c) confocalDomain ∧
      (![π, 0] : Fin 2 → ℝ) ∈ confocalDomain ∧
      metricTensor (confocalChart a b c) ![π, 0] =
        !![b, 0; 0, c * √((b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2))] ∧
      curvatureTensor (confocalChart a b c) ![π, 0] = !![a / b ^ 2, 0; 0, a / c ^ 2] ∧
      torsionForm (confocalChart a b c) ![π, 0] = 0 := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hd : (![π, 0] : Fin 2 → ℝ) ∈ confocalDomain := by simp [confocalDomain]
  have hμ : confocalMu a b ((![π, 0] : Fin 2 → ℝ) 0) = b ^ 2 := by simp [confocalMu]
  have hν : confocalNu b c ((![π, 0] : Fin 2 → ℝ) 1) = c ^ 2 := by simp [confocalNu]
  have hk := k_pos hcb hba hc
  have hbc : 0 < b ^ 2 - c ^ 2 := by nlinarith
  have hac : 0 < a ^ 2 - c ^ 2 := by nlinarith
  have hpt : confocalChart a b c ![π, 0] = WithLp.toLp 2 ![-a, 0, 0] := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [confocalChart, confocalX, confocalNu]
    field_simp
  refine ⟨hpt, ?_, isOrthogonalChartOn_confocalChart hcb hba hc, hd, ?_, ?_, ?_⟩
  · rw [gaussNormal_confocalChart hcb hba hc hd, normalizedField,
      norm_ellipsoidField_confocalChart hcb hba hc, hμ, hν, hpt,
      show b ^ 2 * c ^ 2 = (b * c) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [ellipsoidField]
    field_simp
  · rw [metricTensor_confocalChart hcb hba hc, hμ, hν]
    have e1 : b ^ 2 * (b ^ 2 - c ^ 2) / (b ^ 2 - c ^ 2) = b ^ 2 := by field_simp
    have e2 : c ^ 2 * (b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2) = c ^ 2 * ((b ^ 2 - c ^ 2) / (a ^ 2 - c ^ 2)) := by
      ring
    rw [e1, e2, Real.sqrt_sq hb.le, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  · rw [curvatureTensor_confocalChart hcb hba hc hd, hμ, hν,
      show b ^ 2 * c ^ 2 = (b * c) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · rw [torsionForm_confocalChart hcb hba hc hd]
    funext i
    fin_cases i <;> simp

/-- The inverse of a diagonal `2 × 2` matrix (supporting lemma for MLS Exercise 15, p. 262). -/
private theorem inv_diag {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    (!![p, 0; 0, q] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![p⁻¹, 0; 0, q⁻¹] := by
  rw [Matrix.inv_eq_left_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp, hq]

/-- Supporting lemma for MLS p. 250: against a flat object (`K_o = 0`) the relative curvature form
is `K_f`. -/
private theorem relativeCurvature_zero (K : Matrix (Fin 2) (Fin 2) ℝ) (ψ : ℝ) :
    relativeCurvature K 0 ψ = K := by
  simp [relativeCurvature, rotatedCurvature]

/-- **MLS Exercise 15(b), p. 262, for three different axes, and the test of Exercise 19, p. 263:
the equations of contact of the ellipsoidal fingertip rolling on the flat object.** With the
confocal chart for the finger and the plane chart of MLS Example 5.7 for the object, along every
motion to which Corollary 5.11.1 (p. 252) applies (a pose curve agreeing near `t` with
`g_of(η(s))`, `α_f(t)` in the patch, pure rolling at `t`), with `r = √(μν)/(abc)`,
`p = ‖c_s‖`, `q = ‖c_t‖` and `T` the torsion form of `torsionForm_confocalChart`:
`(u̇_f, v̇_f, u̇_o, v̇_o, ψ̇) = (0, ν r/q, −ν r sin ψ, −ν r cos ψ, T₂ ν r) ω_x +
(−μ r/p, 0, −μ r cos ψ, μ r sin ψ, −T₁ μ r) ω_y`, `(ω_x, ω_y)` the rolling velocities. -/
theorem exercise15b_confocal (hcb : c < b) (hba : b < a) (hc : 0 < c) {αf αo : ℝ → Fin 2 → ℝ}
    {ψ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t)
    (hαo : HasDerivAt αo αo' t) (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ confocalDomain)
    {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose (confocalChart a b c) planeChart (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (confocalChart a b c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) :
    let ω := (Twist.adjoint (contactFrame (confocalChart a b c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    let μ := confocalMu a b (αf t 0)
    let ν := confocalNu b c (αf t 1)
    let r := √(μ * ν) / (a * b * c)
    let p := √(μ * (μ - ν) / (μ - c ^ 2))
    let q := √(ν * (μ - ν) / (a ^ 2 - ν))
    let T := torsionForm (confocalChart a b c) (αf t)
    ![αf' 0, αf' 1, αo' 0, αo' 1, ψ'] =
      ω 0 • ![0, ν * r / q, -(ν * r) * sin (ψ t), -(ν * r) * cos (ψ t), T 1 * ν * r] +
        ω 1 • ![-(μ * r / p), 0, -(μ * r) * cos (ψ t), μ * r * sin (ψ t), -(T 0 * μ * r)] := by
  intro ω μ ν r p q T
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hm : 0 < μ := mu_pos hcb hba hc _
  have hn : 0 < ν := nu_pos hc hcb _
  have hs : 0 < √(μ * ν) := Real.sqrt_pos.mpr (mul_pos hm hn)
  have hp : 0 < p := Real.sqrt_pos.mpr (normU_arg_pos hcb hba hc hft)
  have hq : 0 < q := Real.sqrt_pos.mpr (normV_arg_pos hcb hba hc hft)
  have hK := curvatureTensor_confocalChart hcb hba hc hft
  have hM := metricTensor_confocalChart hcb hba hc (αf t)
  have hK' : relativeCurvature (curvatureTensor (confocalChart a b c) (αf t))
      (curvatureTensor planeChart (αo t)) (ψ t) =
        !![a * b * c / (μ * √(μ * ν)), 0; 0, a * b * c / (ν * √(μ * ν))] := by
    rw [hK, curvatureTensor_planeChart, relativeCurvature_zero]
  have hX : IsUnit (relativeCurvature (curvatureTensor (confocalChart a b c) (αf t))
      (curvatureTensor planeChart (αo t)) (ψ t)).det := by
    rw [hK', isUnit_iff_ne_zero, Matrix.det_fin_two_of, mul_zero, sub_zero]
    positivity
  obtain ⟨hf, ho, hψ'⟩ := rollingEquations_of_hasDerivAt
    (isOrthogonalChartOn_confocalChart hcb hba hc) isOrthogonalChartOn_planeChart hαf hαo hψ hft
    (Set.mem_univ _) hX hg hD hr
  have hMpq : metricTensor (confocalChart a b c) (αf t) = !![p, 0; 0, q] := hM
  rw [hK', hMpq] at hf
  rw [hK', metricTensor_planeChart] at ho
  rw [hMpq, metricTensor_planeChart, torsionForm_planeChart] at hψ'
  have hω : ω = (Twist.adjoint (contactFrame (confocalChart a b c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular := rfl
  have hT : T = torsionForm (confocalChart a b c) (αf t) := rfl
  rw [← hω] at hf ho
  rw [← hT] at hψ'
  rw [inv_diag hp.ne' hq.ne', inv_diag (by positivity) (by positivity)] at hf
  rw [inv_diag (by positivity) (by positivity), inv_one, one_mulVec] at ho
  have hr' : r = √(μ * ν) / (a * b * c) := rfl
  funext i
  fin_cases i
  · simp [hf, dotProduct, Fin.sum_univ_two, hr']
    field_simp
  · simp [hf, dotProduct, Fin.sum_univ_two, hr']
    field_simp
  · simp [ho, dotProduct, Fin.sum_univ_two, angleMatrix, hr']
    field_simp
    ring
  · simp [ho, dotProduct, Fin.sum_univ_two, angleMatrix, hr']
    field_simp
    ring
  · simp [hψ', hf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hr']
    field_simp
    ring

/-- **MLS Exercise 15(c), p. 262, for three different axes: the rolling velocity that produces
`α̇_o = (0, v)`.** Under the hypotheses of `exercise15b_confocal`, the object contact velocity is
`α̇_o = (0, v)` exactly when the rolling velocities are `ω_x = −cos ψ v/(ν r)` and
`ω_y = sin ψ v/(μ r)`, with `r = √(μν)/(abc)`. The other components of `V^b_{l_o l_f}` are fixed by
the pure-rolling hypothesis (`v_x = v_y = ω_z = 0`, p. 249) and by Theorem 5.11 (`v_z = 0`, p. 250)
and are not restated. -/
theorem exercise15c_confocal (hcb : c < b) (hba : b < a) (hc : 0 < c) {αf αo : ℝ → Fin 2 → ℝ}
    {ψ : ℝ → ℝ} {αf' αo' : Fin 2 → ℝ} {ψ' t : ℝ} (hαf : HasDerivAt αf αf' t)
    (hαo : HasDerivAt αo αo' t) (hψ : HasDerivAt ψ ψ' t) (hft : αf t ∈ confocalDomain)
    {g : ℝ → RigidTransform}
    (hg : ∀ᶠ s in 𝓝 t, g s = relativePose (confocalChart a b c) planeChart (αf s) (αo s) (ψ s))
    {D : HomogeneousMatrix} (hD : HasDerivAt (fun s => (g s).toHomogeneous) D t)
    (hr : IsRolling (Twist.adjoint (contactFrame (confocalChart a b c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD))) (v : ℝ) :
    let ω := (Twist.adjoint (contactFrame (confocalChart a b c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular
    let μ := confocalMu a b (αf t 0)
    let ν := confocalNu b c (αf t 1)
    let r := √(μ * ν) / (a * b * c)
    αo' = ![0, v] ↔ ω 0 = -(cos (ψ t) * v / (ν * r)) ∧ ω 1 = sin (ψ t) * v / (μ * r) := by
  intro ω μ ν r
  have h := exercise15b_confocal hcb hba hc hαf hαo hψ hft hg hD hr
  have hω : ω = (Twist.adjoint (contactFrame (confocalChart a b c) (αf t))⁻¹
      (RigidTransform.bodyVelocity g D t hD)).angular := rfl
  have hrdef : r = √(μ * ν) / (a * b * c) := rfl
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [← hω] at h2 h3
  simp at h2 h3
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hm : 0 < μ := mu_pos hcb hba hc _
  have hn : 0 < ν := nu_pos hc hcb _
  have hr0 : 0 < r := div_pos (Real.sqrt_pos.mpr (mul_pos hm hn)) (by positivity)
  have hA : μ * r * ω 1 = sin (ψ t) * αo' 1 - cos (ψ t) * αo' 0 := by
    rw [h2, h3]
    linear_combination (-(μ * r * ω 1)) * sin_sq_add_cos_sq (ψ t)
  have hB : ν * r * ω 0 = -(cos (ψ t) * αo' 1) - sin (ψ t) * αo' 0 := by
    rw [h2, h3]
    linear_combination (-(ν * r * ω 0)) * sin_sq_add_cos_sq (ψ t)
  constructor
  · intro hv
    have e0 : αo' 0 = 0 := by simp [hv]
    have e1 : αo' 1 = v := by simp [hv]
    rw [e0, e1] at hA hB
    constructor
    · field_simp
      linear_combination hB
    · field_simp
      linear_combination hA
  · rintro ⟨h0, h1⟩
    have k0 : ω 0 * (ν * r) = -(cos (ψ t) * v) := by
      rw [h0]
      field_simp
    have k1 : ω 1 * (μ * r) = sin (ψ t) * v := by
      rw [h1]
      field_simp
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [h2]
      linear_combination (-sin (ψ t)) * k0 + (-cos (ψ t)) * k1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h3]
      linear_combination (-cos (ψ t)) * k0 + sin (ψ t) * k1 + v * sin_sq_add_cos_sq (ψ t)

end Examples
end RoboLean
