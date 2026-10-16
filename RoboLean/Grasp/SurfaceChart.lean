import RoboLean.Geometry.RotationPlane
import RoboLean.Geometry.TwistAdjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Surface charts, the first fundamental form and the normalized Gauss frame

MLS Chapter 5, §6.1 "Surface models", printed pp. 243–246, equations (5.17)–(5.19) and (5.22).

**What MLS states.** A local coordinate chart `c : U ⊂ ℝ² → ℝ³` takes `(u, v)` to a point of the
surface written in the object frame (p. 243). A surface is regular when, near each point, a chart
exists such that "1. `c` is differentiable", "2. `c` is a homeomorphism from `U` to `V ∩ S`" and "3.
for every `α = (u, v) ∈ U`, the map `∂c/∂α (α) : ℝ² → ℝ³` is injective" (p. 243). The tangent plane
is spanned by `c_u := ∂c/∂u` and `c_v := ∂c/∂v`; a chart is orthogonal if `c_u` and `c_v` are
orthogonal (pp. 243–244). The first fundamental form is
`I_p = [[c_uᵀ c_u, c_uᵀ c_v], [c_vᵀ c_u, c_vᵀ c_v]]` (5.17), "symmetric and positive definite"; the
metric tensor `M_p` satisfies `I_p = M_p · M_p` and for an orthogonal chart
`M_p = diag(‖c_u‖, ‖c_v‖)` (5.18). The Gauss map is `N(u, v) = c_u × c_v / |c_u × c_v|` (5.19),
written `n`; for an orthogonal chart the normalized Gauss frame is
`[x y z] = [c_u/‖c_u‖, c_v/‖c_v‖, n]` (5.22), "an orthonormal frame at each point" (p. 245).

**Formalized.** A chart is a map `c : (Fin 2 → ℝ) → Vec3`, the coordinates `α = (u, v)` indexed
`0, 1`; `c_u` and `c_v` are `partialU c α` and `partialV c α`, the derivative `fderiv ℝ c α` applied
to the coordinate vectors. Hypotheses are explicit per statement; `IsOrthogonalChartOn c U` bundles,
for an open `U`, conditions 1 and 3 with orthogonality. Condition 1 is taken as twice continuous
differentiability (`ContDiffOn ℝ 2`): the book prints only "differentiable", but the derivatives of
the normal in (5.20)–(5.21) and of the frame in (5.24) use second derivatives of `c`. Condition 2
(homeomorphism) is used by no statement here. The metric tensor is defined by the orthogonal-chart
form (5.18); for an orthogonal chart it squares to `I_p` (`metricTensor_mul_self`), and the general
positive definite square root is not used.

**Normal orientation.** The normal is exactly the book's `n = c_u × c_v / ‖c_u × c_v‖`, with no sign
chosen by the library. Whether it points out of the body depends on the chart: p. 244 calls the
normal "outward pointing", which holds for some charts and not for others (for the chart of MLS
Example 5.6, p. 247, `c_u × c_v` points into the sphere). Where a statement needs the outward
normal, that is the explicit hypothesis `IsOutwardNormal h c α` for a body `{x | h x ≤ 0}`. The
contact frame of MLS §6 has its `z`-axis along `n` (p. 246, footnote 2); the contact models of MLS
§2 use the inward normal, and the two are related by a fixed rotation (`RoboLean.Rolling`).

The normalized Gauss frame is the matrix `gaussFrameMatrix c α` with columns `x, y, n`; it is a
proper rotation for an orthogonal chart with `c_u, c_v ≠ 0` (`gaussFrameMatrix_mem`), and
`gaussFrame c α : Rotation` is that matrix where it is a rotation (the identity elsewhere).
`contactFrame c α = (c(α), [x y z])` is the frame `g_oc` of the proof of MLS Lemma 5.10, p. 247.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Surface

section Partials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The partial derivative `∂f/∂u` along the first chart coordinate (MLS p. 243,
`c_u := ∂c/∂u`):** the derivative `fderiv ℝ f α` applied to the coordinate vector `(1, 0)`.
Coordinates `α = (u, v)` are `Fin 2 → ℝ`, indexed `0, 1`. -/
def partialU (f : (Fin 2 → ℝ) → E) (α : Fin 2 → ℝ) : E :=
  fderiv ℝ f α (Pi.single 0 1)

/-- **The partial derivative `∂f/∂v` along the second chart coordinate (MLS p. 243,
`c_v := ∂c/∂v`):** the derivative `fderiv ℝ f α` applied to the coordinate vector `(0, 1)`. -/
def partialV (f : (Fin 2 → ℝ) → E) (α : Fin 2 → ℝ) : E :=
  fderiv ℝ f α (Pi.single 1 1)

/-- A coordinate vector splits along the two coordinate directions (supporting lemma for MLS p. 243:
every tangent vector is a combination of `c_u` and `c_v`). -/
private theorem eq_single_add_single (a : Fin 2 → ℝ) :
    a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 := by
  funext i
  fin_cases i <;> simp

/-- **Every directional derivative is a combination of the partials (MLS p. 243–244: a tangent
vector at `c(u, v)` "may be expressed as a linear combination of the vectors `c_u` and `c_v`"):**
`Df(α) a = a_u f_u + a_v f_v`. -/
theorem fderiv_apply_eq (f : (Fin 2 → ℝ) → E) (α a : Fin 2 → ℝ) :
    fderiv ℝ f α a = a 0 • partialU f α + a 1 • partialV f α := by
  conv_lhs => rw [eq_single_add_single a]
  rw [map_add, map_smul, map_smul]
  rfl

/-- **The partial `∂f/∂u` is the derivative along the coordinate line `s ↦ f(u + s, v)` (MLS p. 243,
`c_u := ∂c/∂u`)**, for `f` differentiable at `α`. -/
theorem hasDerivAt_lineU {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f α) :
    HasDerivAt (fun s : ℝ => f (α + s • Pi.single 0 1)) (partialU f α) 0 := by
  have hl : HasDerivAt (fun s : ℝ => α + s • (Pi.single 0 1 : Fin 2 → ℝ)) (Pi.single 0 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ)).const_add α
  have hf' : HasFDerivAt f (fderiv ℝ f α) (α + (0 : ℝ) • Pi.single 0 1) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl

/-- **The partial `∂f/∂v` is the derivative along the coordinate line `s ↦ f(u, v + s)` (MLS p. 243,
`c_v := ∂c/∂v`)**, for `f` differentiable at `α`. -/
theorem hasDerivAt_lineV {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f α) :
    HasDerivAt (fun s : ℝ => f (α + s • Pi.single 1 1)) (partialV f α) 0 := by
  have hl : HasDerivAt (fun s : ℝ => α + s • (Pi.single 1 1 : Fin 2 → ℝ)) (Pi.single 1 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ)).const_add α
  have hf' : HasFDerivAt f (fderiv ℝ f α) (α + (0 : ℝ) • Pi.single 1 1) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl

/-- **Computing `∂f/∂u` from the coordinate line (MLS p. 243):** if `f` is differentiable at `α` and
`s ↦ f(u + s, v)` has the derivative `w` at `0`, then `f_u = w`. -/
theorem partialU_eq_of_hasDerivAt {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} {w : E}
    (hf : DifferentiableAt ℝ f α) (h : HasDerivAt (fun s : ℝ => f (α + s • Pi.single 0 1)) w 0) :
    partialU f α = w :=
  (hasDerivAt_lineU hf).unique h

/-- **Computing `∂f/∂v` from the coordinate line (MLS p. 243):** if `f` is differentiable at `α` and
`s ↦ f(u, v + s)` has the derivative `w` at `0`, then `f_v = w`. -/
theorem partialV_eq_of_hasDerivAt {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} {w : E}
    (hf : DifferentiableAt ℝ f α) (h : HasDerivAt (fun s : ℝ => f (α + s • Pi.single 1 1)) w 0) :
    partialV f α = w :=
  (hasDerivAt_lineV hf).unique h

/-- **Partials of functions that agree near `α` agree (MLS p. 243, `c_u := ∂c/∂u`).** -/
theorem partialU_congr {f g : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} (h : f =ᶠ[𝓝 α] g) :
    partialU f α = partialU g α := by
  rw [partialU, partialU, h.fderiv_eq]

/-- **Partials of functions that agree near `α` agree (MLS p. 243, `c_v := ∂c/∂v`).** -/
theorem partialV_congr {f g : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} (h : f =ᶠ[𝓝 α] g) :
    partialV f α = partialV g α := by
  rw [partialV, partialV, h.fderiv_eq]

/-- **A twice continuously differentiable chart has differentiable partials (MLS pp. 245–246: `n_u`,
`x_u` and `c_uu` are derivatives of `c_u`):** `β ↦ c_u(β)` is differentiable at `α`. -/
theorem differentiableAt_partialU {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f α) : DifferentiableAt ℝ (partialU f) α := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) α := hf.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)

/-- **A twice continuously differentiable chart has differentiable partials (MLS pp. 245–246: `n_v`,
`x_v` and `c_uv` are derivatives of `c_u`, `c_v`):** `β ↦ c_v(β)` is differentiable at `α`. -/
theorem differentiableAt_partialV {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ}
    (hf : ContDiffAt ℝ 2 f α) : DifferentiableAt ℝ (partialV f) α := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) α := hf.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)

/-- **Mixed partials commute (MLS p. 246, `c_uv := ∂²c/∂u∂v`):** for `f` twice continuously
differentiable at `α`, the derivative of `f_u` along `v` equals the derivative of `f_v` along `u`,
so the order in `c_uv` does not matter. -/
theorem partialV_partialU {f : (Fin 2 → ℝ) → E} {α : Fin 2 → ℝ} (hf : ContDiffAt ℝ 2 f α) :
    partialV (partialU f) α = partialU (partialV f) α := by
  have hs := hf.isSymmSndFDerivAt (by simp)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) α := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) α := h1.differentiableAt (by norm_num)
  have hU : partialV (partialU f) α = fderiv ℝ (fderiv ℝ f) α (Pi.single 1 1) (Pi.single 0 1) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single 0 1)) α (Pi.single 1 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hV : partialU (partialV f) α = fderiv ℝ (fderiv ℝ f) α (Pi.single 0 1) (Pi.single 1 1) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single 1 1)) α (Pi.single 0 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [hU, hV, hs]

end Partials

variable {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}

/-! ### Orthogonal charts and regularity -/

/-- **An orthogonal chart at `α` (MLS p. 244):** "A coordinate chart is an orthogonal coordinate
chart if `c_u` and `c_v` are orthogonal", here at the point `α`: `⟨c_u, c_v⟩ = 0`. -/
def IsOrthogonalAt (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Prop :=
  inner ℝ (partialU c α) (partialV c α) = 0

/-- **Condition 3 of a regular surface for an orthogonal chart (MLS p. 243):** at a point where
`c_u ⟂ c_v`, the differential `∂c/∂α (α) : ℝ² → ℝ³` is injective exactly when `c_u ≠ 0` and
`c_v ≠ 0`. -/
theorem injective_fderiv_iff (h : IsOrthogonalAt c α) :
    Function.Injective (fderiv ℝ c α) ↔ partialU c α ≠ 0 ∧ partialV c α ≠ 0 := by
  constructor
  · intro hi
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have : fderiv ℝ c α (Pi.single 0 1) = fderiv ℝ c α 0 := by rw [map_zero]; exact h0
      have h1 := congrFun (hi this) 0
      simp at h1
    · have : fderiv ℝ c α (Pi.single 1 1) = fderiv ℝ c α 0 := by rw [map_zero]; exact h0
      have h1 := congrFun (hi this) 1
      simp at h1
  · rintro ⟨hu, hv⟩
    refine (injective_iff_map_eq_zero (fderiv ℝ c α)).mpr fun a ha => ?_
    have ha' : a 0 • partialU c α + a 1 • partialV c α = 0 := by
      rw [← fderiv_apply_eq]; exact ha
    have e0 := congrArg (fun w => inner ℝ (partialU c α) w) ha'
    have e1 := congrArg (fun w => inner ℝ (partialV c α) w) ha'
    simp only [inner_add_right, inner_smul_right, inner_zero_right] at e0 e1
    have h' : inner ℝ (partialV c α) (partialU c α) = 0 := by
      rw [real_inner_comm]; exact h
    rw [h] at e0
    rw [h'] at e1
    have a0 : a 0 = 0 := (by simpa using e0 : a 0 = 0 ∨ partialU c α = 0).resolve_right hu
    have a1 : a 1 = 0 := (by simpa using e1 : a 1 = 0 ∨ partialV c α = 0).resolve_right hv
    funext i
    fin_cases i <;> simp [a0, a1]

/-- **An orthogonal chart on an open set (MLS pp. 243–244), as a hypothesis structure:** `U` is
open, `c` is twice continuously differentiable on `U` (condition 1 of a regular surface, with the
order of differentiability the book leaves unstated fixed at two), `∂c/∂α` is injective at every
point of `U` (condition 3), and `c_u ⟂ c_v` at every point of `U` (an orthogonal chart, p. 244).
Condition 2 (homeomorphism onto the surface patch) is not part of the structure: no statement uses
it. -/
structure IsOrthogonalChartOn (c : (Fin 2 → ℝ) → Vec3) (U : Set (Fin 2 → ℝ)) : Prop where
  /-- The chart domain `U ⊂ ℝ²` is open (MLS p. 243). -/
  isOpen : IsOpen U
  /-- Condition 1 of MLS p. 243, "`c` is differentiable", taken as twice continuously
  differentiable. -/
  contDiffOn : ContDiffOn ℝ 2 c U
  /-- Condition 3 of MLS p. 243: `∂c/∂α (α)` is injective for every `α ∈ U`. -/
  injective : ∀ α ∈ U, Function.Injective (fderiv ℝ c α)
  /-- The chart is orthogonal, `c_u ⟂ c_v` on `U` (MLS p. 244). -/
  orthogonal : ∀ α ∈ U, IsOrthogonalAt c α

namespace IsOrthogonalChartOn

variable {U : Set (Fin 2 → ℝ)}

/-- An orthogonal chart (MLS pp. 243–244) is twice continuously differentiable at every point of its
open domain. -/
theorem contDiffAt (hc : IsOrthogonalChartOn c U) (hα : α ∈ U) : ContDiffAt ℝ 2 c α :=
  hc.contDiffOn.contDiffAt (hc.isOpen.mem_nhds hα)

/-- On an orthogonal chart (MLS pp. 243–244), `c_u ≠ 0` at every point of the domain. -/
theorem partialU_ne_zero (hc : IsOrthogonalChartOn c U) (hα : α ∈ U) : partialU c α ≠ 0 :=
  ((injective_fderiv_iff (hc.orthogonal α hα)).mp (hc.injective α hα)).1

/-- On an orthogonal chart (MLS pp. 243–244), `c_v ≠ 0` at every point of the domain. -/
theorem partialV_ne_zero (hc : IsOrthogonalChartOn c U) (hα : α ∈ U) : partialV c α ≠ 0 :=
  ((injective_fderiv_iff (hc.orthogonal α hα)).mp (hc.injective α hα)).2

/-- **The hypotheses of an orthogonal chart from pointwise facts (MLS pp. 243–244):** an open `U` on
which `c` is twice continuously differentiable, `c_u ⟂ c_v`, `c_u ≠ 0` and `c_v ≠ 0`. -/
theorem of_ne_zero (hU : IsOpen U) (hc : ContDiffOn ℝ 2 c U)
    (horth : ∀ α ∈ U, IsOrthogonalAt c α) (hu : ∀ α ∈ U, partialU c α ≠ 0)
    (hv : ∀ α ∈ U, partialV c α ≠ 0) : IsOrthogonalChartOn c U :=
  ⟨hU, hc, fun α hα => (injective_fderiv_iff (horth α hα)).mpr ⟨hu α hα, hv α hα⟩, horth⟩

end IsOrthogonalChartOn

/-! ### The first fundamental form and the metric tensor -/

/-- **The first fundamental form (MLS eq. (5.17), p. 244):**
`I_p = [[c_uᵀ c_u, c_uᵀ c_v], [c_vᵀ c_u, c_vᵀ c_v]]`, the matrix of the inner product of tangent
vectors in chart coordinates. -/
def firstFundamentalForm (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![inner ℝ (partialU c α) (partialU c α), inner ℝ (partialU c α) (partialV c α);
    inner ℝ (partialV c α) (partialU c α), inner ℝ (partialV c α) (partialV c α)]

/-- **`I_p` is symmetric (MLS p. 244, below eq. (5.17)).** -/
theorem firstFundamentalForm_transpose :
    (firstFundamentalForm c α)ᵀ = firstFundamentalForm c α := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstFundamentalForm, real_inner_comm]

/-- **`I_p` gives the inner product of tangent vectors (MLS p. 244):** for coordinate velocities
`a, b ∈ ℝ²`, `aᵀ I_p b = ⟨Dc(α) a, Dc(α) b⟩`. -/
theorem dotProduct_firstFundamentalForm_mulVec (a b : Fin 2 → ℝ) :
    a ⬝ᵥ (firstFundamentalForm c α *ᵥ b) = inner ℝ (fderiv ℝ c α a) (fderiv ℝ c α b) := by
  rw [fderiv_apply_eq c α a, fderiv_apply_eq c α b]
  simp only [firstFundamentalForm, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, dotProduct, Fin.sum_univ_two, Matrix.mulVec,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

/-- **`I_p` is positive definite (MLS p. 244, below eq. (5.17)):** under condition 3 of a regular
surface (`∂c/∂α` injective), `aᵀ I_p a > 0` for every coordinate vector `a ≠ 0`. -/
theorem dotProduct_firstFundamentalForm_mulVec_pos (h : Function.Injective (fderiv ℝ c α))
    {a : Fin 2 → ℝ} (ha : a ≠ 0) : 0 < a ⬝ᵥ (firstFundamentalForm c α *ᵥ a) := by
  rw [dotProduct_firstFundamentalForm_mulVec, real_inner_self_eq_norm_sq]
  have : fderiv ℝ c α a ≠ 0 := fun h0 => ha (h (by rw [h0, map_zero]))
  positivity

/-- **For an orthogonal chart only the diagonal of `I_p` is nonzero (MLS p. 244, below eq.
(5.17)):** `I_p = diag(‖c_u‖², ‖c_v‖²)`. -/
theorem firstFundamentalForm_of_isOrthogonalAt (h : IsOrthogonalAt c α) :
    firstFundamentalForm c α = !![‖partialU c α‖ ^ 2, 0; 0, ‖partialV c α‖ ^ 2] := by
  have h' : inner ℝ (partialV c α) (partialU c α) = 0 := by rw [real_inner_comm]; exact h
  simp only [firstFundamentalForm, real_inner_self_eq_norm_sq]
  rw [show inner ℝ (partialU c α) (partialV c α) = 0 from h, h']

/-- **The metric tensor of an orthogonal chart (MLS eq. (5.18), p. 244):**
`M_p = diag(‖c_u‖, ‖c_v‖)`. The book defines `M_p` as the positive definite square root of `I_p` and
prints this form for orthogonal charts; the library uses the printed form. -/
def metricTensor (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![‖partialU c α‖, 0; 0, ‖partialV c α‖]

/-- **`I_p = M_p · M_p` for an orthogonal chart (MLS p. 244, eq. (5.18)).** -/
theorem metricTensor_mul_self (h : IsOrthogonalAt c α) :
    metricTensor c α * metricTensor c α = firstFundamentalForm c α := by
  rw [firstFundamentalForm_of_isOrthogonalAt h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metricTensor, Matrix.mul_apply, Fin.sum_univ_two, pow_two]

/-- **`M_p` is symmetric (MLS eq. (5.18), p. 244).** -/
theorem metricTensor_transpose : (metricTensor c α)ᵀ = metricTensor c α := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metricTensor]

/-- **`M_p` is positive definite (MLS p. 244, "the positive definite matrix which satisfies
`I_p = M_p · M_p`"), for `c_u ≠ 0` and `c_v ≠ 0`:** `aᵀ M_p a > 0` for every `a ≠ 0`. -/
theorem dotProduct_metricTensor_mulVec_pos (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0)
    {a : Fin 2 → ℝ} (ha : a ≠ 0) : 0 < a ⬝ᵥ (metricTensor c α *ᵥ a) := by
  have hu' : 0 < ‖partialU c α‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖partialV c α‖ := norm_pos_iff.mpr hv
  have e : a ⬝ᵥ (metricTensor c α *ᵥ a) = ‖partialU c α‖ * a 0 ^ 2 + ‖partialV c α‖ * a 1 ^ 2 := by
    simp [metricTensor, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  rw [e]
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro h1
      exact ha (by funext i; fin_cases i <;> simp [h0, h1])
    have := pow_pos (abs_pos.mpr h1) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (a 0)]
  · have := pow_pos (abs_pos.mpr h0) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (a 1)]

/-- **`M_p` is invertible (MLS eq. (5.18), p. 244; used for `M_p⁻¹` in eq. (5.21)), for `c_u ≠ 0`
and `c_v ≠ 0`:** `det M_p = ‖c_u‖ ‖c_v‖ ≠ 0`. -/
theorem isUnit_det_metricTensor (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    IsUnit (metricTensor c α).det := by
  rw [isUnit_iff_ne_zero, metricTensor, Matrix.det_fin_two_of]
  simp [hu, hv]

/-! ### The Gauss map and the normalized Gauss frame -/

/-- **The Gauss map in local coordinates (MLS eq. (5.19), p. 245):**
`N(u, v) = c_u × c_v / ‖c_u × c_v‖`, written `n`, with the right-handed cross product of MLS p. 26.
No orientation is imposed: whether `n` points out of the body depends on the chart
(`IsOutwardNormal`). -/
def gaussNormal (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Vec3 :=
  ‖Vec3.cross (partialU c α) (partialV c α)‖⁻¹ • Vec3.cross (partialU c α) (partialV c α)

/-- **The first axis of the normalized Gauss frame (MLS eq. (5.22), p. 245):** `x = c_u / ‖c_u‖`. -/
def frameX (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Vec3 :=
  ‖partialU c α‖⁻¹ • partialU c α

/-- **The second axis of the normalized Gauss frame (MLS eq. (5.22), p. 245):** `y = c_v / ‖c_v‖`.
-/
def frameY (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Vec3 :=
  ‖partialV c α‖⁻¹ • partialV c α

/-- **The normal is orthogonal to `c_u` (MLS p. 245: the Gauss map gives "the unit normal"):**
`⟨n, c_u⟩ = 0` at every point, from `c_u × c_v ⟂ c_u`. -/
@[simp] theorem inner_gaussNormal_partialU : inner ℝ (gaussNormal c α) (partialU c α) = 0 := by
  rw [gaussNormal, inner_smul_left, real_inner_comm, Vec3.inner_cross_left]
  simp

/-- **The normal is orthogonal to `c_v` (MLS p. 245: the Gauss map gives "the unit normal"):**
`⟨n, c_v⟩ = 0` at every point. -/
@[simp] theorem inner_gaussNormal_partialV : inner ℝ (gaussNormal c α) (partialV c α) = 0 := by
  rw [gaussNormal, inner_smul_left, real_inner_comm, Vec3.inner_cross_right]
  simp

/-- **For an orthogonal chart, `‖c_u × c_v‖ = ‖c_u‖ ‖c_v‖` (MLS p. 247, the proof of Lemma 5.10
writes `z = c_u × c_v / ‖c_u × c_v‖`).** -/
theorem norm_cross_partial (h : IsOrthogonalAt c α) :
    ‖Vec3.cross (partialU c α) (partialV c α)‖ = ‖partialU c α‖ * ‖partialV c α‖ := by
  have hsq := Vec3.norm_cross_sq (partialU c α) (partialV c α)
  rw [show inner ℝ (partialU c α) (partialV c α) = 0 from h] at hsq
  have h0 : ‖Vec3.cross (partialU c α) (partialV c α)‖ ^ 2 =
      (‖partialU c α‖ * ‖partialV c α‖) ^ 2 := by rw [hsq]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h0

/-- **`x` is a unit vector (MLS p. 245: the normalized Gauss frame is orthonormal), for `c_u ≠ 0`.**
-/
theorem norm_frameX (hu : partialU c α ≠ 0) : ‖frameX c α‖ = 1 := by
  rw [frameX, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

/-- **`y` is a unit vector (MLS p. 245: the normalized Gauss frame is orthonormal), for `c_v ≠ 0`.**
-/
theorem norm_frameY (hv : partialV c α ≠ 0) : ‖frameY c α‖ = 1 := by
  rw [frameY, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- **`x ⟂ y` for an orthogonal chart (MLS p. 245: the normalized Gauss frame is orthonormal).** -/
theorem inner_frameX_frameY (h : IsOrthogonalAt c α) : inner ℝ (frameX c α) (frameY c α) = 0 := by
  rw [frameX, frameY, inner_smul_left, inner_smul_right, show inner ℝ (partialU c α)
    (partialV c α) = 0 from h]
  simp

/-- **The third axis is `x × y` (MLS p. 245, eq. (5.22), and p. 247, the proof of Lemma 5.10): for
an orthogonal chart with `c_u, c_v ≠ 0`, `n = c_u × c_v / ‖c_u × c_v‖ = x × y`**, so the normalized
Gauss frame is right-handed. -/
theorem gaussNormal_eq_cross (h : IsOrthogonalAt c α) :
    gaussNormal c α = Vec3.cross (frameX c α) (frameY c α) := by
  rw [gaussNormal, norm_cross_partial h, frameX, frameY, Vec3.smul_cross, Vec3.cross_smul,
    smul_smul, mul_inv]

/-- **`n` is a unit vector (MLS eq. (5.19), p. 245: the Gauss map takes values in the unit sphere),
for an orthogonal chart with `c_u, c_v ≠ 0`.** -/
theorem norm_gaussNormal (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) : ‖gaussNormal c α‖ = 1 := by
  rw [gaussNormal_eq_cross h]
  exact Vec3.norm_cross_of_unit_orthogonal _ _ (norm_frameX hu) (norm_frameY hv)
    (inner_frameX_frameY h)

/-- **The normalized Gauss frame as a matrix (MLS eq. (5.22), p. 245):** the `3 × 3` matrix with
columns `x = c_u/‖c_u‖`, `y = c_v/‖c_v‖` and `n`, the orientation `R_oc = [x y z]` of the contact
frame in the proof of MLS Lemma 5.10, p. 247. -/
def gaussFrameMatrix (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (Matrix.of ![WithLp.ofLp (frameX c α), WithLp.ofLp (frameY c α),
    WithLp.ofLp (gaussNormal c α)])ᵀ

/-- Supporting lemma: three orthonormal vectors with `z = x × y`, as the columns of a matrix, give a
proper rotation (MLS p. 245, "the normalized Gauss frame provides an orthonormal frame", and pp.
23–24, `SO(3)`). -/
private theorem columns_mem_specialOrthogonalGroup (x y : Vec3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) :
    (Matrix.of ![WithLp.ofLp x, WithLp.ofLp y, WithLp.ofLp (Vec3.cross x y)])ᵀ ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  set z := Vec3.cross x y
  have hz : ‖z‖ = 1 := Vec3.norm_cross_of_unit_orthogonal x y hx hy hxy
  have hxz : inner ℝ x z = 0 := Vec3.inner_cross_left x y
  have hyz : inner ℝ y z = 0 := Vec3.inner_cross_right x y
  have dot : ∀ a b : Vec3, WithLp.ofLp a ⬝ᵥ WithLp.ofLp b = inner ℝ a b := fun a b => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have hzz : inner ℝ z z = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff', transpose_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, dot, hxy, hxz, hyz, real_inner_comm, ← dotProduct.eq_def, hx, hy, hz]
  · rw [Matrix.det_transpose]
    change Matrix.det ![WithLp.ofLp x, WithLp.ofLp y, WithLp.ofLp z] = 1
    rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation]
    change WithLp.ofLp z ⬝ᵥ WithLp.ofLp z = 1
    rw [dot, hzz]

/-- **The normalized Gauss frame is a proper rotation (MLS p. 245: "an orthonormal frame at each
point"; p. 247: `R_oc = [x y z]`), for an orthogonal chart with `c_u ≠ 0` and `c_v ≠ 0`.** -/
theorem gaussFrameMatrix_mem (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) : gaussFrameMatrix c α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [gaussFrameMatrix, gaussNormal_eq_cross h]
  exact columns_mem_specialOrthogonalGroup _ _ (norm_frameX hu) (norm_frameY hv)
    (inner_frameX_frameY h)

open Classical in
/-- **The normalized Gauss frame as a rotation (MLS eq. (5.22), p. 245):** the matrix `[x y n]`
where it is a proper rotation (for an orthogonal chart with `c_u, c_v ≠ 0`, `gaussFrameMatrix_mem`),
and the identity elsewhere, so that a curve of frames is defined for every coordinate curve. -/
def gaussFrame (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Rotation :=
  if h : gaussFrameMatrix c α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ then ⟨_, h⟩ else 1

/-- **The rotation `gaussFrame` is the matrix `[x y n]` of MLS eq. (5.22), p. 245**, for an
orthogonal chart with `c_u ≠ 0` and `c_v ≠ 0`. -/
theorem gaussFrame_val (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    (gaussFrame c α).val = gaussFrameMatrix c α := by
  simp [gaussFrame, gaussFrameMatrix_mem h hu hv]

/-- **Coordinates in the normalized Gauss frame (MLS p. 247, the proof of Lemma 5.10:
`v_oc = R_ocᵀ ṗ_oc` with rows `xᵀ, yᵀ, zᵀ`):** for an orthogonal chart with `c_u, c_v ≠ 0`, the
inverse rotation takes `w` to `(⟨x, w⟩, ⟨y, w⟩, ⟨n, w⟩)`. -/
theorem gaussFrame_inv_act (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) (w : Vec3) :
    (gaussFrame c α)⁻¹.act w = WithLp.toLp 2
      ![inner ℝ (frameX c α) w, inner ℝ (frameY c α) w, inner ℝ (gaussNormal c α) w] := by
  apply WithLp.ofLp_injective
  ext i
  rw [Rotation.act_apply, Rotation.inv_val, gaussFrame_val h hu hv, gaussFrameMatrix,
    transpose_transpose]
  fin_cases i <;>
    simp [Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- **The contact frame at a surface point (MLS p. 246 and the proof of Lemma 5.10, p. 247):**
`g_oc = (p_oc, R_oc)` with position `p_oc = c(α)` and orientation the normalized Gauss frame
`R_oc = [x y z]`; the same frame is MLS eq. (5.42), p. 255, with `∂c/∂α M⁻¹ = [x y]`. -/
def contactFrame (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : RigidTransform :=
  ⟨gaussFrame c α, c α⟩

/-- The origin of the contact frame is the surface point `c(α)` (MLS p. 247, `p_oc = c(α(t))`). -/
@[simp] theorem contactFrame_translation : (contactFrame c α).translation = c α := rfl

/-- The orientation of the contact frame is the normalized Gauss frame (MLS p. 247,
`R_oc = [x y z]`). -/
@[simp] theorem contactFrame_rotation : (contactFrame c α).rotation = gaussFrame c α := rfl

/-! ### Outward normals -/

/-- **The Gauss normal points out of a body (MLS p. 244, "an outward pointing unit normal"; p. 255,
"`n_{oᵢ}` is the outward pointing surface normal"):** for a body described as `{x | h x ≤ 0}` with
`h` differentiable and the surface point `c(α)` on its boundary, the normal `n` is outward when the
directional derivative of `h` along `n` is positive, so that moving from `c(α)` along `n` leaves the
body to first order. This is a hypothesis on a chart, not a consequence of eq. (5.19). -/
def IsOutwardNormal (h : Vec3 → ℝ) (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Prop :=
  0 < fderiv ℝ h (c α) (gaussNormal c α)

end Surface
end RoboLean
