import RoboLean.Grasp.GeometricParameters
import RoboLean.Grasp.ContactCoordinates

/-!
# The curvature tensor of a surface given by a normal field (MLS Exercise 19)

MLS Chapter 5, Exercise 19, printed p. 263: "Rederive the contact kinematics when the finger and
object surfaces are given as the level sets of functions `h_f : ℝ³ → ℝ` and `h_o : ℝ³ → ℝ` (for
example, a sphere of radius `ρ` satisfies `h_f(x) = x₁² + x₂² + x₃² − ρ² = 0`). Test your solution
using an ellipsoid rolling on a plane." The kinematics of contact (5.28), p. 250, depend on the two
surfaces only through their geometric parameters `(M, K, T)` of (5.18), (5.21) and (5.24),
pp. 244–246; of these only the curvature tensor `K` involves the normal.

**Reading fixed here.** For a surface `{h = 0}`, the outward unit normal is `∇h/‖∇h‖`; the part of
the contact kinematics that the level set changes is the curvature tensor, and it is computed from
the derivative of the normal field without differentiating the chart twice. The statement is made
for any field `G : ℝ³ → ℝ³` whose normalization `G/‖G‖` is the chart's Gauss normal near the point
(for a level set, `G = ∇h` or any positive multiple of it): then
`c_iᵀ n_j = c_iᵀ DG(c) c_j / ‖G(c)‖` for `i, j ∈ {u, v}`, so that
`K = [[c_uᵀ DG c_u/‖c_u‖², c_uᵀ DG c_v/(‖c_u‖ ‖c_v‖)], [c_vᵀ DG c_u/(‖c_u‖ ‖c_v‖), c_vᵀ DG c_v/‖c_v‖²]]/‖G‖`
(`curvatureTensor_eq_of_gaussNormal`). For `G = ∇h`, `DG` is the Hessian of `h`. The test of the
exercise, an ellipsoid rolling on a plane, is `RoboLean.Examples.exercise15b_confocal`, where the
curvature of a three-axis ellipsoid is computed this way. The metric tensor and the torsion form
are those of the chart and are not restated. Not formalized: a chart-free form of (5.28) in which
the contact point is a pair of points of `ℝ³` instead of chart coordinates.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Surface

variable {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}

/-- **The normalized field `G/‖G‖` (for MLS Exercise 19, p. 263):** for a level set `{h = 0}` and
`G = ∇h`, the unit normal `∇h/‖∇h‖` of the surface. -/
def normalizedField (G : Vec3 → Vec3) (x : Vec3) : Vec3 := ‖G x‖⁻¹ • G x

/-- **The derivative of a normalized field along the tangent plane (for MLS Exercise 19, p. 263, and
eq. (5.20), p. 245):** for `G` differentiable at `x` with `G x ≠ 0` and a vector `w ⟂ G x`,
`wᵀ D(G/‖G‖)(x) w' = wᵀ DG(x) w' / ‖G x‖`. The derivative of the factor `‖G‖⁻¹` drops out because
it multiplies `G x`. -/
theorem inner_fderiv_normalizedField {G : Vec3 → Vec3} {x : Vec3} (hG : DifferentiableAt ℝ G x)
    (h0 : G x ≠ 0) {w : Vec3} (hw : inner ℝ w (G x) = 0) (w' : Vec3) :
    inner ℝ w (fderiv ℝ (normalizedField G) x w') = inner ℝ w (fderiv ℝ G x w') / ‖G x‖ := by
  have hk : DifferentiableAt ℝ (fun y => ‖G y‖⁻¹) x :=
    (hG.norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)
  change inner ℝ w (fderiv ℝ (fun y => ‖G y‖⁻¹ • G y) x w') = _
  rw [fderiv_fun_smul hk hG]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, inner_add_right, inner_smul_right, hw, mul_zero,
    add_zero]
  rw [div_eq_inv_mul]

/-- **A normalized field is differentiable where the field is nonzero (supporting lemma for MLS
Exercise 19, p. 263).** -/
theorem differentiableAt_normalizedField {G : Vec3 → Vec3} {x : Vec3}
    (hG : DifferentiableAt ℝ G x) (h0 : G x ≠ 0) : DifferentiableAt ℝ (normalizedField G) x :=
  ((hG.norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)).smul hG

/-- **The tangent vectors are orthogonal to the field (for MLS Exercise 19, p. 263):** where the
Gauss normal of eq. (5.19) is `G/‖G‖` at `c(α)` and `G(c(α)) ≠ 0`, `c_u ⟂ G(c(α))` and
`c_v ⟂ G(c(α))`. -/
theorem inner_partial_field_eq_zero {G : Vec3 → Vec3} (h0 : G (c α) ≠ 0)
    (hn : gaussNormal c α = normalizedField G (c α)) :
    inner ℝ (partialU c α) (G (c α)) = 0 ∧ inner ℝ (partialV c α) (G (c α)) = 0 := by
  have hG : G (c α) = ‖G (c α)‖ • gaussNormal c α := by
    rw [hn, normalizedField, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0), one_smul]
  constructor
  · rw [hG, inner_smul_right, real_inner_comm, inner_gaussNormal_partialU, mul_zero]
  · rw [hG, inner_smul_right, real_inner_comm, inner_gaussNormal_partialV, mul_zero]

/-- **The partials of the Gauss map from a normal field (for MLS eq. (5.20), p. 245, and Exercise
19, p. 263):** if near `α` the Gauss normal is `G/‖G‖` along the chart, `c` is differentiable at
`α` and `G` is differentiable at `c(α)` with `G(c(α)) ≠ 0`, then `n_u = D(G/‖G‖)(c(α)) c_u` and
`n_v = D(G/‖G‖)(c(α)) c_v`. -/
theorem partial_gaussNormal_eq {G : Vec3 → Vec3} (hc : DifferentiableAt ℝ c α)
    (hG : DifferentiableAt ℝ G (c α)) (h0 : G (c α) ≠ 0)
    (hn : gaussNormal c =ᶠ[𝓝 α] fun β => normalizedField G (c β)) :
    partialU (gaussNormal c) α = fderiv ℝ (normalizedField G) (c α) (partialU c α) ∧
      partialV (gaussNormal c) α = fderiv ℝ (normalizedField G) (c α) (partialV c α) := by
  have hN := differentiableAt_normalizedField hG h0
  have hcomp : fderiv ℝ (fun β => normalizedField G (c β)) α =
      (fderiv ℝ (normalizedField G) (c α)).comp (fderiv ℝ c α) :=
    fderiv_comp (g := normalizedField G) (f := c) α hN hc
  constructor
  · rw [partialU_congr hn, partialU, hcomp]
    rfl
  · rw [partialV_congr hn, partialV, hcomp]
    rfl

/-- **MLS eq. (5.21), p. 245, from a normal field (the reading of Exercise 19, p. 263, fixed in the
module docstring):** if near `α` the Gauss normal of eq. (5.19) is `G/‖G‖` along the chart, with
`c` differentiable at `α`, `G` differentiable at `c(α)` and `G(c(α)) ≠ 0`, then
`K = [[c_uᵀ DG c_u/‖c_u‖², c_uᵀ DG c_v/(‖c_u‖ ‖c_v‖)], [c_vᵀ DG c_u/(‖c_u‖ ‖c_v‖), c_vᵀ DG c_v/‖c_v‖²]]/‖G‖`,
with `DG = DG(c(α))`. For a level set `{h = 0}` with outward normal, `G = ∇h` and `DG` is the
Hessian of `h`; no second derivative of the chart enters. -/
theorem curvatureTensor_eq_of_gaussNormal {G : Vec3 → Vec3} (hc : DifferentiableAt ℝ c α)
    (hG : DifferentiableAt ℝ G (c α)) (h0 : G (c α) ≠ 0)
    (hn : gaussNormal c =ᶠ[𝓝 α] fun β => normalizedField G (c β)) :
    curvatureTensor c α =
      !![inner ℝ (partialU c α) (fderiv ℝ G (c α) (partialU c α)) /
          (‖G (c α)‖ * ‖partialU c α‖ ^ 2),
        inner ℝ (partialU c α) (fderiv ℝ G (c α) (partialV c α)) /
          (‖G (c α)‖ * (‖partialU c α‖ * ‖partialV c α‖));
        inner ℝ (partialV c α) (fderiv ℝ G (c α) (partialU c α)) /
          (‖G (c α)‖ * (‖partialU c α‖ * ‖partialV c α‖)),
        inner ℝ (partialV c α) (fderiv ℝ G (c α) (partialV c α)) /
          (‖G (c α)‖ * ‖partialV c α‖ ^ 2)] := by
  obtain ⟨hu, hv⟩ := partial_gaussNormal_eq hc hG h0 hn
  obtain ⟨ou, ov⟩ := inner_partial_field_eq_zero h0 hn.self_of_nhds
  rw [curvatureTensor, hu, hv, inner_fderiv_normalizedField hG h0 ou,
    inner_fderiv_normalizedField hG h0 ou, inner_fderiv_normalizedField hG h0 ov,
    inner_fderiv_normalizedField hG h0 ov]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [div_div]

/-- **`c_vᵀ c_uu = −c_uᵀ c_uv` for a chart orthogonal near `α` (supporting MLS eq. (5.24), p. 246):**
differentiating `c_uᵀ c_v = 0` along `u`, for `c` twice continuously differentiable at `α`. -/
theorem inner_partialV_partialU_partialU (hc : ContDiffAt ℝ 2 c α)
    (horth : ∀ᶠ β in 𝓝 α, IsOrthogonalAt c β) :
    inner ℝ (partialV c α) (partialU (partialU c) α) =
      -inner ℝ (partialU c α) (partialV (partialU c) α) := by
  have d := fderiv_inner_apply ℝ (differentiableAt_partialU hc) (differentiableAt_partialV hc)
    (Pi.single 0 1)
  have hz : (fun β => inner ℝ (partialU c β) (partialV c β)) =ᶠ[𝓝 α] fun _ => (0 : ℝ) :=
    horth.mono fun β hβ => hβ
  rw [hz.fderiv_eq, fderiv_const_apply] at d
  change (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 0 1) =
    inner ℝ (partialU c α) (partialU (partialV c) α) +
      inner ℝ (partialU (partialU c) α) (partialV c α) at d
  rw [← partialV_partialU hc] at d
  simp only [_root_.zero_apply] at d
  rw [real_inner_comm]
  linarith

/-- **MLS eq. (5.24), p. 246, with the mixed partial only:**
`T_p = [−c_uᵀ c_uv/(‖c_u‖² ‖c_v‖), c_vᵀ c_uv/(‖c_u‖ ‖c_v‖²)]` for a chart twice continuously
differentiable at `α`, orthogonal on a neighbourhood of `α`, with `c_u, c_v ≠ 0`; the second
expression of (5.24) after `c_vᵀ c_uu = −c_uᵀ c_uv`. -/
theorem torsionForm_eq_of_orthogonal (hc : ContDiffAt ℝ 2 c α)
    (horth : ∀ᶠ β in 𝓝 α, IsOrthogonalAt c β) (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    torsionForm c α =
      ![-inner ℝ (partialU c α) (partialV (partialU c) α) / (‖partialU c α‖ ^ 2 * ‖partialV c α‖),
        inner ℝ (partialV c α) (partialV (partialU c) α) /
          (‖partialU c α‖ * ‖partialV c α‖ ^ 2)] := by
  rw [torsionForm_eq hc horth.self_of_nhds hu hv, inner_partialV_partialU_partialU hc horth]

/-! ### Surfaces given as level sets -/

/-- **A vector orthogonal to the tangent plane is a multiple of the normal (MLS p. 245: the Gauss
map gives "the unit normal"):** at a point of an orthogonal chart with `c_u, c_v ≠ 0`, if `w ⟂ c_u`
and `w ⟂ c_v`, then `w = ⟨n, w⟩ n`. -/
theorem eq_inner_smul_gaussNormal (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) {w : Vec3} (h1 : inner ℝ (partialU c α) w = 0)
    (h2 : inner ℝ (partialV c α) w = 0) : w = inner ℝ (gaussNormal c α) w • gaussNormal c α := by
  have e := gaussFrame_inv_act h hu hv w
  have hx : inner ℝ (frameX c α) w = 0 := by rw [frameX, inner_smul_left, h1, mul_zero]
  have hy : inner ℝ (frameY c α) w = 0 := by rw [frameY, inner_smul_left, h2, mul_zero]
  rw [hx, hy] at e
  have hz : (WithLp.toLp 2 ![0, 0, inner ℝ (gaussNormal c α) w] : Vec3) =
      inner ℝ (gaussNormal c α) w • (WithLp.toLp 2 ![0, 0, 1] : Vec3) := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp
  calc w = (gaussFrame c α).act ((gaussFrame c α)⁻¹.act w) := (Rotation.act_inv_act _ _).symm
    _ = inner ℝ (gaussNormal c α) w • gaussNormal c α := by
      rw [e, hz, map_smul, gaussFrame_act_axisZ h hu hv]

/-- **The Gauss normal of a chart of a level set (MLS Exercise 19, p. 263):** if `f(c(β)) = 0` for
`β` near `α`, `f` is differentiable at `c(α)` with gradient `G` (`Df(c(α)) w = ⟨G, w⟩`), the chart
is orthogonal at `α` with `c_u, c_v ≠ 0`, and the normal (5.19) points out of `{f ≤ 0}`
(`IsOutwardNormal`), then `n = G/‖G‖`. -/
theorem gaussNormal_eq_of_levelSet (hc : DifferentiableAt ℝ c α) (h : IsOrthogonalAt c α)
    (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) {f : Vec3 → ℝ} {G : Vec3}
    (hf : DifferentiableAt ℝ f (c α)) (hG : ∀ w, fderiv ℝ f (c α) w = inner ℝ G w)
    (hlev : ∀ᶠ β in 𝓝 α, f (c β) = 0) (hout : IsOutwardNormal f c α) :
    gaussNormal c α = ‖G‖⁻¹ • G := by
  have hcomp : fderiv ℝ (fun β => f (c β)) α = (fderiv ℝ f (c α)).comp (fderiv ℝ c α) :=
    fderiv_comp (g := f) (f := c) α hf hc
  have hl : (fun β => f (c β)) =ᶠ[𝓝 α] fun _ => (0 : ℝ) := hlev
  have hzero : fderiv ℝ (fun β => f (c β)) α = 0 := by
    rw [hl.fderiv_eq]
    exact fderiv_const_apply 0
  have h1 : inner ℝ (partialU c α) G = 0 := by
    rw [real_inner_comm, ← hG]
    have := congrArg (fun L => L (Pi.single 0 1)) (hcomp.symm.trans hzero)
    simpa [partialU] using this
  have h2 : inner ℝ (partialV c α) G = 0 := by
    rw [real_inner_comm, ← hG]
    have := congrArg (fun L => L (Pi.single 1 1)) (hcomp.symm.trans hzero)
    simpa [partialV] using this
  have hGn := eq_inner_smul_gaussNormal h hu hv h1 h2
  have hpos : 0 < inner ℝ (gaussNormal c α) G := by
    rw [real_inner_comm, ← hG]
    exact hout
  have hnorm : ‖G‖ = inner ℝ (gaussNormal c α) G := by
    conv_lhs => rw [hGn]
    rw [norm_smul, norm_gaussNormal h hu hv, mul_one, Real.norm_of_nonneg hpos.le]
  calc gaussNormal c α = (inner ℝ (gaussNormal c α) G)⁻¹ •
        (inner ℝ (gaussNormal c α) G • gaussNormal c α) := by
        rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    _ = ‖G‖⁻¹ • G := by rw [← hGn, hnorm]

/-- **MLS eq. (5.21), p. 245, for a surface given as a level set (the reading of Exercise 19,
p. 263):** let `(c, U)` be an orthogonal chart of the level set `{f = 0}` (`f(c(β)) = 0` on `U`)
whose normal points out of `{f ≤ 0}` on `U`, with `f` differentiable along the chart, `G` a gradient
field of `f` (`Df(x) w = ⟨G(x), w⟩`) differentiable at `c(α)`. Then the curvature tensor at
`α ∈ U` is the Hessian `DG` restricted to the tangent plane and divided by `‖G‖`:
`K = [[c_uᵀ DG c_u/‖c_u‖², c_uᵀ DG c_v/(‖c_u‖ ‖c_v‖)], [c_vᵀ DG c_u/(‖c_u‖ ‖c_v‖), c_vᵀ DG c_v/‖c_v‖²]]/‖G‖`. -/
theorem curvatureTensor_of_levelSet {U : Set (Fin 2 → ℝ)} (hU : IsOrthogonalChartOn c U)
    (hα : α ∈ U) {f : Vec3 → ℝ} {G : Vec3 → Vec3} (hf : ∀ β ∈ U, DifferentiableAt ℝ f (c β))
    (hG : ∀ x w, fderiv ℝ f x w = inner ℝ (G x) w) (hGd : DifferentiableAt ℝ G (c α))
    (hlev : ∀ β ∈ U, f (c β) = 0) (hout : ∀ β ∈ U, IsOutwardNormal f c β) :
    curvatureTensor c α =
      !![inner ℝ (partialU c α) (fderiv ℝ G (c α) (partialU c α)) /
          (‖G (c α)‖ * ‖partialU c α‖ ^ 2),
        inner ℝ (partialU c α) (fderiv ℝ G (c α) (partialV c α)) /
          (‖G (c α)‖ * (‖partialU c α‖ * ‖partialV c α‖));
        inner ℝ (partialV c α) (fderiv ℝ G (c α) (partialU c α)) /
          (‖G (c α)‖ * (‖partialU c α‖ * ‖partialV c α‖)),
        inner ℝ (partialV c α) (fderiv ℝ G (c α) (partialV c α)) /
          (‖G (c α)‖ * ‖partialV c α‖ ^ 2)] := by
  have hcd : ∀ β ∈ U, DifferentiableAt ℝ c β := fun β hβ =>
    (hU.contDiffAt hβ).differentiableAt (by norm_num)
  have hnβ : ∀ β ∈ U, gaussNormal c β = normalizedField G (c β) := fun β hβ =>
    gaussNormal_eq_of_levelSet (hcd β hβ) (hU.orthogonal β hβ) (hU.partialU_ne_zero hβ)
      (hU.partialV_ne_zero hβ) (hf β hβ) (hG (c β))
      (Filter.eventually_of_mem (hU.isOpen.mem_nhds hβ) hlev) (hout β hβ)
  have h0 : G (c α) ≠ 0 := by
    intro h0
    have := hout α hα
    rw [IsOutwardNormal, hG, h0, inner_zero_left] at this
    exact lt_irrefl 0 this
  exact curvatureTensor_eq_of_gaussNormal (hcd α hα) hGd h0
    (Filter.eventually_of_mem (hU.isOpen.mem_nhds hα) hnβ)

end Surface
end RoboLean
