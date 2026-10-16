import RoboLean.Grasp.SurfaceChart

/-!
# The geometric parameters of a surface chart: metric, curvature and torsion

MLS Chapter 5, §6.1, printed pp. 245–246, equations (5.20)–(5.24).

**What MLS states.** The second fundamental form is
`II_p = [[c_uᵀ n_u, c_uᵀ n_v], [c_vᵀ n_u, c_vᵀ n_v]]` (5.20), with `n_u := ∂n/∂u`, `n_v := ∂n/∂v`.
"For an orthogonal set of coordinates, the curvature tensor" is `K_p = M_p⁻ᵀ II_p M_p⁻¹`
`= [[c_uᵀ n_u/‖c_u‖², c_uᵀ n_v/(‖c_u‖ ‖c_v‖)],` `[c_vᵀ n_u/(‖c_u‖ ‖c_v‖), c_vᵀ n_v/‖c_v‖²]]` (5.21);
in terms of the normalized Gauss frame `K_p = [xᵀ; yᵀ] [n_u/‖c_u‖, n_v/‖c_v‖]` (5.23); "If the
surface is flat, then `n_u = n_v = 0` and `K_p = 0`" (p. 246). The torsion form is the row vector
`T_p = yᵀ [x_u/‖c_u‖, x_v/‖c_v‖] = [c_vᵀ c_uu/(‖c_u‖² ‖c_v‖), c_vᵀ c_uv/(‖c_u‖ ‖c_v‖²)]` (5.24), "If
a surface is flat, then `T_p = 0`". `(M_p, K_p, T_p)` are the geometric parameters (p. 246).

**Formalized.** `secondFundamentalForm`, `curvatureTensor` (defined by the entries of (5.21)) and
`torsionForm` (defined by the first expression of (5.24), as a vector `Fin 2 → ℝ` read as a row, so
that `T M α̇` is `torsionForm c α ⬝ᵥ (metricTensor c α *ᵥ α̇)`). Theorems: the matrix form of (5.21)
(`curvatureTensor_eq_mul`), (5.23) (`curvatureTensor_eq_frame`, an identity at every point), the
second expression of (5.24) for a twice continuously differentiable orthogonal chart
(`torsionForm_eq`, using `x ⟂ y` and `c_u ⟂ c_v`), and the flat case for affine charts
(`curvatureTensor_affine`, `torsionForm_affine`). The book's flatness claim for `T_p` depends on the
chart, not only on the surface: an affine chart of a plane has `T_p = 0`, a polar chart of the same
plane does not. Not printed by the book: `K_p` is symmetric (`curvatureTensor_transpose`), from
`⟨c_u, n⟩ = ⟨c_v, n⟩ = 0` and the symmetry of second derivatives. The normal is the book's
`n = c_u × c_v / ‖c_u × c_v‖`, so the sign of `K_p` depends on the orientation of the chart.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Surface

variable {c : (Fin 2 → ℝ) → Vec3} {α : Fin 2 → ℝ}

/-! ### Differentiability of the frame -/

/-- The cross product of MLS p. 26 as a bilinear map (supporting definition for the derivatives of
the Gauss map, MLS p. 245). -/
private def crossBilin : Vec3 →ₗ[ℝ] Vec3 →ₗ[ℝ] Vec3 :=
  LinearMap.mk₂ ℝ Vec3.cross (fun u v w => Vec3.add_cross u v w)
    (fun a u v => Vec3.smul_cross u v a) (fun u v w => Vec3.cross_add u v w)
    (fun a u v => Vec3.cross_smul u v a)

/-- The cross product of MLS p. 26 as a continuous bilinear map (supporting definition for the
derivatives of the Gauss map, MLS p. 245). -/
private def crossCLM : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ crossBilin)

private theorem crossCLM_apply (u v : Vec3) : crossCLM u v = Vec3.cross u v := rfl

/-- **The cross product of differentiable vector fields is differentiable (supporting lemma for the
Gauss map of MLS eq. (5.19), p. 245, and its derivatives `n_u`, `n_v`).** -/
theorem differentiableAt_cross {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Vec3} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => Vec3.cross (f y) (g y)) x := by
  have h : DifferentiableAt ℝ (fun y => crossCLM (f y) (g y)) x :=
    (crossCLM.differentiableAt.comp x hf).clm_apply hg
  simpa only [crossCLM_apply] using h

/-- **The first frame axis `x = c_u/‖c_u‖` is differentiable (MLS p. 246: its partials `x_u`, `x_v`
enter the torsion form (5.24))**, for `c` twice continuously differentiable at `α` and `c_u ≠ 0`. -/
theorem differentiableAt_frameX (hc : ContDiffAt ℝ 2 c α) (hu : partialU c α ≠ 0) :
    DifferentiableAt ℝ (frameX c) α := by
  have h1 := differentiableAt_partialU hc
  exact ((h1.norm ℝ hu).inv (norm_ne_zero_iff.mpr hu)).smul h1

/-- **The second frame axis `y = c_v/‖c_v‖` is differentiable (MLS p. 247: `ẏ` enters the proof of
Lemma 5.10)**, for `c` twice continuously differentiable at `α` and `c_v ≠ 0`. -/
theorem differentiableAt_frameY (hc : ContDiffAt ℝ 2 c α) (hv : partialV c α ≠ 0) :
    DifferentiableAt ℝ (frameY c) α := by
  have h1 := differentiableAt_partialV hc
  exact ((h1.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul h1

/-- **The Gauss map is differentiable (MLS p. 245: "For smooth, orientable surfaces, the Gauss map
is a well defined, differentiable mapping")**, for `c` twice continuously differentiable at `α` with
`c_u × c_v ≠ 0`. -/
theorem differentiableAt_gaussNormal (hc : ContDiffAt ℝ 2 c α)
    (h0 : Vec3.cross (partialU c α) (partialV c α) ≠ 0) :
    DifferentiableAt ℝ (gaussNormal c) α := by
  have h1 := differentiableAt_cross (differentiableAt_partialU hc) (differentiableAt_partialV hc)
  exact ((h1.norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)).smul h1

/-- **For an orthogonal chart, `c_u × c_v ≠ 0` (MLS p. 247, the proof of Lemma 5.10 divides by
`‖c_u × c_v‖`)**, when `c_u ≠ 0` and `c_v ≠ 0`. -/
theorem cross_partial_ne_zero (h : IsOrthogonalAt c α) (hu : partialU c α ≠ 0)
    (hv : partialV c α ≠ 0) : Vec3.cross (partialU c α) (partialV c α) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cross_partial h]
  exact mul_ne_zero (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hv)

/-! ### The second fundamental form and the curvature tensor -/

/-- **The second fundamental form (MLS eq. (5.20), p. 245):**
`II_p = [[c_uᵀ n_u, c_uᵀ n_v], [c_vᵀ n_u, c_vᵀ n_v]]`, with `n_u`, `n_v` the partials of the Gauss
map `n = c_u × c_v / ‖c_u × c_v‖` of eq. (5.19) (no sign is added to the book's definition). -/
def secondFundamentalForm (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![inner ℝ (partialU c α) (partialU (gaussNormal c) α),
      inner ℝ (partialU c α) (partialV (gaussNormal c) α);
    inner ℝ (partialV c α) (partialU (gaussNormal c) α),
      inner ℝ (partialV c α) (partialV (gaussNormal c) α)]

/-- **The curvature tensor of an orthogonal chart (MLS eq. (5.21), p. 245):**
`K_p = [[c_uᵀ n_u/‖c_u‖², c_uᵀ n_v/(‖c_u‖ ‖c_v‖)], [c_vᵀ n_u/(‖c_u‖ ‖c_v‖), c_vᵀ n_v/‖c_v‖²]]`,
defined by its printed entries, with `n` the Gauss map of eq. (5.19). -/
def curvatureTensor (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![inner ℝ (partialU c α) (partialU (gaussNormal c) α) / ‖partialU c α‖ ^ 2,
      inner ℝ (partialU c α) (partialV (gaussNormal c) α) / (‖partialU c α‖ * ‖partialV c α‖);
    inner ℝ (partialV c α) (partialU (gaussNormal c) α) / (‖partialU c α‖ * ‖partialV c α‖),
      inner ℝ (partialV c α) (partialV (gaussNormal c) α) / ‖partialV c α‖ ^ 2]

/-- **MLS eq. (5.21), p. 245, matrix form: `K_p = M_p⁻ᵀ II_p M_p⁻¹`**, for an orthogonal chart's
metric tensor `M_p = diag(‖c_u‖, ‖c_v‖)` with `c_u ≠ 0` and `c_v ≠ 0`. -/
theorem curvatureTensor_eq_mul (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    curvatureTensor c α =
      ((metricTensor c α)⁻¹)ᵀ * secondFundamentalForm c α * (metricTensor c α)⁻¹ := by
  have hu' : ‖partialU c α‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv' : ‖partialV c α‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hinv : (metricTensor c α)⁻¹ = !![‖partialU c α‖⁻¹, 0; 0, ‖partialV c α‖⁻¹] := by
    rw [Matrix.inv_eq_left_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [metricTensor, Matrix.mul_apply, Fin.sum_univ_two, hu', hv']
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureTensor, secondFundamentalForm, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

/-- **MLS eq. (5.23), p. 245: the curvature tensor in the normalized Gauss frame,
`K_p = [xᵀ; yᵀ] [n_u/‖c_u‖, n_v/‖c_v‖]`**, with `x = c_u/‖c_u‖`, `y = c_v/‖c_v‖`; an identity at
every point. -/
theorem curvatureTensor_eq_frame :
    curvatureTensor c α =
      !![inner ℝ (frameX c α) (partialU (gaussNormal c) α) / ‖partialU c α‖,
          inner ℝ (frameX c α) (partialV (gaussNormal c) α) / ‖partialV c α‖;
        inner ℝ (frameY c α) (partialU (gaussNormal c) α) / ‖partialU c α‖,
          inner ℝ (frameY c α) (partialV (gaussNormal c) α) / ‖partialV c α‖] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureTensor, frameX, frameY, inner_smul_left, div_eq_mul_inv, pow_two, mul_comm,
      mul_left_comm, mul_assoc]

/-- **The curvature tensor is symmetric (not printed by MLS; supports eqs. (5.21), (5.23), p.
245):** for `c` twice continuously differentiable at `α` with `c_u × c_v ≠ 0`, `K_pᵀ = K_p`, because
`c_uᵀ n_v = c_vᵀ n_u`. -/
theorem curvatureTensor_transpose (hc : ContDiffAt ℝ 2 c α)
    (h0 : Vec3.cross (partialU c α) (partialV c α) ≠ 0) :
    (curvatureTensor c α)ᵀ = curvatureTensor c α := by
  have hn := differentiableAt_gaussNormal hc h0
  have hcu := differentiableAt_partialU hc
  have hcv := differentiableAt_partialV hc
  have zu : (fun β => inner ℝ (partialU c β) (gaussNormal c β)) = fun _ => (0 : ℝ) := by
    funext β; rw [real_inner_comm]; exact inner_gaussNormal_partialU
  have zv : (fun β => inner ℝ (partialV c β) (gaussNormal c β)) = fun _ => (0 : ℝ) := by
    funext β; rw [real_inner_comm]; exact inner_gaussNormal_partialV
  have du := fderiv_inner_apply ℝ hcu hn (Pi.single 1 1)
  have dv := fderiv_inner_apply ℝ hcv hn (Pi.single 0 1)
  rw [zu, fderiv_const_apply] at du
  rw [zv, fderiv_const_apply] at dv
  have hs := partialV_partialU hc
  have key : inner ℝ (partialU c α) (partialV (gaussNormal c) α) =
      inner ℝ (partialV c α) (partialU (gaussNormal c) α) := by
    change (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 1 1) = inner ℝ (partialU c α)
      (partialV (gaussNormal c) α) + inner ℝ (partialV (partialU c) α) (gaussNormal c α) at du
    change (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (Pi.single 0 1) = inner ℝ (partialV c α)
      (partialU (gaussNormal c) α) + inner ℝ (partialU (partialV c) α) (gaussNormal c α) at dv
    rw [hs] at du
    simp only [_root_.zero_apply] at du dv
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [curvatureTensor, key]

/-! ### The torsion form -/

/-- **The torsion form (MLS eq. (5.24), p. 246, first expression):** the row vector
`T_p = yᵀ [x_u/‖c_u‖, x_v/‖c_v‖]`, with `x_u`, `x_v` the partials of the frame axis `x = c_u/‖c_u‖`;
a vector `Fin 2 → ℝ` read as a row, so `T M α̇ = T ⬝ᵥ (M α̇)`. -/
def torsionForm (c : (Fin 2 → ℝ) → Vec3) (α : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![inner ℝ (frameY c α) (partialU (frameX c) α) / ‖partialU c α‖,
    inner ℝ (frameY c α) (partialV (frameX c) α) / ‖partialV c α‖]

/-- The partials of the frame axis `x = c_u/‖c_u‖`: `x_e = ‖c_u‖⁻¹ ∂_e c_u + (∂_e ‖c_u‖⁻¹) c_u`
(supporting lemma for MLS eq. (5.24), p. 246). -/
private theorem fderiv_frameX_apply (hc : ContDiffAt ℝ 2 c α) (hu : partialU c α ≠ 0)
    (e : Fin 2 → ℝ) :
    fderiv ℝ (frameX c) α e = ‖partialU c α‖⁻¹ • fderiv ℝ (partialU c) α e +
      (fderiv ℝ (fun β => ‖partialU c β‖⁻¹) α e) • partialU c α := by
  have h1 := differentiableAt_partialU hc
  have hk : DifferentiableAt ℝ (fun β => ‖partialU c β‖⁻¹) α :=
    (h1.norm ℝ hu).inv (norm_ne_zero_iff.mpr hu)
  change fderiv ℝ (fun β => ‖partialU c β‖⁻¹ • partialU c β) α e = _
  rw [fderiv_fun_smul hk h1]
  simp

/-- **MLS eq. (5.24), p. 246, second expression:
`T_p = [c_vᵀ c_uu/(‖c_u‖² ‖c_v‖), c_vᵀ c_uv/(‖c_u‖ ‖c_v‖²)]`**, for a chart twice continuously
differentiable at `α`, orthogonal at `α`, with `c_u ≠ 0` and `c_v ≠ 0`; `c_uu = ∂c_u/∂u` and
`c_uv = ∂c_u/∂v` (equal to `∂c_v/∂u` by `partialV_partialU`). -/
theorem torsionForm_eq (hc : ContDiffAt ℝ 2 c α) (h : IsOrthogonalAt c α)
    (hu : partialU c α ≠ 0) (hv : partialV c α ≠ 0) :
    torsionForm c α =
      ![inner ℝ (partialV c α) (partialU (partialU c) α) / (‖partialU c α‖ ^ 2 * ‖partialV c α‖),
        inner ℝ (partialV c α) (partialV (partialU c) α) /
          (‖partialU c α‖ * ‖partialV c α‖ ^ 2)] := by
  have hvu : inner ℝ (frameY c α) (partialU c α) = 0 := by
    rw [frameY, inner_smul_left, real_inner_comm, show inner ℝ (partialU c α) (partialV c α) = 0
      from h]
    simp
  have e0 := fderiv_frameX_apply hc hu (Pi.single 0 1)
  have e1 := fderiv_frameX_apply hc hu (Pi.single 1 1)
  have hu' : ‖partialU c α‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv' : ‖partialV c α‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have c0 : inner ℝ (frameY c α) (fderiv ℝ (frameX c) α (Pi.single 0 1)) / ‖partialU c α‖ =
      inner ℝ (partialV c α) (partialU (partialU c) α) /
        (‖partialU c α‖ ^ 2 * ‖partialV c α‖) := by
    rw [e0, inner_add_right, inner_smul_right, inner_smul_right, hvu, frameY, inner_smul_left]
    simp only [RCLike.conj_to_real, mul_zero, add_zero]
    change ‖partialU c α‖⁻¹ * (‖partialV c α‖⁻¹ * inner ℝ (partialV c α)
      (partialU (partialU c) α)) / ‖partialU c α‖ = _
    field_simp
  have c1 : inner ℝ (frameY c α) (fderiv ℝ (frameX c) α (Pi.single 1 1)) / ‖partialV c α‖ =
      inner ℝ (partialV c α) (partialV (partialU c) α) /
        (‖partialU c α‖ * ‖partialV c α‖ ^ 2) := by
    rw [e1, inner_add_right, inner_smul_right, inner_smul_right, hvu, frameY, inner_smul_left]
    simp only [RCLike.conj_to_real, mul_zero, add_zero]
    change ‖partialU c α‖⁻¹ * (‖partialV c α‖⁻¹ * inner ℝ (partialV c α)
      (partialV (partialU c) α)) / ‖partialV c α‖ = _
    field_simp
  funext i
  fin_cases i
  · exact c0
  · exact c1

/-! ### Flat surfaces -/

/-- **A flat surface has zero curvature (MLS p. 246: "If the surface is flat, then `n_u = n_v = 0`
and `K_p = 0`"):** at a point where the partials of the Gauss map vanish, `K_p = 0`. -/
theorem curvatureTensor_eq_zero (hnu : partialU (gaussNormal c) α = 0)
    (hnv : partialV (gaussNormal c) α = 0) : curvatureTensor c α = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [curvatureTensor, hnu, hnv]

/-- The partials of an affine chart `β ↦ p + L β` are the constant vectors `L e_u`, `L e_v`
(supporting lemma for the flat case of MLS p. 246). -/
private theorem fderiv_affine (p : Vec3) (L : (Fin 2 → ℝ) →L[ℝ] Vec3) (β : Fin 2 → ℝ) :
    fderiv ℝ (fun γ => p + L γ) β = L :=
  (L.hasFDerivAt.const_add p).fderiv

/-- **MLS p. 246, the flat case of the curvature tensor, for an affine chart:** if `c(β) = p + L β`
with `L` linear, the Gauss map is constant, `n_u = n_v = 0` and `K_p = 0` at every point. -/
theorem curvatureTensor_affine (p : Vec3) (L : (Fin 2 → ℝ) →L[ℝ] Vec3) (α : Fin 2 → ℝ) :
    curvatureTensor (fun γ => p + L γ) α = 0 := by
  have hn : gaussNormal (fun γ => p + L γ) = fun _ =>
      ‖Vec3.cross (L (Pi.single 0 1)) (L (Pi.single 1 1))‖⁻¹ •
        Vec3.cross (L (Pi.single 0 1)) (L (Pi.single 1 1)) := by
    funext β
    simp only [gaussNormal, partialU, partialV, fderiv_affine]
  apply curvatureTensor_eq_zero <;> simp [partialU, partialV, hn]

/-- **MLS p. 246, the flat case of the torsion form, for an affine chart:** if `c(β) = p + L β` with
`L` linear, the frame axis `x` is constant, `x_u = x_v = 0` and `T_p = 0` at every point. (For a
non-affine chart of a plane the torsion form need not vanish.) -/
theorem torsionForm_affine (p : Vec3) (L : (Fin 2 → ℝ) →L[ℝ] Vec3) (α : Fin 2 → ℝ) :
    torsionForm (fun γ => p + L γ) α = 0 := by
  have hx : frameX (fun γ => p + L γ) = fun _ => ‖L (Pi.single 0 1)‖⁻¹ • L (Pi.single 0 1) := by
    funext β
    simp only [frameX, partialU, fderiv_affine]
  funext i
  fin_cases i <;> simp [torsionForm, partialU, partialV, hx]

end Surface
end RoboLean
