import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import RoboLean.Control.MatrixAnalysis

/-!
# The Jacobian matrix of a coordinate map and its rate (MLS §5.4, p. 196)

MLS workspace control (§5.4, printed pp. 195–199) takes a map `f : Q → ℝᵖ` from joint variables
to workspace variables and writes `ẋ = J(θ) θ̇` with `J(θ) = ∂f/∂θ`, "the Jacobian of the mapping
`f` and not the manipulator Jacobian" (p. 196); it then uses `θ̇ = J⁻¹ ẋ` and
`θ̈ = J⁻¹ ẍ + (d/dt)(J⁻¹) ẋ`. Here:

* `jac f θ` is the matrix of the Fréchet derivative of `f : ℝⁿ → ℝᵐ` at `θ`: its column `j` is the
  derivative of `f` in the direction of the `j`th coordinate vector, so `jac f θ v = Df(θ) v`
  (`jac_mulVec`) and its entries come from the derivatives of the components
  (`jac_apply_of_hasFDerivAt`); it is distinct from the twist Jacobians of
  `RoboLean.Kinematics.Jacobian` (`6 × n`, indexed by `Fin 3 ⊕ Fin 3`); linear coordinates
  `x = A θ` have `J = A` and `J̇ = 0` (`jac_linear`, `jacDot_linear`, `contDiff_linear`);
* `jacDot f θ v` is the matrix of the second derivative `D²f(θ)(v, ·)`; along a motion `θ(t)` with
  velocity `θ̇` it is the actual derivative `J̇` of `t ↦ J(θ(t))` (`hasDerivAt_jac_comp`), and
  `ẍ = J̇ θ̇ + J θ̈` (`hasDerivAt_jac_mulVec_comp`);
* the derivatives of matrix products, transposes and inverses along a curve are stated entry by
  entry (`Control.hasDerivAt_matrix_mul`, `Control.hasDerivAt_matrix_transpose`,
  `Control.hasDerivAt_matrix_inv`), the library's convention since E013;
  `Control.hasDerivAt_matrix_iff` is the bridge to Mathlib's `HasDerivAt` for matrix-valued curves
  (product topology). These four live in `RoboLean.Control.MatrixAnalysis` since E030; the
  `MapJacobian.*` names are deprecated aliases;
* `(d/dt)(J⁻¹) = −J⁻¹ J̇ J⁻¹` (`hasDerivAt_jac_inv_comp`) and the two formulas of p. 196
  (`velocity_eq_inv_mulVec`, `acceleration_eq_inv_mulVec`) hold where `J(θ(t))` is invertible;
* an invertible `J(a)` makes `f` a homeomorphism between open neighborhoods of `a` and `f(a)`
  whose inverse is `C²` at `f(a)` (`exists_localInverse_of_isUnit_det_jac`, Mathlib's inverse
  function theorem): the property "`f` is locally invertible" that MLS invokes on p. 197.

Conventions: vectors are `Fin n → ℝ`; matrices act by `Matrix.mulVec`; the inverse is Mathlib's
`Matrix.inv` (the zero matrix for a singular matrix, so every statement that uses `J⁻¹` assumes
`IsUnit (jac f θ).det` at the point where it is used); `f` is `C²` on all of `ℝⁿ`
(`ContDiff ℝ 2 f`) where a second derivative is used. MLS asks `f` to be "smooth and invertible"
(p. 196); its proofs use only that `J` is invertible (p. 197), which is the hypothesis here.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace MapJacobian

variable {m n : ℕ}

/-- **The Jacobian matrix `J(θ) = ∂f/∂θ` of a map `f : ℝⁿ → ℝᵐ` (MLS p. 196).** Entry `(i, j)` is
the `i`th component of the Fréchet derivative of `f` at `θ` applied to the `j`th coordinate vector
`e_j = Pi.single j 1`. Where `f` is not differentiable, Mathlib's `fderiv` and hence `jac f θ` are
zero. -/
def jac (f : (Fin n → ℝ) → Fin m → ℝ) (θ : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ f θ (Pi.single j 1) i

/-- **The rate `J̇` of the Jacobian matrix (MLS p. 196, `(d/dt) J`):** `jacDot f θ v` is the matrix
of the second derivative `D²f(θ)(v, ·)`, entry `(i, j)` being `D²f(θ)(v, e_j)ᵢ`. Along a motion with
velocity `θ̇`, `J̇ = jacDot f θ θ̇` (`hasDerivAt_jac_comp`). -/
def jacDot (f : (Fin n → ℝ) → Fin m → ℝ) (θ v : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fderiv ℝ f) θ v (Pi.single j 1) i

/-- A matrix whose entry `(i, j)` is `L e_j` at `i` for a linear map `L` represents `L`. -/
private theorem of_mulVec_eq (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (v : Fin n → ℝ) :
    (Matrix.of fun i j => L (Pi.single j 1) i) *ᵥ v = L v := by
  conv_rhs => rw [pi_eq_sum_univ' v]
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, Finset.sum_apply, mul_comm]

/-- **`ẋ = J(θ) θ̇` (MLS p. 196):** the Jacobian matrix applied to `v` is the Fréchet derivative of
`f` at `θ` applied to `v`, for every map `f`. -/
theorem jac_mulVec (f : (Fin n → ℝ) → Fin m → ℝ) (θ v : Fin n → ℝ) :
    jac f θ *ᵥ v = fderiv ℝ f θ v :=
  of_mulVec_eq _ v

/-- **`J̇ w = D²f(θ)(v, w)` (MLS p. 196):** the rate matrix `jacDot f θ v` applied to `w` is the
second Fréchet derivative of `f` at `θ` applied to `(v, w)`, for every map `f`. -/
theorem jacDot_mulVec (f : (Fin n → ℝ) → Fin m → ℝ) (θ v w : Fin n → ℝ) :
    jacDot f θ v *ᵥ w = fderiv ℝ (fderiv ℝ f) θ v w :=
  of_mulVec_eq _ w

/-- **The Jacobian matrix from the derivatives of the components (MLS p. 196, `J = ∂f/∂θ`):** if
each component `x ↦ f(x)ᵢ` has the Fréchet derivative `L i` at `θ`, then `J(θ)ᵢⱼ = L i e_j`. -/
theorem jac_apply_of_hasFDerivAt {f : (Fin n → ℝ) → Fin m → ℝ} {θ : Fin n → ℝ}
    {L : Fin m → ((Fin n → ℝ) →L[ℝ] ℝ)} (hL : ∀ i, HasFDerivAt (fun x => f x i) (L i) θ)
    (i : Fin m) (j : Fin n) : jac f θ i j = L i (Pi.single j 1) := by
  have h : HasFDerivAt f (ContinuousLinearMap.pi L) θ := hasFDerivAt_pi.mpr hL
  simp [jac, h.fderiv]

/-- **Linear workspace coordinates `x = A θ` (MLS p. 196):** the map `θ ↦ A θ` is `C^k` for every
`k`. -/
theorem contDiff_linear (A : Matrix (Fin m) (Fin n) ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k fun q : Fin n → ℝ => A *ᵥ q :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff

private theorem fderiv_linear (A : Matrix (Fin m) (Fin n) ℝ) :
    fderiv ℝ (fun q : Fin n → ℝ => A *ᵥ q) =
      fun _ => LinearMap.toContinuousLinearMap (Matrix.mulVecLin A) := by
  funext θ
  exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).hasFDerivAt.fderiv

/-- **Linear workspace coordinates `x = A θ` (MLS p. 196):** their Jacobian matrix is `A` at every
configuration. -/
theorem jac_linear (A : Matrix (Fin m) (Fin n) ℝ) (θ : Fin n → ℝ) :
    jac (fun q => A *ᵥ q) θ = A := by
  ext i j
  simp [jac, fderiv_linear]

/-- **Linear workspace coordinates `x = A θ` (MLS p. 196):** the rate `J̇` of their Jacobian
matrix is zero. -/
theorem jacDot_linear (A : Matrix (Fin m) (Fin n) ℝ) (θ v : Fin n → ℝ) :
    jacDot (fun q => A *ᵥ q) θ v = 0 := by
  ext i j
  simp [jacDot, fderiv_linear]

/-! ### Derivatives along a motion -/

/-- **`ẋ = J(θ) θ̇` along a motion (MLS p. 196):** if `f` is differentiable at `θ(t)` and the
motion `θ` has velocity `θ'` at `t`, then `x = f ∘ θ` has velocity `J(θ(t)) θ'` at `t`. -/
theorem hasDerivAt_comp {f : (Fin n → ℝ) → Fin m → ℝ} {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hf : DifferentiableAt ℝ f (θ t)) (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => f (θ s)) (jac f (θ t) *ᵥ θ') t := by
  rw [jac_mulVec]
  exact hf.hasFDerivAt.comp_hasDerivAt t hθ

private theorem hasDerivAt_fderiv_comp {f : (Fin n → ℝ) → Fin m → ℝ} (hf : ContDiff ℝ 2 f)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => fderiv ℝ f (θ s)) (fderiv ℝ (fderiv ℝ f) (θ t) θ') t := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) (θ t) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) (θ t)
  exact h1.hasFDerivAt.comp_hasDerivAt t hθ

/-- **`J̇` is the actual derivative of `J(θ(t))` (MLS p. 196):** for a `C²` map `f` and a motion
`θ` with velocity `θ'` at `t`, every entry of `s ↦ J(θ(s))` has the derivative
`jacDot f (θ t) θ'` (same entry) at `t`. -/
theorem hasDerivAt_jac_comp {f : (Fin n → ℝ) → Fin m → ℝ} (hf : ContDiff ℝ 2 f)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t) (i : Fin m)
    (j : Fin n) :
    HasDerivAt (fun s => jac f (θ s) i j) (jacDot f (θ t) θ' i j) t := by
  have h := (hasDerivAt_fderiv_comp hf hθ).clm_apply (hasDerivAt_const t (Pi.single j (1 : ℝ)))
  simp only [map_zero, add_zero] at h
  exact hasDerivAt_pi.mp h i

/-- **`ẍ = J̇ θ̇ + J θ̈` (MLS p. 196, differentiating `ẋ = J(θ) θ̇`):** for a `C²` map `f`, a motion
`θ` with velocity `θ'(t)` at `t` and a velocity curve `θ'` with derivative `θ''` at `t`,
`s ↦ J(θ(s)) θ'(s)` has the derivative `jacDot f (θ t) (θ' t) θ'(t) + J(θ(t)) θ''` at `t`. -/
theorem hasDerivAt_jac_mulVec_comp {f : (Fin n → ℝ) → Fin m → ℝ} (hf : ContDiff ℝ 2 f)
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ (θ' t) t)
    (hθ' : HasDerivAt θ' θ'' t) :
    HasDerivAt (fun s => jac f (θ s) *ᵥ θ' s)
      (jacDot f (θ t) (θ' t) *ᵥ θ' t + jac f (θ t) *ᵥ θ'') t := by
  simp only [jac_mulVec, jacDot_mulVec]
  exact (hasDerivAt_fderiv_comp hf hθ).clm_apply hθ'

/-! The entry-by-entry derivatives of matrix-valued curves moved to the `Control` namespace
(`RoboLean.Control.MatrixAnalysis`) on 2026-10-13; the old names remain as deprecated aliases. -/

@[deprecated Control.hasDerivAt_matrix_iff (since := "2026-10-13")]
alias hasDerivAt_matrix_iff := Control.hasDerivAt_matrix_iff

@[deprecated Control.hasDerivAt_matrix_mul (since := "2026-10-13")]
alias hasDerivAt_matrix_mul := Control.hasDerivAt_matrix_mul

@[deprecated Control.hasDerivAt_matrix_transpose (since := "2026-10-13")]
alias hasDerivAt_matrix_transpose := Control.hasDerivAt_matrix_transpose

@[deprecated Control.hasDerivAt_matrix_inv (since := "2026-10-13")]
alias hasDerivAt_matrix_inv := Control.hasDerivAt_matrix_inv

/-- **`(d/dt)(J⁻¹) = −J⁻¹ J̇ J⁻¹` along a motion (MLS p. 196):** for a `C²` map `f`, a motion `θ`
with velocity `θ'` at `t`, and `J(θ(t))` invertible, every entry of `s ↦ J(θ(s))⁻¹` has the
derivative `−J⁻¹ J̇ J⁻¹` (same entry) at `t`, with `J = jac f (θ t)` and
`J̇ = jacDot f (θ t) θ'`. -/
theorem hasDerivAt_jac_inv_comp {f : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hJ : IsUnit (jac f (θ t)).det) (i j : Fin n) :
    HasDerivAt (fun s => (jac f (θ s))⁻¹ i j)
      ((-((jac f (θ t))⁻¹ * jacDot f (θ t) θ' * (jac f (θ t))⁻¹)) i j) t :=
  Control.hasDerivAt_matrix_inv (A := fun s => jac f (θ s)) (hasDerivAt_jac_comp hf hθ) hJ i j

/-! ### The joint velocity and acceleration from the workspace ones (MLS p. 196) -/

/-- **`θ̇ = J⁻¹ ẋ` (MLS p. 196):** where `J(θ)` is invertible, the joint rate `v` is recovered from
the workspace rate `J(θ) v`. -/
theorem velocity_eq_inv_mulVec {f : (Fin n → ℝ) → Fin n → ℝ} {q : Fin n → ℝ}
    (hJ : IsUnit (jac f q).det) (v : Fin n → ℝ) : v = (jac f q)⁻¹ *ᵥ (jac f q *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]

/-- **`θ̈ = J⁻¹ ẍ + (d/dt)(J⁻¹) ẋ` (MLS p. 196):** for a `C²` map `f`, a motion `θ` with velocity
`θ'` at `t` and `J(θ(t))` invertible, every actual derivative `X'` of `s ↦ J(θ(s))⁻¹` at `t`
(entry by entry) and every `θ''` satisfy `θ'' = J⁻¹ ẍ + X' ẋ`, where `ẋ = J θ'` and
`ẍ = J̇ θ' + J θ''` are the workspace velocity and acceleration (`hasDerivAt_comp`,
`hasDerivAt_jac_mulVec_comp`). -/
theorem acceleration_eq_inv_mulVec {f : (Fin n → ℝ) → Fin n → ℝ} (hf : ContDiff ℝ 2 f)
    {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hJ : IsUnit (jac f (θ t)).det) {X' : Matrix (Fin n) (Fin n) ℝ}
    (hX' : ∀ i j, HasDerivAt (fun s => (jac f (θ s))⁻¹ i j) (X' i j) t) (θ'' : Fin n → ℝ) :
    θ'' = (jac f (θ t))⁻¹ *ᵥ (jacDot f (θ t) θ' *ᵥ θ' + jac f (θ t) *ᵥ θ'') +
      X' *ᵥ (jac f (θ t) *ᵥ θ') := by
  have hX : X' = -((jac f (θ t))⁻¹ * jacDot f (θ t) θ' * (jac f (θ t))⁻¹) := by
    ext i j
    exact (hX' i j).unique (hasDerivAt_jac_inv_comp hf hθ hJ i j)
  rw [hX, Matrix.mulVec_add, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ,
    Matrix.mul_one, Matrix.one_mulVec]
  abel

/-! ### Local invertibility (MLS p. 197) -/

/-- **An invertible Jacobian matrix makes `f` locally invertible (MLS p. 197, "since `f` is locally
invertible").** For a `C²` map `f : ℝⁿ → ℝⁿ` with `J(a)` invertible there is an open partial
homeomorphism `g` that agrees with `f` everywhere, has `a` in its (open) source, and whose
inverse is `C²` at `f(a)`. This is Mathlib's inverse function theorem
(`ContDiffAt.toOpenPartialHomeomorph`, `OpenPartialHomeomorph.contDiffAt_symm`); the hypothesis is
the invertibility of `J` used by MLS's proofs, not the global invertibility of `f` stated on
p. 196. -/
theorem exists_localInverse_of_isUnit_det_jac {f : (Fin n → ℝ) → Fin n → ℝ}
    (hf : ContDiff ℝ 2 f) {a : Fin n → ℝ} (hJ : IsUnit (jac f a).det) :
    ∃ g : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ), a ∈ g.source ∧
      (g : (Fin n → ℝ) → Fin n → ℝ) = f ∧ ContDiffAt ℝ 2 g.symm (f a) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have : Invertible (jac f a) :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr hJ).nonempty_invertible.some
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (Matrix.toLinearEquiv' (jac f a) inferInstance).toContinuousLinearEquiv
  have he : (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ f a := by
    ext v : 1
    rw [← jac_mulVec f a v]
    rfl
  have hF : HasFDerivAt f (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := by
    rw [he]
    exact (hd a).hasFDerivAt
  have hc : ContDiffAt ℝ 2 f a := hf.contDiffAt
  set g := hc.toOpenPartialHomeomorph f hF (by norm_num) with hg
  have hsrc : a ∈ g.source := hc.mem_toOpenPartialHomeomorph_source hF (by norm_num)
  have hmem : f a ∈ g.target := hc.image_mem_toOpenPartialHomeomorph_target hF (by norm_num)
  have hcoe : (g : (Fin n → ℝ) → (Fin n → ℝ)) = f := hc.toOpenPartialHomeomorph_coe hF (by norm_num)
  have hleft : g.symm (f a) = a := by
    have := g.left_inv hsrc
    rwa [hcoe] at this
  refine ⟨g, hsrc, hcoe, ?_⟩
  refine g.contDiffAt_symm (f₀' := e) hmem ?_ ?_
  · rw [hleft, hcoe]
    exact hF
  · rw [hleft, hcoe]
    exact hc

end MapJacobian
end RoboLean
