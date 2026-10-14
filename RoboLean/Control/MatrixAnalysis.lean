import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix

/-!
# Matrix and derivative lemmas shared by the control modules

Small facts about dot products, matrix–vector products, positive definite matrices and the norm
of a pair, used in MLS Chapter 4, Section 5 (printed pp. 189–195): the derivative of the energy
`½ θ̇ᵀ M θ̇ + ½ eᵀ K_p e` along motions (p. 193), the inverse of the positive definite inertia
matrix in the closed loop (pp. 190–191), and comparisons of `‖(e, ė)‖²` with `‖e‖² + ‖ė‖²`.

Conventions: vectors are `Fin n → ℝ` with Mathlib's dot product `⬝ᵥ` and matrix–vector product
`*ᵥ`; the norm on `Fin n → ℝ` and on products is Mathlib's sup norm (maximum of the components);
"positive definite" is Mathlib's `Matrix.PosDef`, which includes symmetry.

These lemmas were collected here in E019 from `ManipulatorSystem` and `PDControl` (E016); their
names are unchanged. E030 added the product rule for a time-varying matrix applied to a curve and
the bilinear bounds `|vᵀ A w| ≤ κ ‖v‖ ‖w‖` (from `AugmentedPD`, names unchanged), and the
entry-by-entry derivatives of matrix-valued curves (`hasDerivAt_matrix_iff`, `_mul`, `_transpose`,
`_inv`, from `MapJacobian`, whose old names are deprecated aliases). E035 added the rectangular
product rule `hasDerivAt_matrix_mulVec_rect` (from `ConstrainedLagrangian`) and the congruence
identity `reduced_sub_two_eq`, `skew_reduced` of Lemmas 4.11(2) and 6.1(2) (from
`CompositeDynamics`); the old names are deprecated aliases.
-/

open Matrix

namespace RoboLean
namespace Control

variable {n : ℕ}

/-- **Product rule for the dot product of two curves in `ℝⁿ`**, used for `V̇` in the proof of
MLS Proposition 4.9 (p. 193) and for the skewed energy of Example 4.5 (p. 186). -/
theorem hasDerivAt_dotProduct {a b : ℝ → Fin n → ℝ} {a' b' : Fin n → ℝ} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => a s ⬝ᵥ b s) (a' ⬝ᵥ b t + a t ⬝ᵥ b') t := by
  have ha' := hasDerivAt_pi.mp ha
  have hb' := hasDerivAt_pi.mp hb
  have h : HasDerivAt (fun s => ∑ i, a s i * b s i) (∑ i, (a' i * b t i + a t i * b' i)) t :=
    HasDerivAt.fun_sum fun i _ => (ha' i).mul (hb' i)
  convert h using 1
  · funext s
    simp only [dotProduct]
  · simp only [dotProduct, Finset.sum_add_distrib]

/-- **A constant matrix applied to a differentiable curve in `ℝⁿ`**, used for the derivative of
`eᵀ K_p e` in the proof of MLS Proposition 4.9 (p. 193). -/
theorem hasDerivAt_mulVec_const (A : Matrix (Fin n) (Fin n) ℝ) {a : ℝ → Fin n → ℝ}
    {a' : Fin n → ℝ} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => A *ᵥ a s) (A *ᵥ a') t := by
  have ha' := hasDerivAt_pi.mp ha
  refine hasDerivAt_pi.mpr fun i => ?_
  have h : HasDerivAt (fun s => ∑ j, A i j * a s j) (∑ j, A i j * a' j) t :=
    HasDerivAt.fun_sum fun j _ => (ha' j).const_mul (A i j)
  simpa [Matrix.mulVec, dotProduct] using h

/-- **A positive definite matrix cancels against its inverse on vectors: `M (M⁻¹ w) = w`**
(MLS pp. 190–191: "since `M(θ)` is always positive definite"). The inverse is Mathlib's
`Matrix.inv`. -/
theorem PosDef.mulVec_inv_mulVec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (w : Fin n → ℝ) : A *ᵥ (A⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hA.isUnit), Matrix.one_mulVec]

/-- **A positive definite matrix cancels against its inverse on vectors: `M⁻¹ (M w) = w`**
(MLS pp. 190–191: "since `M(θ)` is always positive definite"). The inverse is Mathlib's
`Matrix.inv`. -/
theorem PosDef.inv_mulVec_mulVec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (w : Fin n → ℝ) : A⁻¹ *ᵥ (A *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    hA.isUnit), Matrix.one_mulVec]

/-- **For a symmetric real matrix, `x ⬝ A y = y ⬝ A x`** (used for `K_p` in the proof of MLS
Proposition 4.9, p. 193, and for the skewed energy of Example 4.5, p. 186). -/
theorem dotProduct_mulVec_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]

/-- **The square of the norm of a pair is at most the sum of the squares of the norms of its
components** (the norm of a product is the maximum, `Prod.norm_def`); used to compare Lyapunov
functions on the state `(θ, θ̇)` with `‖(θ, θ̇)‖²` (MLS Definition 4.4, p. 182). -/
theorem sq_norm_prod_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (z : E × F) :
    ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases max_choice ‖z.1‖ ‖z.2‖ with h | h <;> rw [h] <;> nlinarith [sq_nonneg ‖z.1‖,
    sq_nonneg ‖z.2‖]


/-! ### Time-varying matrices and bilinear bounds -/

/-- **Product rule for a time-varying matrix applied to a curve in `ℝⁿ`** (used for
`d/dt (M(θ) ė)` in the proof of MLS Proposition 4.10, p. 195): if every entry of `A` has the
derivative `A'ᵢⱼ` at `t` and `b` has the derivative `b'`, then `s ↦ A(s) b(s)` has the derivative
`A' b(t) + A(t) b'`. -/
theorem hasDerivAt_matrix_mulVec {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {A' : Matrix (Fin n) (Fin n) ℝ} {b : ℝ → Fin n → ℝ} {b' : Fin n → ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => A s *ᵥ b s) (A' *ᵥ b t + A t *ᵥ b') t := by
  have hb' := hasDerivAt_pi.mp hb
  refine hasDerivAt_pi.mpr fun i => ?_
  have h : HasDerivAt (fun s => ∑ j, A s i j * b s j)
      (∑ j, (A' i j * b t j + A t i j * b' j)) t :=
    HasDerivAt.fun_sum fun j _ => (hA i j).mul (hb' j)
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using h

section Rectangular

variable {k : ℕ}

/-- **Product rule for a rectangular matrix-valued curve applied to a curve** (for
`(d/dt)(A(q) q̇) = Ȧ q̇ + A q̈`, MLS p. 269): if every entry of `A` has the derivative `A'ᵢⱼ` at `t`
and `b` has the derivative `b'`, then `s ↦ A(s) b(s)` has the derivative `A' b(t) + A(t) b'`. The
square case is `Control.hasDerivAt_matrix_mulVec`. -/
theorem hasDerivAt_matrix_mulVec_rect {A : ℝ → Matrix (Fin k) (Fin n) ℝ}
    {A' : Matrix (Fin k) (Fin n) ℝ} {b : ℝ → Fin n → ℝ} {b' : Fin n → ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => A s *ᵥ b s) (A' *ᵥ b t + A t *ᵥ b') t := by
  have hb' := hasDerivAt_pi.mp hb
  refine hasDerivAt_pi.mpr fun i => ?_
  have h : HasDerivAt (fun s => ∑ j, A s i j * b s j)
      (∑ j, (A' i j * b t j + A t i j * b' j)) t :=
    HasDerivAt.fun_sum fun j _ => (hA i j).mul (hb' j)
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using h

end Rectangular

/-- **A bilinear bound for a real square matrix** in the sup norm on `ℝⁿ`:
`|vᵀ A w| ≤ (∑ᵢⱼ |Aᵢⱼ|) ‖v‖ ‖w‖`; used for the cross terms of the skewed energy in the proof of
MLS Proposition 4.10 (p. 195) and Example 4.5 (p. 186). -/
theorem abs_dotProduct_mulVec_le (A : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    |v ⬝ᵥ (A *ᵥ w)| ≤ (∑ i, ∑ j, |A i j|) * ‖v‖ * ‖w‖ := by
  have hv : ∀ i, |v i| ≤ ‖v‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hw : ∀ j, |w j| ≤ ‖w‖ := fun j => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm w j
  have key : v ⬝ᵥ (A *ᵥ w) = ∑ i, ∑ j, v i * A i j * w j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 : |v i| * |A i j| ≤ ‖v‖ * |A i j| := mul_le_mul_of_nonneg_right (hv i) (abs_nonneg _)
  calc |v i| * |A i j| * |w j| ≤ ‖v‖ * |A i j| * ‖w‖ :=
        mul_le_mul h1 (hw j) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    _ = |A i j| * ‖v‖ * ‖w‖ := by ring

/-- **A bilinear bound for a real square matrix** (MLS p. 195, the cross terms of `V̇`): some
`κ ≥ 0` gives `|vᵀ A w| ≤ κ ‖v‖ ‖w‖` for all `v, w` (sup norm on `ℝⁿ`). -/
theorem exists_abs_dotProduct_mulVec_le (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ κ ≥ 0, ∀ v w : Fin n → ℝ, |v ⬝ᵥ (A *ᵥ w)| ≤ κ * ‖v‖ * ‖w‖ :=
  ⟨∑ i, ∑ j, |A i j|, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _,
    abs_dotProduct_mulVec_le A⟩

/-! ### Matrix-valued curves, entry by entry -/

/-- **Matrix-valued curves, entry by entry** (for `(d/dt) J` and `(d/dt)(J⁻¹)`, MLS p. 196): a
matrix-valued curve has a derivative (Mathlib's `HasDerivAt`, product topology on matrices) exactly
when every entry has the corresponding derivative. -/
theorem hasDerivAt_matrix_iff {a b : ℕ} {A : ℝ → Matrix (Fin a) (Fin b) ℝ}
    {A' : Matrix (Fin a) (Fin b) ℝ} {t : ℝ} :
    HasDerivAt A A' t ↔ ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t := by
  refine ⟨fun h i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j,
    fun h => hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h i j⟩

/-- **Product rule for matrix-valued curves, entry by entry** (used for `(d/dt)(J⁻ᵀ M J⁻¹)` in the
proof of MLS Lemma 4.11(2), p. 197): `d/dt (A B) = A' B + A B'`. -/
theorem hasDerivAt_matrix_mul {a b c : ℕ} {A : ℝ → Matrix (Fin a) (Fin b) ℝ}
    {B : ℝ → Matrix (Fin b) (Fin c) ℝ} {A' : Matrix (Fin a) (Fin b) ℝ}
    {B' : Matrix (Fin b) (Fin c) ℝ} {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i : Fin a) (k : Fin c) :
    HasDerivAt (fun s => (A s * B s) i k) ((A' * B t + A t * B') i k) t := by
  have h : HasDerivAt (fun s => ∑ j, A s i j * B s j k)
      (∑ j, (A' i j * B t j k + A t i j * B' j k)) t :=
    HasDerivAt.fun_sum fun j _ => (hA i j).mul (hB j k)
  simpa [Matrix.mul_apply, dotProduct, Finset.sum_add_distrib] using h

/-- **Transpose of a matrix-valued curve, entry by entry** (MLS p. 197, `(d/dt)(J⁻ᵀ)`):
`d/dt Aᵀ = (A')ᵀ`. -/
theorem hasDerivAt_matrix_transpose {a b : ℕ} {A : ℝ → Matrix (Fin a) (Fin b) ℝ}
    {A' : Matrix (Fin a) (Fin b) ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (i : Fin b) (j : Fin a) :
    HasDerivAt (fun s => (A s)ᵀ i j) (A'ᵀ i j) t :=
  hA j i

open scoped Matrix.Norms.Operator in
/-- **The derivative of the matrix inverse along a curve** (MLS p. 196, `(d/dt)(J⁻¹)`): if every
entry of `A` has the derivative `A'` at `t` and `A(t)` is invertible, then every entry of
`s ↦ A(s)⁻¹` has the derivative `−A(t)⁻¹ A' A(t)⁻¹` at `t`. The inverse is `Matrix.inv`. -/
theorem hasDerivAt_matrix_inv {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {A' : Matrix (Fin n) (Fin n) ℝ}
    {t : ℝ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) (hu : IsUnit (A t).det)
    (i j : Fin n) :
    HasDerivAt (fun s => (A s)⁻¹ i j) ((-((A t)⁻¹ * A' * (A t)⁻¹)) i j) t := by
  have hu' : IsUnit (A t) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
  have hA' : HasDerivAt A A' t := hasDerivAt_matrix_iff.mpr hA
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) hu'.unit).comp_hasDerivAt t (f := A) (by exact hA')
  have e : (fun s => (A s)⁻¹) = Ring.inverse ∘ A := by
    funext s
    exact Matrix.nonsing_inv_eq_ringInverse (A s)
  have hinv : ((hu'.unit⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) =
      (A t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    conv_rhs => rw [← hu'.unit_spec]
    rw [Ring.inverse_unit]
  have h2 : HasDerivAt (fun s => (A s)⁻¹) (-((A t)⁻¹ * A' * (A t)⁻¹)) t := by
    rw [e]
    convert h using 1
    case e'_9 =>
      rw [hinv]
      simp [ContinuousLinearMap.mulLeftRight_apply]
    all_goals rfl
  exact hasDerivAt_matrix_iff.mp h2 i j

/-! ### The congruence identity (MLS Lemmas 4.11(2) and 6.1(2), pp. 197, 279) -/

section Congruence

variable {ι κ : Type*} [Fintype ι]

/-- **The identity in the proof of MLS Lemma 6.1(2), p. 279, for a rectangular reduction `S`.** With
`M̃ = Sᵀ M S`, `M̃˙ = S'ᵀ M S + Sᵀ Ṁ S + Sᵀ M S'` and `C̃ = Sᵀ (C S + M S')`,
`M̃˙ − 2C̃ = Sᵀ (Ṁ − 2C) S + S'ᵀ M S − Sᵀ M S'`. For `S = J_h⁻¹ Gᵀ` this is the printed identity of
p. 279 (finger part); for `S = J⁻¹` it is Lemma 4.11's (p. 197). -/
theorem reduced_sub_two_eq (M Md C : Matrix ι ι ℝ) (S S' : Matrix ι κ ℝ) :
    S'ᵀ * M * S + Sᵀ * Md * S + Sᵀ * M * S' - (2 : ℝ) • (Sᵀ * (C * S + M * S')) =
      Sᵀ * (Md - (2 : ℝ) • C) * S + S'ᵀ * M * S - Sᵀ * M * S' := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]
  module

/-- **The congruence step of MLS Lemma 6.1(2), p. 279, for a rectangular reduction `S`:** "Taking
transposes and using symmetry of `M_f` inverts the sign of the last line". If `M` is symmetric and
`Ṁ − 2C` is skew-symmetric, then `S'ᵀ M S + Sᵀ Ṁ S + Sᵀ M S' − 2 Sᵀ (C S + M S')` is skew-symmetric
for all `S`, `S'`. -/
theorem skew_reduced {M Md C : Matrix ι ι ℝ} {S S' : Matrix ι κ ℝ} (hM : Mᵀ = M)
    (hs : (Md - (2 : ℝ) • C)ᵀ = -(Md - (2 : ℝ) • C)) :
    (S'ᵀ * M * S + Sᵀ * Md * S + Sᵀ * M * S' - (2 : ℝ) • (Sᵀ * (C * S + M * S')))ᵀ =
      -(S'ᵀ * M * S + Sᵀ * Md * S + Sᵀ * M * S' - (2 : ℝ) • (Sᵀ * (C * S + M * S'))) := by
  rw [reduced_sub_two_eq, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, hs, hM, Matrix.transpose_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  module

end Congruence

end Control
end RoboLean
