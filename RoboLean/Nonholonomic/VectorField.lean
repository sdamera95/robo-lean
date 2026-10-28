import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import RoboLean.Geometry.TwistBracket
import RoboLean.Geometry.TwistTrajectory

/-!
# Vector fields, Lie derivatives and Lie brackets (MLS Chapter 7, §2.1–2.2)

MLS Chapter 7, printed pp. 322–325: vector fields on `ℝⁿ` as right-hand sides of `q̇ = f(q)`
(eq. (7.7)), the Lie derivative `L_f V = (∂V/∂q) f` (p. 322), the Lie bracket
`[f, g](q) = (∂g/∂q) f(q) − (∂f/∂q) g(q)` (p. 324), Example 7.1 (linear fields), Proposition 7.1
(p. 325) and the alternative definition `L_[f,g] α = L_f (L_g α) − L_g (L_f α)` (p. 325,
Exercise 9, p. 351).

**Carrier and convention.** A vector field is a function `f : E → E` on a real normed space `E`
(MLS works in `ℝⁿ`, p. 321; `Fin n → ℝ` is an instance). The bracket is Mathlib's
`VectorField.lieBracket ℝ f g q = Dg(q) (f q) − Df(q) (g q)`, which is the book's sign. For linear
fields `q ↦ A q`, `q ↦ B q` the bracket is `q ↦ (B A − A B) q`, the book's "commutator" of
Example 7.1; it is the negative of Mathlib's ring commutator `⁅A, B⁆ = A B − B A`, and on the hat
matrices of twists it is the negative of the library's `Twist.bracket` (MLS Appendix A). The
fields `g ↦ g ξ̂` on homogeneous matrices have the bracket `g ↦ g (Twist.bracket ξ η)^`; the
fields `g ↦ ξ̂ g` have its negative, and `t ↦ exp(ξ̂ t) g₀` is an integral curve of `g ↦ ξ̂ g`.

**Smoothness.** MLS asks every field and function to be smooth. Each statement below names the
differentiability it uses: the Jacobi identity and the Lie-derivative identity need class `C²` at
the point, the product rule only differentiability at the point.
-/

noncomputable section

open Set Filter Topology Matrix VectorField
open scoped ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RoboLean
namespace Nonholonomic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **MLS p. 322: the Lie derivative `L_f V := (∂V/∂q) f(q)`** of a function `α : E → F` along a
vector field `f : E → E`, the rate of change of `α` along the solutions of `q̇ = f(q)`. Where `α`
is not differentiable, Mathlib's `fderiv` and hence the Lie derivative are zero. -/
def lieDerivative (f : E → E) (α : E → F) : E → F := fun q => fderiv ℝ α q (f q)

/-- **MLS p. 322:** `L_f α (q) = Dα(q) (f q)`, by definition. -/
theorem lieDerivative_apply (f : E → E) (α : E → F) (q : E) :
    lieDerivative f α q = fderiv ℝ α q (f q) := by
  rfl

/-- **MLS p. 324: the Lie bracket `[f, g](q) = (∂g/∂q) f(q) − (∂f/∂q) g(q)`** is Mathlib's
`VectorField.lieBracket ℝ f g q`, with the same sign; in Lie derivatives of the fields themselves,
`[f, g] = L_f g − L_g f`. -/
theorem lieBracket_eq_lieDerivative_sub (f g : E → E) :
    lieBracket ℝ f g = lieDerivative f g - lieDerivative g f := by
  rfl

/-- A derivative along a line: `Dg(q) v = d/dt g(q + t v)` at `t = 0` (supporting lemma for
MLS p. 324). -/
private theorem fderiv_apply_eq_deriv_line {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} {q : E} (v : E) (hg : DifferentiableAt ℝ g q) :
    fderiv ℝ g q v = deriv (fun t : ℝ => g (q + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hg' : HasFDerivAt g (fderiv ℝ g q) (q + (0 : ℝ) • v) := by simpa using hg.hasFDerivAt
  exact ((hg'.comp_hasDerivAt (0 : ℝ) hl).deriv).symm

/-- **The bracket of MLS p. 324 by derivatives along lines:** for fields differentiable at `q`,
`[f, g](q) = d/dt g(q + t f(q)) − d/dt f(q + t g(q))` at `t = 0`, a computational form used for
the examples of MLS pp. 341–344. -/
theorem lieBracket_eq_deriv {f g : E → E} {q : E} (hf : DifferentiableAt ℝ f q)
    (hg : DifferentiableAt ℝ g q) :
    lieBracket ℝ f g q =
      deriv (fun t : ℝ => g (q + t • f q)) 0 - deriv (fun t : ℝ => f (q + t • g q)) 0 := by
  simp only [lieBracket, fderiv_apply_eq_deriv_line _ hg, fderiv_apply_eq_deriv_line _ hf]

/-- **MLS Proposition 7.1 (1), p. 325: skew-symmetry `[f, g] = −[g, f]`,** for all fields. -/
theorem lieBracket_antisymm (f g : E → E) : lieBracket ℝ f g = -lieBracket ℝ g f := by
  funext x
  rw [Pi.neg_apply]
  exact lieBracket_swap

/-- **The bracket is additive-inverse in its second argument (MLS p. 324):**
`[f, −g] = −[f, g]`, for all fields. -/
theorem lieBracket_neg_right (f g : E → E) : lieBracket ℝ f (-g) = -lieBracket ℝ f g := by
  funext x
  simp only [lieBracket, Pi.neg_apply, fderiv_neg, map_neg]
  rw [show (-fderiv ℝ g x) (f x) = -(fderiv ℝ g x (f x)) from rfl]
  abel

/-- **MLS Proposition 7.1 (2), p. 325: the Jacobi identity**
`[f, [g, h]] + [h, [f, g]] + [g, [h, f]] = 0` at `q`, for fields of class `C²` at `q` (MLS:
smooth). -/
theorem lieBracket_jacobi {f g h : E → E} {q : E} (hf : ContDiffAt ℝ 2 f q)
    (hg : ContDiffAt ℝ 2 g q) (hh : ContDiffAt ℝ 2 h q) :
    lieBracket ℝ f (lieBracket ℝ g h) q + lieBracket ℝ h (lieBracket ℝ f g) q +
      lieBracket ℝ g (lieBracket ℝ h f) q = 0 := by
  have hn : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) := by simp
  rw [leibniz_identity_lieBracket hn hf hg hh, lieBracket_swap (V := h) (W := lieBracket ℝ f g),
    lieBracket_antisymm h f, lieBracket_neg_right]
  simp only [Pi.neg_apply]
  abel

/-- **MLS Proposition 7.1 (3), p. 325:**
`[α f, β g] = α β [f, g] + α (L_f β) g − β (L_g α) f` at `q`, for functions `α, β : E → ℝ` and
fields `f, g` differentiable at `q` (MLS: smooth). -/
theorem lieBracket_smul_smul {f g : E → E} {α β : E → ℝ} {q : E}
    (hα : DifferentiableAt ℝ α q) (hβ : DifferentiableAt ℝ β q) (hf : DifferentiableAt ℝ f q)
    (hg : DifferentiableAt ℝ g q) :
    lieBracket ℝ (fun x => α x • f x) (fun x => β x • g x) q =
      (α q * β q) • lieBracket ℝ f g q + (α q * lieDerivative f β q) • g q -
        (β q * lieDerivative g α q) • f q := by
  rw [lieBracket_smul_right (V := fun x => α x • f x) hβ hg, lieBracket_smul_left hα hf]
  simp only [lieDerivative, map_smul, smul_eq_mul, smul_add, smul_smul]
  module

/-- **MLS Example 7.1, p. 324, for continuous linear fields:** the bracket of `q ↦ A q` and
`q ↦ B q` is `q ↦ B (A q) − A (B q)`. -/
theorem lieBracket_continuousLinearMap (A B : E →L[ℝ] E) (q : E) :
    lieBracket ℝ (⇑A) (⇑B) q = B (A q) - A (B q) := by
  simp [lieBracket, ContinuousLinearMap.fderiv]

section Matrices

variable {ι : Type*} [Fintype ι]

/-- **MLS Example 7.1, p. 324: linear vector fields** `f(q) = A q`, `g(q) = B q` on `ι → ℝ` (MLS:
`ℝⁿ`) have the bracket `[f, g](q) = (B A − A B) q`. -/
theorem lieBracket_mulVec (A B : Matrix ι ι ℝ) (q : ι → ℝ) :
    lieBracket ℝ (fun x => A *ᵥ x) (fun x => B *ᵥ x) q = (B * A - A * B) *ᵥ q := by
  have key : ∀ M : Matrix ι ι ℝ,
      (fun x => M *ᵥ x) = ⇑(LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)) := by
    intro M
    funext x
    simp
  rw [key A, key B, lieBracket_continuousLinearMap]
  simp [Matrix.mulVec_mulVec, Matrix.sub_mulVec]

/-- **Sign convention for MLS Example 7.1, p. 324:** the bracket of the linear fields `q ↦ A q`
and `q ↦ B q` is minus Mathlib's ring commutator `⁅A, B⁆ = A B − B A` applied to `q`; the book's
"commutator of the two matrices" is `B A − A B`. -/
theorem lieBracket_mulVec_eq_neg_lie (A B : Matrix ι ι ℝ) (q : ι → ℝ) :
    lieBracket ℝ (fun x => A *ᵥ x) (fun x => B *ᵥ x) q = -(⁅A, B⁆ *ᵥ q) := by
  rw [lieBracket_mulVec, Ring.lie_def, ← Matrix.neg_mulVec, neg_sub]

end Matrices

/-- **MLS Example 7.1 (p. 324) on twists (MLS Appendix A, p. 411):** the linear fields
`x ↦ ξ̂ x`, `x ↦ η̂ x` on homogeneous coordinates have the bracket `x ↦ −(Twist.bracket ξ η)^ x`;
the library's twist bracket has the opposite sign of the Chapter 7 bracket on these fields. -/
theorem lieBracket_hat_mulVec (ξ η : Twist) (x : HomogeneousIndex → ℝ) :
    lieBracket ℝ (fun y => ξ.hat *ᵥ y) (fun y => η.hat *ᵥ y) x =
      -((Twist.bracket ξ η).hat *ᵥ x) := by
  rw [lieBracket_mulVec_eq_neg_lie, ← Twist.hat_bracket_lie]

section HomogeneousMatrices

open scoped Matrix.Norms.Elementwise

/-- **The fields `g ↦ ξ̂ g` on homogeneous matrices (MLS p. 324 with Appendix A, p. 411),** with
the entrywise norm on matrices: their bracket is `g ↦ −(Twist.bracket ξ η)^ g`. -/
theorem lieBracket_hat_mul (ξ η : Twist) (g : HomogeneousMatrix) :
    lieBracket ℝ (fun x => ξ.hat * x) (fun x => η.hat * x) g =
      -((Twist.bracket ξ η).hat * g) := by
  let L : HomogeneousMatrix → HomogeneousMatrix →L[ℝ] HomogeneousMatrix := fun M =>
    { toFun := fun x => M * x
      map_add' := fun x y => mul_add M x y
      map_smul' := fun c x => mul_smul_comm c M x
      cont := by fun_prop }
  refine (lieBracket_continuousLinearMap (L ξ.hat) (L η.hat) g).trans ?_
  show η.hat * (ξ.hat * g) - ξ.hat * (η.hat * g) = -((Twist.bracket ξ η).hat * g)
  rw [Twist.hat_bracket]
  noncomm_ring

/-- **The fields `g ↦ g ξ̂` on homogeneous matrices (MLS p. 324 with Appendix A, p. 411),** with
the entrywise norm on matrices: their bracket is `g ↦ g (Twist.bracket ξ η)^`, the library's twist
bracket with its own sign. -/
theorem lieBracket_mul_hat (ξ η : Twist) (g : HomogeneousMatrix) :
    lieBracket ℝ (fun x => x * ξ.hat) (fun x => x * η.hat) g =
      g * (Twist.bracket ξ η).hat := by
  let L : HomogeneousMatrix → HomogeneousMatrix →L[ℝ] HomogeneousMatrix := fun M =>
    { toFun := fun x => x * M
      map_add' := fun x y => add_mul x y M
      map_smul' := fun c x => smul_mul_assoc c x M
      cont := by fun_prop }
  refine (lieBracket_continuousLinearMap (L ξ.hat) (L η.hat) g).trans ?_
  show g * ξ.hat * η.hat - g * η.hat * ξ.hat = g * (Twist.bracket ξ η).hat
  rw [Twist.hat_bracket]
  noncomm_ring

end HomogeneousMatrices

section HomogeneousFlow

open scoped Matrix.Norms.Operator

/-- **The flow of the field `g ↦ ξ̂ g` (MLS eq. (7.7), p. 322, with eq. (2.37), p. 42):** the
curve `t ↦ exp(ξ̂ t) g₀` of homogeneous matrices solves `ġ = ξ̂ g`. -/
theorem hasDerivAt_exp_mul (ξ : Twist) (g₀ : HomogeneousMatrix) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Twist.exp ξ s).toHomogeneous * g₀)
      (ξ.hat * ((Twist.exp ξ t).toHomogeneous * g₀)) t := by
  have h := (Twist.hasDerivAt_exp_toHomogeneous ξ t).mul_const g₀
  rw [mul_assoc] at h
  exact h

end HomogeneousFlow

/-- **MLS p. 325 (Exercise 9, p. 351): `L_[f,g] α = L_f (L_g α) − L_g (L_f α)`** at `q`, for a
function `α` of class `C²` at `q` and fields differentiable at `q` (MLS: smooth). -/
theorem lieDerivative_lieBracket {f g : E → E} {α : E → F} {q : E} (hα : ContDiffAt ℝ 2 α q)
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    lieDerivative (lieBracket ℝ f g) α q =
      lieDerivative f (lieDerivative g α) q - lieDerivative g (lieDerivative f α) q := by
  have hn : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞) := by simp
  simp only [lieDerivative]
  exact fderiv_apply_lieBracket hα hn hg hf

/-- **MLS Exercise 9, p. 351: the two definitions of the bracket agree.** For fields `f, g`
differentiable at `q`, a field `h` has the value `[f, g](q)` at `q` exactly when
`L_h α (q) = L_f (L_g α)(q) − L_g (L_f α)(q)` for every function `α : E → ℝ` of class `C²`. -/
theorem eq_lieBracket_iff_lieDerivative {f g h : E → E} {q : E} (hf : DifferentiableAt ℝ f q)
    (hg : DifferentiableAt ℝ g q) :
    h q = lieBracket ℝ f g q ↔ ∀ α : E → ℝ, ContDiff ℝ 2 α →
      lieDerivative h α q =
        lieDerivative f (lieDerivative g α) q - lieDerivative g (lieDerivative f α) q := by
  constructor
  · intro h α hα
    rw [← lieDerivative_lieBracket hα.contDiffAt hf hg]
    simp only [lieDerivative, h]
  · intro H
    rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
    intro ℓ
    have h1 := H ℓ ℓ.contDiff
    rw [← lieDerivative_lieBracket ℓ.contDiff.contDiffAt hf hg] at h1
    simpa [lieDerivative, ContinuousLinearMap.fderiv] using h1

end Nonholonomic
end RoboLean
