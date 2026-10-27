import RoboLean.Geometry.TwistExp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smoothness of exponentials along a line and of rigid motions in homogeneous coordinates

MLS defines the rotation exponential `e^{ω̂t} = I + ω̂t + (ω̂t)²/2! + ⋯` (printed p. 27, eqs.
(2.9), (2.11)) and the twist exponential `e^{ξ̂t} = I + ξ̂t + (ξ̂t)²/2! + ⋯` of a `4 × 4` matrix
(p. 40) as power series, and it differentiates the product of exponentials by the chain rule
(p. 115, eqs. (3.51)–(3.53)), which presupposes that these maps are differentiable. The book does
not state their smoothness as a result.

**Formalized.** Smoothness classes are Mathlib's `ContDiff ℝ k` for every order
`k : WithTop ℕ∞`: `k = ∞` is the book's "smooth" (`C^∞`) and `k = ω` is analytic.

* In every complete normed real algebra, `t ↦ exp(t x)` is analytic at every `t`
  (`analyticAt_exp_smul_const`) and hence `C^k` for every `k` (`contDiff_exp_smul_const`).
* For a real square matrix `A`, `t ↦ exp(t A)` is `C^k` as a map into `ℝ^{m×m}`
  (`contDiff_matrix_exp_smul`), entry by entry (`contDiff_matrix_exp_smul_apply`). These statements
  use no matrix norm; the proofs use the `L^∞` operator norm of `Matrix.Norms.Operator`, the norm
  the library's exponentials are built with.
* The rotation exponential `Rotation.exp ω t` and the twist exponential `Twist.exp ξ t` are `C^k`
  in `t`, entry by entry (`Rotation.contDiff_exp_val_apply`,
  `Twist.contDiff_exp_toHomogeneous_apply`), for every axis and every twist.
* A family of rigid motions `x ↦ g(x)` is read through the entries of its homogeneous matrix
  `[R p; 0 1]` (MLS pp. 36–37, eqs. (2.23)–(2.24)), the representation in which the library
  differentiates poses. Entrywise `C^k` families are closed under products
  (`RigidTransform.contDiff_toHomogeneous_mul`), ordered list products
  (`RigidTransform.contDiff_toHomogeneous_list_prod`) and inverses
  (`RigidTransform.contDiff_toHomogeneous_inv`), and a family is entrywise `C^k` exactly when its
  rotation entries and its translation are (`RigidTransform.contDiff_toHomogeneous_iff`).

The statements are about the coordinate maps; nothing is claimed about `SE(3)` as a manifold.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace RoboLean

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The exponential along a line is analytic (MLS p. 27, eq. (2.11), and p. 40: the exponential
as a power series).** In every complete normed real algebra, `t ↦ exp(t x)` is analytic at every
real `t`, because the exponential series has infinite radius of convergence. -/
theorem analyticAt_exp_smul_const (x : 𝔸) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => NormedSpace.exp (u • x)) t :=
  AnalyticAt.comp (g := NormedSpace.exp) (f := fun u : ℝ => u • x)
    (NormedSpace.exp_analytic (𝕂 := ℝ) (t • x))
    (((ContinuousLinearMap.id ℝ ℝ).smulRight x).analyticAt t)

/-- **The exponential along a line is smooth (MLS p. 27, eq. (2.11), and p. 40).** In every
complete normed real algebra, `t ↦ exp(t x)` is `C^k` for every order `k`, in particular `C^∞`
(`k = ∞`) and analytic (`k = ω`). -/
theorem contDiff_exp_smul_const (x : 𝔸) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun u : ℝ => NormedSpace.exp (u • x)) :=
  AnalyticOnNhd.contDiff fun t _ => analyticAt_exp_smul_const x t

end Algebra

section MatrixExp

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Each entry of the matrix exponential `exp(t A)` is a smooth function of `t` (MLS p. 27, eq.
(2.11), and p. 40).** For every real square matrix `A`, every entry of `exp(t A)` is `C^k` in `t`
for every order `k`. -/
theorem contDiff_matrix_exp_smul_apply (A : Matrix m m ℝ) (i j : m) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun t : ℝ => NormedSpace.exp (t • A) i j) :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp (contDiff_exp_smul_const A)

/-- **The matrix exponential along a line is smooth (MLS p. 27, eq. (2.11), and p. 40).** For
every real square matrix `A`, the map `t ↦ exp(t A)`, read as a point of `ℝ^{m×m}` through its
entries, is `C^k` for every order `k`; no matrix norm enters the statement. -/
theorem contDiff_matrix_exp_smul (A : Matrix m m ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun t : ℝ => fun i j => NormedSpace.exp (t • A) i j) :=
  contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => contDiff_matrix_exp_smul_apply A i j

end MatrixExp

namespace Rotation

/-- **The rotation exponential is smooth in its parameter (MLS p. 27, eqs. (2.9), (2.11)).** For
every axis `ω`, unit or not, every entry of `Rotation.exp ω t = e^{ω̂t}` is `C^k` in `t` for every
order `k`. -/
theorem contDiff_exp_val_apply (ω : Vec3) (i j : Fin 3) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun t : ℝ => (exp ω t).val i j) :=
  contDiff_matrix_exp_smul_apply (Vec3.hat ω) i j

end Rotation

namespace Twist

/-- **The twist exponential is smooth in its parameter (MLS p. 40, the `4 × 4` matrix
exponential, and Proposition 2.8, pp. 41–42).** For every twist `ξ`, every entry of the
homogeneous matrix of `Twist.exp ξ t = e^{ξ̂t}` is `C^k` in `t` for every order `k`. -/
theorem contDiff_exp_toHomogeneous_apply (ξ : Twist) (i j : HomogeneousIndex)
    {k : WithTop ℕ∞} : ContDiff ℝ k (fun t : ℝ => (exp ξ t).toHomogeneous i j) := by
  simp only [toHomogeneous_exp]
  exact contDiff_matrix_exp_smul_apply ξ.hat i j

end Twist

namespace RigidTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

/-- **Smoothness in homogeneous coordinates is smoothness of the rotation and the translation
(MLS pp. 36–37, eq. (2.23), `ḡ = [R p; 0 1]`).** A family of rigid motions has `C^k` homogeneous
entries exactly when its rotation entries and its translation are `C^k`. -/
theorem contDiff_toHomogeneous_iff {g : E → RigidTransform} :
    (∀ i j, ContDiff ℝ k fun x => (g x).toHomogeneous i j) ↔
      (∀ i j, ContDiff ℝ k fun x => (g x).rotation.val i j) ∧
        ContDiff ℝ k fun x => (g x).translation := by
  constructor
  · intro h
    refine ⟨fun i j => h (Sum.inl i) (Sum.inl j), ?_⟩
    exact (contDiff_piLp 2).mpr fun i => h (Sum.inl i) (Sum.inr 0)
  · rintro ⟨hR, hp⟩ i j
    rcases i with i | i <;> rcases j with j | j
    · exact hR i j
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      exact (contDiff_piLp 2).mp hp i
    · exact contDiff_const
    · exact contDiff_const

/-- **Products of smooth families of rigid motions are smooth (MLS p. 37, eq. (2.24),
`ḡ_ac = ḡ_ab ḡ_bc`).** If two families have `C^k` homogeneous entries, so does their product. -/
theorem contDiff_toHomogeneous_mul {g h : E → RigidTransform}
    (hg : ∀ i j, ContDiff ℝ k fun x => (g x).toHomogeneous i j)
    (hh : ∀ i j, ContDiff ℝ k fun x => (h x).toHomogeneous i j) :
    ∀ i j, ContDiff ℝ k fun x => (g x * h x).toHomogeneous i j := by
  intro i j
  simp only [toHomogeneous_mul, Matrix.mul_apply]
  exact ContDiff.sum fun l _ => (hg i l).mul (hh l j)

/-- **Ordered products of smooth families of rigid motions are smooth (MLS p. 37, eq. (2.24),
applied to the ordered products of MLS eq. (3.3), p. 87).** If each of `N` families has `C^k`
homogeneous entries, so does the ordered product `f₀(x) f₁(x) ⋯ f_{N−1}(x)`. -/
theorem contDiff_toHomogeneous_list_prod {N : ℕ} {f : Fin N → E → RigidTransform}
    (hf : ∀ l i j, ContDiff ℝ k fun x => (f l x).toHomogeneous i j) :
    ∀ i j, ContDiff ℝ k fun x => (List.ofFn fun l => f l x).prod.toHomogeneous i j := by
  induction N with
  | zero =>
    intro i j
    simp only [List.ofFn_zero, List.prod_nil]
    exact contDiff_const
  | succ N ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact contDiff_toHomogeneous_mul (hf 0) (ih fun l => hf l.succ)

/-- **Inverses of smooth families of rigid motions are smooth (MLS p. 37, `g⁻¹ = (−Rᵀp, Rᵀ)`).**
If a family has `C^k` homogeneous entries, so does the family of its inverses. -/
theorem contDiff_toHomogeneous_inv {g : E → RigidTransform}
    (hg : ∀ i j, ContDiff ℝ k fun x => (g x).toHomogeneous i j) :
    ∀ i j, ContDiff ℝ k fun x => (g x)⁻¹.toHomogeneous i j := by
  obtain ⟨hR, hp⟩ := contDiff_toHomogeneous_iff.mp hg
  have hpi : ∀ l, ContDiff ℝ k fun x => (g x).translation l := (contDiff_piLp 2).mp hp
  refine contDiff_toHomogeneous_iff.mpr ⟨fun i j => ?_, ?_⟩
  · simpa only [inv_rotation, Rotation.inv_val, Matrix.transpose_apply] using hR j i
  · refine (contDiff_piLp 2).mpr fun i => ?_
    simp only [inv_translation, PiLp.neg_apply, Rotation.act_apply, Rotation.inv_val,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact (ContDiff.sum fun l _ => (hR l i).mul (hpi l)).neg

end RigidTransform

end RoboLean
