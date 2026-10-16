import RoboLean.Dynamics.Lagrangian
import RoboLean.Kinematics.MapJacobian
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Pfaffian constraints, Lagrange multipliers and the Lagrange–d'Alembert equations

MLS Chapter 6, §1, printed pp. 265–274: eqs. (6.1)–(6.9), the constraint forces of pp. 267–268,
d'Alembert's principle (pp. 268, 271), the multiplier formula (6.6) and the reduction (6.9).

**Carrier.** As MLS does from p. 266 on ("the configuration space `Q` is an open subset of `ℝⁿ`"),
configurations and velocities are `Fin n → ℝ`, and a Pfaffian constraint is a field
`A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ`, read as `A(q) q̇ = 0` (eq. (6.3)). The open set `Q` is
the whole of `ℝⁿ` unless a statement names a set or a neighborhood. The library's Lagrange predicate
`Lagrangian.LagrangeEquationsAt` (MLS Theorem 4.1) is reused unchanged.

**Formalized.**

* (6.3) as `PfaffianAt`; "pointwise linearly independent" (p. 267) as `LinearIndependent ℝ A.row`,
  equivalent to the injectivity of `λ ↦ Aᵀ λ` (`transpose_mulVec_injective_iff`).
* Virtual displacements and virtual work (p. 271): a force `F` does no virtual work at a
  configuration with constraint matrix `A` when `F ⬝ δq = 0` for every `δq` with `A δq = 0`
  (`DoesNoVirtualWork`). Constraint forces `Aᵀ λ` do no virtual work, and conversely every force
  doing no virtual work is `Aᵀ λ` for some `λ` (`doesNoVirtualWork_iff_exists`), by Mathlib's
  `mem_span_of_iInf_ker_le_ker`. This is the linear algebra behind "The constraint forces at a
  configuration `q` have the form `Γ = Aᵀ(q) λ`" (p. 268).
* Holonomic constraints `h(q) = 0` (6.2) with `∂h/∂q = MapJacobian.jac h q`: along a motion that
  stays on `h = 0` near `t`, `(∂h/∂q) q̇ = 0`, and the constraint force `(∂h/∂q)ᵀ λ` does no work
  (p. 267); integrable Pfaffian constraints (pp. 267–268) and the equality of the ranges of `Aᵀ` and
  `(∂h/∂q)ᵀ` for them (p. 268).
* The multiplier form (6.4) as `MultiplierEquationsAt`, which is Lagrange's equations with the
  generalized force `Υ − Aᵀ λ`; the Lagrange–d'Alembert equations (6.7)–(6.8) as
  `LagrangeDAlembertAt`; their equivalence `LdA ⇔ ∃ λ, (6.4)` with no rank hypothesis, and
  uniqueness of `λ` exactly when the rows of `A` are independent; without constraints (`A = 0`) the
  Lagrange–d'Alembert equations are Lagrange's equations (p. 272).
* (6.5) for `L = ½ q̇ᵀ M(q) q̇ − V(q)`, and the energy balance: the constraint forces do no work
  along a motion satisfying (6.3), so the energy derivative is `q̇ ⬝ Υ` (p. 268).
* (6.6): `A M⁻¹ Aᵀ` is positive definite when `M` is and the rows of `A` are independent, and along
  a motion that satisfies (6.3) near `t`, (6.5) holds at `t` exactly when (6.5) holds with `λ` given
  by (6.6) (`multiplierEquationsAt_mechanical_iff_multiplier`).
* (6.9): for `A = [A₁ A₂]` with `A₂` invertible, after a relabeling `e : Fin r ⊕ Fin k ≃ Fin n` of
  the coordinates (`q₁ = q ∘ e ∘ inl`, `q₂ = q ∘ e ∘ inr`), `A δq = 0 ⇔ δq₂ = −A₂⁻¹ A₁ δq₁` and the
  Lagrange–d'Alembert equations are (6.9); "this can always be achieved locally by reordering" (p.
  272) as `exists_split_isUnit_det` and `eventually_isUnit_det_submatrix`.

**Hypotheses the book does not print, all explicit:** `M(q)` positive definite where `M⁻¹` is used
(p. 269 says only "if the constraints are independent"); the derivative of `s ↦ A(q(s))` along the
motion where `Ȧ` is used ("smooth", p. 269); the constraint holding on a neighborhood of `t` where
it is differentiated ("for all time", p. 269); continuity of `A` for the local reordering.
d'Alembert's principle is a modeling assumption in MLS (pp. 268, 271): here it is built into the
definitions, as the generalized force `Aᵀ λ` in (6.4) and as the restriction to virtual
displacements in (6.7)–(6.8); it is not derived. Nothing here concerns existence or uniqueness of
solutions of the constrained equations, friction, or a physical system.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Constrained

variable {n k : ℕ}

/-! ### Pfaffian constraints and independent rows (MLS p. 267, eq. (6.3)) -/

/-- **MLS eq. (6.3), p. 269 (and p. 267): the Pfaffian constraint `A(q) q̇ = 0`** for a constraint
field `A : ℝⁿ → ℝᵏˣⁿ`, at the configuration `q` with velocity `v`. -/
def PfaffianAt (A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (q v : Fin n → ℝ) : Prop :=
  A q *ᵥ v = 0

/-- **MLS p. 267: "pointwise linearly independent" constraints.** The rows of `A` are linearly
independent exactly when `λ ↦ Aᵀ λ` is injective, i.e. a constraint force `Aᵀ λ` determines its
multipliers `λ`. -/
theorem transpose_mulVec_injective_iff (A : Matrix (Fin k) (Fin n) ℝ) :
    Function.Injective (Aᵀ *ᵥ ·) ↔ LinearIndependent ℝ A.row := by
  rw [← Matrix.vecMul_injective_iff]
  simp only [Matrix.mulVec_transpose]

/-- **Independent rows from an invertible `k × k` minor (MLS p. 272).** If the columns `c` of `A`
form an invertible `k × k` matrix, the rows of `A` are linearly independent (the constraint `A` has
full row rank, MLS p. 267). -/
theorem linearIndependent_row_of_isUnit_det {A : Matrix (Fin k) (Fin n) ℝ} (c : Fin k → Fin n)
    (hc : IsUnit (A.submatrix id c).det) : LinearIndependent ℝ A.row := by
  rw [← transpose_mulVec_injective_iff]
  intro μ ν h
  have hinj : Function.Injective ((A.submatrix id c)ᵀ *ᵥ ·) :=
    Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_transpose _).mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hc))
  apply hinj
  funext j
  have := congrFun h (c j)
  simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply] using this

/-! ### Virtual displacements and d'Alembert's principle (MLS pp. 268, 271) -/

/-- **MLS p. 271: a force `F` does no virtual work** at a configuration with constraint matrix `A`:
`F ⬝ δq = 0` for every virtual displacement `δq`, i.e. every `δq` with `A δq = 0`. D'Alembert's
principle (pp. 268, 271) is the assumption that the constraint forces have this property. -/
def DoesNoVirtualWork (A : Matrix (Fin k) (Fin n) ℝ) (F : Fin n → ℝ) : Prop :=
  ∀ δq : Fin n → ℝ, A *ᵥ δq = 0 → F ⬝ᵥ δq = 0

/-- **MLS p. 271: constraint forces `Aᵀ λ` do no virtual work,** `(Aᵀ λ) ⬝ δq = λ ⬝ (A δq) = 0` for
`A δq = 0`. -/
theorem doesNoVirtualWork_transpose_mulVec (A : Matrix (Fin k) (Fin n) ℝ) (μ : Fin k → ℝ) :
    DoesNoVirtualWork A (Aᵀ *ᵥ μ) := by
  intro δq hδ
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hδ, dotProduct_zero]

/-- **MLS p. 268: the forces that do no virtual work are exactly the constraint forces
`Γ = Aᵀ(q) λ`.** No rank hypothesis is needed. The nontrivial direction is Mathlib's
`mem_span_of_iInf_ker_le_ker`: a linear functional vanishing on the common kernel of the constraint
rows is a combination of them. -/
theorem doesNoVirtualWork_iff_exists (A : Matrix (Fin k) (Fin n) ℝ) (F : Fin n → ℝ) :
    DoesNoVirtualWork A F ↔ ∃ μ : Fin k → ℝ, Aᵀ *ᵥ μ = F := by
  refine ⟨fun h => ?_, fun ⟨μ, hμ⟩ => hμ ▸ doesNoVirtualWork_transpose_mulVec A μ⟩
  let L : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun i => (LinearMap.proj i).comp A.mulVecLin
  let K : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ F
  have hK : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker K := by
    intro δ hδ
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hδ
    have hA : A *ᵥ δ = 0 := funext fun i => by simpa [L] using hδ i
    simpa [K] using h δ hA
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker hK)
  refine ⟨c, funext fun j => ?_⟩
  have h1 := LinearMap.congr_fun hc (Pi.single j 1)
  simp [L, K] at h1
  rw [← h1]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

/-- **MLS p. 268: two constraint matrices with the same virtual displacements have constraint forces
with the same range.** If `A δq = 0 ⇔ B δq = 0` for every `δq`, then a force is `Aᵀ λ` for some `λ`
exactly when it is `Bᵀ μ` for some `μ` (the numbers of rows may differ). -/
theorem exists_transpose_mulVec_eq_iff_of_ker {k' : ℕ} {A : Matrix (Fin k) (Fin n) ℝ}
    {B : Matrix (Fin k') (Fin n) ℝ} (h : ∀ δq, A *ᵥ δq = 0 ↔ B *ᵥ δq = 0) (F : Fin n → ℝ) :
    (∃ μ, Aᵀ *ᵥ μ = F) ↔ ∃ ν, Bᵀ *ᵥ ν = F := by
  rw [← doesNoVirtualWork_iff_exists, ← doesNoVirtualWork_iff_exists]
  exact forall_congr' fun δq => imp_congr_left (h δq)

/-! ### Holonomic and integrable constraints (MLS pp. 266–268, eqs. (6.1)–(6.2)) -/

/-- **MLS p. 267: a holonomic constraint `h(q(s)) = 0` near `t` gives the Pfaffian constraint
`(∂h/∂q) q̇ = 0` at `t`**, with `∂h/∂q = MapJacobian.jac h`, for `h` differentiable at `q(t)` and a
motion with velocity `q'` at `t`: the time derivative of `h(q(t))` vanishes. -/
theorem jac_mulVec_eq_zero_of_eventually {h : (Fin n → ℝ) → Fin k → ℝ} {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hh : DifferentiableAt ℝ h (θ t)) (hθ : HasDerivAt θ θ' t)
    (hc : ∀ᶠ s in 𝓝 t, h (θ s) = 0) : MapJacobian.jac h (θ t) *ᵥ θ' = 0 := by
  have h1 := MapJacobian.hasDerivAt_comp hh hθ
  have h0 : HasDerivAt (fun s => h (θ s)) 0 t :=
    (hasDerivAt_const t (0 : Fin k → ℝ)).congr_of_eventuallyEq hc
  exact h1.unique h0

/-- **MLS p. 267, along a motion: a holonomic constraint is a Pfaffian constraint with
`A = ∂h/∂q`.** If `h` is differentiable everywhere, the motion has velocity `q'(s)` near `t` and
`h(q(s)) = 0` near `t`, then `(∂h/∂q)(q(s)) q'(s) = 0` near `t`. -/
theorem eventually_pfaffianAt_jac {h : (Fin n → ℝ) → Fin k → ℝ} {θ θ' : ℝ → Fin n → ℝ} {t : ℝ}
    (hh : Differentiable ℝ h) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hc : ∀ᶠ s in 𝓝 t, h (θ s) = 0) : ∀ᶠ s in 𝓝 t, PfaffianAt (MapJacobian.jac h) (θ s) (θ' s) := by
  filter_upwards [hθ, hc.eventually_nhds] with s hs hcs
  exact jac_mulVec_eq_zero_of_eventually (hh _) hs hcs

/-- **MLS p. 267: the constraint force of a holonomic constraint does no work along feasible
trajectories,** `Γ ⬝ q̇ = λᵀ (∂h/∂q) q̇ = λᵀ (d/dt) h(q) = 0`, for `Γ = (∂h/∂q)ᵀ λ` and a motion
that stays on `h = 0` near `t`. -/
theorem dotProduct_constraintForce_eq_zero {h : (Fin n → ℝ) → Fin k → ℝ} {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hh : DifferentiableAt ℝ h (θ t)) (hθ : HasDerivAt θ θ' t)
    (hc : ∀ᶠ s in 𝓝 t, h (θ s) = 0) (μ : Fin k → ℝ) :
    ((MapJacobian.jac h (θ t))ᵀ *ᵥ μ) ⬝ᵥ θ' = 0 :=
  doesNoVirtualWork_transpose_mulVec _ μ θ' (jac_mulVec_eq_zero_of_eventually hh hθ hc)

/-- **MLS pp. 267–268: an integrable Pfaffian constraint** on a set `Q` of configurations: there is
a map `h : Q → ℝᵏ`, differentiable on `Q`, whose Jacobian has the same null space as `A(q)` at every
`q ∈ Q`, `A(q) q̇ = 0 ⇔ (∂h/∂q) q̇ = 0` ("we do not require that `A = ∂h/∂q`, but only that they
define the same subspace of the allowable velocities at every `q ∈ Q`"). A Pfaffian constraint that
is not integrable is nonholonomic (p. 268). -/
def IsIntegrableOn (A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (Q : Set (Fin n → ℝ)) : Prop :=
  ∃ h : (Fin n → ℝ) → Fin k → ℝ, ∀ q ∈ Q, DifferentiableAt ℝ h q ∧
    ∀ v, A q *ᵥ v = 0 ↔ MapJacobian.jac h q *ᵥ v = 0

/-- **MLS pp. 267–268: a holonomic constraint is integrable,** with `A = ∂h/∂q`. -/
theorem isIntegrableOn_jac {h : (Fin n → ℝ) → Fin k → ℝ} {Q : Set (Fin n → ℝ)}
    (hh : ∀ q ∈ Q, DifferentiableAt ℝ h q) : IsIntegrableOn (MapJacobian.jac h) Q :=
  ⟨h, fun q hq => ⟨hh q hq, fun _ => Iff.rfl⟩⟩

/-- **MLS p. 268: "If the constraint happens to be integrable, then this is identical to the
holonomic case since `Aᵀ(q)` and `(∂h/∂q)ᵀ` will have the same range space."** For an integrable
constraint there is a map `h` such that at every `q ∈ Q` the constraint forces `A(q)ᵀ λ` are exactly
the forces `(∂h/∂q)ᵀ μ`. -/
theorem IsIntegrableOn.exists_range_eq {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {Q : Set (Fin n → ℝ)} (hA : IsIntegrableOn A Q) :
    ∃ h : (Fin n → ℝ) → Fin k → ℝ, ∀ q ∈ Q, ∀ F : Fin n → ℝ,
      (∃ μ, (A q)ᵀ *ᵥ μ = F) ↔ ∃ ν, (MapJacobian.jac h q)ᵀ *ᵥ ν = F := by
  obtain ⟨h, hh⟩ := hA
  exact ⟨h, fun q hq F => exists_transpose_mulVec_eq_iff_of_ker (hh q hq).2 F⟩

/-! ### Lagrange multipliers and the Lagrange–d'Alembert equations (MLS eqs. (6.4), (6.7)–(6.8)) -/

/-- **MLS eq. (6.4), p. 269: the equations of motion with Lagrange multipliers,**
`d/dt ∂L/∂q̇ − ∂L/∂q + Aᵀ(q) λ − Υ = 0` at time `t`, i.e. Lagrange's equations
(`Lagrangian.LagrangeEquationsAt`, MLS Theorem 4.1) with the generalized force `Υ − Aᵀ(q(t)) λ`. The
multipliers `λ ∈ ℝᵏ` are a value at `t`; d'Alembert's principle (p. 268) is the choice of the
constraint force `Aᵀ λ`. -/
def MultiplierEquationsAt (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (θ : ℝ → Fin n → ℝ) (Υ : Fin n → ℝ)
    (μ : Fin k → ℝ) (t : ℝ) : Prop :=
  Lagrangian.LagrangeEquationsAt L θ (Υ - (A (θ t))ᵀ *ᵥ μ) t

/-- **MLS eqs. (6.7)–(6.8), p. 272: the Lagrange–d'Alembert equations at time `t`,**
`(d/dt ∂L/∂q̇ − ∂L/∂q − Υ) · δq = 0` for every `δq` with `A(q) δq = 0`. As in
`Lagrangian.LagrangeEquationsAt`, the existence of the derivative of `s ↦ ∂L/∂q̇ (q(s), q̇(s))` at
`t` is part of the predicate; `p` is that derivative. The velocity is `deriv θ`. -/
def LagrangeDAlembertAt (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ) (θ : ℝ → Fin n → ℝ) (Υ : Fin n → ℝ) (t : ℝ) :
    Prop :=
  ∃ p : Fin n → ℝ,
    (∀ i, HasDerivAt (fun s => Lagrangian.velocityPartial L (θ s) (deriv θ s) i) (p i) t) ∧
      DoesNoVirtualWork (A (θ t))
        (p - (fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i) - Υ)

/-- **MLS pp. 269–272: the Lagrange–d'Alembert equations (6.7)–(6.8) hold exactly when the
multiplier equations (6.4) hold for some `λ`.** The direction (6.4) ⇒ (6.7) is the projection of p.
272 ("Since `(Aᵀ λ) · δq = 0`"); the converse, the existence of the multipliers, is the duality step
`doesNoVirtualWork_iff_exists`. No rank hypothesis is needed for either direction. -/
theorem lagrangeDAlembertAt_iff_exists_multiplier {L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {θ : ℝ → Fin n → ℝ} {Υ : Fin n → ℝ} {t : ℝ} :
    LagrangeDAlembertAt L A θ Υ t ↔ ∃ μ, MultiplierEquationsAt L A θ Υ μ t := by
  constructor
  · rintro ⟨p, hp, hw⟩
    obtain ⟨μ, hμ⟩ := (doesNoVirtualWork_iff_exists _ _).mp hw
    refine ⟨-μ, fun i => ?_⟩
    convert hp i using 1
    have := congrFun hμ i
    simp only [Pi.sub_apply, Matrix.mulVec_neg, Pi.neg_apply] at this ⊢
    linarith
  · rintro ⟨μ, hμ⟩
    refine ⟨fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i +
      (Υ - (A (θ t))ᵀ *ᵥ μ) i, hμ, ?_⟩
    have e : ((fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i +
        (Υ - (A (θ t))ᵀ *ᵥ μ) i) - (fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i) -
          Υ) = (A (θ t))ᵀ *ᵥ (-μ) := by
      funext i
      simp only [Pi.sub_apply, Matrix.mulVec_neg, Pi.neg_apply]
      ring
    rw [e]
    exact doesNoVirtualWork_transpose_mulVec _ _

/-- **The multipliers of (6.4) are unique when the constraints are independent (MLS pp. 267, 269).**
If the rows of `A(q(t))` are linearly independent, two multiplier vectors satisfying (6.4) at `t`
are equal. -/
theorem MultiplierEquationsAt.unique {L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {θ : ℝ → Fin n → ℝ} {Υ : Fin n → ℝ}
    {μ ν : Fin k → ℝ} {t : ℝ} (hA : LinearIndependent ℝ (A (θ t)).row)
    (hμ : MultiplierEquationsAt L A θ Υ μ t) (hν : MultiplierEquationsAt L A θ Υ ν t) : μ = ν := by
  apply (transpose_mulVec_injective_iff _).mpr hA
  funext i
  have := (hμ i).unique (hν i)
  simp only [Pi.sub_apply] at this
  linarith

/-- **Uniqueness of the multipliers characterizes independent constraints (MLS pp. 267, 269).**
Given one solution `λ` of (6.4) at `t`, it is the only one exactly when the rows of `A(q(t))` are
linearly independent: a dependent row combination `Aᵀ ν = 0` could be added to `λ`. -/
theorem multiplier_unique_iff {L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {θ : ℝ → Fin n → ℝ} {Υ : Fin n → ℝ}
    {μ : Fin k → ℝ} {t : ℝ} (hμ : MultiplierEquationsAt L A θ Υ μ t) :
    (∀ ν, MultiplierEquationsAt L A θ Υ ν t → ν = μ) ↔ LinearIndependent ℝ (A (θ t)).row := by
  refine ⟨fun h => ?_, fun hA ν hν => hν.unique hA hμ⟩
  rw [← transpose_mulVec_injective_iff]
  intro a b hab
  have hsub : (A (θ t))ᵀ *ᵥ (a - b) = 0 := by
    simp only [Matrix.mulVec_sub] at hab ⊢
    exact sub_eq_zero.mpr hab
  have h1 := h (μ + (a - b)) (by
    unfold MultiplierEquationsAt
    rwa [Matrix.mulVec_add, hsub, add_zero])
  have : a - b = 0 := by simpa using h1
  exact sub_eq_zero.mp this

/-- **MLS p. 272: "in the case where there are no constraints on the system, `δq` is free and
equation (6.7) reduces to the usual form of Lagrange's equations."** With the zero constraint
matrix, the Lagrange–d'Alembert equations are `Lagrangian.LagrangeEquationsAt`. -/
theorem lagrangeDAlembertAt_zero_iff {L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ} {θ : ℝ → Fin n → ℝ}
    {Υ : Fin n → ℝ} {t : ℝ} :
    LagrangeDAlembertAt L (fun _ => (0 : Matrix (Fin k) (Fin n) ℝ)) θ Υ t ↔
      Lagrangian.LagrangeEquationsAt L θ Υ t := by
  rw [lagrangeDAlembertAt_iff_exists_multiplier]
  simp [MultiplierEquationsAt]

/-- **The Lagrange–d'Alembert equations against a known inertial term (MLS p. 272).** If the motion
satisfies Lagrange's equations at `t` with some generalized force `R` (for a mechanical Lagrangian,
`R = M q̈ + C q̇ + ∂V/∂q`), then the Lagrange–d'Alembert equations with force `Υ` hold exactly when
`R − Υ` does no virtual work. -/
theorem lagrangeDAlembertAt_iff_of_lagrangeEquationsAt {L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {θ : ℝ → Fin n → ℝ} {R Υ : Fin n → ℝ} {t : ℝ}
    (hR : Lagrangian.LagrangeEquationsAt L θ R t) :
    LagrangeDAlembertAt L A θ Υ t ↔ DoesNoVirtualWork (A (θ t)) (R - Υ) := by
  constructor
  · rintro ⟨p, hp, hw⟩
    have e : p - (fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i) - Υ = R - Υ := by
      funext i
      have := (hp i).unique (hR i)
      simp only [Pi.sub_apply]
      linarith
    rwa [e] at hw
  · intro hw
    refine ⟨fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i + R i, hR, ?_⟩
    convert hw using 1
    funext i
    simp only [Pi.sub_apply]
    ring

/-! ### Mechanical systems: eq. (6.5) and the energy balance (MLS pp. 268–269) -/

/-- **MLS eq. (6.5), p. 269: for `L = ½ q̇ᵀ M(q) q̇ − V(q)`, the multiplier equations (6.4) are
`M(q) q̈ + C(q, q̇) q̇ + ∂V/∂q + Aᵀ(q) λ = Υ`,** with `C` the Christoffel Coriolis matrix of MLS eq.
(4.23). Hypotheses as in `Lagrangian.lagrangeEquationsAt_mechanical_iff`: `M(q)` symmetric at
every configuration, Fréchet derivative data of `M` and `V` at `q(t)`, velocity `θ'` near `t` and
acceleration `θ''` at `t` as actual derivatives. -/
theorem multiplierEquationsAt_mechanical_iff {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t)) (hV : HasFDerivAt V V' (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (Υ : Fin n → ℝ)
    (μ : Fin k → ℝ) :
    MultiplierEquationsAt (Lagrangian.mechanical M V) A θ Υ μ t ↔
      M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        Lagrangian.gradient V' + (A (θ t))ᵀ *ᵥ μ = Υ := by
  rw [MultiplierEquationsAt, Lagrangian.lagrangeEquationsAt_mechanical_iff hsymm hM hV hθ hθ']
  constructor
  · intro h
    rw [h, sub_add_cancel]
  · intro h
    rw [← h, add_sub_cancel_right]

/-- **MLS eq. (6.5), p. 269, with the forces split as on pp. 170 and 269:** with `Υ = F − Nₑ`
(external forces `F`, further joint forces `Nₑ` such as friction), (6.4) is
`M(q) q̈ + C(q, q̇) q̇ + N + Aᵀ(q) λ = F` with `N = ∂V/∂q + Nₑ`. Same hypotheses as
`multiplierEquationsAt_mechanical_iff`. -/
theorem multiplierEquationsAt_mechanical_iff_force {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t)) (hV : HasFDerivAt V V' (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (F Nₑ : Fin n → ℝ)
    (μ : Fin k → ℝ) :
    MultiplierEquationsAt (Lagrangian.mechanical M V) A θ (F - Nₑ) μ t ↔
      M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        (Lagrangian.gradient V' + Nₑ) + (A (θ t))ᵀ *ᵥ μ = F := by
  rw [multiplierEquationsAt_mechanical_iff hsymm hM hV hθ hθ']
  constructor
  · intro h
    rw [← add_assoc, add_right_comm _ Nₑ, h, sub_add_cancel]
  · intro h
    rw [← h]
    abel

/-- **The inertial term of a mechanical system (MLS eqs. (4.21), (6.5)):** along a motion with
actual velocity and acceleration, `L = ½ q̇ᵀ M q̇ − V` satisfies Lagrange's equations at `t` with
the generalized force `M q̈ + C q̇ + ∂V/∂q`. Same hypotheses as
`Lagrangian.lagrangeEquationsAt_mechanical_iff`. -/
theorem lagrangeEquationsAt_mechanical_inertial {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hsymm : ∀ q, (M q).IsSymm) (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) :
    Lagrangian.LagrangeEquationsAt (Lagrangian.mechanical M V) θ
      (M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        Lagrangian.gradient V') t :=
  (Lagrangian.lagrangeEquationsAt_mechanical_iff hsymm hM hV hθ hθ' _).mpr rfl

/-- **MLS eqs. (6.7)–(6.8) for `L = ½ q̇ᵀ M q̇ − V` (p. 272):** the Lagrange–d'Alembert equations
hold at `t` exactly when `M q̈ + C q̇ + ∂V/∂q − Υ` does no virtual work. Same hypotheses as
`multiplierEquationsAt_mechanical_iff`. -/
theorem lagrangeDAlembertAt_mechanical_iff {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t)) (hV : HasFDerivAt V V' (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (Υ : Fin n → ℝ) :
    LagrangeDAlembertAt (Lagrangian.mechanical M V) A θ Υ t ↔
      DoesNoVirtualWork (A (θ t))
        (M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
          Lagrangian.gradient V' - Υ) :=
  lagrangeDAlembertAt_iff_of_lagrangeEquationsAt
    (lagrangeEquationsAt_mechanical_inertial hsymm hM hV hθ hθ')

/-- **MLS p. 268: the constraint forces "do no work on the system, and hence conserve energy".**
Along a motion satisfying the Pfaffian constraint at `t` and the multiplier equations (6.4) for
`L = ½ q̇ᵀ M q̇ − V`, the total energy `½ q̇ᵀ M(q) q̇ + V(q)` has derivative `q̇ ⬝ Υ` at `t`: the
constraint force `Aᵀ λ` contributes no power. Same hypotheses as
`multiplierEquationsAt_mechanical_iff` (compare `Lagrangian.hasDerivAt_energy`). -/
theorem hasDerivAt_energy_of_multiplierEquationsAt {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t)) (hV : HasFDerivAt V V' (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) {Υ : Fin n → ℝ}
    {μ : Fin k → ℝ} (hc : PfaffianAt A (θ t) (θ' t))
    (hL : MultiplierEquationsAt (Lagrangian.mechanical M V) A θ Υ μ t) :
    HasDerivAt (fun s => Lagrangian.energy M V (θ s) (θ' s)) (θ' t ⬝ᵥ Υ) t := by
  have h := Lagrangian.hasDerivAt_energy hsymm hM hV hθ hθ' hL
  have hw : θ' t ⬝ᵥ ((A (θ t))ᵀ *ᵥ μ) = 0 := by
    rw [dotProduct_comm]
    exact doesNoVirtualWork_transpose_mulVec _ μ _ hc
  rwa [dotProduct_sub, hw, sub_zero] at h

/-! ### The multiplier formula (MLS eq. (6.6), pp. 269–270) -/

/-- **MLS p. 269: "The configuration dependent matrix `A M⁻¹ Aᵀ` is full rank if the constraints are
independent"**, here positive definite, for `M` positive definite (an assumption MLS carries from
Chapter 4, Lemma 4.2(1)) and linearly independent rows of `A`. The inverse is `Matrix.inv`. -/
theorem posDef_mul_inv_mul_transpose {M : Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin k) (Fin n) ℝ}
    (hM : M.PosDef) (hA : LinearIndependent ℝ A.row) : (A * M⁻¹ * Aᵀ).PosDef := by
  have h := hM.inv.conjTranspose_mul_mul_same ((transpose_mulVec_injective_iff A).mpr hA)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- **MLS eq. (6.6), p. 270: the Lagrange multipliers**
`λ = (A M⁻¹ Aᵀ)⁻¹ (A M⁻¹ (F − C q̇ − N) + Ȧ q̇)`, as a function of the constraint matrix `A`, the
inertia `M`, the force `w = F − C q̇ − N` and the vector `a = Ȧ q̇`. The inverses are `Matrix.inv`;
the formula is meaningful where `M` is positive definite and the rows of `A` are independent
(`posDef_mul_inv_mul_transpose`). -/
def multiplier (A : Matrix (Fin k) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (a : Fin k → ℝ) : Fin k → ℝ :=
  (A * M⁻¹ * Aᵀ)⁻¹ *ᵥ ((A * M⁻¹) *ᵥ w + a)

/-- **The algebra of MLS eq. (6.6), p. 269.** For `M` positive definite and independent rows of `A`,
if `M q̈ + Aᵀ λ = w` (eq. (6.5) with `w = F − C q̇ − N`), then the differentiated constraint
`A q̈ + Ȧ q̇ = 0` (with `a = Ȧ q̇`) holds exactly when `λ` is given by (6.6). -/
theorem add_eq_zero_iff_eq_multiplier {M : Matrix (Fin n) (Fin n) ℝ}
    {A : Matrix (Fin k) (Fin n) ℝ} (hM : M.PosDef) (hA : LinearIndependent ℝ A.row)
    {acc w : Fin n → ℝ} {a μ : Fin k → ℝ} (h : M *ᵥ acc + Aᵀ *ᵥ μ = w) :
    A *ᵥ acc + a = 0 ↔ μ = multiplier A M w a := by
  have hacc : acc = M⁻¹ *ᵥ (w - Aᵀ *ᵥ μ) := by
    rw [← h, add_sub_cancel_right, Control.PosDef.inv_mulVec_mulVec hM]
  have hu : IsUnit (A * M⁻¹ * Aᵀ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (posDef_mul_inv_mul_transpose hM hA).isUnit
  have e : A *ᵥ acc + a = ((A * M⁻¹) *ᵥ w + a) - (A * M⁻¹ * Aᵀ) *ᵥ μ := by
    rw [hacc]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    abel
  rw [e, sub_eq_zero, multiplier]
  constructor
  · intro h2
    rw [h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · intro h2
    rw [h2, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

/-! The rectangular product rule moved to the `Control` namespace
(`RoboLean.Control.MatrixAnalysis`) on 2026-10-14; the old name remains as a deprecated alias. -/

@[deprecated Control.hasDerivAt_matrix_mulVec_rect (since := "2026-10-14")]
alias hasDerivAt_matrix_mulVec_rect := Control.hasDerivAt_matrix_mulVec_rect

/-- **The rate `Ȧ` of a constraint field along a motion (MLS p. 269, "Differentiating the constraint
equation (6.3)"):** if every entry of `A` has the Fréchet derivative `A' i j` at `q(t)` and the
motion has velocity `q'` at `t`, then every entry of `s ↦ A(q(s))` has the derivative `A' i j q'` at
`t`, the entry of `Ȧ = ∑ₖ q̇ₖ ∂A/∂qₖ`. -/
theorem hasDerivAt_constraint_comp {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {A' : Fin k → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ} {t : ℝ}
    (hA : ∀ i j, HasFDerivAt (fun q => A q i j) (A' i j) (θ t)) (hθ : HasDerivAt θ θ' t)
    (i : Fin k) (j : Fin n) : HasDerivAt (fun s => A (θ s) i j) (A' i j θ') t :=
  (hA i j).comp_hasDerivAt t hθ

/-- **MLS p. 269: "Differentiating the constraint equation (6.3) yields `A(q) q̈ + Ȧ(q) q̇ = 0`".**
If the motion satisfies the Pfaffian constraint near `t`, the entries of `s ↦ A(q(s))` have the
derivatives `Ad` at `t` (the book's `Ȧ`) and the velocity `q'` has the derivative `q''` at `t`, then
`A(q(t)) q'' + Ȧ q'(t) = 0`. -/
theorem mulVec_add_mulVec_eq_zero {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {Ad : Matrix (Fin k) (Fin n) ℝ} {t : ℝ}
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt A (θ s) (θ' s))
    (hAd : ∀ i j, HasDerivAt (fun s => A (θ s) i j) (Ad i j) t) (hθ' : HasDerivAt θ' θ'' t) :
    A (θ t) *ᵥ θ'' + Ad *ᵥ θ' t = 0 := by
  have h1 := Control.hasDerivAt_matrix_mulVec_rect hAd hθ'
  have h0 : HasDerivAt (fun s => A (θ s) *ᵥ θ' s) 0 t :=
    (hasDerivAt_const t (0 : Fin k → ℝ)).congr_of_eventuallyEq hc
  rw [add_comm]
  exact h1.unique h0

/-- **MLS eqs. (6.5)–(6.6), pp. 269–270: "The equations of motion are now given by equation (6.5)
with `λ` defined as in equation (6.6)."** For `L = ½ q̇ᵀ M q̇ − V` with `Υ = F − Nₑ`, along a motion
that satisfies the Pfaffian constraint near `t`, with `M(q(t))` positive definite, independent rows
of `A(q(t))` and the derivative `Ad` of `s ↦ A(q(s))` at `t` (the book's `Ȧ`), the multiplier
equations (6.4) hold at `t` exactly when (6.5) holds and `λ` is the multiplier (6.6) with
`F − C q̇ − N`, `N = ∂V/∂q + Nₑ`. Hypotheses otherwise as in `multiplierEquationsAt_mechanical_iff`.
-/
theorem multiplierEquationsAt_mechanical_iff_multiplier
    {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {V : (Fin n → ℝ) → ℝ} {V' : (Fin n → ℝ) →L[ℝ] ℝ}
    {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ}
    {Ad : Matrix (Fin k) (Fin n) ℝ} {t : ℝ} (hsymm : ∀ q, (M q).IsSymm)
    (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t)) (hV : HasFDerivAt V V' (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t)
    (hMpd : (M (θ t)).PosDef) (hA : LinearIndependent ℝ (A (θ t)).row)
    (hc : ∀ᶠ s in 𝓝 t, PfaffianAt A (θ s) (θ' s))
    (hAd : ∀ i j, HasDerivAt (fun s => A (θ s) i j) (Ad i j) t) (F Nₑ : Fin n → ℝ)
    (μ : Fin k → ℝ) :
    MultiplierEquationsAt (Lagrangian.mechanical M V) A θ (F - Nₑ) μ t ↔
      M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
          (Lagrangian.gradient V' + Nₑ) + (A (θ t))ᵀ *ᵥ μ = F ∧
        μ = multiplier (A (θ t)) (M (θ t))
          (F - Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t -
            (Lagrangian.gradient V' + Nₑ)) (Ad *ᵥ θ' t) := by
  rw [multiplierEquationsAt_mechanical_iff_force hsymm hM hV hθ hθ']
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have h' : M (θ t) *ᵥ θ'' + (A (θ t))ᵀ *ᵥ μ =
      F - Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t -
        (Lagrangian.gradient V' + Nₑ) := by
    rw [← h]
    abel
  exact (add_eq_zero_iff_eq_multiplier hMpd hA h').mp (mulVec_add_mulVec_eq_zero hc hAd hθ')

/-- **MLS p. 269, read backwards: (6.5) with `λ` from (6.6) enforces the differentiated
constraint.** For `M` positive definite and independent rows of `A`, if `M q̈ + Aᵀ λ = w` with
`λ = multiplier A M w (Ȧ q̇)`, then `A q̈ + Ȧ q̇ = 0`: the multipliers (6.6) are exactly those that
keep the acceleration tangent to the constraint. -/
theorem mulVec_add_eq_zero_of_eq_multiplier {M : Matrix (Fin n) (Fin n) ℝ}
    {A : Matrix (Fin k) (Fin n) ℝ} (hM : M.PosDef) (hA : LinearIndependent ℝ A.row)
    {acc w : Fin n → ℝ} {a : Fin k → ℝ} (h : M *ᵥ acc + Aᵀ *ᵥ multiplier A M w a = w) :
    A *ᵥ acc + a = 0 :=
  (add_eq_zero_iff_eq_multiplier hM hA h).mpr rfl

/-! ### Reduction to independent coordinates (MLS eq. (6.9), p. 272) -/

variable {r k' : ℕ}

/-- **MLS p. 272: the relabeled coordinates `q₁`.** For a relabeling `e : Fin r ⊕ Fin k ≃ Fin n` of
the coordinates, `splitFst e v = (v_{e (inl a)})ₐ`, the `r = n − k` coordinates of `q₁`. -/
def splitFst (e : Fin r ⊕ Fin k ≃ Fin n) (v : Fin n → ℝ) : Fin r → ℝ :=
  fun a => v (e (Sum.inl a))

/-- **MLS p. 272: the relabeled coordinates `q₂`,** `splitSnd e v = (v_{e (inr b)})_b`, the `k`
coordinates eliminated by the constraint. -/
def splitSnd (e : Fin r ⊕ Fin k ≃ Fin n) (v : Fin n → ℝ) : Fin k → ℝ :=
  fun b => v (e (Sum.inr b))

/-- **MLS p. 272: the vector `q = (q₁, q₂)`** assembled from its two parts through the relabeling
`e`. -/
def splitJoin (e : Fin r ⊕ Fin k ≃ Fin n) (v₁ : Fin r → ℝ) (v₂ : Fin k → ℝ) : Fin n → ℝ :=
  fun j => Sum.elim v₁ v₂ (e.symm j)

/-- **MLS p. 272: the block `A₁` of `A(q) = [A₁(q) A₂(q)]`,** the columns of `q₁`. -/
def colsFst (A : Matrix (Fin k') (Fin n) ℝ) (e : Fin r ⊕ Fin k ≃ Fin n) :
    Matrix (Fin k') (Fin r) ℝ :=
  A.submatrix id (e ∘ Sum.inl)

/-- **MLS p. 272: the block `A₂` of `A(q) = [A₁(q) A₂(q)]`,** the columns of `q₂`. -/
def colsSnd (A : Matrix (Fin k') (Fin n) ℝ) (e : Fin r ⊕ Fin k ≃ Fin n) :
    Matrix (Fin k') (Fin k) ℝ :=
  A.submatrix id (e ∘ Sum.inr)

/-- `q₁` of `(q₁, q₂)` is `q₁` (MLS p. 272). -/
@[simp] theorem splitFst_splitJoin (e : Fin r ⊕ Fin k ≃ Fin n) (v₁ : Fin r → ℝ)
    (v₂ : Fin k → ℝ) : splitFst e (splitJoin e v₁ v₂) = v₁ := by
  funext a
  simp [splitFst, splitJoin]

/-- `q₂` of `(q₁, q₂)` is `q₂` (MLS p. 272). -/
@[simp] theorem splitSnd_splitJoin (e : Fin r ⊕ Fin k ≃ Fin n) (v₁ : Fin r → ℝ)
    (v₂ : Fin k → ℝ) : splitSnd e (splitJoin e v₁ v₂) = v₂ := by
  funext b
  simp [splitSnd, splitJoin]

/-- **`A q = A₁ q₁ + A₂ q₂` (MLS p. 272)** for the relabeling `e`. -/
theorem mulVec_split (A : Matrix (Fin k') (Fin n) ℝ) (e : Fin r ⊕ Fin k ≃ Fin n)
    (v : Fin n → ℝ) :
    A *ᵥ v = colsFst A e *ᵥ splitFst e v + colsSnd A e *ᵥ splitSnd e v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, colsFst, colsSnd, splitFst, splitSnd,
    Matrix.submatrix_apply, id, Function.comp_apply]
  rw [← Fintype.sum_sum_type (fun s => A i (e s) * v (e s))]
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

/-- **`x · v = x₁ · v₁ + x₂ · v₂` (MLS p. 272, "the properties of the inner product")** for the
relabeling `e`. -/
theorem dotProduct_split (e : Fin r ⊕ Fin k ≃ Fin n) (x v : Fin n → ℝ) :
    x ⬝ᵥ v = splitFst e x ⬝ᵥ splitFst e v + splitSnd e x ⬝ᵥ splitSnd e v := by
  simp only [dotProduct, splitFst, splitSnd]
  rw [← Fintype.sum_sum_type (fun s => x (e s) * v (e s))]
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

/-- **MLS p. 272: "`A(q) · δq = 0 ⟺ δq₂ = −A₂⁻¹(q) A₁(q) δq₁`, where `δq₁` is free"**, for
`A = [A₁ A₂]` (after the relabeling `e`) with `A₂` invertible. The same statement with `q̇` in place
of `δq` is the elimination `q̇₂ = −A₂⁻¹ A₁ q̇₁` of p. 272. -/
theorem mulVec_eq_zero_iff_split {A : Matrix (Fin k) (Fin n) ℝ} {e : Fin r ⊕ Fin k ≃ Fin n}
    (h₂ : IsUnit (colsSnd A e).det) (v : Fin n → ℝ) :
    A *ᵥ v = 0 ↔ splitSnd e v = -((colsSnd A e)⁻¹ * colsFst A e) *ᵥ splitFst e v := by
  rw [mulVec_split A e v]
  constructor
  · intro h
    have h' : colsSnd A e *ᵥ splitSnd e v = -(colsFst A e *ᵥ splitFst e v) :=
      eq_neg_of_add_eq_zero_right h
    have := congrArg ((colsSnd A e)⁻¹ *ᵥ ·) h'
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h₂, Matrix.one_mulVec,
      Matrix.mulVec_neg] at this
    rw [this, Matrix.neg_mulVec]
  · intro h
    rw [h, Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ h₂, Matrix.one_mul, add_neg_cancel]

/-- **The linear algebra of MLS eq. (6.9), p. 272.** For `A = [A₁ A₂]` (after the relabeling `e`)
with `A₂` invertible, a generalized force `x` does no virtual work exactly when
`x₁ − A₁ᵀ A₂⁻ᵀ x₂ = 0` ("since `δq₁` is free"). -/
theorem doesNoVirtualWork_iff_split {A : Matrix (Fin k) (Fin n) ℝ} {e : Fin r ⊕ Fin k ≃ Fin n}
    (h₂ : IsUnit (colsSnd A e).det) (x : Fin n → ℝ) :
    DoesNoVirtualWork A x ↔
      splitFst e x - ((colsFst A e)ᵀ * ((colsSnd A e)⁻¹)ᵀ) *ᵥ splitSnd e x = 0 := by
  set B := (colsSnd A e)⁻¹ * colsFst A e
  have hBt : (colsFst A e)ᵀ * ((colsSnd A e)⁻¹)ᵀ = Bᵀ := by
    rw [Matrix.transpose_mul]
  rw [hBt]
  have key : ∀ v₁ : Fin r → ℝ, splitFst e x ⬝ᵥ v₁ + splitSnd e x ⬝ᵥ (-B *ᵥ v₁) =
      (splitFst e x - Bᵀ *ᵥ splitSnd e x) ⬝ᵥ v₁ := by
    intro v₁
    rw [sub_dotProduct, Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose, sub_eq_add_neg]
  constructor
  · intro h
    set y := splitFst e x - Bᵀ *ᵥ splitSnd e x
    have hv : A *ᵥ splitJoin e y (-B *ᵥ y) = 0 := by
      rw [mulVec_eq_zero_iff_split h₂]
      simp [B]
    have h0 := h _ hv
    rw [dotProduct_split e, splitFst_splitJoin, splitSnd_splitJoin, key] at h0
    exact dotProduct_self_eq_zero.mp h0
  · intro h δq hδ
    rw [mulVec_eq_zero_iff_split h₂] at hδ
    rw [dotProduct_split e, hδ, key, h, zero_dotProduct]

/-- **MLS eq. (6.9), p. 272: the Lagrange–d'Alembert equations in the relabeled coordinates.** For
`A(q(t)) = [A₁ A₂]` (after the relabeling `e`) with `A₂` invertible, (6.7)–(6.8) hold at `t` exactly
when `(d/dt ∂L/∂q̇₁ − ∂L/∂q₁ − Υ₁) − A₁ᵀ A₂⁻ᵀ (d/dt ∂L/∂q̇₂ − ∂L/∂q₂ − Υ₂) = 0`, with the derivative
`p` of `s ↦ ∂L/∂q̇ (q(s), q̇(s))` at `t` part of the statement as in `LagrangeDAlembertAt`. -/
theorem lagrangeDAlembertAt_iff_split {L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ} {θ : ℝ → Fin n → ℝ} {Υ : Fin n → ℝ} {t : ℝ}
    {e : Fin r ⊕ Fin k ≃ Fin n} (h₂ : IsUnit (colsSnd (A (θ t)) e).det) :
    LagrangeDAlembertAt L A θ Υ t ↔ ∃ p : Fin n → ℝ,
      (∀ i, HasDerivAt (fun s => Lagrangian.velocityPartial L (θ s) (deriv θ s) i) (p i) t) ∧
        splitFst e (p - (fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i) - Υ) -
          ((colsFst (A (θ t)) e)ᵀ * ((colsSnd (A (θ t)) e)⁻¹)ᵀ) *ᵥ
            splitSnd e (p - (fun i => Lagrangian.positionPartial L (θ t) (deriv θ t) i) - Υ) =
          0 := by
  unfold LagrangeDAlembertAt
  simp only [doesNoVirtualWork_iff_split h₂]

/-! ### "This can always be achieved locally by reordering" (MLS p. 272) -/

/-- **MLS p. 272, the reordering, pointwise.** A `k × n` matrix with linearly independent rows has
`k` columns forming an invertible `k × k` matrix: there is an injective choice `c` of columns with
`A.submatrix id c` invertible. -/
theorem exists_isUnit_det_submatrix {A : Matrix (Fin k) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A.row) :
    ∃ c : Fin k → Fin n, Function.Injective c ∧ IsUnit (A.submatrix id c).det := by
  have hrank : Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) = k := by
    rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_row,
      finrank_span_eq_card hA, Fintype.card_fin]
  have htop : Submodule.span ℝ (Set.range A.col) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fin_fun])
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ A.col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan, htop, finrank_top,
      Module.finrank_fin_fun]
  let eκ := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ eκ.symm, ha.comp eκ.symm.injective, ?_⟩
  have hcol : (A.submatrix id (a ∘ eκ.symm)).col = A.col ∘ a ∘ eκ.symm := by
    funext j i
    rfl
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit, hcol]
  exact hli.comp eκ.symm eκ.symm.injective

/-- **MLS p. 272: "This can always be achieved locally by reordering the configuration space
variables."** A constraint matrix with linearly independent rows admits a relabeling
`e : Fin r ⊕ Fin k ≃ Fin n` of the coordinates, `q = (q₁, q₂)`, for which the block `A₂` is
invertible. -/
theorem exists_split_isUnit_det {A : Matrix (Fin k) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A.row) :
    ∃ (r : ℕ) (e : Fin r ⊕ Fin k ≃ Fin n), IsUnit (colsSnd A e).det := by
  classical
  obtain ⟨c, hc, hdet⟩ := exists_isUnit_det_submatrix hA
  let p : Fin n → Prop := fun j => j ∈ Set.range c
  let eK : Fin k ≃ {j // p j} := Equiv.ofInjective c hc
  let eR : Fin (Fintype.card {j // ¬p j}) ≃ {j // ¬p j} := (Fintype.equivFin _).symm
  let e : Fin (Fintype.card {j // ¬p j}) ⊕ Fin k ≃ Fin n :=
    (Equiv.sumComm _ _).trans ((Equiv.sumCongr eK eR).trans (Equiv.sumCompl p))
  refine ⟨_, e, ?_⟩
  have h : colsSnd A e = A.submatrix id c := by
    funext i b
    simp [colsSnd, e, eK]
    rfl
  rwa [h]

/-- **MLS p. 272, "locally": the reordering persists near a configuration.** If the constraint field
`A` is continuous at `q₀` and the columns `c` of `A(q₀)` form an invertible matrix, the same columns
form an invertible matrix at every configuration near `q₀`. -/
theorem eventually_isUnit_det_submatrix {A : (Fin n → ℝ) → Matrix (Fin k) (Fin n) ℝ}
    {q₀ : Fin n → ℝ} (hA : ContinuousAt A q₀) (c : Fin k → Fin n)
    (h : IsUnit ((A q₀).submatrix id c).det) :
    ∀ᶠ q in 𝓝 q₀, IsUnit ((A q).submatrix id c).det := by
  have hcont : ContinuousAt (fun q => ((A q).submatrix id c).det) q₀ :=
    ((continuous_id.matrix_submatrix id c).matrix_det.continuousAt).comp hA
  filter_upwards [hcont.eventually_ne (isUnit_iff_ne_zero.mp h)] with q hq
  exact isUnit_iff_ne_zero.mpr hq

end Constrained
end RoboLean
