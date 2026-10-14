import RoboLean.Dynamics.ConstrainedLagrangian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Substituting a Pfaffian constraint into the Lagrangian, eq. (6.15) (MLS §6.1.4)

MLS Chapter 6, §1.4, printed pp. 274–276 (renders inspected this session).

**What MLS states.** For a "three-dimensional, unforced Pfaffian system with configuration
`q = (r, s) ∈ ℝ² × ℝ`, constraint `ṡ + aᵀ(r) ṙ = 0`", a Lagrangian `L(r, ṙ, ṡ)` with no dependence
on `s`, and the constrained Lagrangian `L_c(r, ṙ) = L(r, ṙ, −aᵀ(r) ṙ)`, Lagrange's equations for
`L_c` expand to (6.15)
`(d/dt ∂L/∂ṙᵢ − ∂L/∂rᵢ) − aᵢ(r)(d/dt ∂L/∂ṡ − ∂L/∂s) = ∂L/∂ṡ (ȧᵢ(r) − Σⱼ ∂aⱼ/∂rᵢ ṙ)`, whose left side
"is exactly the Lagrange–d'Alembert equation for the system"; "in general, substituting a set of
Pfaffian constraints into the Lagrangian and then applying the Lagrange–d'Alembert equations gives
the wrong equations", and if `aᵢ = ∂h/∂rᵢ` the right side "is identically zero since mixed partials
commute" (p. 276).

**Formalized** (for `r ∈ ℝᵏ`, any `k`; `L` is a function of `(r, ṙ, ṡ)` with joint Fréchet
derivative `DL`, so `∂L/∂rᵢ = DL(eᵢ, 0, 0)`, `∂L/∂ṙᵢ = DL(0, eᵢ, 0)`, `∂L/∂ṡ = DL(0, 0, 1)`;
`∂L/∂s = 0` since `L` has no `s` argument; `Da` is the Fréchet derivative of `a`, so
`∂aⱼ/∂rᵢ = (Da eᵢ)ⱼ` and `ȧ = Da ṙ`):

* `constrainedLagrangian L a` (`L_c`) and its partial derivatives by the chain rule
  (`velocityPartial_constrainedLagrangian`, `positionPartial_constrainedLagrangian`), the expansion
  printed above (6.15);
* (6.15) along a motion (`lagrangeEquationsAt_constrainedLagrangian_iff`), with the last sum read as
  `Σⱼ (∂aⱼ/∂rᵢ) ṙⱼ`, as in the expansion above (6.15); the printed `ṙᵢ` in (6.15) and in the
  holonomic check of p. 276 is E034's observation O7;
* the holonomic case: for `a = ∂h/∂r` with `h` of class `C²` the right side vanishes
  (`holonomic_rhs_eq_zero`) and Lagrange's equations of `L_c` are the left side of (6.15) set to
  zero (`lagrangeEquationsAt_constrainedLagrangian_iff_of_gradient`);
* a nonholonomic instance with a nonzero right side: `L = ½(ṙ₁² + ṙ₂² + ṡ²)`, `a(r) = (r₂, −r₁)`
  (`heisenbergConstraint`, `heisenberg_rhs_eq`, `heisenberg_rhs_ne_zero`), and so this `a` is not
  the gradient of any `C²` function (`not_exists_gradient_heisenbergConstraint`).

The identification of the left side with the Lagrange–d'Alembert equations of the system on
`q = (r, s)` (the instance of (6.9) with `A₁ = aᵀ`, `A₂ = 1`) is stated in this docstring, not as a
separate theorem. Hypotheses the book does not print: the joint differentiability of `L` near the
motion, the differentiability of `a` near the motion and the time derivatives of the momenta at `t`.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace Constrained

variable {k : ℕ}

/-- **The constrained Lagrangian of MLS printed p. 275:** `L_c(r, ṙ) = L(r, ṙ, −aᵀ(r) ṙ)`, for a
Lagrangian `L(r, ṙ, ṡ)` without `s` dependence and the constraint `ṡ + aᵀ(r) ṙ = 0`. -/
def constrainedLagrangian (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ → ℝ)
    (a : (Fin k → ℝ) → Fin k → ℝ) : (Fin k → ℝ) → (Fin k → ℝ) → ℝ :=
  fun r v => L r v (-(a r ⬝ᵥ v))

/-- **MLS p. 275, the expansion of `∂L_c/∂ṙᵢ`:** `∂L_c/∂ṙᵢ = ∂L/∂ṙᵢ − aᵢ(r) ∂L/∂ṡ`, at
`ṡ = −aᵀ(r) ṙ`, for `L` jointly differentiable there with derivative `DL`. -/
theorem velocityPartial_constrainedLagrangian {L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ → ℝ}
    {a : (Fin k → ℝ) → Fin k → ℝ} {r v : Fin k → ℝ}
    {DL : ((Fin k → ℝ) × (Fin k → ℝ) × ℝ) →L[ℝ] ℝ}
    (hL : HasFDerivAt (fun z : (Fin k → ℝ) × (Fin k → ℝ) × ℝ => L z.1 z.2.1 z.2.2) DL
      (r, v, -(a r ⬝ᵥ v))) (i : Fin k) :
    Lagrangian.velocityPartial (constrainedLagrangian L a) r v i =
      DL (0, Pi.single i 1, 0) - a r i * DL (0, 0, 1) := by
  have hs : HasDerivAt (fun s : ℝ => -(a r ⬝ᵥ (v + s • Pi.single i (1 : ℝ)))) (-(a r i)) 0 := by
    have hf : (fun s : ℝ => -(a r ⬝ᵥ (v + s • Pi.single i (1 : ℝ)))) =
        fun s => -(a r ⬝ᵥ v) + s * -(a r i) := by
      funext s
      simp only [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
      ring
    rw [hf]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-(a r i))).const_add (-(a r ⬝ᵥ v))
  have hv : HasDerivAt (fun s : ℝ => v + s • Pi.single i (1 : ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add v
  have hc := (hasDerivAt_const (0 : ℝ) r).prodMk (hv.prodMk hs)
  have hcomp := hL.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  rw [Lagrangian.velocityPartial]
  refine hcomp.deriv.trans ?_
  rw [show ((0 : Fin k → ℝ), Pi.single i (1 : ℝ), -(a r i)) =
      ((0 : Fin k → ℝ), Pi.single i (1 : ℝ), (0 : ℝ)) +
        (-(a r i)) • ((0 : Fin k → ℝ), (0 : Fin k → ℝ), (1 : ℝ)) by simp,
    map_add, map_smul, smul_eq_mul]
  ring

/-- The derivative of `s ↦ f(s) ⬝ v` for a fixed vector `v` (the term `aᵀ(r) ṙ` of MLS p. 275). -/
private theorem hasDerivAt_dotProduct_const {f : ℝ → Fin k → ℝ} {f' : Fin k → ℝ} {x : ℝ}
    (hf : HasDerivAt f f' x) (v : Fin k → ℝ) : HasDerivAt (fun s => f s ⬝ᵥ v) (f' ⬝ᵥ v) x := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.mp hf j).mul_const (v j)

/-- **MLS p. 275, the expansion of `∂L_c/∂rᵢ`:** `∂L_c/∂rᵢ = ∂L/∂rᵢ − ∂L/∂ṡ Σⱼ (∂aⱼ/∂rᵢ) ṙⱼ`, for
`L` jointly differentiable at `(r, ṙ, −aᵀ(r) ṙ)` and `a` differentiable at `r` with derivative `Da`.
-/
theorem positionPartial_constrainedLagrangian {L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ → ℝ}
    {a : (Fin k → ℝ) → Fin k → ℝ} {r v : Fin k → ℝ}
    {DL : ((Fin k → ℝ) × (Fin k → ℝ) × ℝ) →L[ℝ] ℝ} {Da : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)}
    (hL : HasFDerivAt (fun z : (Fin k → ℝ) × (Fin k → ℝ) × ℝ => L z.1 z.2.1 z.2.2) DL
      (r, v, -(a r ⬝ᵥ v))) (ha : HasFDerivAt a Da r) (i : Fin k) :
    Lagrangian.positionPartial (constrainedLagrangian L a) r v i =
      DL (Pi.single i 1, 0, 0) - DL (0, 0, 1) * (Da (Pi.single i 1) ⬝ᵥ v) := by
  have hx : HasDerivAt (fun s : ℝ => r + s • Pi.single i (1 : ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add r
  have ha' : HasDerivAt (fun s : ℝ => a (r + s • Pi.single i (1 : ℝ))) (Da (Pi.single i 1)) 0 :=
    ha.comp_hasDerivAt_of_eq (0 : ℝ) hx (by simp)
  have hc := hx.prodMk ((hasDerivAt_const (0 : ℝ) v).prodMk (hasDerivAt_dotProduct_const ha' v).neg)
  have hcomp := hL.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  rw [Lagrangian.positionPartial]
  refine hcomp.deriv.trans ?_
  rw [show (Pi.single i (1 : ℝ), (0 : Fin k → ℝ), -(Da (Pi.single i 1) ⬝ᵥ v)) =
      (Pi.single i (1 : ℝ), (0 : Fin k → ℝ), (0 : ℝ)) +
        (-(Da (Pi.single i 1) ⬝ᵥ v)) • ((0 : Fin k → ℝ), (0 : Fin k → ℝ), (1 : ℝ)) by simp,
    map_add, map_smul, smul_eq_mul]
  ring

/-- **MLS eq. (6.15), printed p. 275.** Along a motion `r` with velocity `r'` near `t`, with `L`
jointly differentiable (derivative `DL s`) at `(r(s), r'(s), −aᵀ(r(s)) r'(s))` and `a`
differentiable (derivative `Da s`) at `r(s)` for `s` near `t`, and with the momenta
`∂L/∂ṙᵢ = DL s (0, eᵢ, 0)` and `∂L/∂ṡ = DL s (0, 0, 1)` having the derivatives `Pᵢ`, `P_s` at `t`:
Lagrange's equations of the constrained Lagrangian `L_c` (unforced) hold at `t` exactly when, for
every `i`, `(d/dt ∂L/∂ṙᵢ − ∂L/∂rᵢ) − aᵢ(r)(d/dt ∂L/∂ṡ − ∂L/∂s) = ∂L/∂ṡ (ȧᵢ − Σⱼ (∂aⱼ/∂rᵢ) ṙⱼ)`, with
`∂L/∂s = 0` and `ȧ = Da ṙ`. -/
theorem lagrangeEquationsAt_constrainedLagrangian_iff {L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ → ℝ}
    {a : (Fin k → ℝ) → Fin k → ℝ} {r r' : ℝ → Fin k → ℝ} {t : ℝ}
    {DL : ℝ → ((Fin k → ℝ) × (Fin k → ℝ) × ℝ) →L[ℝ] ℝ} {Da : ℝ → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)}
    {Pv : Fin k → ℝ} {Ps : ℝ} (hr : ∀ᶠ s in 𝓝 t, HasDerivAt r (r' s) s)
    (hL : ∀ᶠ s in 𝓝 t, HasFDerivAt (fun z : (Fin k → ℝ) × (Fin k → ℝ) × ℝ => L z.1 z.2.1 z.2.2)
      (DL s) (r s, r' s, -(a (r s) ⬝ᵥ r' s)))
    (ha : ∀ᶠ s in 𝓝 t, HasFDerivAt a (Da s) (r s))
    (hPv : ∀ i, HasDerivAt (fun s => DL s (0, Pi.single i 1, 0)) (Pv i) t)
    (hPs : HasDerivAt (fun s => DL s (0, 0, 1)) Ps t) :
    Lagrangian.LagrangeEquationsAt (constrainedLagrangian L a) r 0 t ↔
      ∀ i, (Pv i - DL t (Pi.single i 1, 0, 0)) - a (r t) i * Ps =
        DL t (0, 0, 1) * (Da t (r' t) i - Da t (Pi.single i 1) ⬝ᵥ r' t) := by
  have hpt : ∀ i, Lagrangian.positionPartial (constrainedLagrangian L a) (r t) (deriv r t) i =
      DL t (Pi.single i 1, 0, 0) - DL t (0, 0, 1) * (Da t (Pi.single i 1) ⬝ᵥ r' t) := fun i => by
    rw [hr.self_of_nhds.deriv]
    exact positionPartial_constrainedLagrangian hL.self_of_nhds ha.self_of_nhds i
  have hcomp : HasDerivAt (fun s => a (r s)) (Da t (r' t)) t :=
    ha.self_of_nhds.comp_hasDerivAt t hr.self_of_nhds
  have key : ∀ i, HasDerivAt
      (fun s => Lagrangian.velocityPartial (constrainedLagrangian L a) (r s) (deriv r s) i)
      (Pv i - (Da t (r' t) i * DL t (0, 0, 1) + a (r t) i * Ps)) t := fun i => by
    refine ((hPv i).sub ((hasDerivAt_pi.mp hcomp i).mul hPs)).congr_of_eventuallyEq ?_
    filter_upwards [hr, hL] with s hrs hLs
    rw [hrs.deriv]
    exact velocityPartial_constrainedLagrangian hLs i
  constructor
  · intro h i
    have h' := (h i).unique (key i)
    rw [hpt, Pi.zero_apply, add_zero] at h'
    linear_combination -h'
  · intro h i
    convert key i using 1
    rw [hpt, Pi.zero_apply, add_zero]
    linear_combination -(h i)

/-- **MLS p. 276: "the right-hand side of equation (6.15) ... is identically zero since mixed
partials commute"**, for a holonomic constraint `aᵢ = ∂h/∂rᵢ` with `h` of class `C²`: with `Da` the
derivative of `a` at `r`, `(Da ṙ)ᵢ − Σⱼ (∂aⱼ/∂rᵢ) ṙⱼ = 0` for every `ṙ`. -/
theorem holonomic_rhs_eq_zero {h : (Fin k → ℝ) → ℝ} (hh : ContDiff ℝ 2 h) {r : Fin k → ℝ}
    {Da : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)}
    (ha : HasFDerivAt (fun y i => fderiv ℝ h y (Pi.single i 1)) Da r) (v : Fin k → ℝ)
    (i : Fin k) : Da v i - Da (Pi.single i 1) ⬝ᵥ v = 0 := by
  have hd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let Φ : ((Fin k → ℝ) →L[ℝ] ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.apply ℝ ℝ (Pi.single j (1 : ℝ))
  have hΦ : HasFDerivAt (fun y j => fderiv ℝ h y (Pi.single j 1))
      (Φ.comp (fderiv ℝ (fderiv ℝ h) r)) r :=
    Φ.hasFDerivAt.comp r (hd r).hasFDerivAt
  have hDa : Da = Φ.comp (fderiv ℝ (fderiv ℝ h) r) := ha.unique hΦ
  have hsymm := (hh.contDiffAt (x := r)).isSymmSndFDerivAt (by simp)
  have h1 : Da v i = fderiv ℝ (fderiv ℝ h) r v (Pi.single i 1) := by
    rw [hDa]
    rfl
  have h2 : Da (Pi.single i 1) ⬝ᵥ v = fderiv ℝ (fderiv ℝ h) r (Pi.single i 1) v := by
    rw [Lagrangian.apply_eq_dotProduct_gradient (fderiv ℝ (fderiv ℝ h) r (Pi.single i 1)) v,
      dotProduct_comm, hDa]
    rfl
  rw [h1, h2, hsymm v (Pi.single i 1), sub_self]

/-- **MLS p. 276: "if the constraints happen to be holonomic, then substituting the constraints into
the Lagrangian will give the correct equations of motion".** Under the hypotheses of
`lagrangeEquationsAt_constrainedLagrangian_iff` with `aᵢ = ∂h/∂rᵢ`, `h` of class `C²`, Lagrange's
equations of `L_c` hold at `t` exactly when the left side of (6.15) vanishes for every `i`. -/
theorem lagrangeEquationsAt_constrainedLagrangian_iff_of_gradient
    {L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ → ℝ} {h : (Fin k → ℝ) → ℝ} (hh : ContDiff ℝ 2 h)
    {r r' : ℝ → Fin k → ℝ} {t : ℝ} {DL : ℝ → ((Fin k → ℝ) × (Fin k → ℝ) × ℝ) →L[ℝ] ℝ}
    {Da : ℝ → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)} {Pv : Fin k → ℝ} {Ps : ℝ}
    (hr : ∀ᶠ s in 𝓝 t, HasDerivAt r (r' s) s)
    (hL : ∀ᶠ s in 𝓝 t, HasFDerivAt (fun z : (Fin k → ℝ) × (Fin k → ℝ) × ℝ => L z.1 z.2.1 z.2.2)
      (DL s) (r s, r' s,
        -((fun y i => fderiv ℝ h y (Pi.single i 1)) (r s) ⬝ᵥ r' s)))
    (ha : ∀ᶠ s in 𝓝 t, HasFDerivAt (fun y i => fderiv ℝ h y (Pi.single i 1)) (Da s) (r s))
    (hPv : ∀ i, HasDerivAt (fun s => DL s (0, Pi.single i 1, 0)) (Pv i) t)
    (hPs : HasDerivAt (fun s => DL s (0, 0, 1)) Ps t) :
    Lagrangian.LagrangeEquationsAt
        (constrainedLagrangian L fun y i => fderiv ℝ h y (Pi.single i 1)) r 0 t ↔
      ∀ i, (Pv i - DL t (Pi.single i 1, 0, 0)) -
        fderiv ℝ h (r t) (Pi.single i 1) * Ps = 0 := by
  rw [lagrangeEquationsAt_constrainedLagrangian_iff (L := L)
    (a := fun y i => fderiv ℝ h y (Pi.single i 1)) hr hL ha hPv hPs]
  have h0 : ∀ i, Da t (r' t) i - Da t (Pi.single i 1) ⬝ᵥ r' t = 0 := fun i =>
    holonomic_rhs_eq_zero hh ha.self_of_nhds (r' t) i
  simp only [h0, mul_zero]

/-! ### A nonholonomic instance with a nonzero right side -/

/-- **A nonintegrable constraint `ṡ + aᵀ(r) ṙ = 0` (MLS p. 275, the setting of (6.15)):**
`a(r) = (r₂, −r₁)`, i.e. `ṡ = r₁ ṙ₂ − r₂ ṙ₁`. -/
def heisenbergConstraint (r : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![r 1, -r 0]

/-- **The derivative of `heisenbergConstraint` (MLS p. 275, `∂aⱼ/∂rᵢ`):** the constant linear map
`ṙ ↦ (ṙ₂, −ṙ₁)`. -/
def heisenbergConstraintDeriv : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin !![0, 1; -1, 0])

/-- `heisenbergConstraint` has the derivative `heisenbergConstraintDeriv` everywhere (MLS p. 275).
-/
theorem hasFDerivAt_heisenbergConstraint (r : Fin 2 → ℝ) :
    HasFDerivAt heisenbergConstraint heisenbergConstraintDeriv r := by
  have hf : heisenbergConstraint = heisenbergConstraintDeriv := by
    funext y j
    fin_cases j <;>
      simp [heisenbergConstraint, heisenbergConstraintDeriv, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  rw [hf]
  exact heisenbergConstraintDeriv.hasFDerivAt

/-- **The right side of (6.15) for `L = ½(ṙ₁² + ṙ₂² + ṡ²)` and `a(r) = (r₂, −r₁)` (MLS p. 275):**
with `∂L/∂ṡ = ṡ = −aᵀ(r) ṙ`, the first component is `ṡ · 2 ṙ₂ = 2 ṙ₂ (r₁ ṙ₂ − r₂ ṙ₁)`. -/
theorem heisenberg_rhs_eq (r v : Fin 2 → ℝ) :
    -(heisenbergConstraint r ⬝ᵥ v) *
        (heisenbergConstraintDeriv v 0 - heisenbergConstraintDeriv (Pi.single 0 1) ⬝ᵥ v) =
      2 * v 1 * (r 0 * v 1 - r 1 * v 0) := by
  simp [heisenbergConstraint, heisenbergConstraintDeriv, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- **MLS p. 275: "in general, substituting a set of Pfaffian constraints into the Lagrangian ...
gives the wrong equations"**: for `L = ½(ṙ₁² + ṙ₂² + ṡ²)` and `a(r) = (r₂, −r₁)`, at `r = (1, 0)`,
`ṙ = (0, 1)` the right side of (6.15) is `2 ≠ 0`. -/
theorem heisenberg_rhs_ne_zero :
    -(heisenbergConstraint ![1, 0] ⬝ᵥ ![0, 1]) *
        (heisenbergConstraintDeriv ![0, 1] 0 -
          heisenbergConstraintDeriv (Pi.single 0 1) ⬝ᵥ ![0, 1]) ≠ 0 := by
  rw [heisenberg_rhs_eq]
  norm_num

/-- **The constraint `ṡ = r₁ ṙ₂ − r₂ ṙ₁` is not holonomic (MLS p. 276):** `a(r) = (r₂, −r₁)` is not
the gradient of any function `h` of class `C²`. -/
theorem not_exists_gradient_heisenbergConstraint :
    ¬ ∃ h : (Fin 2 → ℝ) → ℝ, ContDiff ℝ 2 h ∧
      ∀ y, (fun i => fderiv ℝ h y (Pi.single i 1)) = heisenbergConstraint y := by
  rintro ⟨h, hh, hg⟩
  have ha : HasFDerivAt (fun y i => fderiv ℝ h y (Pi.single i 1)) heisenbergConstraintDeriv
      (0 : Fin 2 → ℝ) := by
    rw [show (fun y i => fderiv ℝ h y (Pi.single i 1)) = heisenbergConstraint from funext hg]
    exact hasFDerivAt_heisenbergConstraint 0
  exact (mul_ne_zero_iff.mp heisenberg_rhs_ne_zero).2 (holonomic_rhs_eq_zero hh ha ![0, 1] 0)

end Constrained
end RoboLean
