import RoboLean.Dynamics.Christoffel

/-!
# Lagrange's equations and the equations of motion of a mechanical system

MLS Chapter 4, printed pp. 157–159 (Theorem 4.1) and §3.2, pp. 169–172 (eqs. (4.20)–(4.24),
Lemma 4.2 and the passivity remark).

**Lagrange's equations (Theorem 4.1, p. 158)** are stated here as a predicate on a trajectory,
not derived. MLS cites a reference ([99]) for the proof and does not prove the theorem; the
variational (or d'Alembert) derivation from Newton's law for constrained particles is not
formalized. For a Lagrangian `L(q, q̇)` on `ℝⁿ × ℝⁿ`, a trajectory `θ : ℝ → ℝⁿ` and a
generalized force `Υ`, `LagrangeEquationsAt L θ Υ t` says that for every `i` the function
`s ↦ ∂L/∂q̇ᵢ (θ(s), θ̇(s))` has an actual derivative at `t`, equal to `∂L/∂qᵢ (θ(t), θ̇(t)) + Υᵢ`,
i.e. `d/dt ∂L/∂q̇ᵢ − ∂L/∂qᵢ = Υᵢ` (eq. (4.5)) with the derivative's existence part of the
statement. The partial derivatives are one-variable derivatives along coordinate lines and the
velocity is `deriv θ`.

**Equations of motion (eqs. (4.20)–(4.24), pp. 169–171).** For the mechanical Lagrangian
`L(q, v) = ½ vᵀ M(q) v − V(q)` with `M(q)` symmetric at every configuration, Fréchet derivative
data `M' i j` of the entries of `M` and `V'` of `V` at `θ(t)`, and a trajectory whose velocity
`θ'` and acceleration `θ''` are actual derivatives, Lagrange's equations at `t` hold exactly when

`M(θ) θ'' + C(θ, θ') θ' + ∂V/∂θ = Υ`,

with `C` the Christoffel Coriolis matrix of eq. (4.23) (`Christoffel.coriolisMatrix`) and
`∂V/∂θ` the gradient read from `V'` (`Lagrangian.gradient`). This is eq. (4.21), and (4.24)
with `N = ∂V/∂θ` plus any further joint forces (`lagrangeEquationsAt_mechanical_iff_torque`).
The open-chain form uses `InertialChain.massMatrix`; differentiability of a general chain's
mass matrix and of its potential energy are hypotheses here.

**Passivity (p. 172).** Along a solution the total energy `½ θ'ᵀ M(θ) θ' + V(θ)` has derivative
`θ'ᵀ Υ` (`hasDerivAt_energy`), by the skew symmetry of `Ṁ − 2C` (Lemma 4.2(2)); with `Υ = 0`
the energy is conserved. MLS refers to its Exercise 8 for this; the exercise text is not
formalized.

Nothing here concerns existence or uniqueness of solutions, friction models, or a physical
manipulator.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean

namespace Lagrangian

variable {n : ℕ}

/-! ### Partial derivatives of a Lagrangian and Lagrange's equations (MLS Theorem 4.1) -/

/-- **The partial derivative `∂L/∂q̇ᵢ` (MLS eq. (4.5), p. 158)** of a Lagrangian
`L(q, q̇)` at `(q, v)`: the one-variable derivative at `0` of `s ↦ L(q, v + s eᵢ)`, with `eᵢ` the
`i`th coordinate vector. -/
def velocityPartial (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (q v : Fin n → ℝ) (i : Fin n) : ℝ :=
  deriv (fun s : ℝ => L q (v + s • Pi.single i 1)) 0

/-- **The partial derivative `∂L/∂qᵢ` (MLS eq. (4.5), p. 158)** of a Lagrangian `L(q, q̇)` at
`(q, v)`: the one-variable derivative at `0` of `s ↦ L(q + s eᵢ, v)`. -/
def positionPartial (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (q v : Fin n → ℝ) (i : Fin n) : ℝ :=
  deriv (fun s : ℝ => L (q + s • Pi.single i 1) v) 0

/-- **MLS Theorem 4.1, eq. (4.5), p. 158: Lagrange's equations at time `t`, as a predicate.**
For a Lagrangian `L(q, q̇)` in generalized coordinates `q ∈ ℝⁿ`, a trajectory `θ` (velocity
`deriv θ`) and a generalized force `Υ ∈ ℝⁿ` acting at time `t`: for every `i`, the function
`s ↦ ∂L/∂q̇ᵢ (θ(s), θ̇(s))` has an actual derivative at `t` equal to
`∂L/∂qᵢ (θ(t), θ̇(t)) + Υᵢ`, i.e. `d/dt ∂L/∂q̇ᵢ − ∂L/∂qᵢ = Υᵢ`. MLS cites [99] for the theorem
that these are the equations of motion of a mechanical system; that derivation is not
formalized, and the predicate is the definition used here. -/
def LagrangeEquationsAt (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (θ : ℝ → Fin n → ℝ)
    (Υ : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ i, HasDerivAt (fun s => velocityPartial L (θ s) (deriv θ s) i)
    (positionPartial L (θ t) (deriv θ t) i + Υ i) t

/-- **MLS Theorem 4.1, eq. (4.5), p. 158, along a whole motion:** Lagrange's equations hold at
every time, with generalized force `Υ(t)`. -/
def LagrangeEquations (L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (θ : ℝ → Fin n → ℝ)
    (Υ : ℝ → Fin n → ℝ) : Prop :=
  ∀ t, LagrangeEquationsAt L θ (Υ t) t

/-! ### The mechanical Lagrangian `½ q̇ᵀ M(q) q̇ − V(q)` (MLS eq. (4.20)) -/

/-- **MLS p. 169, eq. (4.20): the Lagrangian `L(q, q̇) = ½ q̇ᵀ M(q) q̇ − V(q)`** of a mechanical
system with inertia matrix field `M` and potential energy `V`. -/
def mechanical (M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (V : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  fun q v => (1 / 2 : ℝ) * (v ⬝ᵥ (M q *ᵥ v)) - V q

/-- **The gradient `∂V/∂q` (MLS pp. 170, 174, the potential-force term)** read from a Fréchet
derivative `V'` of the potential at a configuration: `(∂V/∂q)ᵢ = V' eᵢ`. -/
def gradient (V' : (Fin n → ℝ) →L[ℝ] ℝ) : Fin n → ℝ :=
  fun i => V' (Pi.single i 1)

/-- The derivative of a Fréchet-differentiable potential along a motion is the gradient paired
with the velocity, `V' θ̇ = θ̇ ⬝ ∂V/∂q` (MLS p. 169). -/
theorem apply_eq_dotProduct_gradient (V' : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    V' v = v ⬝ᵥ gradient V' := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, gradient, dotProduct]

/-- **MLS total energy (p. 172, passivity remark):** `E(q, q̇) = ½ q̇ᵀ M(q) q̇ + V(q)`. -/
def energy (M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (V : (Fin n → ℝ) → ℝ)
    (q v : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (v ⬝ᵥ (M q *ᵥ v)) + V q

private theorem dotProduct_mulVec_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) = ∑ j, ∑ k, v j * A j k * v k := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hasDerivAt_line (q e : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => q + s • e) e 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add q

private theorem hasDerivAt_quadratic_line (A : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => (a + s • b) ⬝ᵥ (A *ᵥ (a + s • b)))
      (b ⬝ᵥ (A *ᵥ a) + a ⬝ᵥ (A *ᵥ b)) 0 := by
  have hf : (fun s : ℝ => (a + s • b) ⬝ᵥ (A *ᵥ (a + s • b))) = fun s =>
      a ⬝ᵥ (A *ᵥ a) + s * (b ⬝ᵥ (A *ᵥ a) + a ⬝ᵥ (A *ᵥ b)) + s ^ 2 * (b ⬝ᵥ (A *ᵥ b)) := by
    funext s
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rw [hf]
  have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (b ⬝ᵥ (A *ᵥ a) + a ⬝ᵥ (A *ᵥ b))).const_add
    (a ⬝ᵥ (A *ᵥ a))
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (b ⬝ᵥ (A *ᵥ b))
  convert h1.add h2 using 1
  · rfl
  · simp

/-- **MLS p. 169: `∂L/∂q̇ᵢ = ∑ⱼ Mᵢⱼ q̇ⱼ`** for the mechanical Lagrangian (4.20) when `M(q)` is
symmetric. -/
theorem velocityPartial_mechanical {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (V : (Fin n → ℝ) → ℝ) {q : Fin n → ℝ} (hsymm : (M q).IsSymm) (v : Fin n → ℝ) (i : Fin n) :
    velocityPartial (mechanical M V) q v i = (M q *ᵥ v) i := by
  have h := ((hasDerivAt_quadratic_line (M q) v (Pi.single i 1)).const_mul (1 / 2 : ℝ)).sub_const
    (V q)
  rw [velocityPartial, show (fun s : ℝ => mechanical M V q (v + s • Pi.single i 1)) =
    fun s => (1 / 2 : ℝ) * ((v + s • Pi.single i 1) ⬝ᵥ (M q *ᵥ (v + s • Pi.single i 1))) - V q
    from rfl, h.deriv]
  rw [single_one_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm.eq,
    dotProduct_single_one]
  ring

/-- **MLS p. 169: `∂L/∂qᵢ = ½ ∑ⱼ,ₖ ∂Mⱼₖ/∂qᵢ q̇ⱼ q̇ₖ − ∂V/∂qᵢ`** for the mechanical Lagrangian
(4.20), with the partial derivatives of `M` and `V` read from Fréchet derivative data at `q`
(`Christoffel.partials`, `gradient`). -/
theorem positionPartial_mechanical {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {q : Fin n → ℝ}
    (hM : ∀ i j, HasFDerivAt (fun p => M p i j) (M' i j) q) (hV : HasFDerivAt V V' q)
    (v : Fin n → ℝ) (i : Fin n) :
    positionPartial (mechanical M V) q v i =
      (1 / 2 : ℝ) * ∑ j, ∑ k, Christoffel.partials M' i j k * v j * v k - gradient V' i := by
  have hl := hasDerivAt_line q (Pi.single i 1 : Fin n → ℝ)
  have hq : q = q + (0 : ℝ) • (Pi.single i 1 : Fin n → ℝ) := by simp
  have hMl : ∀ j k, HasDerivAt (fun s : ℝ => M (q + s • Pi.single i 1) j k)
      (Christoffel.partials M' i j k) 0 := fun j k =>
    (hM j k).comp_hasDerivAt_of_eq (0 : ℝ) hl hq
  have hVl : HasDerivAt (fun s : ℝ => V (q + s • Pi.single i 1)) (gradient V' i) 0 :=
    hV.comp_hasDerivAt_of_eq (0 : ℝ) hl hq
  have hjk : ∀ j k, HasDerivAt (fun s : ℝ => v j * M (q + s • Pi.single i 1) j k * v k)
      (Christoffel.partials M' i j k * v j * v k) 0 := by
    intro j k
    convert ((hMl j k).const_mul (v j)).mul_const (v k) using 1
    ring
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ j, ∑ k, v j * M (q + s • Pi.single i 1) j k * v k)
      (∑ j, ∑ k, Christoffel.partials M' i j k * v j * v k) 0 :=
    HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => hjk j k
  have hf : (fun s : ℝ => mechanical M V (q + s • Pi.single i 1) v) = fun s =>
      (1 / 2 : ℝ) * (∑ j, ∑ k, v j * M (q + s • Pi.single i 1) j k * v k) -
        V (q + s • Pi.single i 1) := by
    funext s
    rw [mechanical, dotProduct_mulVec_eq_sum]
  rw [positionPartial, hf]
  exact ((hsum.const_mul (1 / 2 : ℝ)).sub hVl).deriv

/-! ### Derivative of the generalized momentum along a motion -/

/-- **MLS p. 169: `d/dt (M(θ) θ̇)ᵢ = ∑ⱼ (Mᵢⱼ θ̈ⱼ + Ṁᵢⱼ θ̇ⱼ)`,** with `Ṁ = ∑ₖ θ̇ₖ ∂M/∂θₖ` by the
chain rule. Hypotheses: Fréchet derivatives `M' i j` of the entries of `M` at `θ(t)`; near `t` the
trajectory has velocity `θ'(s)`; the velocity has derivative `θ''` at `t`. -/
theorem hasDerivAt_mulVec {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ}
    {t : ℝ} (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (i : Fin n) :
    HasDerivAt (fun s => (M (θ s) *ᵥ θ' s) i)
      ((M (θ t) *ᵥ θ'') i + (Christoffel.rate (Christoffel.partials M') (θ' t) *ᵥ θ' t) i) t := by
  have hθt : ∀ k, HasDerivAt (fun s => θ s k) (θ' t k) t :=
    hasDerivAt_pi.mp hθ.self_of_nhds
  have hθ'k : ∀ k, HasDerivAt (fun s => θ' s k) (θ'' k) t := hasDerivAt_pi.mp hθ'
  have h : HasDerivAt (fun s => ∑ j, M (θ s) i j * θ' s j)
      (∑ j, (Christoffel.rate (Christoffel.partials M') (θ' t) i j * θ' t j +
        M (θ t) i j * θ'' j)) t :=
    HasDerivAt.fun_sum fun j _ => (Christoffel.hasDerivAt_comp hM hθt i j).mul (hθ'k j)
  convert h using 1
  · rfl
  · rw [Finset.sum_add_distrib, add_comm]
    rfl

/-! ### The equations of motion (MLS eqs. (4.21), (4.24)) -/

/-- **MLS eqs. (4.20)–(4.21), pp. 169–170, and (4.24), p. 171: Lagrange's equations for
`L = ½ q̇ᵀ M(q) q̇ − V(q)` are the equations of motion `M(θ) θ̈ + C(θ, θ̇) θ̇ + ∂V/∂θ = Υ`.**
Hypotheses (explicit; MLS states them only as smoothness of the data): `M(q)` symmetric at every
configuration; Fréchet derivatives `M' i j` of the entries of `M` and `V'` of `V` at `θ(t)`;
near `t` the trajectory has velocity `θ'(s)`, and `θ'` has derivative `θ''` at `t`. `C` is the
Christoffel Coriolis matrix of eq. (4.23) built from the partials of `M` at `θ(t)`, and `∂V/∂θ`
is `gradient V'`. -/
theorem lagrangeEquationsAt_mechanical_iff {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hsymm : ∀ q, (M q).IsSymm) (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (Υ : Fin n → ℝ) :
    LagrangeEquationsAt (mechanical M V) θ Υ t ↔
      M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        gradient V' = Υ := by
  have hderiv : deriv θ =ᶠ[𝓝 t] θ' := hθ.mono fun s hs => hs.deriv
  have hdt : deriv θ t = θ' t := hderiv.self_of_nhds
  have hmom : ∀ i, HasDerivAt (fun s => velocityPartial (mechanical M V) (θ s) (deriv θ s) i)
      ((M (θ t) *ᵥ θ'') i + (Christoffel.rate (Christoffel.partials M') (θ' t) *ᵥ θ' t) i) t := by
    intro i
    refine (hasDerivAt_mulVec hM hθ hθ' i).congr_of_eventuallyEq ?_
    filter_upwards [hderiv] with s hs
    rw [velocityPartial_mechanical V (hsymm (θ s)), hs]
  have hpos : ∀ i, positionPartial (mechanical M V) (θ t) (deriv θ t) i =
      (1 / 2 : ℝ) * ∑ j, ∑ k, Christoffel.partials M' i j k * θ' t j * θ' t k -
        gradient V' i := by
    intro i
    rw [hdt]
    exact positionPartial_mechanical hM hV (θ' t) i
  constructor
  · intro hL
    funext i
    have e := (hL i).unique (hmom i)
    rw [hpos i] at e
    simp only [Pi.add_apply]
    rw [Christoffel.coriolisMatrix_mulVec_eq_rate_mulVec_sub]
    linarith
  · intro hE i
    have e := congrFun hE i
    simp only [Pi.add_apply] at e
    rw [Christoffel.coriolisMatrix_mulVec_eq_rate_mulVec_sub] at e
    convert hmom i using 1
    rw [hpos i]
    linarith

/-- **MLS eq. (4.24), p. 171, with the forces split as on p. 170.** If the generalized force is
the actuator torque `τ` minus further joint forces `Nₑ` (for example viscous friction
`Nₑ = β θ̇`), Lagrange's equations for `L = ½ q̇ᵀ M q̇ − V` are
`M(θ) θ̈ + C(θ, θ̇) θ̇ + N = τ` with `N = ∂V/∂θ + Nₑ`. Same hypotheses as
`lagrangeEquationsAt_mechanical_iff`. -/
theorem lagrangeEquationsAt_mechanical_iff_torque {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hsymm : ∀ q, (M q).IsSymm) (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (τ Nₑ : Fin n → ℝ) :
    LagrangeEquationsAt (mechanical M V) θ (τ - Nₑ) t ↔
      M (θ t) *ᵥ θ'' + Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        (gradient V' + Nₑ) = τ := by
  rw [lagrangeEquationsAt_mechanical_iff hsymm hM hV hθ hθ']
  constructor
  · intro h
    rw [← add_assoc, h, sub_add_cancel]
  · intro h
    rw [← h]
    abel

/-! ### Passivity: the energy balance along solutions (MLS p. 172) -/

/-- **MLS p. 172, the passivity property, as an energy balance.** Along a solution of Lagrange's
equations for `L = ½ q̇ᵀ M q̇ − V` with generalized force `Υ`, the total energy
`½ θ̇ᵀ M(θ) θ̇ + V(θ)` has derivative `θ̇ᵀ Υ` at `t`, the power of the generalized forces. The
proof uses `θ̇ᵀ (Ṁ − 2C) θ̇ = 0` (Lemma 4.2(2),
`Christoffel.dotProduct_rate_sub_two_coriolisMatrix_mulVec`), whose symmetric partial
derivatives follow from `M` symmetric everywhere. Same hypotheses as
`lagrangeEquationsAt_mechanical_iff`. -/
theorem hasDerivAt_energy {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hsymm : ∀ q, (M q).IsSymm) (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) {Υ : Fin n → ℝ}
    (hL : LagrangeEquationsAt (mechanical M V) θ Υ t) :
    HasDerivAt (fun s => energy M V (θ s) (θ' s)) (θ' t ⬝ᵥ Υ) t := by
  have hE := (lagrangeEquationsAt_mechanical_iff hsymm hM hV hθ hθ' Υ).mp hL
  have hθ'k : ∀ k, HasDerivAt (fun s => θ' s k) (θ'' k) t := hasDerivAt_pi.mp hθ'
  set dM := Christoffel.partials M'
  set R := Christoffel.rate dM (θ' t)
  set C := Christoffel.coriolisMatrix dM (θ' t)
  have hkin : HasDerivAt (fun s => θ' s ⬝ᵥ (M (θ s) *ᵥ θ' s))
      (∑ i, (θ'' i * (M (θ t) *ᵥ θ' t) i + θ' t i * ((M (θ t) *ᵥ θ'') i + (R *ᵥ θ' t) i))) t :=
    HasDerivAt.fun_sum fun i _ => (hθ'k i).mul (hasDerivAt_mulVec hM hθ hθ' i)
  have hpot : HasDerivAt (fun s => V (θ s)) (θ' t ⬝ᵥ gradient V') t := by
    rw [← apply_eq_dotProduct_gradient]
    exact hV.comp_hasDerivAt t hθ.self_of_nhds
  have hsum : (∑ i, (θ'' i * (M (θ t) *ᵥ θ' t) i + θ' t i * ((M (θ t) *ᵥ θ'') i +
      (R *ᵥ θ' t) i))) =
      2 * (θ' t ⬝ᵥ (M (θ t) *ᵥ θ'')) + θ' t ⬝ᵥ (R *ᵥ θ' t) := by
    have hs : θ'' ⬝ᵥ (M (θ t) *ᵥ θ' t) = θ' t ⬝ᵥ (M (θ t) *ᵥ θ'') := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, (hsymm (θ t)).eq,
        dotProduct_comm]
    simp only [dotProduct, mul_add, Finset.sum_add_distrib] at hs ⊢
    rw [hs]
    ring
  have hskew : θ' t ⬝ᵥ (R *ᵥ θ' t) = 2 * (θ' t ⬝ᵥ (C *ᵥ θ' t)) := by
    have h0 := Christoffel.dotProduct_rate_sub_two_coriolisMatrix_mulVec
      (Christoffel.partials_isSymm hsymm hM) (θ' t)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at h0
    linarith
  have hacc : M (θ t) *ᵥ θ'' = Υ - C *ᵥ θ' t - gradient V' := by
    rw [← hE]
    abel
  have := (hkin.const_mul (1 / 2 : ℝ)).add hpot
  convert this using 1
  · rfl
  · rw [hsum, hskew, hacc, dotProduct_sub, dotProduct_sub]
    ring

/-- **MLS p. 172: conservation of energy.** With zero generalized force (no actuation and no
friction), the total energy `½ θ̇ᵀ M(θ) θ̇ + V(θ)` has derivative `0` along a solution of
Lagrange's equations. -/
theorem hasDerivAt_energy_of_force_eq_zero {M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hsymm : ∀ q, (M q).IsSymm) (hM : ∀ i j, HasFDerivAt (fun q => M q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (hL : LagrangeEquationsAt (mechanical M V) θ 0 t) :
    HasDerivAt (fun s => energy M V (θ s) (θ' s)) 0 t := by
  simpa using hasDerivAt_energy hsymm hM hV hθ hθ' hL

end Lagrangian

/-! ### The open-chain manipulator (MLS §3.1–3.2, pp. 168–171) -/

namespace InertialChain

variable {n : ℕ} (ch : InertialChain n)

/-- **MLS p. 169: the Lagrangian of an open-chain manipulator**, `L(θ, θ̇) = ½ θ̇ᵀ M(θ) θ̇ − V(θ)`,
with `M` the manipulator inertia matrix of eq. (4.19) and `V` a potential energy (for gravity,
`InertialChain.potentialEnergy`). -/
def lagrangian (V : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
  Lagrangian.mechanical ch.massMatrix V

/-- The chain Lagrangian is kinetic minus potential energy, `T(θ, θ̇) − V(θ)` (MLS p. 169,
eq. (4.18)). -/
theorem lagrangian_apply (V : (Fin n → ℝ) → ℝ) (θ θ' : Fin n → ℝ) :
    ch.lagrangian V θ θ' = ch.kineticEnergy θ θ' - V θ := rfl

/-- **MLS eqs. (4.21) and (4.24), pp. 170–171, for an open chain.** With symmetric link
inertias, Lagrange's equations for `L = ½ θ̇ᵀ M(θ) θ̇ − V(θ)` hold at `t` exactly when
`M(θ) θ̈ + C(θ, θ̇) θ̇ + ∂V/∂θ = Υ`, `M = ∑ₖ Jₖᵀ 𝓜ₖ Jₖ` (eq. (4.19)) and `C` its Christoffel
Coriolis matrix (4.23). The Fréchet derivative data `M'` of the mass-matrix entries at `θ(t)`
and `V'` of `V` are hypotheses here. -/
theorem lagrangeEquationsAt_iff (h : ∀ k, (ch.linkInertia k).IsSymm)
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hM : ∀ i j, HasFDerivAt (fun q => ch.massMatrix q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) (Υ : Fin n → ℝ) :
    Lagrangian.LagrangeEquationsAt (ch.lagrangian V) θ Υ t ↔
      ch.massMatrix (θ t) *ᵥ θ'' +
          Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        Lagrangian.gradient V' = Υ :=
  Lagrangian.lagrangeEquationsAt_mechanical_iff (ch.massMatrix_isSymm h) hM hV hθ hθ' Υ

/-- **MLS p. 172, passivity for an open chain.** Along a solution of Lagrange's equations with
generalized force `Υ`, the total energy `T(θ, θ̇) + V(θ)` has derivative `θ̇ᵀ Υ`; with
symmetric link inertias and the derivative data of `lagrangeEquationsAt_iff`. -/
theorem hasDerivAt_energy (h : ∀ k, (ch.linkInertia k).IsSymm)
    {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)} {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hM : ∀ i j, HasFDerivAt (fun q => ch.massMatrix q i j) (M' i j) (θ t))
    (hV : HasFDerivAt V V' (θ t)) (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s)
    (hθ' : HasDerivAt θ' θ'' t) {Υ : Fin n → ℝ}
    (hL : Lagrangian.LagrangeEquationsAt (ch.lagrangian V) θ Υ t) :
    HasDerivAt (fun s => ch.kineticEnergy (θ s) (θ' s) + V (θ s)) (θ' t ⬝ᵥ Υ) t :=
  Lagrangian.hasDerivAt_energy (ch.massMatrix_isSymm h) hM hV hθ hθ' hL

end InertialChain
end RoboLean
