import RoboLean.Dynamics.Lagrangian

/-!
# Potential energy and the gravity term of an open chain

MLS Chapter 4, printed p. 169 and pp. 174–175, eq. (4.25). "Let `hᵢ(θ)` be the height of the
center of mass of the `i`th link (height is the component of the position of the center of mass
opposite the direction of gravity). The potential energy for the `i`th link is
`Vᵢ(θ) = mᵢ g hᵢ(θ)`" and `V(θ) = ∑ᵢ mᵢ g hᵢ(θ)`; the gravity term is `N(θ) = ∂V/∂θ` (p. 174).

Conventions (recorded for the conventions document):

* gravity is uniform, given by a scalar `g` (MLS "the gravitational constant") and a vector
  `up` in base coordinates pointing opposite to gravity; the height of a point `p` is the
  inner product `⟪up, p⟫`. `up` is meant to be a unit vector; no theorem here needs that, and
  the gravitational acceleration vector is `-g • up`;
* the mass center of link `k` is the origin of its link frame `L_k`, as in MLS p. 168 (the
  convention under which the generalized inertia is block diagonal, eq. (4.9)), so
  `h_k(θ) = ⟪up, p_k(θ)⟫` with `p_k(θ)` the translation of `g_{sl_k}(θ)`
  (`InertialChain.linkPose`);
* the link masses `m k` are an explicit argument; for the book's model they are the masses in
  the generalized inertias `𝓜_k = [[m_k I, 0], [0, 𝓘_k]]`, which the types do not enforce.

`gravityTerm` is defined as the gradient of `V` read from its Fréchet derivative
(`Lagrangian.gradient (fderiv ℝ V θ)`), the style of the derivative data in
`RoboLean.Dynamics.Christoffel`. For every chain and every differentiable joint trajectory,
`hasDerivAt_potentialEnergy` computes the actual rate of change of `V(θ(t))` as `θ̇ ⬝ G(θ)`
with the explicit Jacobian form `G = gravityJacobian` (the joint torques of the link weights
through the spatial Jacobians of the link frames, MLS p. 117 for the point velocity); and
`gravityTerm_eq_gravityJacobian` identifies `N` with `G` wherever `V` is differentiable.
Differentiability of `V` for a general chain is a hypothesis here.

Friction and other non-conservative joint forces, also collected in `N` on p. 170, enter through
`Lagrangian.lagrangeEquationsAt_mechanical_iff_torque`.
-/

noncomputable section

open Matrix Filter Topology

namespace RoboLean
namespace InertialChain

variable {n : ℕ} (ch : InertialChain n)

/-- **MLS p. 169: the height `h_k(θ)` of the mass center of link `k`**, the component of its
position along `up` (the direction opposite gravity), `h_k(θ) = ⟪up, p_k(θ)⟫`, where `p_k(θ)` is
the origin of the link frame `g_{sl_k}(θ)` (MLS p. 168: the link frame is at the mass center). -/
def linkHeight (up : Vec3) (k : Fin n) (θ : Fin n → ℝ) : ℝ :=
  inner ℝ up (ch.linkPose k θ).translation

/-- **MLS p. 169: the potential energy of an open chain in uniform gravity**,
`V(θ) = ∑ₖ m_k g h_k(θ)`, with link masses `m`, gravitational constant `g` and upward vector
`up` (heights `⟪up, p_k(θ)⟫`). -/
def potentialEnergy (m : Fin n → ℝ) (g : ℝ) (up : Vec3) (θ : Fin n → ℝ) : ℝ :=
  ∑ k, m k * g * ch.linkHeight up k θ

/-- **MLS p. 174, eq. (4.25): the gravity term `N(θ) = ∂V/∂θ`**, the gradient of the potential
energy `V = potentialEnergy m g up` read from its Fréchet derivative at `θ`. Where `V` is not
differentiable this is `0` (the convention of `fderiv`); every theorem about it assumes or proves
differentiability. -/
def gravityTerm (m : Fin n → ℝ) (g : ℝ) (up : Vec3) (θ : Fin n → ℝ) : Fin n → ℝ :=
  Lagrangian.gradient (fderiv ℝ (ch.potentialEnergy m g up) θ)

/-- **The gravity term from derivative data (MLS p. 174).** If `V = potentialEnergy m g up` has
Fréchet derivative `V'` at `θ`, then `N(θ) = ∂V/∂θ` is the gradient read from `V'`. -/
theorem gravityTerm_eq_gradient {m : Fin n → ℝ} {g : ℝ} {up : Vec3} {θ : Fin n → ℝ}
    {V' : (Fin n → ℝ) →L[ℝ] ℝ} (h : HasFDerivAt (ch.potentialEnergy m g up) V' θ) :
    ch.gravityTerm m g up θ = Lagrangian.gradient V' := by
  rw [gravityTerm, h.fderiv]

/-- **The Jacobian form of the gravity term (MLS p. 174 with p. 117).** Component `i` is
`∑ₖ m_k g ⟪up, ωᵢₖ × p_k(θ) + vᵢₖ⟫`, where `(vᵢₖ, ωᵢₖ)` is column `i` of the spatial Jacobian of
the frame of link `k` (the chain `linkChain k`) and `ωᵢₖ × p_k + vᵢₖ` is the velocity of the mass
center of link `k` per unit rate of joint `i`. -/
def gravityJacobian (m : Fin n → ℝ) (g : ℝ) (up : Vec3) (θ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ k, m k * g * inner ℝ up
    (Vec3.cross ((ch.linkChain k).spatialJacobian θ i).angular (ch.linkPose k θ).translation +
      ((ch.linkChain k).spatialJacobian θ i).linear)

/-- **Rate of change of a link height along a motion (MLS p. 169, with p. 117).** For every
differentiable joint trajectory, `d/dt h_k(θ(t)) = ⟪up, ω × p_k + v⟫` with `(v, ω) = J θ̇` the
spatial velocity of the frame of link `k` (E009 `SerialChain.hasDerivAt_fk_translation`). -/
theorem hasDerivAt_linkHeight (up : Vec3) (k : Fin n) {θ : ℝ → Fin n → ℝ} {θ' : Fin n → ℝ}
    {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) :
    HasDerivAt (fun s => ch.linkHeight up k (θ s))
      (∑ i, θ' i * inner ℝ up
        (Vec3.cross ((ch.linkChain k).spatialJacobian (θ t) i).angular
            (ch.linkPose k (θ t)).translation +
          ((ch.linkChain k).spatialJacobian (θ t) i).linear)) t := by
  have h := (ch.linkChain k).hasDerivAt_fk_translation hθ
  have hi := (innerSL ℝ up).hasFDerivAt.comp_hasDerivAt t h
  refine hi.congr_deriv ?_
  rw [innerSL_apply_apply, Twist.sum_angular, Twist.sum_linear, Vec3.sum_cross,
    ← Finset.sum_add_distrib, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Twist.smul_angular, Twist.smul_linear, Vec3.smul_cross, ← smul_add, inner_smul_right]
  rfl

/-- **MLS p. 169: the rate of change of the potential energy along a motion.** For every open
chain and every differentiable joint trajectory, `d/dt V(θ(t)) = θ̇ ⬝ G(θ(t))` with
`G = gravityJacobian`. No differentiability hypothesis on `V` is needed. -/
theorem hasDerivAt_potentialEnergy (m : Fin n → ℝ) (g : ℝ) (up : Vec3) {θ : ℝ → Fin n → ℝ}
    {θ' : Fin n → ℝ} {t : ℝ} (hθ : ∀ i, HasDerivAt (fun s => θ s i) (θ' i) t) :
    HasDerivAt (fun s => ch.potentialEnergy m g up (θ s))
      (θ' ⬝ᵥ ch.gravityJacobian m g up (θ t)) t := by
  have h : HasDerivAt (fun s => ∑ k, m k * g * ch.linkHeight up k (θ s))
      (∑ k, m k * g * ∑ i, θ' i * inner ℝ up
        (Vec3.cross ((ch.linkChain k).spatialJacobian (θ t) i).angular
            (ch.linkPose k (θ t)).translation +
          ((ch.linkChain k).spatialJacobian (θ t) i).linear)) t :=
    HasDerivAt.fun_sum fun k _ => (ch.hasDerivAt_linkHeight up k hθ).const_mul (m k * g)
  refine h.congr_deriv ?_
  simp only [dotProduct, gravityJacobian, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **MLS p. 174: the gravity term is the Jacobian form wherever `V` is differentiable.**
If the potential energy is differentiable at `θ`, then `N(θ) = ∂V/∂θ = gravityJacobian`, by
differentiating along the coordinate lines through `θ`. -/
theorem gravityTerm_eq_gravityJacobian {m : Fin n → ℝ} {g : ℝ} {up : Vec3} {θ : Fin n → ℝ}
    (h : DifferentiableAt ℝ (ch.potentialEnergy m g up) θ) :
    ch.gravityTerm m g up θ = ch.gravityJacobian m g up θ := by
  funext i
  have hl : ∀ j, HasDerivAt (fun s : ℝ => (θ + s • (Pi.single i 1 : Fin n → ℝ)) j)
      ((Pi.single i 1 : Fin n → ℝ) j) 0 := by
    intro j
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single i 1 : Fin n → ℝ) j)).const_add
      (θ j)
  have h1 := ch.hasDerivAt_potentialEnergy m g up hl
  have hline : HasDerivAt (fun s : ℝ => θ + s • (Pi.single i 1 : Fin n → ℝ))
      (Pi.single i 1) 0 := hasDerivAt_pi.mpr hl
  have h2 := h.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have e := h2.unique h1
  rw [zero_smul, add_zero] at e
  rw [gravityTerm, Lagrangian.gradient, e, single_one_dotProduct]

/-- **MLS eqs. (4.24)–(4.25), pp. 171–175: the equations of motion of an open chain in uniform
gravity.** With symmetric link inertias, Fréchet derivative data `M'` of the mass-matrix entries
at `θ(t)` and a potential energy `V = potentialEnergy m g up` differentiable at `θ(t)`,
Lagrange's equations for `L = ½ θ̇ᵀ M(θ) θ̇ − V(θ)` with generalized force `Υ` hold at `t` exactly
when `M(θ) θ̈ + C(θ, θ̇) θ̇ + N(θ) = Υ`, with `N = gravityTerm`. The differentiability of `M` and
`V` for a general chain are hypotheses here. -/
theorem lagrangeEquationsAt_gravity_iff (h : ∀ k, (ch.linkInertia k).IsSymm)
    {m : Fin n → ℝ} {g : ℝ} {up : Vec3} {M' : Fin n → Fin n → ((Fin n → ℝ) →L[ℝ] ℝ)}
    {θ θ' : ℝ → Fin n → ℝ} {θ'' : Fin n → ℝ} {t : ℝ}
    (hM : ∀ i j, HasFDerivAt (fun q => ch.massMatrix q i j) (M' i j) (θ t))
    (hV : DifferentiableAt ℝ (ch.potentialEnergy m g up) (θ t))
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (θ' s) s) (hθ' : HasDerivAt θ' θ'' t) (Υ : Fin n → ℝ) :
    Lagrangian.LagrangeEquationsAt (ch.lagrangian (ch.potentialEnergy m g up)) θ Υ t ↔
      ch.massMatrix (θ t) *ᵥ θ'' +
          Christoffel.coriolisMatrix (Christoffel.partials M') (θ' t) *ᵥ θ' t +
        ch.gravityTerm m g up (θ t) = Υ := by
  rw [ch.lagrangeEquationsAt_iff h hM hV.hasFDerivAt hθ hθ' Υ, gravityTerm]

end InertialChain
end RoboLean
