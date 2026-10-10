import RoboLean.Kinematics.Jacobian

/-!
# Closed chains: the structure equation and its differential

MLS Chapter 3, §5.2, printed pp. 132–134. A parallel (closed-chain) manipulator joins the
base to the end-effector by two or more serial chains. This file treats two chains, given in
one base frame and one tool frame (p. 133: "all quantities are specified relative to a single
base and tool frame").

* `ClosedChain.admissible` is the joint space `Q′ ⊂ Q` of p. 133: pairs of joint vectors, each
  admissible for its own chain, that satisfy the structure (loop) equation (3.65)
  `g₁(θ₁) = g₂(θ₂)`.
* `ClosedChain.sum_spatialJacobian_eq` is the differential of the structure equation,
  eq. (3.67): along joint trajectories that keep the loop closed near time `t`,
  `J₁ˢ(θ₁) θ̇₁ = J₂ˢ(θ₂) θ̇₂`, and both equal the spatial velocity of the end-effector.
* `ClosedChain.admissibleVelocities` is the space of admissible end-effector velocities of
  p. 134, the intersection of the ranges of the two Jacobians, and
  `ClosedChain.structureRank` is its dimension, the rank `ρ` of the structure equations,
  eq. (3.70).

Not formalized: Gruebler's formula (3.66), the stacked form (3.68), the meaning of "the rank
drops" in the book's definition of a kinematic singularity of a parallel mechanism (p. 134; it
compares `ρ` with its value at nearby configurations), actuator singularities, and any
statement that `Q′` is a manifold of a given dimension, which would need an implicit-function
argument and a rank hypothesis. The two chains may have different reference tool poses; the
book writes one `g_st(0)` for both, which here is the condition that the reference
configuration lies in `Q′` (`zero_mem_admissible_iff`). Joint coordinates are the real lift of
ledger K01. These are statements about the coordinate model only.
-/

noncomputable section

open Filter
open scoped Matrix.Norms.Operator

namespace RoboLean

/-- A closed-chain (parallel) mechanism with two serial chains from the base frame `S` to the
tool frame `T`, MLS p. 132: `chain₁` has `n₁` joints and `chain₂` has `n₂`, each with its own
reference twists, reference tool pose and admissible set (ledger K01–K02). Both chains use
the same base and tool frames (p. 133). -/
structure ClosedChain (n₁ n₂ : ℕ) where
  /-- The first serial chain from the base to the tool (MLS eq. (3.65), left side). -/
  chain₁ : SerialChain n₁
  /-- The second serial chain from the base to the tool (MLS eq. (3.65), right side). -/
  chain₂ : SerialChain n₂

namespace ClosedChain

variable {n₁ n₂ : ℕ}

/-- **MLS eq. (3.65) and p. 133: the joint space `Q′` of a parallel mechanism.** The pairs
`(θ₁, θ₂)` with each `θᵢ` admissible for its chain whose forward kinematics agree,
`g₁(θ₁) = g₂(θ₂)` (the structure or loop equation). Product-of-exponentials forward
kinematics, eq. (3.3); joint coordinates are the real lift. -/
def admissible (c : ClosedChain n₁ n₂) : Set ((Fin n₁ → ℝ) × (Fin n₂ → ℝ)) :=
  {θ | θ.1 ∈ c.chain₁.admissible ∧ θ.2 ∈ c.chain₂.admissible ∧
    c.chain₁.fk θ.1 = c.chain₂.fk θ.2}

/-- Membership in the joint space `Q′` of MLS p. 133 unfolds to the two admissibility
conditions and the structure equation (3.65). -/
theorem mem_admissible_iff (c : ClosedChain n₁ n₂) (θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) :
    θ ∈ c.admissible ↔ θ.1 ∈ c.chain₁.admissible ∧ θ.2 ∈ c.chain₂.admissible ∧
      c.chain₁.fk θ.1 = c.chain₂.fk θ.2 := Iff.rfl

/-- The end-effector pose of the parallel mechanism, computed through the first chain,
`g_st = e^{ξ̂₁₁θ₁₁} ⋯ g_st(0)` (MLS eq. (3.65), left side). -/
def fk (c : ClosedChain n₁ n₂) (θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) : RigidTransform :=
  c.chain₁.fk θ.1

/-- On the joint space `Q′`, the end-effector pose computed through the second chain is the
same (MLS eq. (3.65)). -/
theorem fk_eq_chain₂ (c : ClosedChain n₁ n₂) {θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)}
    (h : θ ∈ c.admissible) : c.fk θ = c.chain₂.fk θ.2 :=
  h.2.2

/-- The reference configuration `θ = 0` lies in `Q′` exactly when both chains admit it and
their reference tool poses agree, the single `g_st(0)` written on both sides of MLS
eq. (3.65). -/
theorem zero_mem_admissible_iff (c : ClosedChain n₁ n₂)
    (h₁ : (0 : Fin n₁ → ℝ) ∈ c.chain₁.admissible) (h₂ : (0 : Fin n₂ → ℝ) ∈ c.chain₂.admissible) :
    ((0, 0) : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) ∈ c.admissible ↔
      c.chain₁.toolRef = c.chain₂.toolRef := by
  simp [admissible, h₁, h₂]

/-- **MLS eq. (3.67), p. 133: the end-effector velocity through either chain.** If the joint
trajectories `θ₁(s)`, `θ₂(s)` keep the structure equation (3.65) for all `s` near `t`, then
for every derivative `D` of the end-effector pose through the first chain, the pose through
the second chain has the same derivative and the two spatial velocities `ġ g⁻¹` agree. -/
theorem spatialVelocity_chain₂_eq (c : ClosedChain n₁ n₂) {θ₁ : ℝ → Fin n₁ → ℝ}
    {θ₂ : ℝ → Fin n₂ → ℝ} {t : ℝ}
    (hloop : ∀ᶠ s in nhds t, c.chain₁.fk (θ₁ s) = c.chain₂.fk (θ₂ s)) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => (c.chain₁.fk (θ₁ s)).toHomogeneous) D t) :
    ∃ hD₂ : HasDerivAt (fun s => (c.chain₂.fk (θ₂ s)).toHomogeneous) D t,
      RigidTransform.spatialVelocity (fun s => c.chain₂.fk (θ₂ s)) D t hD₂ =
        RigidTransform.spatialVelocity (fun s => c.chain₁.fk (θ₁ s)) D t hD := by
  have hD₂ : HasDerivAt (fun s => (c.chain₂.fk (θ₂ s)).toHomogeneous) D t :=
    hD.congr_of_eventuallyEq (hloop.mono fun s hs => by beta_reduce; rw [hs])
  refine ⟨hD₂, Twist.hat_injective ?_⟩
  rw [RigidTransform.hat_spatialVelocity, RigidTransform.hat_spatialVelocity,
    hloop.self_of_nhds]

/-- **MLS eq. (3.67), p. 133: the differential of the structure equation.** If the joint
trajectories `θ₁(s)`, `θ₂(s)` have joint rates `θ̇₁`, `θ̇₂` at `t` and keep the loop equation
(3.65) for all `s` near `t`, then `J₁ˢ(θ₁) θ̇₁ = J₂ˢ(θ₂) θ̇₂`, with the spatial Jacobians of
eq. (3.54) in column form. "Not all joint velocities can be specified independently" (p. 134)
is this linear constraint on `(θ̇₁, θ̇₂)`. -/
theorem sum_spatialJacobian_eq (c : ClosedChain n₁ n₂) {θ₁ : ℝ → Fin n₁ → ℝ}
    {θ₂ : ℝ → Fin n₂ → ℝ} {θ₁' : Fin n₁ → ℝ} {θ₂' : Fin n₂ → ℝ} {t : ℝ}
    (h₁ : ∀ i, HasDerivAt (fun s => θ₁ s i) (θ₁' i) t)
    (h₂ : ∀ j, HasDerivAt (fun s => θ₂ s j) (θ₂' j) t)
    (hloop : ∀ᶠ s in nhds t, c.chain₁.fk (θ₁ s) = c.chain₂.fk (θ₂ s)) :
    ∑ i, θ₁' i • c.chain₁.spatialJacobian (θ₁ t) i =
      ∑ j, θ₂' j • c.chain₂.spatialJacobian (θ₂ t) j := by
  have hD := c.chain₁.hasDerivAt_fk_toHomogeneous h₁
  obtain ⟨hD₂, hV⟩ := c.spatialVelocity_chain₂_eq hloop hD
  rw [← c.chain₁.spatialVelocity_fk h₁ hD, ← hV, c.chain₂.spatialVelocity_fk h₂ hD₂]

/-- **MLS p. 134, eqs. (3.69)–(3.70): admissible end-effector velocities.** At a
configuration `θ = (θ₁, θ₂)`, the twists `V` reachable through both chains, `V = J₁ˢ(θ₁) θ̇₁`
and `V = J₂ˢ(θ₂) θ̇₂` for some joint rates: the intersection of the ranges of the two spatial
Jacobians (the span of their columns), a linear subspace of twists. -/
def admissibleVelocities (c : ClosedChain n₁ n₂) (θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) :
    Submodule ℝ Twist :=
  Submodule.span ℝ (Set.range (c.chain₁.spatialJacobian θ.1)) ⊓
    Submodule.span ℝ (Set.range (c.chain₂.spatialJacobian θ.2))

/-- A twist is an admissible end-effector velocity in the sense of MLS p. 134 exactly when
joint rates of each chain produce it, `V = J₁ˢ θ̇₁ = J₂ˢ θ̇₂` (eq. (3.69)). -/
theorem mem_admissibleVelocities_iff (c : ClosedChain n₁ n₂)
    (θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) (V : Twist) :
    V ∈ c.admissibleVelocities θ ↔
      (∃ θ₁' : Fin n₁ → ℝ, ∑ i, θ₁' i • c.chain₁.spatialJacobian θ.1 i = V) ∧
        ∃ θ₂' : Fin n₂ → ℝ, ∑ j, θ₂' j • c.chain₂.spatialJacobian θ.2 j = V := by
  rw [admissibleVelocities, Submodule.mem_inf, Submodule.mem_span_range_iff_exists_fun,
    Submodule.mem_span_range_iff_exists_fun]

/-- **MLS eq. (3.70), p. 134: the rank `ρ` of the structure equations** at a configuration, the
dimension of the space of admissible end-effector velocities. -/
def structureRank (c : ClosedChain n₁ n₂) (θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) : ℕ :=
  Module.finrank ℝ (c.admissibleVelocities θ)

/-- The rank `ρ` of eq. (3.70), MLS p. 134, is at most the dimension of the span of either
chain's Jacobian columns. -/
theorem structureRank_le (c : ClosedChain n₁ n₂) (θ : (Fin n₁ → ℝ) × (Fin n₂ → ℝ)) :
    c.structureRank θ ≤
        Module.finrank ℝ (Submodule.span ℝ (Set.range (c.chain₁.spatialJacobian θ.1))) ∧
      c.structureRank θ ≤
        Module.finrank ℝ (Submodule.span ℝ (Set.range (c.chain₂.spatialJacobian θ.2))) :=
  ⟨Submodule.finrank_mono inf_le_left, Submodule.finrank_mono inf_le_right⟩

/-- **MLS eqs. (3.67) and (3.69), pp. 133–134.** Along joint trajectories that keep the loop
closed near `t`, the end-effector spatial velocity `J₁ˢ(θ₁) θ̇₁` is an admissible velocity at
the configuration `(θ₁(t), θ₂(t))`. -/
theorem sum_spatialJacobian_mem_admissibleVelocities (c : ClosedChain n₁ n₂)
    {θ₁ : ℝ → Fin n₁ → ℝ} {θ₂ : ℝ → Fin n₂ → ℝ} {θ₁' : Fin n₁ → ℝ} {θ₂' : Fin n₂ → ℝ}
    {t : ℝ} (h₁ : ∀ i, HasDerivAt (fun s => θ₁ s i) (θ₁' i) t)
    (h₂ : ∀ j, HasDerivAt (fun s => θ₂ s j) (θ₂' j) t)
    (hloop : ∀ᶠ s in nhds t, c.chain₁.fk (θ₁ s) = c.chain₂.fk (θ₂ s)) :
    ∑ i, θ₁' i • c.chain₁.spatialJacobian (θ₁ t) i ∈ c.admissibleVelocities (θ₁ t, θ₂ t) := by
  rw [mem_admissibleVelocities_iff]
  exact ⟨⟨θ₁', rfl⟩, ⟨θ₂', (c.sum_spatialJacobian_eq h₁ h₂ hloop).symm⟩⟩

end ClosedChain

end RoboLean
