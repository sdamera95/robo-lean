import RoboLean.Kinematics.ClosedChain
import RoboLean.Kinematics.ForcePullback
import RoboLean.Geometry.Reciprocal
import Mathlib.Data.Matrix.Block

/-!
# Parallel mechanisms with `k` chains: the stacked structure equations and singularities

MLS Chapter 3, §5.2, printed pp. 132–135, and §5.4, pp. 140–142. A parallel mechanism joins the
base to the end-effector by `k` serial chains given in one base frame and one tool frame. This
module generalizes the two-chain `ClosedChain` (which it does not change) to `k` chains:

* `ParallelMechanism k n` holds `k` serial chains, chain `i` with `n i` joints; a configuration
  `Θ = (Θ₁, …, Θₖ)` is a function `(i : Fin k) → Fin (n i) → ℝ` (real-lift joint coordinates);
  the joint space `Q′` (p. 133) requires each `Θᵢ` admissible for its chain and the structure
  equations `g₁(Θ₁) = ⋯ = gₖ(Θₖ)` (eq. (3.65) for `k` chains);
* the differential of the structure equations (eq. (3.69)): along trajectories that keep the
  loops closed, `J₁ˢ Θ̇₁ = ⋯ = Jₖˢ Θ̇ₖ`, all equal to the spatial velocity of the end-effector;
* the stacked form (eq. (3.68), printed for two chains): the block-diagonal matrix of the
  spatial Jacobian matrices times the stacked joint rates equals the stacked identity `[I; ⋯; I]`
  times `Vˢ` exactly when every chain produces `Vˢ`;
* admissible end-effector velocities and the rank `ρ` of the structure equations
  (eqs. (3.69)–(3.70)), with the two-chain case equal to `ClosedChain`'s;
* kinematic singularities, "the rank of the structure equations drops at that point" (p. 134):
  `IsKinematicallySingular` means that every neighbourhood of `Θ` contains a configuration of
  `Q′` with a larger rank `ρ` (a convention: the book compares with nearby configurations without
  fixing the comparison); at such a point `ρ < 6`, so some end-effector twist is not admissible
  ("the tool loses the ability to move instantaneously in some direction");
* actuator singularities (pp. 135, 141): with a choice of actuated joints in each chain, chain `i`
  can transmit to the tool exactly the wrenches whose pairing with every passive joint's twist is
  zero (passive joints carry no torque, MLS eq. (3.60), p. 121); the mechanism is actuator
  singular when these wrenches, summed over the chains, are not all wrenches. If every chain
  transmits only pure forces through one common point (concurrent zero-pitch wrenches, as in
  Example 3.18, p. 142), the mechanism is actuator singular.

These are statements about the coordinate model; nothing here claims that `Q′` is a manifold or
that a physical mechanism moves as modelled.
-/

noncomputable section

open Filter

namespace RoboLean

/-- A parallel (closed-chain) mechanism with `k` serial chains from the base frame `S` to the
tool frame `T`, MLS pp. 132–134: chain `i` has `n i` joints, its own reference twists, reference
tool pose and admissible set; all chains use the same base and tool frames (p. 133). -/
structure ParallelMechanism (k : ℕ) (n : Fin k → ℕ) where
  /-- The `i`-th serial chain from the base to the tool (MLS eq. (3.65), eq. (3.69)). -/
  chain : (i : Fin k) → SerialChain (n i)

namespace ParallelMechanism

variable {k : ℕ} {n : Fin k → ℕ}

/-- **MLS p. 133 and eq. (3.65) for `k` chains: the joint space `Q′`.** The configurations
`Θ = (Θ₁, …, Θₖ)` with each `Θᵢ` admissible for its chain and all chains' forward kinematics
equal (the structure or loop equations). -/
def admissible (P : ParallelMechanism k n) : Set ((i : Fin k) → Fin (n i) → ℝ) :=
  {Θ | (∀ i, Θ i ∈ (P.chain i).admissible) ∧ ∀ i j, (P.chain i).fk (Θ i) = (P.chain j).fk (Θ j)}

/-- Membership in `Q′` (MLS p. 133) unfolds to admissibility of each chain and the structure
equations (3.65). -/
theorem mem_admissible_iff (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) :
    Θ ∈ P.admissible ↔
      (∀ i, Θ i ∈ (P.chain i).admissible) ∧ ∀ i j, (P.chain i).fk (Θ i) = (P.chain j).fk (Θ j) :=
  Iff.rfl

/-- **MLS eq. (3.69), p. 134: the differential of the structure equations.** If the joint
trajectories `Θ(s)` have joint rates `Θ̇` at `t` and keep all structure equations for `s` near
`t`, then `Jᵢˢ(Θᵢ) Θ̇ᵢ = Jⱼˢ(Θⱼ) Θ̇ⱼ` for every two chains, spatial Jacobians in column form
(eq. (3.54)). -/
theorem sum_spatialJacobian_eq (P : ParallelMechanism k n) {Θ : ℝ → (i : Fin k) → Fin (n i) → ℝ}
    {Θ' : (i : Fin k) → Fin (n i) → ℝ} {t : ℝ}
    (hΘ : ∀ i l, HasDerivAt (fun s => Θ s i l) (Θ' i l) t)
    (hloop : ∀ᶠ s in nhds t, ∀ i j, (P.chain i).fk (Θ s i) = (P.chain j).fk (Θ s j))
    (i j : Fin k) :
    ∑ l, Θ' i l • (P.chain i).spatialJacobian (Θ t i) l =
      ∑ l, Θ' j l • (P.chain j).spatialJacobian (Θ t j) l := by
  exact ClosedChain.sum_spatialJacobian_eq ⟨P.chain i, P.chain j⟩ (θ₁ := fun s => Θ s i)
    (θ₂ := fun s => Θ s j) (hΘ i) (hΘ j) (hloop.mono fun _ hs => hs i j)

/-- **MLS eq. (3.69), p. 134: every chain produces the end-effector velocity.** Under the
hypotheses of `sum_spatialJacobian_eq`, for every derivative `D` of the end-effector pose computed
through chain `i₀`, every chain `i` gives the spatial velocity `Vˢ = ġ g⁻¹` of the end-effector:
`Jᵢˢ(Θᵢ) Θ̇ᵢ = Vˢ`. -/
theorem sum_spatialJacobian_eq_spatialVelocity (P : ParallelMechanism k n)
    {Θ : ℝ → (i : Fin k) → Fin (n i) → ℝ} {Θ' : (i : Fin k) → Fin (n i) → ℝ} {t : ℝ}
    (hΘ : ∀ i l, HasDerivAt (fun s => Θ s i l) (Θ' i l) t)
    (hloop : ∀ᶠ s in nhds t, ∀ i j, (P.chain i).fk (Θ s i) = (P.chain j).fk (Θ s j))
    (i₀ : Fin k) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((P.chain i₀).fk (Θ s i₀)).toHomogeneous) D t) (i : Fin k) :
    ∑ l, Θ' i l • (P.chain i).spatialJacobian (Θ t i) l =
      RigidTransform.spatialVelocity (fun s => (P.chain i₀).fk (Θ s i₀)) D t hD := by
  rw [(P.chain i₀).spatialVelocity_fk (θ := fun s => Θ s i₀) (hΘ i₀) hD]
  exact P.sum_spatialJacobian_eq hΘ hloop i i₀

/-- The stacked spatial Jacobian of MLS eq. (3.68), p. 134: the block-diagonal matrix whose
`i`-th block is the `6 × nᵢ` spatial Jacobian matrix of chain `i` (rows `(v, ω)` as in
`SerialChain.spatialJacobianMatrix`), printed for two chains as `[J₁ˢ 0; 0 J₂ˢ]`. -/
def stackedJacobian (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) :
    Matrix ((_ : Fin k) × (Fin 3 ⊕ Fin 3)) ((i : Fin k) × Fin (n i)) ℝ :=
  Matrix.blockDiagonal' fun i => (P.chain i).spatialJacobianMatrix (Θ i)

/-- The stacked identity `[I; ⋯; I]` of MLS eq. (3.68), p. 134: `k` copies of the `6 × 6`
identity on twist coordinates `(v, ω)`. -/
def stackedIdentity (k : ℕ) : Matrix ((_ : Fin k) × (Fin 3 ⊕ Fin 3)) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.of fun r c => if r.2 = c then 1 else 0

/-- The stacked joint rates `Θ̇ = (Θ̇₁, …, Θ̇ₖ)` of MLS eq. (3.68), p. 134, as one vector indexed
by (chain, joint). -/
def stackRates (Θ' : (i : Fin k) → Fin (n i) → ℝ) : ((i : Fin k) × Fin (n i)) → ℝ :=
  fun p => Θ' p.1 p.2

/-- Row `(i, r)` of the stacked product of MLS eq. (3.68) is row `r` of chain `i`'s product
`Jᵢˢ(Θᵢ) Θ̇ᵢ` in twist coordinates `(v, ω)`. -/
private theorem stackedJacobian_mulVec_apply (P : ParallelMechanism k n)
    (Θ Θ' : (i : Fin k) → Fin (n i) → ℝ) (i : Fin k) (r : Fin 3 ⊕ Fin 3) :
    (P.stackedJacobian Θ).mulVec (stackRates Θ') ⟨i, r⟩ =
      (∑ l, Θ' i l • (P.chain i).spatialJacobian (Θ i) l).coordinates r := by
  rw [← SerialChain.spatialJacobianMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, stackedJacobian, stackRates, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j _ hj
    exact Finset.sum_eq_zero fun l _ => by
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Row `(i, r)` of the stacked identity of MLS eq. (3.68) times `x` is `x r`. -/
private theorem stackedIdentity_mulVec_apply (x : Fin 3 ⊕ Fin 3 → ℝ) (i : Fin k)
    (r : Fin 3 ⊕ Fin 3) : (stackedIdentity k).mulVec x ⟨i, r⟩ = x r := by
  simp [stackedIdentity, Matrix.mulVec, dotProduct]

/-- **MLS eq. (3.68), p. 134: the stacked form of the velocity constraints.**
`[J₁ˢ ⋯ 0; ⋮ ⋱ ⋮; 0 ⋯ Jₖˢ] Θ̇ = [I; ⋯; I] Vˢ` holds exactly when every chain produces the twist
`Vˢ`, `Jᵢˢ(Θᵢ) Θ̇ᵢ = Vˢ` (eq. (3.69)); twist coordinates `(v, ω)`. -/
theorem stackedJacobian_mulVec_eq_iff (P : ParallelMechanism k n)
    (Θ Θ' : (i : Fin k) → Fin (n i) → ℝ) (V : Twist) :
    (P.stackedJacobian Θ).mulVec (stackRates Θ') = (stackedIdentity k).mulVec V.coordinates ↔
      ∀ i, ∑ l, Θ' i l • (P.chain i).spatialJacobian (Θ i) l = V := by
  constructor
  · intro h i
    apply Twist.coordinates_injective
    funext r
    have := congrFun h ⟨i, r⟩
    rwa [stackedJacobian_mulVec_apply, stackedIdentity_mulVec_apply] at this
  · intro h
    funext p
    obtain ⟨i, r⟩ := p
    rw [stackedJacobian_mulVec_apply, stackedIdentity_mulVec_apply, h i]

/-- **MLS eqs. (3.67)–(3.68), pp. 133–134, along motions.** Under the hypotheses of
`sum_spatialJacobian_eq_spatialVelocity`, the stacked equation (3.68) holds with `Vˢ` the spatial
velocity of the end-effector. -/
theorem stackedJacobian_mulVec_spatialVelocity (P : ParallelMechanism k n)
    {Θ : ℝ → (i : Fin k) → Fin (n i) → ℝ} {Θ' : (i : Fin k) → Fin (n i) → ℝ} {t : ℝ}
    (hΘ : ∀ i l, HasDerivAt (fun s => Θ s i l) (Θ' i l) t)
    (hloop : ∀ᶠ s in nhds t, ∀ i j, (P.chain i).fk (Θ s i) = (P.chain j).fk (Θ s j))
    (i₀ : Fin k) {D : HomogeneousMatrix}
    (hD : HasDerivAt (fun s => ((P.chain i₀).fk (Θ s i₀)).toHomogeneous) D t) :
    (P.stackedJacobian (Θ t)).mulVec (stackRates Θ') =
      (stackedIdentity k).mulVec
        (RigidTransform.spatialVelocity (fun s => (P.chain i₀).fk (Θ s i₀)) D t
          hD).coordinates := by
  exact (P.stackedJacobian_mulVec_eq_iff (Θ t) Θ' _).2
    (P.sum_spatialJacobian_eq_spatialVelocity hΘ hloop i₀ hD)

/-- **MLS p. 134, eqs. (3.69)–(3.70): admissible end-effector velocities.** The twists produced
by every chain, the intersection of the ranges (column spans) of the `k` spatial Jacobians. -/
def admissibleVelocities (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) :
    Submodule ℝ Twist :=
  ⨅ i, Submodule.span ℝ (Set.range ((P.chain i).spatialJacobian (Θ i)))

/-- A twist is an admissible end-effector velocity (MLS p. 134) exactly when joint rates of every
chain produce it (eq. (3.69)). -/
theorem mem_admissibleVelocities_iff (P : ParallelMechanism k n)
    (Θ : (i : Fin k) → Fin (n i) → ℝ) (V : Twist) :
    V ∈ P.admissibleVelocities Θ ↔
      ∀ i, ∃ Θ'ᵢ : Fin (n i) → ℝ, ∑ l, Θ'ᵢ l • (P.chain i).spatialJacobian (Θ i) l = V := by
  simp only [admissibleVelocities, Submodule.mem_iInf, Submodule.mem_span_range_iff_exists_fun]

/-- **MLS eq. (3.70), p. 134: the rank `ρ` of the structure equations**, the dimension of the
space of admissible end-effector velocities. -/
def structureRank (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) : ℕ :=
  Module.finrank ℝ (P.admissibleVelocities Θ)

/-- The rank `ρ` of eq. (3.70), MLS p. 134, is at most six, the dimension of the twists. -/
theorem structureRank_le_six (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) :
    P.structureRank Θ ≤ 6 := by
  exact Twist.finrank_eq_six ▸ Submodule.finrank_le _

/-- Every end-effector twist is admissible (MLS p. 141, "all tool velocities are admissible")
exactly when the rank `ρ` of eq. (3.70) is six. -/
theorem admissibleVelocities_eq_top_iff (P : ParallelMechanism k n)
    (Θ : (i : Fin k) → Fin (n i) → ℝ) :
    P.admissibleVelocities Θ = ⊤ ↔ P.structureRank Θ = 6 := by
  constructor
  · intro h
    rw [structureRank, h, finrank_top, Twist.finrank_eq_six]
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans Twist.finrank_eq_six.symm)

/-- **MLS p. 134: kinematic singularity of a parallel mechanism, "the rank of the structure
equations drops at that point".** Convention: every neighbourhood of `Θ` contains a configuration
of the joint space `Q′` at which the rank `ρ` of eq. (3.70) is larger than at `Θ`. -/
def IsKinematicallySingular (P : ParallelMechanism k n) (Θ : (i : Fin k) → Fin (n i) → ℝ) :
    Prop :=
  ∀ U ∈ nhds Θ, ∃ Θ₁ ∈ U, Θ₁ ∈ P.admissible ∧ P.structureRank Θ < P.structureRank Θ₁

/-- **MLS p. 134: "In this case, the tool loses the ability to move instantaneously in some
direction."** At a kinematic singularity `ρ < 6`, so some end-effector twist is not admissible. -/
theorem exists_not_mem_admissibleVelocities_of_isKinematicallySingular
    (P : ParallelMechanism k n) {Θ : (i : Fin k) → Fin (n i) → ℝ}
    (h : P.IsKinematicallySingular Θ) : ∃ V : Twist, V ∉ P.admissibleVelocities Θ := by
  obtain ⟨Θ₁, -, -, hlt⟩ := h Set.univ Filter.univ_mem
  have hne : P.admissibleVelocities Θ ≠ ⊤ := fun htop => by
    have h6 := (P.admissibleVelocities_eq_top_iff Θ).1 htop
    have := P.structureRank_le_six Θ₁
    omega
  by_contra hall
  exact hne (Submodule.eq_top_iff'.2 fun V => by_contra fun hV => hall ⟨V, hV⟩)

/-- At a configuration where every end-effector twist is admissible (`ρ = 6`), a parallel
mechanism is not kinematically singular (MLS p. 141: the Stewart platform's Jacobians are never
singular, "hence all tool velocities are admissible"). -/
theorem not_isKinematicallySingular_of_structureRank_eq_six (P : ParallelMechanism k n)
    {Θ : (i : Fin k) → Fin (n i) → ℝ} (h : P.structureRank Θ = 6) :
    ¬ P.IsKinematicallySingular Θ := by
  intro hs
  obtain ⟨Θ₁, -, -, hlt⟩ := hs Set.univ Filter.univ_mem
  have := P.structureRank_le_six Θ₁
  omega

/-- **The wrenches chain `i` can transmit with its passive joints free (MLS pp. 135, 141).**
With `actuated i` the set of actuated joints of chain `i`, the wrenches `F` (in base coordinates,
moment about the base origin, as in eq. (3.60), p. 121) whose pairing with every passive joint's
current twist `Jᵢˢ(Θᵢ)ₗ`, `l ∉ actuated i`, is zero: the joint torques `τ = Jᵀ F` of a static
chain vanish at its passive joints. -/
def transmissibleWrenches (P : ParallelMechanism k n) (actuated : (i : Fin k) → Set (Fin (n i)))
    (Θ : (i : Fin k) → Fin (n i) → ℝ) (i : Fin k) : Submodule ℝ Wrench where
  carrier := {F | ∀ l, l ∉ actuated i → Wrench.pair F ((P.chain i).spatialJacobian (Θ i) l) = 0}
  add_mem' := by
    intro F G hF hG l hl
    rw [Wrench.pair_add_left, hF l hl, hG l hl, add_zero]
  zero_mem' := by
    intro l _
    exact Wrench.pair_zero_left _
  smul_mem' := by
    intro c F hF l hl
    rw [Wrench.pair_smul_left, hF l hl, mul_zero]

/-- **The wrenches the actuated joints can generate on the tool (MLS p. 141):** the sums
`F₁ + ⋯ + Fₖ` of wrenches transmissible by the chains. -/
def actuatorWrenches (P : ParallelMechanism k n) (actuated : (i : Fin k) → Set (Fin (n i)))
    (Θ : (i : Fin k) → Fin (n i) → ℝ) : Submodule ℝ Wrench :=
  ⨆ i, P.transmissibleWrenches actuated Θ i

/-- **MLS p. 141: actuator singularity**, "a failure of the actuated joints to be able to
generate arbitrary wrenches in the tool frame": some wrench is not a sum of transmissible
wrenches of the chains. -/
def IsActuatorSingular (P : ParallelMechanism k n) (actuated : (i : Fin k) → Set (Fin (n i)))
    (Θ : (i : Fin k) → Fin (n i) → ℝ) : Prop :=
  P.actuatorWrenches actuated Θ ≠ ⊤

/-- The pure forces through a point `q`: wrenches `(f, q × f)` (MLS p. 64, zero-pitch wrenches
with axis through `q`, moment about the base origin). -/
def forcesThrough (q : Vec3) : Submodule ℝ Wrench where
  carrier := {F | F.torque = Vec3.cross q F.force}
  add_mem' := by
    intro F G hF hG
    change F.torque = Vec3.cross q F.force at hF
    change G.torque = Vec3.cross q G.force at hG
    change (F + G).torque = Vec3.cross q (F + G).force
    rw [Wrench.add_torque, Wrench.add_force, Vec3.cross_add, hF, hG]
  zero_mem' := by
    change (0 : Wrench).torque = Vec3.cross q (0 : Wrench).force
    rw [Wrench.zero_torque, Wrench.zero_force, Vec3.cross_zero]
  smul_mem' := by
    intro c F hF
    change F.torque = Vec3.cross q F.force at hF
    change (c • F).torque = Vec3.cross q (c • F).force
    rw [Wrench.smul_torque, Wrench.smul_force, Vec3.cross_smul, hF]

/-- **MLS p. 142, Example 3.18: concurrent zero-pitch wrenches give an actuator singularity.** If
every chain can transmit only pure forces through one common point `q`, the actuated joints
cannot generate a pure torque about `q`, so the mechanism is actuator singular. -/
theorem isActuatorSingular_of_le_forcesThrough (P : ParallelMechanism k n)
    (actuated : (i : Fin k) → Set (Fin (n i))) (Θ : (i : Fin k) → Fin (n i) → ℝ) (q : Vec3)
    (h : ∀ i, P.transmissibleWrenches actuated Θ i ≤ forcesThrough q) :
    P.IsActuatorSingular actuated Θ := by
  intro htop
  have hle : P.actuatorWrenches actuated Θ ≤ forcesThrough q := iSup_le h
  obtain ⟨e, he⟩ := exists_ne (0 : Vec3)
  have hmem : (⟨0, e⟩ : Wrench) ∈ forcesThrough q := hle (htop ▸ Submodule.mem_top)
  change e = Vec3.cross q 0 at hmem
  exact he (hmem.trans (Vec3.cross_zero q))

/-- A pure torque about `q` is not a pure force through `q` (MLS p. 142, Example 3.18: "it is not
possible for the mechanism to generate pure torques around the point of common intersection"). -/
theorem pureTorque_not_mem_forcesThrough (q τ : Vec3) (hτ : τ ≠ 0) :
    (⟨0, τ⟩ : Wrench) ∉ forcesThrough q := by
  intro h
  change τ = Vec3.cross q 0 at h
  exact hτ (h.trans (Vec3.cross_zero q))

/-! ### The two-chain case -/

/-- The `k = 2` parallel mechanism of a two-chain `ClosedChain` (MLS eq. (3.65), p. 132): chain
`0` is `chain₁` and chain `1` is `chain₂`. -/
def ofClosedChain {n₁ n₂ : ℕ} (c : ClosedChain n₁ n₂) : ParallelMechanism 2 ![n₁, n₂] where
  chain := Fin.cases c.chain₁ (Fin.cases c.chain₂ fun j => j.elim0)

/-- The configurations of a two-chain mechanism as pairs `(θ₁, θ₂)` (MLS p. 133). -/
def pairEquiv (n₁ n₂ : ℕ) :
    ((i : Fin 2) → Fin (![n₁, n₂] i) → ℝ) ≃ (Fin n₁ → ℝ) × (Fin n₂ → ℝ) where
  toFun Θ := (Θ 0, Θ 1)
  invFun θ := Fin.cases θ.1 (Fin.cases θ.2 fun j => j.elim0)
  left_inv := by
    intro Θ
    funext i
    fin_cases i <;> rfl
  right_inv := by
    intro θ
    rfl

/-- **Bridge to `ClosedChain` (MLS p. 133).** The joint space `Q′` of the two-chain parallel
mechanism is the closed chain's joint space under `pairEquiv`. -/
theorem mem_admissible_ofClosedChain_iff {n₁ n₂ : ℕ} (c : ClosedChain n₁ n₂)
    (Θ : (i : Fin 2) → Fin (![n₁, n₂] i) → ℝ) :
    Θ ∈ (ofClosedChain c).admissible ↔ pairEquiv n₁ n₂ Θ ∈ c.admissible := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁ 0, h₁ 1, h₂ 0 1⟩
  · rintro ⟨h₀, h₁, h₀₁⟩
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · fin_cases i
      exacts [h₀, h₁]
    · fin_cases i <;> fin_cases j
      exacts [rfl, h₀₁, h₀₁.symm, rfl]

/-- **Bridge to `ClosedChain` (MLS p. 134).** The admissible velocities of the two-chain parallel
mechanism are the closed chain's. -/
theorem admissibleVelocities_ofClosedChain {n₁ n₂ : ℕ} (c : ClosedChain n₁ n₂)
    (Θ : (i : Fin 2) → Fin (![n₁, n₂] i) → ℝ) :
    (ofClosedChain c).admissibleVelocities Θ = c.admissibleVelocities (pairEquiv n₁ n₂ Θ) := by
  ext V
  rw [mem_admissibleVelocities_iff, ClosedChain.mem_admissibleVelocities_iff, Fin.forall_fin_two]
  rfl

/-- **Bridge to `ClosedChain` (MLS eq. (3.70), p. 134).** The rank `ρ` of the two-chain parallel
mechanism is the closed chain's `structureRank`. -/
theorem structureRank_ofClosedChain {n₁ n₂ : ℕ} (c : ClosedChain n₁ n₂)
    (Θ : (i : Fin 2) → Fin (![n₁, n₂] i) → ℝ) :
    (ofClosedChain c).structureRank Θ = c.structureRank (pairEquiv n₁ n₂ Θ) := by
  rw [structureRank, ClosedChain.structureRank, admissibleVelocities_ofClosedChain]

end ParallelMechanism
end RoboLean
