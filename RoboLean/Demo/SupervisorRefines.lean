import RoboLean.Demo.Supervisor
import RoboLean.Demo.PlanarArmFrames
import RoboLean.Design.PlanarArmTimeoutSupervisor

/-!
# The executable supervisor refines the design supervisor

`RoboLean.Demo.Supervisor` defines an executable timeout supervisor over rational targets. This
file relates it to the design relation `RoboLean.Design.PlanarArmTimeoutSupervisor.Step` with the
guard `planarGuard a b` read on the target's library point:

* a target `(x, y)` of the book's frame is the library point `toVec3 (x, y) = vec (-y) x 0`
  (the frames differ by `R_z(π/2)`, `Examples.planarTwoLinkPosition_eq_vec_iff`), and a concrete
  state is read as a design state by `State.abstract`, each list as the set of its members;
* the executable guard decides the annulus condition exactly:
  `reachable p t = true ↔ planarGuard p.a p.b (toVec3 t)` (`reachable_eq_true_iff`);
* every transition of `step` is a design step on the abstracted states (`step_sound`), and
  `step` blocks an action exactly when a guard of the design constructor of the same name fails
  (`step_isSome_iff`); every state that `run` reaches from `State.init` abstracts to a reachable
  state of the design supervisor (`reachableState_of_run`);
* hence, on the concrete state, the age never exceeds the bound, an idle supervisor has age zero,
  every commanded target passes the executable guard, and, for positive link lengths, every
  commanded target is a tool position of the ideal arm, `planarTwoLinkPosition a b q`, and the
  end-effector point `planarArmXY a b q` of the book's frame for the same joint vector `q`; when
  `a ≠ b` the elbow-down solution of MLS eq. (3.16), p. 98, is such a joint vector.

The reachable workspace is that of MLS eq. (3.12), printed p. 95, and the joint vectors come from
the inverse kinematics of MLS p. 98, eq. (3.16), through the workspace certificate. The
supervisor is a design model, not taken from MLS. These theorems concern the Lean definitions of
the executable supervisor and the ideal position model of the arm; the compiler or interpreter
that executes the definitions, the operating system, the text protocol, the controller, the motion
between targets, timing and a physical arm are outside them.
-/

noncomputable section

namespace RoboLean.Demo

open RoboLean.Examples RoboLean.Design

/-- The library point of a target: the book's point `(x, y)` (zero configuration along `+x`,
MLS Figure 3.7a, p. 97) is the point `vec (-y) x 0` of the library's frame for the kinematic arm
`Examples.planarTwoLink` (zero configuration along `+y`, MLS eq. (3.4), p. 89, specialized); the
frames differ by `R_z(π/2)`. The rational coordinates are cast to `ℝ`. -/
def toVec3 (t : Target) : Vec3 :=
  vec (-(t.2 : ℝ)) (t.1 : ℝ) 0

/-- Read a concrete state as a state of the design supervisor
`RoboLean.Design.PlanarArmTimeoutSupervisor`: each list becomes the set of its members, the flag
and the age are kept. A design convention, not from MLS. -/
def State.abstract (s : State) : PlanarArmTimeoutSupervisor.State Target where
  requested := {t | t ∈ s.requested}
  commanded := {t | t ∈ s.commanded}
  rejected := {t | t ∈ s.rejected}
  busy := s.busy
  timedOut := {t | t ∈ s.timedOut}
  age := s.age

/-- The library point of a target lies in the plane `x₃ = 0` of the planar arm. -/
theorem toVec3_two (t : Target) : toVec3 t 2 = 0 := by
  simp [toVec3, vec]

/-- The squared distance of a target from the base: `‖vec (-y) x 0‖² = x² + y²`, the `r²` of
MLS p. 98. -/
theorem norm_toVec3_sq (t : Target) : ‖toVec3 t‖ ^ 2 = (t.1 : ℝ) ^ 2 + (t.2 : ℝ) ^ 2 := by
  rw [toVec3, norm_vec_neg, Real.sq_sqrt (by positivity)]

/-- **The executable guard decides the workspace guard.** For all rational link lengths and
every rational target `(x, y)` of the book's frame, `reachable p (x, y)` is `true` exactly when
the library point `vec (-y) x 0` satisfies `planarGuard a b`: it lies in the plane `x₃ = 0` and
`|a - b| ≤ ‖vec (-y) x 0‖ ≤ a + b`, the annulus that, for positive lengths, is the reachable
workspace of MLS eq. (3.12), printed p. 95, of the planar two-link arm with unrestricted joints.
The squared form over `ℚ` is transferred to `ℝ` by the order-preserving cast. -/
theorem reachable_eq_true_iff (p : Params) (t : Target) :
    reachable p t = true ↔ planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t) := by
  set r := ‖toVec3 t‖
  have hr : 0 ≤ r := norm_nonneg _
  have hn : (t.1 : ℝ) * t.1 + t.2 * t.2 = r ^ 2 := by
    rw [norm_toVec3_sq]
    ring
  have e₀ : (0 ≤ p.a + p.b) ↔ (0 : ℝ) ≤ p.a + p.b := by
    rw [← Rat.cast_add, Rat.cast_nonneg]
  have e₁ : ((p.a - p.b) * (p.a - p.b) ≤ t.1 * t.1 + t.2 * t.2) ↔ |(p.a : ℝ) - p.b| ≤ r := by
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    rw [hn, ← sq, ← sq_abs, pow_le_pow_iff_left₀ (abs_nonneg _) hr two_ne_zero]
  have e₂ : (t.1 * t.1 + t.2 * t.2 ≤ (p.a + p.b) * (p.a + p.b)) ↔
      r ^ 2 ≤ ((p.a : ℝ) + p.b) ^ 2 := by
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    rw [hn, ← sq]
  simp only [reachable, Bool.and_eq_true, decide_eq_true_eq, planarGuard, toVec3_two, true_and]
  rw [e₀, e₁, e₂]
  constructor
  · rintro ⟨⟨hB, hA⟩, hR⟩
    exact ⟨hA, (pow_le_pow_iff_left₀ hr hB two_ne_zero).mp hR⟩
  · rintro ⟨hA, hR⟩
    exact ⟨⟨hr.trans hR, hA⟩, pow_le_pow_left₀ hr hR 2⟩

/-- Two states of the design supervisor with the same six components are equal. -/
private theorem timeoutState_ext {u v : PlanarArmTimeoutSupervisor.State Target}
    (h₁ : u.requested = v.requested) (h₂ : u.commanded = v.commanded)
    (h₃ : u.rejected = v.rejected) (h₄ : u.busy = v.busy) (h₅ : u.timedOut = v.timedOut)
    (h₆ : u.age = v.age) : u = v := by
  rcases u with ⟨⟨_, _, _, _⟩, _, _⟩
  rcases v with ⟨⟨_, _, _, _⟩, _, _⟩
  simp only at h₁ h₂ h₃ h₄ h₅ h₆
  subst h₁ h₂ h₃ h₄ h₅ h₆
  rfl

/-- Membership in a list into which another list is inserted element by element. -/
private theorem mem_foldr_insert (u : Target) (l m : List Target) :
    u ∈ l.foldr List.insert m ↔ u ∈ l ∨ u ∈ m := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.foldr_cons, List.mem_insert_iff, ih, List.mem_cons]
    tauto

/-- **Soundness of one step.** Every transition of the executable supervisor is a step of the
design relation `PlanarArmTimeoutSupervisor.Step` with the guard
`fun t => planarGuard a b (toVec3 t)` and the same age bound, on the abstracted states: an
action that `step` accepts satisfies the guards of the design constructor of the same name
(through `reachable_eq_true_iff` for the workspace guard), and its effect on the lists is the
design effect on the sets of their members. The guard is the annulus of MLS eq. (3.12), p. 95;
the supervisor is a design model, not from MLS. -/
theorem step_sound {p : Params} {s s' : State} {act : Action} (h : step p s act = some s') :
    PlanarArmTimeoutSupervisor.Step (fun t => planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t))
      p.bound s.abstract s'.abstract := by
  unfold step at h
  split at h
  · exact absurd h (by simp)
  rename_i hb
  cases h
  cases act with
  | request t =>
    convert PlanarArmTimeoutSupervisor.Step.request s.abstract t using 1
    apply timeoutState_ext <;> simp [State.abstract, State.apply, Set.ext_iff]
  | admit t =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂ h₃
    have hreq : t ∈ s.abstract.requested := by simpa [State.abstract] using h₁
    have hreach : planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t) :=
      (reachable_eq_true_iff p t).mp (by simpa using h₂)
    have hidle : s.abstract.busy = false := by simpa [State.abstract] using h₃
    convert PlanarArmTimeoutSupervisor.Step.admit
      (reachable := fun t => planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t)) (bound := p.bound)
      s.abstract t hreq hreach hidle using 1
    apply timeoutState_ext <;> simp [State.abstract, State.apply, Set.ext_iff]
  | reject t =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    have hreq : t ∈ s.abstract.requested := by simpa [State.abstract] using h₁
    have hunreach : ¬ planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t) := by
      rw [← reachable_eq_true_iff]
      exact h₂
    convert PlanarArmTimeoutSupervisor.Step.reject
      (reachable := fun t => planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t)) (bound := p.bound)
      s.abstract t hreq hunreach using 1
    apply timeoutState_ext <;> simp [State.abstract, State.apply, Set.ext_iff]
  | finish =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁
    have hbusy : s.abstract.busy = true := h₁
    convert PlanarArmTimeoutSupervisor.Step.finish s.abstract hbusy using 1
    apply timeoutState_ext <;> simp [State.abstract, State.apply]
  | tick =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    have hbusy : s.abstract.busy = true := by simpa [State.abstract] using h₁
    have hage : s.abstract.age < p.bound := h₂
    convert PlanarArmTimeoutSupervisor.Step.tick s.abstract hbusy hage using 1
    apply timeoutState_ext <;> simp [State.abstract, State.apply]
  | timeout =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    have hbusy : s.abstract.busy = true := by simpa [State.abstract] using h₁
    have hage : s.abstract.age = p.bound := h₂
    convert PlanarArmTimeoutSupervisor.Step.timeout s.abstract hbusy hage using 1
    apply timeoutState_ext <;> simp [State.abstract, State.apply, Set.ext_iff, mem_foldr_insert,
      or_comm]

/-- The guards of an action in a state, read on the abstracted state with the guard
`planarGuard a b` on the library point: those of the constructor of the same name of
`RoboLean.Design.PlanarArmTimeoutSupervisor.Step`. A design model, not from MLS. -/
def Action.Enabled (p : Params) (s : State) : Action → Prop
  | .request _ => True
  | .admit t => t ∈ s.requested ∧ planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t) ∧ s.busy = false
  | .reject t => t ∈ s.requested ∧ ¬ planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t)
  | .finish => s.busy = true
  | .tick => s.busy = true ∧ s.age < p.bound
  | .timeout => s.busy = true ∧ s.age = p.bound

/-- **Blocked exactly when a design guard fails.** The executable supervisor accepts an action
exactly when the guards of the design constructor of the same name hold (`Action.Enabled`),
with the workspace guard `planarGuard a b` on the library point; otherwise `step` returns `none`
and `Action.blocker` names the first failing guard. A design model, not from MLS. -/
theorem step_isSome_iff (p : Params) (s : State) (act : Action) :
    (step p s act).isSome = true ↔ act.Enabled p s := by
  cases act <;>
    simp only [step, Action.blocker, Action.Enabled, ← reachable_eq_true_iff] <;>
    (try split_ifs) <;> simp_all

/-- **Soundness of runs.** If the executable supervisor runs a list of actions from a state `s`
to a state `s'`, the design supervisor reaches the abstraction of `s'` from that of `s` in
finitely many steps, with the guard `fun t => planarGuard a b (toVec3 t)` and the same bound.
By induction over the actions from `step_sound`. A design model, not from MLS. -/
theorem run_sound {p : Params} {s s' : State} {acts : List Action} (h : run p s acts = some s') :
    Relation.ReflTransGen
      (PlanarArmTimeoutSupervisor.Step (fun t => planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t))
        p.bound) s.abstract s'.abstract := by
  induction acts generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst h
    exact .refl
  | cons act acts ih =>
    simp only [run] at h
    split at h
    · exact absurd h (by simp)
    · rename_i s₁ h₁
      exact .head (step_sound h₁) (ih h)

/-- The initial state of the executable supervisor abstracts to the initial state of the design
supervisor. -/
theorem abstract_init : State.init.abstract = PlanarArmTimeoutSupervisor.init := by
  apply timeoutState_ext <;>
    simp [State.abstract, State.init, PlanarArmTimeoutSupervisor.init]

/-- **Refinement.** Every state that the executable supervisor reaches from `State.init` by a
list of accepted actions abstracts to a reachable state of the design supervisor
`PlanarArmTimeoutSupervisor` with the guard `fun t => planarGuard a b (toVec3 t)` and the same
age bound, so every invariant proved for the design supervisor holds on it. The guard is the
annulus of MLS eq. (3.12), p. 95. A design model, not from MLS. -/
theorem reachableState_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p State.init acts = some s) :
    PlanarArmTimeoutSupervisor.ReachableState
      (fun t => planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t)) p.bound s.abstract := by
  unfold PlanarArmTimeoutSupervisor.ReachableState
  rw [← abstract_init]
  exact run_sound h

/-- **The age bound on the concrete state.** In every state that the executable supervisor
reaches from `State.init`, the age of the active command is at most the bound. From
`reachableState_of_run` and the design invariant `ReachableState.ageBounded`. A design model,
not from MLS. -/
theorem age_le_bound_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p State.init acts = some s) : s.age ≤ p.bound :=
  (reachableState_of_run h).ageBounded

/-- **Idle means age zero on the concrete state.** In every state that the executable supervisor
reaches from `State.init`, an idle supervisor has age zero. From `reachableState_of_run` and the
design invariant `ReachableState.idleAgeZero`. A design model, not from MLS. -/
theorem age_eq_zero_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p State.init acts = some s) (hidle : s.busy = false) : s.age = 0 :=
  (reachableState_of_run h).idleAgeZero hidle

/-- **Commanded targets pass the guard.** In every state that the executable supervisor reaches
from `State.init`, every commanded target satisfies the executable guard `reachable`. From the
design invariant `ReachableState.commandedReachable` and `reachable_eq_true_iff`. A design model,
not from MLS. -/
theorem reachable_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p State.init acts = some s) : ∀ t ∈ s.commanded, reachable p t = true :=
  fun t ht => (reachable_eq_true_iff p t).mpr ((reachableState_of_run h).commandedReachable t ht)

/-- **Commanded targets are tool positions of the ideal arm.** For positive link lengths, in
every state that the executable supervisor reaches from `State.init`, every commanded target
`(x, y)` is the tool position `planarTwoLinkPosition a b q = vec (-y) x 0` of the kinematic arm
for some joint vector `q`. From `reachableState_of_run` and the design refinement
`PlanarArmTimeoutSupervisor.ReachableState.exists_planarTwoLinkPosition_eq_pos`, whose joint
vectors come from the workspace certificate and the inverse kinematics of MLS p. 98,
eq. (3.16); the reachable workspace is that of MLS eq. (3.12), p. 95. Position reachability of
the ideal model only. -/
theorem exists_planarTwoLinkPosition_eq_of_run {p : Params} {acts : List Action} {s : State}
    (ha : 0 < p.a) (hb : 0 < p.b) (h : run p State.init acts = some s) :
    ∀ t ∈ s.commanded, ∃ q : Fin 2 → ℝ, planarTwoLinkPosition (p.a : ℝ) (p.b : ℝ) q = toVec3 t :=
  fun _ ht => (reachableState_of_run h).exists_planarTwoLinkPosition_eq_pos
    (Rat.cast_pos.mpr ha) (Rat.cast_pos.mpr hb) toVec3 ht

/-- **Commanded targets are set points of the dynamic arm.** For positive link lengths, in every
state that the executable supervisor reaches from `State.init`, every commanded target `(x, y)`
is the end-effector point `planarArmXY a b q = (x, y)` of the book's frame (MLS p. 97 and
Figure 4.4, p. 164) for some joint vector `q`, the joint vector of
`exists_planarTwoLinkPosition_eq_of_run` through the frame bridge
`planarTwoLinkPosition_eq_vec_iff_planarArmXY_eq`. Position reachability of the ideal model
only. -/
theorem exists_planarArmXY_eq_of_run {p : Params} {acts : List Action} {s : State}
    (ha : 0 < p.a) (hb : 0 < p.b) (h : run p State.init acts = some s) :
    ∀ t ∈ s.commanded, ∃ q : Fin 2 → ℝ, planarArmXY (p.a : ℝ) (p.b : ℝ) q = ![(t.1 : ℝ), t.2] := by
  intro t ht
  obtain ⟨q, hq⟩ := exists_planarTwoLinkPosition_eq_of_run ha hb h t ht
  exact ⟨q, (planarTwoLinkPosition_eq_vec_iff_planarArmXY_eq _ _ _ _ q).mp hq⟩

/-- **The elbow-down set point reaches every commanded target.** For positive and distinct link
lengths, in every state that the executable supervisor reaches from `State.init`, every commanded
target `(x, y)` is reached by the elbow-down joint vector of MLS eq. (3.16), p. 98,
`elbowDown a b x y = (atan2(y, x) - β, π - α)`: `planarArmXY a b (elbowDown a b x y) = (x, y)`.
Distinct lengths keep the target away from the base, `r ≥ |a - b| > 0`, where the formula for `β`
divides by `r`. From the design invariant `ReachableState.commandedReachable`, which puts the
target in the annulus, and `planarArmXY_elbowDown`. Exact real arithmetic; a floating-point
evaluation of the same formula is not covered. -/
theorem planarArmXY_elbowDown_of_run {p : Params} {acts : List Action} {s : State}
    (ha : 0 < p.a) (hb : 0 < p.b) (hab : p.a ≠ p.b) (h : run p State.init acts = some s) :
    ∀ t ∈ s.commanded,
      planarArmXY (p.a : ℝ) (p.b : ℝ) (elbowDown (p.a : ℝ) (p.b : ℝ) (t.1 : ℝ) (t.2 : ℝ)) =
        ![(t.1 : ℝ), t.2] := by
  intro t ht
  have hg : planarGuard (p.a : ℝ) (p.b : ℝ) (toVec3 t) :=
    (reachableState_of_run h).commandedReachable t ht
  obtain ⟨-, h₁, h₂⟩ := hg
  have hn : ‖toVec3 t‖ = √((t.1 : ℝ) ^ 2 + (t.2 : ℝ) ^ 2) := norm_vec_neg _ _
  rw [hn] at h₁ h₂
  have hab' : 0 < |(p.a : ℝ) - p.b| :=
    abs_pos.mpr (sub_ne_zero.mpr fun e => hab (Rat.cast_injective e))
  exact planarArmXY_elbowDown (Rat.cast_pos.mpr ha) (Rat.cast_pos.mpr hb) (hab'.trans_le h₁) h₁ h₂

end RoboLean.Demo
