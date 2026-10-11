import RoboLean.Design.PlanarArmSupervisor

/-!
# A target supervisor with a command timeout for the planar two-link arm

This file extends the target supervisor of `RoboLean.Design.PlanarArmSupervisor` (design rows C09,
C10) with a command age. While a command is active, a clock `tick` increments the age `age : ℕ`
of the command up to a bound `bound : ℕ`; when the age equals the bound, `timeout` clears the
active command and records it in `timedOut`. `admit`, `finish` and `timeout` reset the age to
zero; `request`, `admit`, `reject` and `finish` act on the other components exactly as in the
first supervisor. The file states the supervisor as a transition system over an abstract target
type and proves three invariants by induction over its steps: every commanded target satisfies
the guard (`ReachableState.commandedReachable`), the age never exceeds the bound
(`ReachableState.ageBounded`), and an idle supervisor has age zero
(`ReachableState.idleAgeZero`) (design row C11). It then shows that forgetting `timedOut` and
`age` maps every run to a run of the first supervisor, a `tick` to no step and a `timeout` to a
`finish` (`ReachableState.toState`), and carries the refinement of row C10 over: with guard
`planarGuard a b`, every commanded target is a tool position of the arm
(`ReachableState.exists_planarTwoLinkPosition_eq`, design row C12).

Correspondence with the Veil model. The same transition system is modelled in Veil, in the
sibling project `robo-lean-veil`, file `Examples/RoboLean/PlanarArmTimeoutSupervisor.lean`,
declaration by declaration: the fields of `State` mirror Veil's `requested`, `commanded`,
`rejected`, `timedOut`, `busy` and `age` (the first four inherited from the first supervisor's
state); `init` mirrors `after_init`; the constructors of `Step` mirror the actions `request`,
`admit`, `reject`, `finish`, `tick` and `timeout`; the parameter `bound` mirrors the immutable
individual `bound : Nat`; `CommandedReachable`, `AgeBounded` and `IdleAgeZero` mirror the
clauses `commanded_reachable`, `age_bounded` and `idle_age_zero`; the cases of the step lemmas
are the counterparts of Veil's verification conditions `<action>_<clause>`. A Veil relation
`r : target → Bool` is a Lean set, with `t ∈ s.r` read as `r t = true`, and Veil's `Nat` is
Lean's `ℕ`. The two projects run on different Lean versions (4.32.0 for Veil, 4.34.1 here) and
cannot import each other, so the correspondence, and reading Veil's uninterpreted `reachable` as
`planarGuard a b`, are recorded conventions (decision D003, entries E018 and E022), not
kernel-checked links.

Sources. The guard is the annulus condition of the workspace certificate C04, which for positive
link lengths characterizes the reachable workspace `W_R = {p(θ) : θ ∈ Q}` of MLS eq. (3.12),
printed p. 95; the joint vectors come from the law-of-cosines inverse kinematics of MLS p. 98,
eq. (3.16) (row C02). The supervisor and its timeout are a design model, not taken from MLS.

These statements concern the ideal transition system and the ideal position model of the arm.
The age counts abstract `tick` steps, not physical time; nothing here says how often the clock
ticks, that a command finishes or times out (a liveness property), or anything about the sampled
implementation, sensing, the motion between targets, orientation, joint limits, collisions or a
physical arm.
-/

namespace RoboLean.Design

namespace PlanarArmTimeoutSupervisor

/-- The state of the timeout supervisor over a target type `Target`: the state of the first
supervisor `PlanarArmSupervisor.State` (pending requests, active command, rejected targets,
whether a command is active), the targets whose command timed out, and the age of the active
command. This mirrors the mutable state of the Veil model `PlanarArmTimeoutSupervisor` (relations
`requested`, `commanded`, `rejected`, `timedOut : target → Bool`, individuals `busy : Bool` and
`age : Nat`); a Veil relation is a Lean set, `t ∈ s.timedOut` read as `timedOut t = true`. A
design model, not from MLS. -/
structure State (Target : Type*) extends PlanarArmSupervisor.State Target where
  /-- Targets whose command timed out. -/
  timedOut : Set Target
  /-- The number of ticks since the active command was admitted. -/
  age : ℕ

variable {Target : Type*}

/-- The initial state: no request, no command, no rejection, no timeout, idle, age zero. This
mirrors the `after_init` block of the Veil model `PlanarArmTimeoutSupervisor`. A design model,
not from MLS. -/
def init : State Target where
  requested := ∅
  commanded := ∅
  rejected := ∅
  busy := false
  timedOut := ∅
  age := 0

/-- One step of the timeout supervisor with guard `reachable` and age bound `bound`; each
constructor mirrors the action of the same name in the Veil model `PlanarArmTimeoutSupervisor`,
with its `require` clauses as hypotheses.

* `request t`: the planner requests `t`.
* `admit t`: a requested target that satisfies the guard is commanded while the supervisor is
  idle; the request is consumed, the supervisor becomes busy and the age is reset to zero.
* `reject t`: a requested target that fails the guard is rejected; the request is consumed.
* `finish`: the arm controller finishes the active command; the supervisor becomes idle and the
  age is reset to zero.
* `tick`: while a command is active and its age is below the bound, the age increases by one.
* `timeout`: while a command is active and its age equals the bound, the active command is
  recorded in `timedOut` and cleared, the supervisor becomes idle and the age is reset to zero.

The guard is any predicate on targets; for the planar two-link arm it is `planarGuard a b`
(MLS p. 95, eq. (3.12), through design row C04). A design model, not from MLS. -/
inductive Step (reachable : Target → Prop) (bound : ℕ) : State Target → State Target → Prop
  /-- The planner requests `t` (Veil action `request`). -/
  | request (s : State Target) (t : Target) :
      Step reachable bound s { s with requested := insert t s.requested }
  /-- A requested target that satisfies the guard is commanded while the supervisor is idle
  (Veil action `admit`). -/
  | admit (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hreachable : reachable t) (hidle : s.busy = false) :
      Step reachable bound s
        { s with requested := s.requested \ {t}, commanded := insert t s.commanded, busy := true,
                 age := 0 }
  /-- A requested target that fails the guard is rejected (Veil action `reject`). -/
  | reject (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hunreachable : ¬ reachable t) :
      Step reachable bound s
        { s with requested := s.requested \ {t}, rejected := insert t s.rejected }
  /-- The arm controller finishes the active command (Veil action `finish`). -/
  | finish (s : State Target) (hbusy : s.busy = true) :
      Step reachable bound s { s with commanded := ∅, busy := false, age := 0 }
  /-- One clock tick while a command is active and below the age bound (Veil action `tick`). -/
  | tick (s : State Target) (hbusy : s.busy = true) (hage : s.age < bound) :
      Step reachable bound s { s with age := s.age + 1 }
  /-- The active command has reached the age bound and times out (Veil action `timeout`). -/
  | timeout (s : State Target) (hbusy : s.busy = true) (hage : s.age = bound) :
      Step reachable bound s
        { s with timedOut := s.timedOut ∪ s.commanded, commanded := ∅, busy := false, age := 0 }

/-- The states of the timeout supervisor with guard `reachable` and age bound `bound` that some
finite sequence of steps reaches from `init`: the reflexive-transitive closure of
`Step reachable bound` from `init`. A design model, not from MLS. -/
def ReachableState (reachable : Target → Prop) (bound : ℕ) (s : State Target) : Prop :=
  Relation.ReflTransGen (Step reachable bound) init s

/-- The first safety property: every commanded target satisfies the guard. This mirrors the Veil
clause `safety [commanded_reachable] commanded T → reachable T`. A design statement, not from
MLS. -/
def CommandedReachable (reachable : Target → Prop) (s : State Target) : Prop :=
  ∀ t ∈ s.commanded, reachable t

/-- The second safety property: the age of the active command never exceeds the bound. This
mirrors the Veil clause `safety [age_bounded] age ≤ bound`. A design statement, not from MLS. -/
def AgeBounded (bound : ℕ) (s : State Target) : Prop :=
  s.age ≤ bound

/-- An auxiliary invariant: an idle supervisor has age zero. This mirrors the Veil clause
`invariant [idle_age_zero] ¬ busy → age = 0`. A design statement, not from MLS. -/
def IdleAgeZero (s : State Target) : Prop :=
  s.busy = false → s.age = 0

/-- The initial state satisfies `CommandedReachable`, since nothing is commanded. Counterpart of
Veil's verification condition `initializer_commanded_reachable`. Design row C11, not from MLS. -/
theorem commandedReachable_init (reachable : Target → Prop) :
    CommandedReachable reachable (init : State Target) := by
  intro t ht
  simp [init] at ht

/-- The initial state satisfies `AgeBounded`, since its age is zero. Counterpart of Veil's
verification condition `initializer_age_bounded`. Design row C11, not from MLS. -/
theorem ageBounded_init (bound : ℕ) : AgeBounded bound (init : State Target) :=
  Nat.zero_le bound

/-- The initial state satisfies `IdleAgeZero`, since its age is zero. Counterpart of Veil's
verification condition `initializer_idle_age_zero`. Design row C11, not from MLS. -/
theorem idleAgeZero_init : IdleAgeZero (init : State Target) :=
  fun _ => rfl

/-- Every step of the timeout supervisor preserves `CommandedReachable`: `admit` commands only a
target that satisfies the guard, `finish` and `timeout` clear the command, and `request`,
`reject` and `tick` leave it unchanged. The six cases are the counterparts of Veil's verification
conditions `<action>_commanded_reachable`. Design row C11, not from MLS. -/
theorem Step.commandedReachable {reachable : Target → Prop} {bound : ℕ} {s s' : State Target}
    (h : Step reachable bound s s') (hs : CommandedReachable reachable s) :
    CommandedReachable reachable s' := by
  cases h with
  | request => exact hs
  | admit t _ hreachable _ =>
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact hreachable
    · exact hs u hu
  | reject => exact hs
  | finish =>
    intro u hu
    simp at hu
  | tick => exact hs
  | timeout =>
    intro u hu
    simp at hu

/-- Every step of the timeout supervisor preserves `AgeBounded`: `tick` fires only below the
bound, `admit`, `finish` and `timeout` reset the age to zero, and `request` and `reject` leave it
unchanged. The six cases are the counterparts of Veil's verification conditions
`<action>_age_bounded`; the `tick` case is the one that needs arithmetic. Design row C11, not from
MLS. -/
theorem Step.ageBounded {reachable : Target → Prop} {bound : ℕ} {s s' : State Target}
    (h : Step reachable bound s s') (hs : AgeBounded bound s) : AgeBounded bound s' := by
  cases h with
  | request => exact hs
  | admit => exact Nat.zero_le bound
  | reject => exact hs
  | finish => exact Nat.zero_le bound
  | tick _ hage => exact hage
  | timeout => exact Nat.zero_le bound

/-- Every step of the timeout supervisor preserves `IdleAgeZero`: `admit` makes the supervisor
busy, `tick` fires only while it is busy and keeps it busy, `finish` and `timeout` reset the age
to zero, and `request` and `reject` change neither `busy` nor the age. The six cases are the
counterparts of Veil's verification conditions `<action>_idle_age_zero`. Design row C11, not from
MLS. -/
theorem Step.idleAgeZero {reachable : Target → Prop} {bound : ℕ} {s s' : State Target}
    (h : Step reachable bound s s') (hs : IdleAgeZero s) : IdleAgeZero s' := by
  cases h with
  | request => exact hs
  | admit => exact fun _ => rfl
  | reject => exact hs
  | finish => exact fun _ => rfl
  | tick hbusy _ =>
    intro hidle
    simp [hbusy] at hidle
  | timeout => exact fun _ => rfl

/-- **Supervisor invariant, guard.** In every reachable state of the timeout supervisor, every
commanded target satisfies the guard, for every guard `reachable` on every target type and every
bound. Proved by induction over the steps from `commandedReachable_init` and
`Step.commandedReachable`; Veil's `#check_invariants` checks the initialization and preservation
conditions, and this theorem also composes them along every finite run of the mirrored system.
Design row C11, not from MLS. -/
theorem ReachableState.commandedReachable {reachable : Target → Prop} {bound : ℕ}
    {s : State Target} (h : ReachableState reachable bound s) :
    CommandedReachable reachable s := by
  induction h with
  | refl => exact commandedReachable_init reachable
  | tail _ hstep ih => exact hstep.commandedReachable ih

/-- **Supervisor invariant, age.** In every reachable state of the timeout supervisor, the age of
the active command is at most the bound, for every guard and every bound. Proved by induction
over the steps from `ageBounded_init` and `Step.ageBounded`. Design row C11, not from MLS. -/
theorem ReachableState.ageBounded {reachable : Target → Prop} {bound : ℕ}
    {s : State Target} (h : ReachableState reachable bound s) : AgeBounded bound s := by
  induction h with
  | refl => exact ageBounded_init bound
  | tail _ hstep ih => exact hstep.ageBounded ih

/-- **Supervisor invariant, idle age.** In every reachable state of the timeout supervisor, an
idle supervisor has age zero, for every guard and every bound. Proved by induction over the steps
from `idleAgeZero_init` and `Step.idleAgeZero`. Design row C11, not from MLS. -/
theorem ReachableState.idleAgeZero {reachable : Target → Prop} {bound : ℕ}
    {s : State Target} (h : ReachableState reachable bound s) : IdleAgeZero s := by
  induction h with
  | refl => exact idleAgeZero_init
  | tail _ hstep ih => exact hstep.idleAgeZero ih

/-- **Simulation, one step.** Forgetting `timedOut` and `age`, each step of the timeout supervisor
is a step of the first supervisor `PlanarArmSupervisor` or no step: `request`, `admit`, `reject`
and `finish` map to the steps of the same name, `tick` to no step, and `timeout` to `finish`.
Design row C12, not from MLS. -/
theorem Step.toState {reachable : Target → Prop} {bound : ℕ} {s s' : State Target}
    (h : Step reachable bound s s') :
    Relation.ReflGen (PlanarArmSupervisor.Step reachable) s.toState s'.toState := by
  cases h with
  | request t => exact .single (PlanarArmSupervisor.Step.request s.toState t)
  | admit t hrequested hreachable hidle =>
    exact .single (PlanarArmSupervisor.Step.admit s.toState t hrequested hreachable hidle)
  | reject t hrequested hunreachable =>
    exact .single (PlanarArmSupervisor.Step.reject s.toState t hrequested hunreachable)
  | finish hbusy => exact .single (PlanarArmSupervisor.Step.finish s.toState hbusy)
  | tick => exact .refl
  | timeout hbusy _ => exact .single (PlanarArmSupervisor.Step.finish s.toState hbusy)

/-- **Simulation.** Forgetting `timedOut` and `age`, every reachable state of the timeout
supervisor with guard `reachable` and any bound is a reachable state of the first supervisor
`PlanarArmSupervisor` with the same guard. By induction over the steps from `Step.toState`. Design
row C12, not from MLS. -/
theorem ReachableState.toState {reachable : Target → Prop} {bound : ℕ} {s : State Target}
    (h : ReachableState reachable bound s) :
    PlanarArmSupervisor.ReachableState reachable s.toState := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans hstep.toState.to_reflTransGen

open RoboLean.Examples

/-- **Refinement, targets with positions.** For positive link lengths `a, b`, any bound, and a
target type whose targets have tool positions `pos t`, run the timeout supervisor with guard
`fun t => planarGuard a b (pos t)`. Then every target commanded in a reachable state is reached by
the planar two-link arm: some joint vector `q` puts the tool at `pos t`. From the simulation
`ReachableState.toState` and the first supervisor's refinement
`PlanarArmSupervisor.ReachableState.exists_planarTwoLinkPosition_eq_pos` (row C10, from C04 and
C02, whose joint vectors come from the inverse kinematics of MLS p. 98, eq. (3.16)); the reachable
workspace is that of MLS p. 95, eq. (3.12). Design row C12, not from MLS. Position reachability
of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq_pos {Target : Type*} {a b : ℝ} {bound : ℕ}
    (ha : 0 < a) (hb : 0 < b) (pos : Target → Vec3) {s : State Target}
    (hs : ReachableState (fun t => planarGuard a b (pos t)) bound s) {t : Target}
    (ht : t ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = pos t :=
  hs.toState.exists_planarTwoLinkPosition_eq_pos ha hb pos ht

/-- **Refinement.** For positive link lengths `a, b` and any bound, run the timeout supervisor over
tool targets `x : Vec3` with guard `planarGuard a b`. Then every target commanded in a reachable
state is the tool position `Examples.planarTwoLinkPosition a b q` of some joint vector `q`. From
the simulation `ReachableState.toState` and
`PlanarArmSupervisor.ReachableState.exists_planarTwoLinkPosition_eq` (row C10; MLS p. 98,
eq. (3.16), and the reachable workspace of MLS p. 95, eq. (3.12)). Design row C12, not from MLS.
Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq {a b : ℝ} {bound : ℕ} (ha : 0 < a)
    (hb : 0 < b) {s : State Vec3} (hs : ReachableState (planarGuard a b) bound s) {x : Vec3}
    (hx : x ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x :=
  hs.toState.exists_planarTwoLinkPosition_eq ha hb hx

/-- **Refinement, workspace form.** For positive link lengths `a, b` and any bound, in every
reachable state of the timeout supervisor over tool targets with guard `planarGuard a b`, the
commanded targets lie in the reachable workspace `W_R` of MLS eq. (3.12), printed p. 95, of
`Examples.planarTwoLink a b` with unrestricted joints (`Q = Set.univ`). From the simulation
`ReachableState.toState` and
`PlanarArmSupervisor.ReachableState.commanded_subset_reachableWorkspace` (row C10). Design row C12,
not from MLS. Position reachability of the ideal model only. -/
theorem ReachableState.commanded_subset_reachableWorkspace {a b : ℝ} {bound : ℕ} (ha : 0 < a)
    (hb : 0 < b) {s : State Vec3} (hs : ReachableState (planarGuard a b) bound s) :
    s.commanded ⊆ (planarTwoLink a b).reachableWorkspace Set.univ :=
  hs.toState.commanded_subset_reachableWorkspace ha hb

end PlanarArmTimeoutSupervisor

end RoboLean.Design
