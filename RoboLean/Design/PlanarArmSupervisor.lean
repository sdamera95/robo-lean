import RoboLean.Examples.PlanarTwoLinkWorkspace

/-!
# A target supervisor for the planar two-link arm

A supervisor sits between a task planner, which requests tool targets, and the arm controller,
which executes commanded targets one at a time. It admits a requested target only when the
target satisfies a guard `reachable` and no command is active, rejects a requested target that
fails the guard, and clears the active command when the controller finishes it. This file states
the supervisor as a transition system over an abstract target type and proves, by induction over
its steps, that every commanded target satisfies the guard (`ReachableState.commandedReachable`,
design row C09). It then instantiates the guard with `planarGuard a b`, the condition of the
workspace certificate C04 for the planar two-link arm, and proves that every commanded target
is the tool position of some joint vector (`ReachableState.exists_planarTwoLinkPosition_eq`,
design row C10).

Correspondence with the Veil model. The same transition system is modelled in Veil, in the
sibling project `robo-lean-veil`, file `Examples/RoboLean/PlanarArmSupervisor.lean`, declaration
by declaration: `State` and its four fields mirror Veil's `requested`, `commanded`, `rejected`
and `busy`; `init` mirrors `after_init`; the constructors of `Step` mirror the actions
`request`, `admit`, `reject` and `finish`; `CommandedReachable` mirrors the safety clause
`commanded_reachable`; `ReachableState.commandedReachable` is the counterpart of Veil's
inductive check. A Veil relation `r : target → Bool` is a Lean set, with `t ∈ s.r` read as
`r t = true`. The two projects run on different Lean versions (4.32.0 for Veil, 4.34.1 here)
and cannot import each other, so reading Veil's uninterpreted `reachable` as `planarGuard a b`
is a recorded convention (see `research/reports/veil-robotics-verification.md`), not a
kernel-checked link.

Sources. The guard is the annulus condition `x₃ = 0`, `|a - b| ≤ ‖x‖ ≤ a + b`, which for
positive link lengths characterizes the reachable workspace `W_R = {p(θ) : θ ∈ Q}` of MLS
eq. (3.12), printed p. 95, of `Examples.planarTwoLink a b` with unrestricted joints (design rows
C01–C04, from `research/reports/mls-lean-assessment.md`, "Robot design and workspace coverage";
not a theorem printed in MLS). The joint vectors come from the law-of-cosines inverse kinematics
of MLS p. 98, eq. (3.16) (row C02). The supervisor itself is a design model, not taken from MLS.

These statements concern the ideal transition system and the ideal position model of the arm.
They say nothing about the sampled implementation of a supervisor, timing, sensing, the motion
between targets, orientation, joint limits, collisions or a physical arm.
-/

namespace RoboLean.Design

namespace PlanarArmSupervisor

/-- The state of the target supervisor over a target type `Target`: the pending requests, the
active command, the targets rejected so far, and whether a command is active. This mirrors the
mutable state of the Veil model `PlanarArmSupervisor` (relations `requested`, `commanded`,
`rejected : target → Bool` and the individual `busy : Bool`); a Veil relation is a Lean set,
`t ∈ s.requested` read as `requested t = true`. A design model, not from MLS. -/
structure State (Target : Type*) where
  /-- Pending requests from the planner. -/
  requested : Set Target
  /-- The active command sent to the arm controller. -/
  commanded : Set Target
  /-- Targets the supervisor has rejected. -/
  rejected : Set Target
  /-- A command is active. -/
  busy : Bool

variable {Target : Type*}

/-- The initial state: no request, no command, no rejection, idle. This mirrors the
`after_init` block of the Veil model `PlanarArmSupervisor`. A design model, not from MLS. -/
def init : State Target where
  requested := ∅
  commanded := ∅
  rejected := ∅
  busy := false

/-- One step of the target supervisor with guard `reachable`; each constructor mirrors the
action of the same name in the Veil model `PlanarArmSupervisor`, with its `require` clauses as
hypotheses.

* `request t`: the planner requests `t`.
* `admit t`: a requested target that satisfies the guard is commanded while the supervisor is
  idle; the request is consumed and the supervisor becomes busy.
* `reject t`: a requested target that fails the guard is rejected; the request is consumed.
* `finish`: the arm controller finishes the active command; the supervisor becomes idle.

The guard is any predicate on targets; for the planar two-link arm it is `planarGuard a b`
(MLS p. 95, eq. (3.12), through design row C04). A design model, not from MLS. -/
inductive Step (reachable : Target → Prop) : State Target → State Target → Prop
  /-- The planner requests `t` (Veil action `request`). -/
  | request (s : State Target) (t : Target) :
      Step reachable s { s with requested := insert t s.requested }
  /-- A requested target that satisfies the guard is commanded while the supervisor is idle
  (Veil action `admit`). -/
  | admit (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hreachable : reachable t) (hidle : s.busy = false) :
      Step reachable s
        { s with requested := s.requested \ {t}, commanded := insert t s.commanded, busy := true }
  /-- A requested target that fails the guard is rejected (Veil action `reject`). -/
  | reject (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hunreachable : ¬ reachable t) :
      Step reachable s { s with requested := s.requested \ {t}, rejected := insert t s.rejected }
  /-- The arm controller finishes the active command (Veil action `finish`). -/
  | finish (s : State Target) (hbusy : s.busy = true) :
      Step reachable s { s with commanded := ∅, busy := false }

/-- The states of the target supervisor with guard `reachable` that some finite sequence of
steps reaches from `init`: the reflexive-transitive closure of `Step reachable` from `init`. A
design model, not from MLS. -/
def ReachableState (reachable : Target → Prop) (s : State Target) : Prop :=
  Relation.ReflTransGen (Step reachable) init s

/-- The safety property of the target supervisor: every commanded target satisfies the guard.
This mirrors the Veil clause `safety [commanded_reachable] commanded T → reachable T`. A design
statement, not from MLS. -/
def CommandedReachable (reachable : Target → Prop) (s : State Target) : Prop :=
  ∀ t ∈ s.commanded, reachable t

/-- The initial state satisfies the safety property, since nothing is commanded. Counterpart of
Veil's verification condition `initializer_commanded_reachable`. Design row C09, not from MLS. -/
theorem commandedReachable_init (reachable : Target → Prop) :
    CommandedReachable reachable (init : State Target) := by
  intro t ht
  simp [init] at ht

/-- Every step of the target supervisor preserves the safety property: `admit` commands only a
target that satisfies the guard, `finish` clears the command, and `request` and `reject` leave
it unchanged. The four cases are the counterparts of Veil's verification conditions
`request_commanded_reachable`, `admit_commanded_reachable`, `reject_commanded_reachable` and
`finish_commanded_reachable`. Design row C09, not from MLS. -/
theorem Step.commandedReachable {reachable : Target → Prop} {s s' : State Target}
    (h : Step reachable s s') (hs : CommandedReachable reachable s) :
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

/-- **Supervisor invariant.** In every reachable state of the target supervisor, every commanded
target satisfies the guard, for every guard `reachable` on every target type. Proved by
induction over the steps from `commandedReachable_init` and `Step.commandedReachable`. Veil's
`#check_invariants` on the clause `commanded_reachable` checks the initialization and
preservation conditions; this theorem also composes them along every finite run of the mirrored
system. Design row C09, not from MLS. -/
theorem ReachableState.commandedReachable {reachable : Target → Prop} {s : State Target}
    (h : ReachableState reachable s) : CommandedReachable reachable s := by
  induction h with
  | refl => exact commandedReachable_init reachable
  | tail _ hstep ih => exact hstep.commandedReachable ih

end PlanarArmSupervisor

open RoboLean.Examples

/-- The guard of the planar-arm supervisor: a tool target `x` lies in the plane `x₃ = 0` (Lean
coordinate `x 2`) with `|a - b| ≤ ‖x‖ ≤ a + b`. This is exactly the condition of the workspace
certificate `Examples.planarTwoLink_workspace_certificate` (design row C04), which for positive
link lengths characterizes the reachable workspace of MLS eq. (3.12), printed p. 95, of
`Examples.planarTwoLink a b` with unrestricted joints
(`Examples.planarTwoLink_subset_reachableWorkspace_iff`). Convention: the uninterpreted
relation `reachable` of the Veil model `PlanarArmSupervisor` is read as `planarGuard a b`. -/
def planarGuard (a b : ℝ) (x : Vec3) : Prop :=
  x 2 = 0 ∧ |a - b| ≤ ‖x‖ ∧ ‖x‖ ≤ a + b

namespace PlanarArmSupervisor

/-- **Refinement, targets with positions.** For positive link lengths `a, b` and a target type
whose targets have tool positions `pos t`, run the supervisor with guard
`fun t => planarGuard a b (pos t)`. Then every target commanded in a reachable state is reached
by the planar two-link arm: some joint vector `q` puts the tool at `pos t`. From the supervisor
invariant (row C09) and the workspace certificate `Examples.planarTwoLink_workspace_certificate`
(row C04), whose joint vectors come from the inverse kinematics of MLS p. 98, eq. (3.16) (row
C02); the reachable workspace is that of MLS p. 95, eq. (3.12). Design row C10, not from MLS.
Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq_pos {Target : Type*} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (pos : Target → Vec3) {s : State Target}
    (hs : ReachableState (fun t => planarGuard a b (pos t)) s) {t : Target}
    (ht : t ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = pos t :=
  planarTwoLink_workspace_certificate ha hb (pos '' s.commanded)
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact hs.commandedReachable u hu)
    (pos t) ⟨t, ht, rfl⟩

/-- **Refinement.** For positive link lengths `a, b`, run the supervisor over tool targets
`x : Vec3` with guard `planarGuard a b`. Then every target commanded in a reachable state is
the tool position `Examples.planarTwoLinkPosition a b q` of some joint vector `q`. The case
`pos = id` of `ReachableState.exists_planarTwoLinkPosition_eq_pos`; from rows C09, C04 and C02
(MLS p. 98, eq. (3.16)), with the reachable workspace of MLS p. 95, eq. (3.12). Design row C10,
not from MLS. Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : State Vec3} (hs : ReachableState (planarGuard a b) s) {x : Vec3}
    (hx : x ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x :=
  hs.exists_planarTwoLinkPosition_eq_pos ha hb id hx

/-- **Refinement, workspace form.** For positive link lengths `a, b`, in every reachable state
of the supervisor over tool targets with guard `planarGuard a b`, the commanded targets lie in
the reachable workspace `W_R` of MLS eq. (3.12), printed p. 95, of `Examples.planarTwoLink a b`
with unrestricted joints (`Q = Set.univ`). From the supervisor invariant (row C09) and
`Examples.planarTwoLink_subset_reachableWorkspace_iff` (row C04). Design row C10, not from MLS.
Position reachability of the ideal model only. -/
theorem ReachableState.commanded_subset_reachableWorkspace {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : State Vec3} (hs : ReachableState (planarGuard a b) s) :
    s.commanded ⊆ (planarTwoLink a b).reachableWorkspace Set.univ :=
  (planarTwoLink_subset_reachableWorkspace_iff ha hb s.commanded).mpr hs.commandedReachable

end PlanarArmSupervisor

end RoboLean.Design
