import RoboLean.Design.PlanarArmSchedulerSupervisor

/-!
# A target supervisor with a wrap-around scheduler for the planar two-link arm

This file restates the scheduler supervisor of `RoboLean.Design.PlanarArmSchedulerSupervisor`
(design rows C15, C16) with the scheduler re-encoded without division and remainder. The state,
the initial state, the actions, the guards and the counters are those of that file; only `tick`
advances the round-robin slot differently: if `slot + 1 = period`, the slot returns to zero and the
count `rounds` of completed periods increases by one, and otherwise the slot increases by one. The
scheduler supervisor of `PlanarArmSchedulerSupervisor` writes the same update as
`rounds := rounds + (slot + 1) / period` and `slot := (slot + 1) % period`.

The file reuses the state `PlanarArmSchedulerSupervisor.State`, its initial state
`PlanarArmSchedulerSupervisor.init` and its clause predicates, and defines a new step relation
`Step` (design row C17). It proves, by induction over the steps, that in every reachable state the
slot is below the period (`ReachableState.slotBounded`, for `1 ≤ period`) and that `period` times
the completed periods plus the slot is the number of ticks spent (`ReachableState.roundsBalance`,
for every `period`). From these two invariants alone it recovers the clauses of the scheduler
supervisor that use `%` and `/`: the slot is `ticksTotal % period` (`ReachableState.slotPhase`)
and the completed periods are `ticksTotal / period` (`ReachableState.roundsCount`), both for
`1 ≤ period`.

The relation to `PlanarArmSchedulerSupervisor` (design row C17): on states whose slot is below the
period, a step of this supervisor is a step of that supervisor and conversely
(`step_iff_schedulerStep`), so for `1 ≤ period` the two supervisors have the same reachable states
(`reachableState_iff_schedulerReachableState`). Through `ReachableState.toSchedulerReachableState`,
every invariant of the scheduler supervisor holds here for `1 ≤ period`, for example the load and
energy bounds `(h.toSchedulerReachableState hperiod).loadBounded` and
`(h.toSchedulerReachableState hperiod).energyBounded`. For every `period`, forgetting the
five counting components maps each step to the step of the same name of the budget supervisor
`PlanarArmBudgetSupervisor` (`ReachableState.toBudgetState`, design row C18), which carries the
budget supervisor's six invariants and its refinement over: with guard `planarGuard a b`, every
commanded target is a tool position of the arm (`ReachableState.exists_planarTwoLinkPosition_eq`).

Correspondence with the Veil model. The same transition system is modelled in Veil, in the
sibling project `robo-lean-veil`, file `Examples/RoboLean/PlanarArmWrapSchedulerSupervisor.lean`
(module `PlanarArmWrapSchedulerSupervisor`): the state components are the fields of
`PlanarArmSchedulerSupervisor.State`, `after_init` is `PlanarArmSchedulerSupervisor.init capacity`,
the constructors of `Step` mirror the actions `request`, `admit`, `reject`, `finish`, `tick` and
`timeout` (the `if … then … else …` of the Veil action `tick` is the `if … then … else …` of the
two updated fields here), the parameters mirror the immutable individuals of the same names, and
the clauses `slot_bounded` and `rounds_balance` are `PlanarArmSchedulerSupervisor.SlotBounded` and
`PlanarArmSchedulerSupervisor.RoundsBalance`. The Veil model states no clause with `%` or `/`; the
two recovered theorems exist only here. The two projects run on different Lean versions (4.32.0
for Veil, 4.34.1 here) and cannot import each other, so the correspondence, and reading Veil's
uninterpreted `reachable` as `planarGuard a b`, are recorded conventions (decision D003, entries
E018, E022, E027, E032 and E036), not kernel-checked links.

Sources. The guard is the annulus condition of the workspace certificate C04, which for positive
link lengths characterizes the reachable workspace `W_R = {p(θ) : θ ∈ Q}` of MLS eq. (3.12),
printed p. 95; the joint vectors come from the law-of-cosines inverse kinematics of MLS p. 98,
eq. (3.16) (row C02). The supervisor and its scheduler are a design model, not taken from MLS.

These statements concern the ideal transition system and the ideal position model of the arm.
The counters count abstract steps; nothing here says how often the clock ticks, that a command
finishes, times out or is ever admitted (liveness), that the scheduler serves any task, or
anything about the sampled implementation, sensing, the motion between targets, orientation,
joint limits, collisions or a physical arm.
-/

namespace RoboLean.Design

namespace PlanarArmWrapSchedulerSupervisor

/-- The wrap-around slot update agrees with the remainder update below the period: if
`slot < period`, then `(if slot + 1 = period then 0 else slot + 1) = (slot + 1) % period`. This is
the arithmetic that relates the `tick` of this supervisor to the `tick` of
`PlanarArmSchedulerSupervisor`. Design row C17, not from MLS. -/
theorem wrapSlot_eq_mod {slot period : ℕ} (h : slot < period) :
    (if slot + 1 = period then 0 else slot + 1) = (slot + 1) % period := by
  split_ifs with hw
  · rw [hw, Nat.mod_self]
  · exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The wrap-around round update agrees with the quotient update below the period: if
`slot < period`, then `(if slot + 1 = period then rounds + 1 else rounds) =
rounds + (slot + 1) / period`. Design row C17, not from MLS. -/
theorem wrapRounds_eq_add_div {slot rounds period : ℕ} (h : slot < period) :
    (if slot + 1 = period then rounds + 1 else rounds) = rounds + (slot + 1) / period := by
  split_ifs with hw
  · rw [hw, Nat.div_self (by omega)]
  · rw [Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- The slot phase from the two scheduler invariants: if the slot is below the period and
`period * rounds + slot = ticksTotal`, then the slot is `ticksTotal % period`, the clause
`PlanarArmSchedulerSupervisor.SlotPhase` (Veil clause `slot_phase` of the E032 model). Holds for
every `period` (the hypothesis `slot < period` forces `0 < period`). Design row C17, not from
MLS. -/
theorem slotPhase_of_roundsBalance {Target : Type*} {period : ℕ}
    {s : PlanarArmSchedulerSupervisor.State Target}
    (hb : PlanarArmSchedulerSupervisor.SlotBounded period s)
    (hr : PlanarArmSchedulerSupervisor.RoundsBalance period s) :
    PlanarArmSchedulerSupervisor.SlotPhase period s := by
  unfold PlanarArmSchedulerSupervisor.SlotBounded at hb
  unfold PlanarArmSchedulerSupervisor.RoundsBalance at hr
  unfold PlanarArmSchedulerSupervisor.SlotPhase
  rw [← hr, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-- The round count from the two scheduler invariants: if the slot is below the period and
`period * rounds + slot = ticksTotal`, then the completed periods are `ticksTotal / period`, the
clause `PlanarArmSchedulerSupervisor.RoundsCount` (Veil clause `rounds_count` of the E032 model).
Holds for every `period` (the hypothesis `slot < period` forces `0 < period`). Design row C17, not
from MLS. -/
theorem roundsCount_of_roundsBalance {Target : Type*} {period : ℕ}
    {s : PlanarArmSchedulerSupervisor.State Target}
    (hb : PlanarArmSchedulerSupervisor.SlotBounded period s)
    (hr : PlanarArmSchedulerSupervisor.RoundsBalance period s) :
    PlanarArmSchedulerSupervisor.RoundsCount period s := by
  unfold PlanarArmSchedulerSupervisor.SlotBounded at hb
  unfold PlanarArmSchedulerSupervisor.RoundsBalance at hr
  unfold PlanarArmSchedulerSupervisor.RoundsCount
  rw [← hr, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero]

variable {Target : Type*} [DecidableEq Target]

/-- One step of the wrap-around scheduler supervisor with guard `reachable`, age bound `bound`,
admission limit `maxAttempts`, energy rate `rate` and scheduler period `period`, over the state
`PlanarArmSchedulerSupervisor.State` of the scheduler supervisor; each constructor mirrors the
action of the same name in the Veil model `PlanarArmWrapSchedulerSupervisor`, with its `require`
clauses as hypotheses. Every constructor except `tick` is the constructor of the same name of
`PlanarArmSchedulerSupervisor.Step`.

* `request t`: the planner requests `t`.
* `admit t`: a requested target that satisfies the guard and has been admitted fewer than
  `maxAttempts` times is commanded while the supervisor is idle; the request is consumed, the
  supervisor becomes busy, the age and the load are reset to zero and the admission count of `t`
  increases by one.
* `reject t`: a requested target that fails the guard is rejected; the request is consumed.
* `finish`: the arm controller finishes the active command; its age is added to `ticksClosed`,
  `closedCount` increases by one, the supervisor becomes idle and the age and the load are reset
  to zero.
* `tick`: while a command is active, its age is below the bound and the budget is at least one,
  the load increases by `2 * age + 1`, the age and `ticksTotal` increase by one, the budget becomes
  `budget - 1` and the energy increases by `rate`; if `slot + 1 = period`, the slot becomes zero
  and `rounds` increases by one, and otherwise the slot increases by one (no `/` or `%`).
* `timeout`: while a command is active and its age equals the bound, the active command is
  recorded in `timedOut` and cleared, its age is added to `ticksClosed`, `closedCount` increases
  by one, the supervisor becomes idle and the age and the load are reset to zero.

A structure update `{ s with … }` reads every right-hand side in the old state `s`; the Veil action
`tick` assigns `load` before `age`, and its `if` tests the slot, which no earlier assignment
changes, so both compute the same post-state.

The guard is any predicate on targets; for the planar two-link arm it is `planarGuard a b`
(MLS p. 95, eq. (3.12), through design row C04). A design model, not from MLS. -/
inductive Step (reachable : Target → Prop) (bound maxAttempts rate period : ℕ) :
    PlanarArmSchedulerSupervisor.State Target → PlanarArmSchedulerSupervisor.State Target → Prop
  /-- The planner requests `t` (Veil action `request`). -/
  | request (s : PlanarArmSchedulerSupervisor.State Target) (t : Target) :
      Step reachable bound maxAttempts rate period s { s with requested := insert t s.requested }
  /-- A requested target that satisfies the guard and is below the admission limit is commanded
  while the supervisor is idle; the load is reset to zero (Veil action `admit`). -/
  | admit (s : PlanarArmSchedulerSupervisor.State Target) (t : Target)
      (hrequested : t ∈ s.requested) (hreachable : reachable t) (hidle : s.busy = false)
      (hattempts : s.attempts t < maxAttempts) :
      Step reachable bound maxAttempts rate period s
        { s with requested := s.requested \ {t}, commanded := insert t s.commanded, busy := true,
                 age := 0, attempts := Function.update s.attempts t (s.attempts t + 1), load := 0 }
  /-- A requested target that fails the guard is rejected (Veil action `reject`). -/
  | reject (s : PlanarArmSchedulerSupervisor.State Target) (t : Target)
      (hrequested : t ∈ s.requested) (hunreachable : ¬ reachable t) :
      Step reachable bound maxAttempts rate period s
        { s with requested := s.requested \ {t}, rejected := insert t s.rejected }
  /-- The arm controller finishes the active command, which is counted as closed (Veil action
  `finish`). -/
  | finish (s : PlanarArmSchedulerSupervisor.State Target) (hbusy : s.busy = true) :
      Step reachable bound maxAttempts rate period s
        { s with commanded := ∅, busy := false, ticksClosed := s.ticksClosed + s.age, age := 0,
                 closedCount := s.closedCount + 1, load := 0 }
  /-- One clock tick while a command is active, below the age bound and with budget left; it
  charges the load and the energy and advances the slot, wrapping it around at `period` (Veil
  action `tick`). -/
  | tick (s : PlanarArmSchedulerSupervisor.State Target) (hbusy : s.busy = true)
      (hage : s.age < bound) (hbudget : 1 ≤ s.budget) :
      Step reachable bound maxAttempts rate period s
        { s with load := s.load + 2 * s.age + 1, age := s.age + 1, budget := s.budget - 1,
                 ticksTotal := s.ticksTotal + 1, energy := s.energy + rate,
                 rounds := if s.slot + 1 = period then s.rounds + 1 else s.rounds,
                 slot := if s.slot + 1 = period then 0 else s.slot + 1 }
  /-- The active command has reached the age bound, times out and is counted as closed (Veil
  action `timeout`). -/
  | timeout (s : PlanarArmSchedulerSupervisor.State Target) (hbusy : s.busy = true)
      (hage : s.age = bound) :
      Step reachable bound maxAttempts rate period s
        { s with timedOut := s.timedOut ∪ s.commanded, commanded := ∅, busy := false,
                 ticksClosed := s.ticksClosed + s.age, age := 0, closedCount := s.closedCount + 1,
                 load := 0 }

/-- The states of the wrap-around scheduler supervisor with guard `reachable`, age bound `bound`,
admission limit `maxAttempts`, tick capacity `capacity`, energy rate `rate` and scheduler period
`period` that some finite sequence of steps reaches from `PlanarArmSchedulerSupervisor.init
capacity`: the reflexive-transitive closure of `Step reachable bound maxAttempts rate period`. A
design model, not from MLS. -/
def ReachableState (reachable : Target → Prop) (bound maxAttempts capacity rate period : ℕ)
    (s : PlanarArmSchedulerSupervisor.State Target) : Prop :=
  Relation.ReflTransGen (Step reachable bound maxAttempts rate period)
    (PlanarArmSchedulerSupervisor.init capacity) s

/-- Every step of the wrap-around scheduler supervisor preserves the slot bound
`PlanarArmSchedulerSupervisor.SlotBounded`, for every `period`: `tick` sets the slot to zero when
`slot + 1 = period` (then `0 < period`) and to `slot + 1 < period` otherwise, and the other actions
leave it unchanged. The six cases are the counterparts of Veil's verification conditions
`<action>_slot_bounded`. Design row C17, not from MLS. -/
theorem Step.slotBounded {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : PlanarArmSchedulerSupervisor.State Target}
    (h : Step reachable bound maxAttempts rate period s s')
    (hs : PlanarArmSchedulerSupervisor.SlotBounded period s) :
    PlanarArmSchedulerSupervisor.SlotBounded period s' := by
  unfold PlanarArmSchedulerSupervisor.SlotBounded at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick =>
    show (if s.slot + 1 = period then 0 else s.slot + 1) < period
    split_ifs with hw <;> omega
  | timeout => exact hs

/-- Every step of the wrap-around scheduler supervisor preserves the round balance
`PlanarArmSchedulerSupervisor.RoundsBalance` (`period * rounds + slot = ticksTotal`), for every
`period`: when `tick` wraps, `period * (rounds + 1) + 0 = period * rounds + slot + 1` because
`slot + 1 = period`, and otherwise the slot and `ticksTotal` both increase by one; the other
actions change none of the three. The six cases are the counterparts of Veil's verification
conditions `<action>_rounds_balance`. Design row C17, not from MLS. -/
theorem Step.roundsBalance {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : PlanarArmSchedulerSupervisor.State Target}
    (h : Step reachable bound maxAttempts rate period s s')
    (hs : PlanarArmSchedulerSupervisor.RoundsBalance period s) :
    PlanarArmSchedulerSupervisor.RoundsBalance period s' := by
  unfold PlanarArmSchedulerSupervisor.RoundsBalance at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick =>
    show period * (if s.slot + 1 = period then s.rounds + 1 else s.rounds) +
        (if s.slot + 1 = period then 0 else s.slot + 1) = s.ticksTotal + 1
    split_ifs with hw
    · rw [Nat.mul_succ]
      omega
    · omega
  | timeout => exact hs

/-- **Supervisor invariant, slot bound.** For `1 ≤ period`, in every reachable state of the
wrap-around scheduler supervisor the slot of the clock is below the period. Proved by induction
over the steps from `PlanarArmSchedulerSupervisor.slotBounded_init` and `Step.slotBounded`. The
hypothesis `1 ≤ period` matches the Veil model's assumption `period ≥ 1`; for `period = 0` the
clause fails at the initial state. Design row C17, not from MLS. -/
theorem ReachableState.slotBounded {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (hperiod : 1 ≤ period) (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmSchedulerSupervisor.SlotBounded period s := by
  induction h with
  | refl => exact PlanarArmSchedulerSupervisor.slotBounded_init hperiod capacity
  | tail _ hstep ih => exact hstep.slotBounded ih

/-- **Supervisor invariant, round balance.** In every reachable state of the wrap-around scheduler
supervisor, for every `period`, `period * rounds + slot = ticksTotal`. Proved by induction over the
steps from `PlanarArmSchedulerSupervisor.roundsBalance_init` and `Step.roundsBalance`. Design row
C17, not from MLS. -/
theorem ReachableState.roundsBalance {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmSchedulerSupervisor.RoundsBalance period s := by
  induction h with
  | refl => exact PlanarArmSchedulerSupervisor.roundsBalance_init period capacity
  | tail _ hstep ih => exact hstep.roundsBalance ih

/-- **Recovered clause, slot phase.** For `1 ≤ period`, in every reachable state of the
wrap-around scheduler supervisor the slot is `ticksTotal % period`: the `%` clause of the
scheduler supervisor, which this supervisor neither computes nor states, follows from
`ReachableState.slotBounded` and `ReachableState.roundsBalance` by `slotPhase_of_roundsBalance`.
Design row C17, not from MLS. -/
theorem ReachableState.slotPhase {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (hperiod : 1 ≤ period) (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmSchedulerSupervisor.SlotPhase period s :=
  slotPhase_of_roundsBalance (h.slotBounded hperiod) h.roundsBalance

/-- **Recovered clause, round count.** For `1 ≤ period`, in every reachable state of the
wrap-around scheduler supervisor the completed periods are `ticksTotal / period`: the `/` clause
of the scheduler supervisor follows from `ReachableState.slotBounded` and
`ReachableState.roundsBalance` by `roundsCount_of_roundsBalance`. Design row C17, not from MLS. -/
theorem ReachableState.roundsCount {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (hperiod : 1 ≤ period) (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmSchedulerSupervisor.RoundsCount period s :=
  roundsCount_of_roundsBalance (h.slotBounded hperiod) h.roundsBalance

/-- **Step correspondence, one direction.** From a state whose slot is below the period, every
step of the wrap-around scheduler supervisor is the step of the same name of the scheduler
supervisor `PlanarArmSchedulerSupervisor` with the same guard, bound, admission limit, rate and
period: the two `tick` updates agree by `wrapSlot_eq_mod` and `wrapRounds_eq_add_div`, and the
other constructors are identical. Design row C17, not from MLS. -/
theorem Step.toSchedulerStep {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : PlanarArmSchedulerSupervisor.State Target}
    (hslot : PlanarArmSchedulerSupervisor.SlotBounded period s)
    (h : Step reachable bound maxAttempts rate period s s') :
    PlanarArmSchedulerSupervisor.Step reachable bound maxAttempts rate period s s' := by
  cases h with
  | request t => exact PlanarArmSchedulerSupervisor.Step.request s t
  | admit t hrequested hreachable hidle hattempts =>
    exact PlanarArmSchedulerSupervisor.Step.admit s t hrequested hreachable hidle hattempts
  | reject t hrequested hunreachable =>
    exact PlanarArmSchedulerSupervisor.Step.reject s t hrequested hunreachable
  | finish hbusy => exact PlanarArmSchedulerSupervisor.Step.finish s hbusy
  | tick hbusy hage hbudget =>
    rw [wrapRounds_eq_add_div hslot, wrapSlot_eq_mod hslot]
    exact PlanarArmSchedulerSupervisor.Step.tick s hbusy hage hbudget
  | timeout hbusy hage => exact PlanarArmSchedulerSupervisor.Step.timeout s hbusy hage

/-- **Step correspondence, other direction.** From a state whose slot is below the period, every
step of the scheduler supervisor `PlanarArmSchedulerSupervisor` is the step of the same name of
the wrap-around scheduler supervisor with the same parameters. Design row C17, not from MLS. -/
theorem Step.ofSchedulerStep {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : PlanarArmSchedulerSupervisor.State Target}
    (hslot : PlanarArmSchedulerSupervisor.SlotBounded period s)
    (h : PlanarArmSchedulerSupervisor.Step reachable bound maxAttempts rate period s s') :
    Step reachable bound maxAttempts rate period s s' := by
  cases h with
  | request t => exact Step.request s t
  | admit t hrequested hreachable hidle hattempts =>
    exact Step.admit s t hrequested hreachable hidle hattempts
  | reject t hrequested hunreachable => exact Step.reject s t hrequested hunreachable
  | finish hbusy => exact Step.finish s hbusy
  | tick hbusy hage hbudget =>
    rw [← wrapRounds_eq_add_div hslot, ← wrapSlot_eq_mod hslot]
    exact Step.tick s hbusy hage hbudget
  | timeout hbusy hage => exact Step.timeout s hbusy hage

/-- **Step correspondence.** On states whose slot is below the period, the step relation of the
wrap-around scheduler supervisor is the step relation of the scheduler supervisor
`PlanarArmSchedulerSupervisor` with the same guard, bound, admission limit, rate and period.
Design row C17, not from MLS. -/
theorem step_iff_schedulerStep {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : PlanarArmSchedulerSupervisor.State Target}
    (hslot : PlanarArmSchedulerSupervisor.SlotBounded period s) :
    Step reachable bound maxAttempts rate period s s' ↔
      PlanarArmSchedulerSupervisor.Step reachable bound maxAttempts rate period s s' :=
  ⟨Step.toSchedulerStep hslot, Step.ofSchedulerStep hslot⟩

/-- **Simulation into the scheduler supervisor.** For `1 ≤ period`, every reachable state of the
wrap-around scheduler supervisor is a reachable state of the scheduler supervisor
`PlanarArmSchedulerSupervisor` with the same guard, bound, admission limit, capacity, rate and
period. By induction over the steps from `Step.toSchedulerStep`, with `ReachableState.slotBounded`
at the state before each step. Through it the nine invariants of row C15 hold here. Design row
C17, not from MLS. -/
theorem ReachableState.toSchedulerReachableState {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (hperiod : 1 ≤ period) (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmSchedulerSupervisor.ReachableState reachable bound maxAttempts capacity rate period s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
    exact ih.tail (hstep.toSchedulerStep (ReachableState.slotBounded hperiod hreach))

/-- **Simulation from the scheduler supervisor.** For `1 ≤ period`, every reachable state of the
scheduler supervisor `PlanarArmSchedulerSupervisor` is a reachable state of the wrap-around
scheduler supervisor with the same parameters. By induction over the steps from
`Step.ofSchedulerStep`, with `PlanarArmSchedulerSupervisor.ReachableState.slotBounded` at the
state before each step. Design row C17, not from MLS. -/
theorem reachableState_of_schedulerReachableState {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (hperiod : 1 ≤ period)
    (h : PlanarArmSchedulerSupervisor.ReachableState reachable bound maxAttempts capacity rate
      period s) :
    ReachableState reachable bound maxAttempts capacity rate period s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
    exact ih.tail (Step.ofSchedulerStep
      (PlanarArmSchedulerSupervisor.ReachableState.slotBounded hperiod hreach) hstep)

/-- **Same reachable states.** For `1 ≤ period`, the wrap-around scheduler supervisor and the
scheduler supervisor `PlanarArmSchedulerSupervisor` with the same guard, bound, admission limit,
capacity, rate and period have the same reachable states. Design row C17, not from MLS. -/
theorem reachableState_iff_schedulerReachableState {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (hperiod : 1 ≤ period) :
    ReachableState reachable bound maxAttempts capacity rate period s ↔
      PlanarArmSchedulerSupervisor.ReachableState reachable bound maxAttempts capacity rate
        period s :=
  ⟨ReachableState.toSchedulerReachableState hperiod,
    reachableState_of_schedulerReachableState hperiod⟩

/-- **Simulation into the budget supervisor, one step.** For every `period`, forgetting
`closedCount`, `load`, `energy`, `slot` and `rounds`, each step of the wrap-around scheduler
supervisor is the step of the same name of the budget supervisor `PlanarArmBudgetSupervisor` with
the same guard, bound and admission limit (the scheduler adds no guard). Design row C18, not from
MLS. -/
theorem Step.toBudgetState {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : PlanarArmSchedulerSupervisor.State Target}
    (h : Step reachable bound maxAttempts rate period s s') :
    PlanarArmBudgetSupervisor.Step reachable bound maxAttempts s.toBudgetState
      s'.toBudgetState := by
  cases h with
  | request t => exact PlanarArmBudgetSupervisor.Step.request s.toBudgetState t
  | admit t hrequested hreachable hidle hattempts =>
    exact PlanarArmBudgetSupervisor.Step.admit s.toBudgetState t hrequested hreachable hidle
      hattempts
  | reject t hrequested hunreachable =>
    exact PlanarArmBudgetSupervisor.Step.reject s.toBudgetState t hrequested hunreachable
  | finish hbusy => exact PlanarArmBudgetSupervisor.Step.finish s.toBudgetState hbusy
  | tick hbusy hage hbudget =>
    exact PlanarArmBudgetSupervisor.Step.tick s.toBudgetState hbusy hage hbudget
  | timeout hbusy hage => exact PlanarArmBudgetSupervisor.Step.timeout s.toBudgetState hbusy hage

/-- **Simulation into the budget supervisor.** For every `period`, forgetting `closedCount`,
`load`, `energy`, `slot` and `rounds`, every reachable state of the wrap-around scheduler
supervisor with guard `reachable`, bound `bound`, admission limit `maxAttempts` and capacity
`capacity` is a reachable state of the budget supervisor `PlanarArmBudgetSupervisor` with the same
guard, bound, admission limit and capacity, so the six invariants of row C13 hold here. By
induction over the steps from `Step.toBudgetState`. Design row C18, not from MLS. -/
theorem ReachableState.toBudgetState {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : PlanarArmSchedulerSupervisor.State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmBudgetSupervisor.ReachableState reachable bound maxAttempts capacity
      s.toBudgetState := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.toBudgetState

open RoboLean.Examples

/-- **Refinement, targets with positions.** For positive link lengths `a, b`, all `bound`,
`maxAttempts`, `capacity`, `rate` and `period`, and a target type whose targets have tool
positions `pos t`, run the wrap-around scheduler supervisor with guard
`fun t => planarGuard a b (pos t)`. Then every target commanded in a reachable state is reached by
the planar two-link arm: some joint vector `q` puts the tool at `pos t`. From the simulation
`ReachableState.toBudgetState` and the budget supervisor's refinement
`PlanarArmBudgetSupervisor.ReachableState.exists_planarTwoLinkPosition_eq_pos` (row C14, through
C12, C10, C04 and C02, whose joint vectors come from the inverse kinematics of MLS p. 98,
eq. (3.16)); the reachable workspace is that of MLS p. 95, eq. (3.12). Design row C18, not from
MLS. Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq_pos {a b : ℝ}
    {bound maxAttempts capacity rate period : ℕ} (ha : 0 < a) (hb : 0 < b) (pos : Target → Vec3)
    {s : PlanarArmSchedulerSupervisor.State Target}
    (hs : ReachableState (fun t => planarGuard a b (pos t)) bound maxAttempts capacity rate period
      s)
    {t : Target} (ht : t ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = pos t :=
  hs.toBudgetState.exists_planarTwoLinkPosition_eq_pos ha hb pos ht

/-- **Refinement.** For positive link lengths `a, b` and all `bound`, `maxAttempts`, `capacity`,
`rate` and `period`, run the wrap-around scheduler supervisor over tool targets `x : Vec3` with
guard `planarGuard a b`. Then every target commanded in a reachable state is the tool position
`Examples.planarTwoLinkPosition a b q` of some joint vector `q`. From the simulation
`ReachableState.toBudgetState` and
`PlanarArmBudgetSupervisor.ReachableState.exists_planarTwoLinkPosition_eq` (row C14; MLS p. 98,
eq. (3.16), and the reachable workspace of MLS p. 95, eq. (3.12)). Design row C18, not from MLS.
Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq {a b : ℝ}
    {bound maxAttempts capacity rate period : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : PlanarArmSchedulerSupervisor.State Vec3}
    (hs : ReachableState (planarGuard a b) bound maxAttempts capacity rate period s) {x : Vec3}
    (hx : x ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x :=
  hs.toBudgetState.exists_planarTwoLinkPosition_eq ha hb hx

/-- **Refinement, workspace form.** For positive link lengths `a, b` and all `bound`,
`maxAttempts`, `capacity`, `rate` and `period`, in every reachable state of the wrap-around
scheduler supervisor over tool targets with guard `planarGuard a b`, the commanded targets lie in
the reachable workspace `W_R` of MLS eq. (3.12), printed p. 95, of `Examples.planarTwoLink a b`
with unrestricted joints (`Q = Set.univ`). From the simulation `ReachableState.toBudgetState` and
`PlanarArmBudgetSupervisor.ReachableState.commanded_subset_reachableWorkspace` (row C14). Design
row C18, not from MLS. Position reachability of the ideal model only. -/
theorem ReachableState.commanded_subset_reachableWorkspace {a b : ℝ}
    {bound maxAttempts capacity rate period : ℕ} (ha : 0 < a) (hb : 0 < b)
    {s : PlanarArmSchedulerSupervisor.State Vec3}
    (hs : ReachableState (planarGuard a b) bound maxAttempts capacity rate period s) :
    s.commanded ⊆ (planarTwoLink a b).reachableWorkspace Set.univ :=
  hs.toBudgetState.commanded_subset_reachableWorkspace ha hb

end PlanarArmWrapSchedulerSupervisor

end RoboLean.Design
