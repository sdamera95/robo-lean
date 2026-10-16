import RoboLean.Design.PlanarArmBudgetSupervisor

/-!
# A target supervisor with a round-robin scheduler for the planar two-link arm

This file extends the budget supervisor of `RoboLean.Design.PlanarArmBudgetSupervisor` (design
rows C13, C14) with five pieces of counting state:

* a count `closedCount` of the commands closed by `finish` or `timeout`;
* a quadratic load `load` of the active command: `admit`, `finish` and `timeout` reset it to zero,
  and `tick` adds `2 * age + 1`, so that it stays the square of the age;
* an energy counter `energy`, charged `rate` by every `tick`;
* a round-robin scheduler with period `period`: the slot `slot` of the clock advances by one at
  every `tick` and wraps around modulo `period`, and the count `rounds` of completed periods
  increases by one at each wrap (`rounds := rounds + (slot + 1) / period`,
  `slot := (slot + 1) % period`).

Every other component and action behaves exactly as in the budget supervisor; no new guard is
added. The file states the supervisor as a transition system over an abstract target type and
proves nine new invariants by induction over its steps (design row C15): the ticks spent by closed
commands are at most `bound` per closed command (`ReachableState.closedTicksBounded`, which needs
the age bound of the budget supervisor), the load is the square of the age
(`ReachableState.loadSquare`) and at most `bound * bound` (`ReachableState.loadBounded`), the
energy is `rate` times the ticks spent (`ReachableState.energyBalance`) and at most
`rate * capacity` (`ReachableState.energyBounded`, which needs the budget balance), the slot is
below the period (`ReachableState.slotBounded`, for `1 ≤ period`), the slot is the remainder of the
ticks spent modulo the period (`ReachableState.slotPhase`), the rounds are their quotient
(`ReachableState.roundsCount`, which needs the slot phase), and the rounds and the slot add up to
the ticks spent (`ReachableState.roundsBalance`). The six invariants of the budget supervisor are
not restated: for a reachable state `h`, they are `h.toBudgetState.commandedReachable`,
`h.toBudgetState.ageBounded`, `h.toBudgetState.idleAgeZero`, `h.toBudgetState.attemptsBounded`,
`h.toBudgetState.ticksBalance` and `h.toBudgetState.budgetBalance`. The file then shows that
forgetting the new components maps every step to a step of the same name of the budget supervisor
(`ReachableState.toBudgetState`), and carries the refinement of rows C10, C12 and C14 over: with
guard `planarGuard a b`, every commanded target is a tool position of the arm
(`ReachableState.exists_planarTwoLinkPosition_eq`, design row C16).

Division and remainder. Here `/` and `%` on `ℕ` are Lean's `Nat.div` and `Nat.mod`: truncated
division, with `n / 0 = 0` and `n % 0 = n`. A Veil model's actions are Lean code, so its `/` and `%`
on `Nat` are the same operations. Veil's SMT backend sends them to cvc5 as integer `div` and `mod`
through lean-smt's embedding lemmas `Int.natCast_ediv` and `Int.natCast_emod`, and in SMT-LIB
division by zero is unspecified; this is why the Veil model assumes `period ≥ 1` for every clause.
Here only `SlotBounded` needs `1 ≤ period`: the other three scheduler invariants (`SlotPhase`,
`RoundsCount`, `RoundsBalance`) hold for every `period` under Lean's conventions.

Correspondence with the Veil model. The same transition system is modelled in Veil, in the
sibling project `robo-lean-veil`, file `Examples/RoboLean/PlanarArmSchedulerSupervisor.lean`
(module `PlanarArmSchedulerSupervisor`), declaration by declaration: the fields of `State` mirror
Veil's state components, those of the budget supervisor through the parent projection
`State.toBudgetState` and the new individuals `closedCount`, `load`, `energy`, `slot` and
`rounds`; `init capacity` mirrors `after_init`; the constructors of `Step` mirror the actions
`request`, `admit`, `reject`, `finish`, `tick` and `timeout`; the parameters `bound`,
`maxAttempts`, `capacity`, `rate` and `period` mirror the immutable individuals of the same names;
the nine new clause predicates mirror the clauses `closed_ticks_bounded`, `load_square`,
`load_bounded`, `energy_balance`, `energy_bounded`, `slot_bounded`, `slot_phase`, `rounds_count`
and `rounds_balance`; the cases of the step lemmas are the counterparts of Veil's verification
conditions `<action>_<clause>`. The two projects run on different Lean versions (4.32.0 for Veil,
4.34.1 here) and cannot import each other, so the correspondence, and reading Veil's
uninterpreted `reachable` as `planarGuard a b`, are recorded conventions (see
`research/reports/veil-robotics-verification.md`), not kernel-checked links.

Sources. The guard is the annulus condition of the workspace certificate C04, which for positive
link lengths characterizes the reachable workspace `W_R = {p(θ) : θ ∈ Q}` of MLS eq. (3.12),
printed p. 95; the joint vectors come from the law-of-cosines inverse kinematics of MLS p. 98,
eq. (3.16) (row C02). The supervisor, its timeout, retry limit, budget, load, energy counter and
scheduler are a design model, not taken from MLS.

These statements concern the ideal transition system and the ideal position model of the arm.
The counters count abstract `tick`, `finish` and `timeout` steps, and `load` and `energy` are
numbers attached to them, not physical time, load or energy; nothing here says how often the
clock ticks, that a command finishes, times out or is ever admitted (liveness), that the scheduler
serves any task, or anything about the sampled implementation, sensing, the motion between
targets, orientation, joint limits, collisions or a physical arm.
-/

namespace RoboLean.Design

namespace PlanarArmSchedulerSupervisor

/-- The state of the scheduler supervisor over a target type `Target`: the state of the budget
supervisor `PlanarArmBudgetSupervisor.State` (pending requests, active command, rejected and
timed-out targets, whether a command is active, the age of the active command, the admission
counts, the remaining budget and the two tick counters), reached through the parent projection
`toBudgetState`, together with the count of closed commands, the load of the active command, the
energy charged, the slot of the clock and the completed scheduler periods. This mirrors the
mutable state of the Veil model `PlanarArmSchedulerSupervisor` (the components of the budget
supervisor and the individuals `closedCount`, `load`, `energy`, `slot`, `rounds : Nat`). A design
model, not from MLS. -/
structure State (Target : Type*) extends
    toBudgetState : PlanarArmBudgetSupervisor.State Target where
  /-- The commands closed by `finish` or `timeout`. -/
  closedCount : ℕ
  /-- The quadratic load of the active command. -/
  load : ℕ
  /-- The energy charged by all ticks. -/
  energy : ℕ
  /-- The round-robin slot of the clock. -/
  slot : ℕ
  /-- The completed scheduler periods. -/
  rounds : ℕ

/-- Build a state of the scheduler supervisor from a state of the budget supervisor and the five
new components (the anonymous constructor of `State`; Veil's `#gen_state` builds the corresponding
state structure). A design model, not from MLS. -/
add_decl_doc State.mk

/-- The state of the budget supervisor inside a state of the scheduler supervisor: forget
`closedCount`, `load`, `energy`, `slot` and `rounds`. This is the map of the simulation into the
budget supervisor (`ReachableState.toBudgetState`, design row C16). A design model, not from
MLS. -/
add_decl_doc State.toBudgetState

variable {Target : Type*}

/-- The initial state for the tick capacity `capacity`: the initial state
`PlanarArmBudgetSupervisor.init capacity` of the budget supervisor (no request, no command, no
rejection, no timeout, idle, age zero, no admission, the full budget, no tick spent), no closed
command, zero load, zero energy, slot zero and no completed period. This mirrors the `after_init`
block of the Veil model `PlanarArmSchedulerSupervisor`. A design model, not from MLS. -/
def init (capacity : ℕ) : State Target where
  toBudgetState := PlanarArmBudgetSupervisor.init capacity
  closedCount := 0
  load := 0
  energy := 0
  slot := 0
  rounds := 0

/-- The closed-tick bound: the ticks spent by closed commands are at most `bound` per closed
command. This mirrors the Veil clause
`safety [closed_ticks_bounded] ticksClosed ≤ bound * closedCount`. Design row C15; a design
statement, not from MLS. -/
def ClosedTicksBounded (bound : ℕ) (s : State Target) : Prop :=
  s.ticksClosed ≤ bound * s.closedCount

/-- The load square: the load of the active command is the square of its age. This mirrors the
Veil clause `invariant [load_square] load = age * age`. Design row C15; a design statement, not
from MLS. -/
def LoadSquare (s : State Target) : Prop :=
  s.load = s.age * s.age

/-- The load bound: the load of the active command is at most `bound * bound`. This mirrors the
Veil clause `safety [load_bounded] load ≤ bound * bound`. Design row C15; a design statement, not
from MLS. -/
def LoadBounded (bound : ℕ) (s : State Target) : Prop :=
  s.load ≤ bound * bound

/-- The energy balance: the energy charged is `rate` times the ticks spent. This mirrors the Veil
clause `invariant [energy_balance] energy = rate * ticksTotal`. Design row C15; a design
statement, not from MLS. -/
def EnergyBalance (rate : ℕ) (s : State Target) : Prop :=
  s.energy = rate * s.ticksTotal

/-- The energy bound: the energy charged is at most `rate * capacity`. This mirrors the Veil
clause `safety [energy_bounded] energy ≤ rate * capacity`. Design row C15; a design statement,
not from MLS. -/
def EnergyBounded (rate capacity : ℕ) (s : State Target) : Prop :=
  s.energy ≤ rate * capacity

/-- The slot bound: the slot of the clock is below the period. This mirrors the Veil clause
`safety [slot_bounded] slot < period`. Design row C15; a design statement, not from MLS. -/
def SlotBounded (period : ℕ) (s : State Target) : Prop :=
  s.slot < period

/-- The slot phase: the slot of the clock is the remainder of the ticks spent modulo the period
(Lean's `Nat.mod`, with `n % 0 = n`). This mirrors the Veil clause
`safety [slot_phase] ticksTotal % period = slot`. Design row C15; a design statement, not from
MLS. -/
def SlotPhase (period : ℕ) (s : State Target) : Prop :=
  s.ticksTotal % period = s.slot

/-- The round count: the completed periods are the quotient of the ticks spent by the period
(Lean's `Nat.div`, with `n / 0 = 0`). This mirrors the Veil clause
`safety [rounds_count] ticksTotal / period = rounds`. Design row C15; a design statement, not
from MLS. -/
def RoundsCount (period : ℕ) (s : State Target) : Prop :=
  s.ticksTotal / period = s.rounds

/-- The round balance: `period` times the completed periods plus the slot is the number of ticks
spent. This mirrors the Veil clause `invariant [rounds_balance] period * rounds + slot =
ticksTotal`. Design row C15; a design statement, not from MLS. -/
def RoundsBalance (period : ℕ) (s : State Target) : Prop :=
  period * s.rounds + s.slot = s.ticksTotal

/-- The initial state satisfies `ClosedTicksBounded`, since no tick has been spent. Counterpart
of Veil's verification condition `initializer_closed_ticks_bounded`. Design row C15, not from
MLS. -/
theorem closedTicksBounded_init (bound capacity : ℕ) :
    ClosedTicksBounded bound (init capacity : State Target) :=
  Nat.zero_le _

/-- The initial state satisfies `LoadSquare`, since its load and its age are zero. Counterpart of
Veil's verification condition `initializer_load_square`. Design row C15, not from MLS. -/
theorem loadSquare_init (capacity : ℕ) : LoadSquare (init capacity : State Target) :=
  rfl

/-- The initial state satisfies `LoadBounded`, since its load is zero. Counterpart of Veil's
verification condition `initializer_load_bounded`. Design row C15, not from MLS. -/
theorem loadBounded_init (bound capacity : ℕ) :
    LoadBounded bound (init capacity : State Target) :=
  Nat.zero_le _

/-- The initial state satisfies `EnergyBalance`, since no energy has been charged and no tick has
been spent. Counterpart of Veil's verification condition `initializer_energy_balance`. Design row
C15, not from MLS. -/
theorem energyBalance_init (rate capacity : ℕ) :
    EnergyBalance rate (init capacity : State Target) :=
  (Nat.mul_zero rate).symm

/-- The initial state satisfies `EnergyBounded`, since no energy has been charged. Counterpart of
Veil's verification condition `initializer_energy_bounded`. Design row C15, not from MLS. -/
theorem energyBounded_init (rate capacity : ℕ) :
    EnergyBounded rate capacity (init capacity : State Target) :=
  Nat.zero_le _

/-- For `1 ≤ period`, the initial state satisfies `SlotBounded`, since its slot is zero; for
`period = 0` the clause fails at the initial state. Counterpart of Veil's verification condition
`initializer_slot_bounded`, which assumes `period ≥ 1`. Design row C15, not from MLS. -/
theorem slotBounded_init {period : ℕ} (hperiod : 1 ≤ period) (capacity : ℕ) :
    SlotBounded period (init capacity : State Target) :=
  hperiod

/-- The initial state satisfies `SlotPhase` for every `period`, since `0 % period = 0`.
Counterpart of Veil's verification condition `initializer_slot_phase`. Design row C15, not from
MLS. -/
theorem slotPhase_init (period capacity : ℕ) : SlotPhase period (init capacity : State Target) :=
  Nat.zero_mod period

/-- The initial state satisfies `RoundsCount` for every `period`, since `0 / period = 0`.
Counterpart of Veil's verification condition `initializer_rounds_count`. Design row C15, not from
MLS. -/
theorem roundsCount_init (period capacity : ℕ) :
    RoundsCount period (init capacity : State Target) :=
  Nat.zero_div period

/-- The initial state satisfies `RoundsBalance` for every `period`, since its rounds, slot and
ticks spent are zero. Counterpart of Veil's verification condition `initializer_rounds_balance`.
Design row C15, not from MLS. -/
theorem roundsBalance_init (period capacity : ℕ) :
    RoundsBalance period (init capacity : State Target) :=
  Nat.mul_zero period

variable [DecidableEq Target]

/-- One step of the scheduler supervisor with guard `reachable`, age bound `bound`, admission
limit `maxAttempts`, energy rate `rate` and scheduler period `period`; each constructor mirrors
the action of the same name in the Veil model `PlanarArmSchedulerSupervisor`, with its `require`
clauses as hypotheses. The guards are those of the budget supervisor: the five new components are
updated but never tested.

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
  `budget - 1`, the energy increases by `rate`, `rounds` increases by `(slot + 1) / period` and the
  slot becomes `(slot + 1) % period`.
* `timeout`: while a command is active and its age equals the bound, the active command is
  recorded in `timedOut` and cleared, its age is added to `ticksClosed`, `closedCount` increases
  by one, the supervisor becomes idle and the age and the load are reset to zero.

A structure update `{ s with … }` reads every right-hand side in the old state `s`, so in `tick`
the load uses the old age and `rounds` the old slot. The Veil action assigns `load` before `age`
and `rounds` before `slot`, and Veil executes the assignments in order, so both compute the same
post-state.

The guard is any predicate on targets; for the planar two-link arm it is `planarGuard a b`
(MLS p. 95, eq. (3.12), through design row C04). A design model, not from MLS. -/
inductive Step (reachable : Target → Prop) (bound maxAttempts rate period : ℕ) :
    State Target → State Target → Prop
  /-- The planner requests `t` (Veil action `request`). -/
  | request (s : State Target) (t : Target) :
      Step reachable bound maxAttempts rate period s { s with requested := insert t s.requested }
  /-- A requested target that satisfies the guard and is below the admission limit is commanded
  while the supervisor is idle; the load is reset to zero (Veil action `admit`). -/
  | admit (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hreachable : reachable t) (hidle : s.busy = false) (hattempts : s.attempts t < maxAttempts) :
      Step reachable bound maxAttempts rate period s
        { s with requested := s.requested \ {t}, commanded := insert t s.commanded, busy := true,
                 age := 0, attempts := Function.update s.attempts t (s.attempts t + 1), load := 0 }
  /-- A requested target that fails the guard is rejected (Veil action `reject`). -/
  | reject (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hunreachable : ¬ reachable t) :
      Step reachable bound maxAttempts rate period s
        { s with requested := s.requested \ {t}, rejected := insert t s.rejected }
  /-- The arm controller finishes the active command, which is counted as closed (Veil action
  `finish`). -/
  | finish (s : State Target) (hbusy : s.busy = true) :
      Step reachable bound maxAttempts rate period s
        { s with commanded := ∅, busy := false, ticksClosed := s.ticksClosed + s.age, age := 0,
                 closedCount := s.closedCount + 1, load := 0 }
  /-- One clock tick while a command is active, below the age bound and with budget left; it
  charges the load, the energy and the scheduler (Veil action `tick`). -/
  | tick (s : State Target) (hbusy : s.busy = true) (hage : s.age < bound)
      (hbudget : 1 ≤ s.budget) :
      Step reachable bound maxAttempts rate period s
        { s with load := s.load + 2 * s.age + 1, age := s.age + 1, budget := s.budget - 1,
                 ticksTotal := s.ticksTotal + 1, energy := s.energy + rate,
                 rounds := s.rounds + (s.slot + 1) / period, slot := (s.slot + 1) % period }
  /-- The active command has reached the age bound, times out and is counted as closed (Veil
  action `timeout`). -/
  | timeout (s : State Target) (hbusy : s.busy = true) (hage : s.age = bound) :
      Step reachable bound maxAttempts rate period s
        { s with timedOut := s.timedOut ∪ s.commanded, commanded := ∅, busy := false,
                 ticksClosed := s.ticksClosed + s.age, age := 0, closedCount := s.closedCount + 1,
                 load := 0 }

/-- The states of the scheduler supervisor with guard `reachable`, age bound `bound`, admission
limit `maxAttempts`, tick capacity `capacity`, energy rate `rate` and scheduler period `period`
that some finite sequence of steps reaches from `init capacity`: the reflexive-transitive closure
of `Step reachable bound maxAttempts rate period` from `init capacity`. A design model, not from
MLS. -/
def ReachableState (reachable : Target → Prop) (bound maxAttempts capacity rate period : ℕ)
    (s : State Target) : Prop :=
  Relation.ReflTransGen (Step reachable bound maxAttempts rate period) (init capacity) s

/-- **Simulation, one step.** Forgetting `closedCount`, `load`, `energy`, `slot` and `rounds`,
each step of the scheduler supervisor is the step of the same name of the budget supervisor
`PlanarArmBudgetSupervisor` with the same guard, bound and admission limit (the scheduler adds no
guard). Design row C16, not from MLS. -/
theorem Step.toBudgetState {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s') :
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

/-- **Simulation.** Forgetting `closedCount`, `load`, `energy`, `slot` and `rounds`, every
reachable state of the scheduler supervisor with guard `reachable`, bound `bound`, admission limit
`maxAttempts`, capacity `capacity` and any rate and period is a reachable state of the budget
supervisor `PlanarArmBudgetSupervisor` with the same guard, bound, admission limit and capacity.
By induction over the steps from `Step.toBudgetState`. Design row C16, not from MLS. -/
theorem ReachableState.toBudgetState {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    PlanarArmBudgetSupervisor.ReachableState reachable bound maxAttempts capacity
      s.toBudgetState := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.toBudgetState

/-- Every step of the scheduler supervisor from a state whose age is at most `bound` preserves
`ClosedTicksBounded`: `finish` and `timeout` add the age, at most `bound`, to `ticksClosed` and
one to `closedCount`, and the other actions change neither. The six cases are the counterparts of
Veil's verification conditions `<action>_closed_ticks_bounded`. Design row C15, not from MLS. -/
theorem Step.closedTicksBounded {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hage : PlanarArmBudgetSupervisor.AgeBounded bound s.toBudgetState)
    (hs : ClosedTicksBounded bound s) : ClosedTicksBounded bound s' := by
  unfold PlanarArmBudgetSupervisor.AgeBounded at hage
  unfold ClosedTicksBounded at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish =>
    simp only
    rw [Nat.mul_succ]
    omega
  | tick => exact hs
  | timeout =>
    simp only
    rw [Nat.mul_succ]
    omega

/-- Every step of the scheduler supervisor preserves `LoadSquare`: `tick` adds `2 * age + 1` to
the load, which turns `age * age` into `(age + 1) * (age + 1)`, `admit`, `finish` and `timeout`
reset the load and the age to zero, and `request` and `reject` change neither. The six cases are
the counterparts of Veil's verification conditions `<action>_load_square`. Design row C15, not
from MLS. -/
theorem Step.loadSquare {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hs : LoadSquare s) : LoadSquare s' := by
  unfold LoadSquare at hs ⊢
  cases h with
  | request => exact hs
  | admit => rfl
  | reject => exact hs
  | finish => rfl
  | tick =>
    simp only
    rw [hs]
    ring
  | timeout => rfl

/-- Every step of the scheduler supervisor from a state with `LoadSquare` preserves
`LoadBounded`: after `tick` the load is `(age + 1) * (age + 1)` with `age < bound`, `admit`,
`finish` and `timeout` reset the load to zero, and `request` and `reject` leave it unchanged. The
six cases are the counterparts of Veil's verification conditions `<action>_load_bounded`. Design
row C15, not from MLS. -/
theorem Step.loadBounded {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hsq : LoadSquare s) (hs : LoadBounded bound s) : LoadBounded bound s' := by
  unfold LoadSquare at hsq
  unfold LoadBounded at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact Nat.zero_le _
  | reject => exact hs
  | finish => exact Nat.zero_le _
  | tick _ hage _ =>
    show s.load + 2 * s.age + 1 ≤ bound * bound
    have h1 : s.load + 2 * s.age + 1 = (s.age + 1) * (s.age + 1) := by
      rw [hsq]
      ring
    rw [h1]
    exact Nat.mul_le_mul hage hage
  | timeout => exact Nat.zero_le _

/-- Every step of the scheduler supervisor preserves `EnergyBalance`: `tick` adds `rate` to the
energy and one to `ticksTotal`, and the other actions change neither. The six cases are the
counterparts of Veil's verification conditions `<action>_energy_balance`. Design row C15, not from
MLS. -/
theorem Step.energyBalance {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hs : EnergyBalance rate s) : EnergyBalance rate s' := by
  unfold EnergyBalance at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick =>
    simp only
    rw [hs, Nat.mul_succ]
  | timeout => exact hs

/-- Every step of the scheduler supervisor from a state with `EnergyBalance` and the budget
balance of the budget supervisor preserves `EnergyBounded`: `tick` fires only with `1 ≤ budget`,
so `ticksTotal + 1 ≤ capacity` and the new energy `rate * (ticksTotal + 1)` is at most
`rate * capacity`, and the other actions leave the energy unchanged. The six cases are the
counterparts of Veil's verification conditions `<action>_energy_bounded`, which assume all
clauses. Design row C15, not from MLS. -/
theorem Step.energyBounded {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {capacity : ℕ} {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hbal : EnergyBalance rate s)
    (hbud : PlanarArmBudgetSupervisor.BudgetBalance capacity s.toBudgetState)
    (hs : EnergyBounded rate capacity s) : EnergyBounded rate capacity s' := by
  unfold EnergyBalance at hbal
  unfold PlanarArmBudgetSupervisor.BudgetBalance at hbud
  unfold EnergyBounded at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick _ _ hbudget =>
    show s.energy + rate ≤ rate * capacity
    have h1 : s.ticksTotal + 1 ≤ capacity := by
      change s.budget + s.ticksTotal = capacity at hbud
      omega
    rw [hbal, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left rate h1
  | timeout => exact hs

/-- For `1 ≤ period`, every step of the scheduler supervisor preserves `SlotBounded`: `tick` sets
the slot to `(slot + 1) % period`, which is below `period`, and the other actions leave it
unchanged. The six cases are the counterparts of Veil's verification conditions
`<action>_slot_bounded`; the hypothesis `1 ≤ period` matches the Veil model's assumption
`period ≥ 1`. Design row C15, not from MLS. -/
theorem Step.slotBounded {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (hperiod : 1 ≤ period)
    (h : Step reachable bound maxAttempts rate period s s') (hs : SlotBounded period s) :
    SlotBounded period s' := by
  unfold SlotBounded at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick => exact Nat.mod_lt _ hperiod
  | timeout => exact hs

/-- Every step of the scheduler supervisor preserves `SlotPhase`, for every `period`: `tick` sets
the slot to `(slot + 1) % period` and adds one to `ticksTotal`, and
`(ticksTotal % period + 1) % period = (ticksTotal + 1) % period` (`Nat.mod_add_mod`, which holds
also for `period = 0`); the other actions change neither. The six cases are the counterparts of
Veil's verification conditions `<action>_slot_phase`. Design row C15, not from MLS. -/
theorem Step.slotPhase {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hs : SlotPhase period s) : SlotPhase period s' := by
  unfold SlotPhase at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick =>
    show (s.ticksTotal + 1) % period = (s.slot + 1) % period
    rw [← hs, Nat.mod_add_mod]
  | timeout => exact hs

/-- Every step of the scheduler supervisor from a state with `SlotPhase` preserves `RoundsCount`,
for every `period`: by `SlotPhase` and `RoundsCount`, `ticksTotal = period * rounds + slot`, so
for `0 < period` the new quotient `(ticksTotal + 1) / period` is `rounds + (slot + 1) / period`
(`Nat.mul_add_div`), and for `period = 0` both sides are zero; the other actions change neither
`ticksTotal` nor `rounds`. The six cases are the counterparts of Veil's verification conditions
`<action>_rounds_count`. Design row C15, not from MLS. -/
theorem Step.roundsCount {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hphase : SlotPhase period s) (hs : RoundsCount period s) : RoundsCount period s' := by
  unfold SlotPhase at hphase
  unfold RoundsCount at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick =>
    show (s.ticksTotal + 1) / period = s.rounds + (s.slot + 1) / period
    rcases Nat.eq_zero_or_pos period with hp | hp
    · subst hp
      simp only [Nat.div_zero] at hs ⊢
      exact hs
    · have h1 : s.ticksTotal + 1 = period * s.rounds + (s.slot + 1) := by
        have := Nat.div_add_mod s.ticksTotal period
        rw [hs, hphase] at this
        omega
      rw [h1, Nat.mul_add_div hp]
  | timeout => exact hs

/-- Every step of the scheduler supervisor preserves `RoundsBalance`, for every `period`: `tick`
adds `(slot + 1) / period` to `rounds` and replaces the slot by `(slot + 1) % period`, and
`period * ((slot + 1) / period) + (slot + 1) % period = slot + 1` (`Nat.div_add_mod`, which holds
also for `period = 0`), so the left side grows by one together with `ticksTotal`; the other actions
change none of the three. The six cases are the counterparts of Veil's verification conditions
`<action>_rounds_balance`. Design row C15, not from MLS. -/
theorem Step.roundsBalance {reachable : Target → Prop} {bound maxAttempts rate period : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts rate period s s')
    (hs : RoundsBalance period s) : RoundsBalance period s' := by
  unfold RoundsBalance at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick =>
    show period * (s.rounds + (s.slot + 1) / period) + (s.slot + 1) % period = s.ticksTotal + 1
    have h1 := Nat.div_add_mod (s.slot + 1) period
    rw [Nat.mul_add]
    omega
  | timeout => exact hs

/-- **Supervisor invariant, closed ticks.** In every reachable state of the scheduler supervisor,
the ticks spent by closed commands are at most `bound` times the number of closed commands.
Proved by induction over the steps from `closedTicksBounded_init` and `Step.closedTicksBounded`,
with the age bound `PlanarArmBudgetSupervisor.ReachableState.ageBounded` at the state before each
step (through `ReachableState.toBudgetState`). Design row C15, not from MLS. -/
theorem ReachableState.closedTicksBounded {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    ClosedTicksBounded bound s := by
  induction h with
  | refl => exact closedTicksBounded_init bound capacity
  | tail hreach hstep ih =>
    exact hstep.closedTicksBounded (ReachableState.toBudgetState hreach).ageBounded ih

/-- **Supervisor invariant, load square.** In every reachable state of the scheduler supervisor,
the load of the active command is the square of its age. Proved by induction over the steps from
`loadSquare_init` and `Step.loadSquare`. Design row C15, not from MLS. -/
theorem ReachableState.loadSquare {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) : LoadSquare s := by
  induction h with
  | refl => exact loadSquare_init capacity
  | tail _ hstep ih => exact hstep.loadSquare ih

/-- **Supervisor invariant, load bound.** In every reachable state of the scheduler supervisor,
the load of the active command is at most `bound * bound`. Proved by induction over the steps from
`loadBounded_init` and `Step.loadBounded`, with `ReachableState.loadSquare` at the state before
each step. Design row C15, not from MLS. -/
theorem ReachableState.loadBounded {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    LoadBounded bound s := by
  induction h with
  | refl => exact loadBounded_init bound capacity
  | tail hreach hstep ih => exact hstep.loadBounded (ReachableState.loadSquare hreach) ih

/-- **Supervisor invariant, energy balance.** In every reachable state of the scheduler
supervisor, the energy charged is `rate` times the ticks spent. Proved by induction over the steps
from `energyBalance_init` and `Step.energyBalance`. Design row C15, not from MLS. -/
theorem ReachableState.energyBalance {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    EnergyBalance rate s := by
  induction h with
  | refl => exact energyBalance_init rate capacity
  | tail _ hstep ih => exact hstep.energyBalance ih

/-- **Supervisor invariant, energy bound.** In every reachable state of the scheduler supervisor
with capacity `capacity`, the energy charged is at most `rate * capacity`. Proved by induction
over the steps from `energyBounded_init` and `Step.energyBounded`, with
`ReachableState.energyBalance` and the budget balance
`PlanarArmBudgetSupervisor.ReachableState.budgetBalance` at the state before each step (through
`ReachableState.toBudgetState`). Design row C15, not from MLS. -/
theorem ReachableState.energyBounded {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    EnergyBounded rate capacity s := by
  induction h with
  | refl => exact energyBounded_init rate capacity
  | tail hreach hstep ih =>
    exact hstep.energyBounded (ReachableState.energyBalance hreach)
      (ReachableState.toBudgetState hreach).budgetBalance ih

/-- **Supervisor invariant, slot bound.** For `1 ≤ period`, in every reachable state of the
scheduler supervisor the slot of the clock is below the period. Proved by induction over the
steps from `slotBounded_init` and `Step.slotBounded`. The hypothesis `1 ≤ period` matches the
Veil model's assumption `period ≥ 1`; for `period = 0` the clause already fails at the initial
state. Design row C15, not from MLS. -/
theorem ReachableState.slotBounded {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target} (hperiod : 1 ≤ period)
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    SlotBounded period s := by
  induction h with
  | refl => exact slotBounded_init hperiod capacity
  | tail _ hstep ih => exact hstep.slotBounded hperiod ih

/-- **Supervisor invariant, slot phase.** In every reachable state of the scheduler supervisor,
for every `period`, the slot of the clock is `ticksTotal % period`. Proved by induction over the
steps from `slotPhase_init` and `Step.slotPhase`. Design row C15, not from MLS. -/
theorem ReachableState.slotPhase {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    SlotPhase period s := by
  induction h with
  | refl => exact slotPhase_init period capacity
  | tail _ hstep ih => exact hstep.slotPhase ih

/-- **Supervisor invariant, round count.** In every reachable state of the scheduler supervisor,
for every `period`, the completed periods are `ticksTotal / period`. Proved by induction over the
steps from `roundsCount_init` and `Step.roundsCount`, with `ReachableState.slotPhase` at the state
before each step. Design row C15, not from MLS. -/
theorem ReachableState.roundsCount {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    RoundsCount period s := by
  induction h with
  | refl => exact roundsCount_init period capacity
  | tail hreach hstep ih => exact hstep.roundsCount (ReachableState.slotPhase hreach) ih

/-- **Supervisor invariant, round balance.** In every reachable state of the scheduler
supervisor, for every `period`, `period * rounds + slot = ticksTotal`. Proved by induction over
the steps from `roundsBalance_init` and `Step.roundsBalance`. Design row C15, not from MLS. -/
theorem ReachableState.roundsBalance {reachable : Target → Prop}
    {bound maxAttempts capacity rate period : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity rate period s) :
    RoundsBalance period s := by
  induction h with
  | refl => exact roundsBalance_init period capacity
  | tail _ hstep ih => exact hstep.roundsBalance ih

open RoboLean.Examples

/-- **Refinement, targets with positions.** For positive link lengths `a, b`, all `bound`,
`maxAttempts`, `capacity`, `rate` and `period`, and a target type whose targets have tool
positions `pos t`, run the scheduler supervisor with guard `fun t => planarGuard a b (pos t)`.
Then every target commanded in a reachable state is reached by the planar two-link arm: some joint
vector `q` puts the tool at `pos t`. From the simulation `ReachableState.toBudgetState` and the
budget supervisor's refinement
`PlanarArmBudgetSupervisor.ReachableState.exists_planarTwoLinkPosition_eq_pos` (row C14, through
C12, C10, C04 and C02, whose joint vectors come from the inverse kinematics of MLS p. 98,
eq. (3.16)); the reachable workspace is that of MLS p. 95, eq. (3.12). Design row C16, not from
MLS. Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq_pos {a b : ℝ}
    {bound maxAttempts capacity rate period : ℕ} (ha : 0 < a) (hb : 0 < b) (pos : Target → Vec3)
    {s : State Target}
    (hs : ReachableState (fun t => planarGuard a b (pos t)) bound maxAttempts capacity rate period
      s)
    {t : Target} (ht : t ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = pos t :=
  hs.toBudgetState.exists_planarTwoLinkPosition_eq_pos ha hb pos ht

/-- **Refinement.** For positive link lengths `a, b` and all `bound`, `maxAttempts`, `capacity`,
`rate` and `period`, run the scheduler supervisor over tool targets `x : Vec3` with guard
`planarGuard a b`. Then every target commanded in a reachable state is the tool position
`Examples.planarTwoLinkPosition a b q` of some joint vector `q`. From the simulation
`ReachableState.toBudgetState` and
`PlanarArmBudgetSupervisor.ReachableState.exists_planarTwoLinkPosition_eq` (row C14; MLS p. 98,
eq. (3.16), and the reachable workspace of MLS p. 95, eq. (3.12)). Design row C16, not from MLS.
Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq {a b : ℝ}
    {bound maxAttempts capacity rate period : ℕ} (ha : 0 < a) (hb : 0 < b) {s : State Vec3}
    (hs : ReachableState (planarGuard a b) bound maxAttempts capacity rate period s) {x : Vec3}
    (hx : x ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x :=
  hs.toBudgetState.exists_planarTwoLinkPosition_eq ha hb hx

/-- **Refinement, workspace form.** For positive link lengths `a, b` and all `bound`,
`maxAttempts`, `capacity`, `rate` and `period`, in every reachable state of the scheduler
supervisor over tool targets with guard `planarGuard a b`, the commanded targets lie in the
reachable workspace `W_R` of MLS eq. (3.12), printed p. 95, of `Examples.planarTwoLink a b` with
unrestricted joints (`Q = Set.univ`). From the simulation `ReachableState.toBudgetState` and
`PlanarArmBudgetSupervisor.ReachableState.commanded_subset_reachableWorkspace` (row C14). Design
row C16, not from MLS. Position reachability of the ideal model only. -/
theorem ReachableState.commanded_subset_reachableWorkspace {a b : ℝ}
    {bound maxAttempts capacity rate period : ℕ} (ha : 0 < a) (hb : 0 < b) {s : State Vec3}
    (hs : ReachableState (planarGuard a b) bound maxAttempts capacity rate period s) :
    s.commanded ⊆ (planarTwoLink a b).reachableWorkspace Set.univ :=
  hs.toBudgetState.commanded_subset_reachableWorkspace ha hb

end PlanarArmSchedulerSupervisor

end RoboLean.Design
