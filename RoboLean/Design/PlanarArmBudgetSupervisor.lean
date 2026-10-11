import RoboLean.Design.PlanarArmTimeoutSupervisor

/-!
# A target supervisor with a retry limit and a tick budget for the planar two-link arm

This file extends the timeout supervisor of `RoboLean.Design.PlanarArmTimeoutSupervisor` (design
rows C11, C12) with three pieces of counting state:

* a per-target admission count `attempts : Target → ℕ` with a limit `maxAttempts`: `admit t`
  requires `attempts t < maxAttempts` and increments `attempts t`;
* two tick counters, `ticksTotal` (ticks spent by all commands) and `ticksClosed` (ticks spent by
  commands that have finished or timed out): `tick` increments `ticksTotal`, and `finish` and
  `timeout` add the age of the active command to `ticksClosed`;
* a tick budget `budget`, which starts at a capacity `capacity`: `tick` requires `1 ≤ budget` and
  replaces `budget` by the truncated difference `budget - 1`.

Every other component and action behaves exactly as in the timeout supervisor. The file states
the supervisor as a transition system over an abstract target type and proves six invariants by
induction over its steps (design row C13): the three of the timeout supervisor (every commanded
target satisfies the guard, the age is at most the bound, an idle supervisor has age zero), no
target is admitted more than `maxAttempts` times (`ReachableState.attemptsBounded`), every tick
spent belongs to a closed command or to the active one (`ReachableState.ticksBalance`, which needs
the idle-age invariant), and the remaining budget and the ticks spent add up to the capacity
(`ReachableState.budgetBalance`, which needs the guard `1 ≤ budget` because `ℕ` subtraction
truncates). It then shows that forgetting the new components maps every step to a step of the
same name of the timeout supervisor (`ReachableState.toTimeoutState`), and carries the refinement
of rows C10 and C12 over: with guard `planarGuard a b`, every commanded target is a tool position
of the arm (`ReachableState.exists_planarTwoLinkPosition_eq`, design row C14).

Correspondence with the Veil model. The same transition system is modelled in Veil, in the
sibling project `robo-lean-veil`, file `Examples/RoboLean/PlanarArmBudgetSupervisor.lean`,
declaration by declaration: the fields of `State` mirror Veil's `requested`, `commanded`,
`rejected`, `timedOut`, `busy`, `age` (inherited from the timeout supervisor's state through the
parent projection `State.toTimeoutState`), `attempts`, `budget`, `ticksTotal` and `ticksClosed`;
`init capacity` mirrors `after_init`; the constructors of `Step` mirror the actions `request`,
`admit`, `reject`, `finish`, `tick` and `timeout`; the parameters `bound`, `maxAttempts` and
`capacity` mirror the immutable individuals of the same names; the six clause predicates mirror
the clauses `commanded_reachable`, `age_bounded`, `idle_age_zero`, `attempts_bounded`,
`ticks_balance` and `budget_balance`; the cases of the step lemmas are the counterparts of Veil's
verification conditions `<action>_<clause>`. A Veil relation `r : target → Bool` is a Lean set,
with `t ∈ s.r` read as `r t = true`; a Veil `function attempts : target → Nat` is a Lean function
`Target → ℕ`, and its update `attempts t := attempts t + 1` is `Function.update`, which needs
`[DecidableEq Target]` (Veil's generated theorems carry `DecidableEq target` too); Veil's `Nat`,
including its truncated subtraction, is Lean's `ℕ`. The two projects run on different Lean versions
(4.32.0 for Veil, 4.34.1 here) and cannot import each other, so the correspondence, and reading
Veil's uninterpreted `reachable` as `planarGuard a b`, are recorded conventions (decision D003,
entries E018, E022 and E027), not kernel-checked links.

Sources. The guard is the annulus condition of the workspace certificate C04, which for positive
link lengths characterizes the reachable workspace `W_R = {p(θ) : θ ∈ Q}` of MLS eq. (3.12),
printed p. 95; the joint vectors come from the law-of-cosines inverse kinematics of MLS p. 98,
eq. (3.16) (row C02). The supervisor, its timeout, its retry limit and its budget are a design
model, not taken from MLS.

These statements concern the ideal transition system and the ideal position model of the arm.
The counters count abstract `tick` and `admit` steps, not physical time or energy; nothing here
says how often the clock ticks, that a command finishes, times out or is ever admitted (liveness),
or anything about the sampled implementation, sensing, the motion between targets, orientation,
joint limits, collisions or a physical arm.
-/

namespace RoboLean.Design

namespace PlanarArmBudgetSupervisor

/-- The state of the budget supervisor over a target type `Target`: the state of the timeout
supervisor `PlanarArmTimeoutSupervisor.State` (pending requests, active command, rejected and
timed-out targets, whether a command is active, the age of the active command), reached through
the parent projection `toTimeoutState`, together with the admission count of each target, the
remaining tick budget, the ticks spent by all commands and the ticks spent by closed commands.
This mirrors the mutable state of the Veil model `PlanarArmBudgetSupervisor` (relations
`requested`, `commanded`, `rejected`, `timedOut : target → Bool`, individuals `busy : Bool`,
`age`, `budget`, `ticksTotal`, `ticksClosed : Nat`, function `attempts : target → Nat`); a Veil
relation is a Lean set, `t ∈ s.timedOut` read as `timedOut t = true`. A design model, not from
MLS. -/
structure State (Target : Type*) extends
    toTimeoutState : PlanarArmTimeoutSupervisor.State Target where
  /-- How often each target has been admitted. -/
  attempts : Target → ℕ
  /-- The ticks still available. -/
  budget : ℕ
  /-- The ticks spent by all commands. -/
  ticksTotal : ℕ
  /-- The ticks spent by commands that have finished or timed out. -/
  ticksClosed : ℕ

/-- Build a state of the budget supervisor from a state of the timeout supervisor and the four
counting components (the anonymous constructor of `State`; Veil's `#gen_state` builds the
corresponding state structure). A design model, not from MLS. -/
add_decl_doc State.mk

/-- The state of the timeout supervisor inside a state of the budget supervisor: forget
`attempts`, `budget`, `ticksTotal` and `ticksClosed`. This is the map of the simulation into the
timeout supervisor (`ReachableState.toTimeoutState`, design row C14). A design model, not from
MLS. -/
add_decl_doc State.toTimeoutState

variable {Target : Type*}

/-- The initial state for the tick capacity `capacity`: no request, no command, no rejection, no
timeout, idle, age zero, no admission, the full budget `capacity`, no tick spent. This mirrors the
`after_init` block of the Veil model `PlanarArmBudgetSupervisor`, where `budget := capacity` reads
the immutable individual `capacity`. A design model, not from MLS. -/
def init (capacity : ℕ) : State Target where
  requested := ∅
  commanded := ∅
  rejected := ∅
  busy := false
  timedOut := ∅
  age := 0
  attempts := fun _ => 0
  budget := capacity
  ticksTotal := 0
  ticksClosed := 0

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

/-- The retry limit: no target has been admitted more than `maxAttempts` times. This mirrors the
Veil clause `safety [attempts_bounded] attempts T ≤ maxAttempts`, whose capital `T` is
universally quantified. A design statement, not from MLS. -/
def AttemptsBounded (maxAttempts : ℕ) (s : State Target) : Prop :=
  ∀ t, s.attempts t ≤ maxAttempts

/-- The tick balance: the ticks spent by closed commands and the age of the active command add up
to the ticks spent by all commands. This mirrors the Veil clause
`safety [ticks_balance] ticksClosed + age = ticksTotal`. A design statement, not from MLS. -/
def TicksBalance (s : State Target) : Prop :=
  s.ticksClosed + s.age = s.ticksTotal

/-- The budget balance: the remaining budget and the ticks spent add up to the capacity. This
mirrors the Veil clause `safety [budget_balance] budget + ticksTotal = capacity`. A design
statement, not from MLS. -/
def BudgetBalance (capacity : ℕ) (s : State Target) : Prop :=
  s.budget + s.ticksTotal = capacity

/-- The initial state satisfies `CommandedReachable`, since nothing is commanded. Counterpart of
Veil's verification condition `initializer_commanded_reachable`. Design row C13, not from MLS. -/
theorem commandedReachable_init (reachable : Target → Prop) (capacity : ℕ) :
    CommandedReachable reachable (init capacity : State Target) := by
  intro t ht
  simp [init] at ht

/-- The initial state satisfies `AgeBounded`, since its age is zero. Counterpart of Veil's
verification condition `initializer_age_bounded`. Design row C13, not from MLS. -/
theorem ageBounded_init (bound capacity : ℕ) : AgeBounded bound (init capacity : State Target) :=
  Nat.zero_le bound

/-- The initial state satisfies `IdleAgeZero`, since its age is zero. Counterpart of Veil's
verification condition `initializer_idle_age_zero`. Design row C13, not from MLS. -/
theorem idleAgeZero_init (capacity : ℕ) : IdleAgeZero (init capacity : State Target) :=
  fun _ => rfl

/-- The initial state satisfies `AttemptsBounded`, since no target has been admitted.
Counterpart of Veil's verification condition `initializer_attempts_bounded`. Design row C13, not
from MLS. -/
theorem attemptsBounded_init (maxAttempts capacity : ℕ) :
    AttemptsBounded maxAttempts (init capacity : State Target) :=
  fun _ => Nat.zero_le maxAttempts

/-- The initial state satisfies `TicksBalance`, since no tick has been spent. Counterpart of Veil's
verification condition `initializer_ticks_balance`. Design row C13, not from MLS. -/
theorem ticksBalance_init (capacity : ℕ) : TicksBalance (init capacity : State Target) :=
  rfl

/-- The initial state satisfies `BudgetBalance`, since its budget is the capacity and no tick has
been spent. Counterpart of Veil's verification condition `initializer_budget_balance`. Design row
C13, not from MLS. -/
theorem budgetBalance_init (capacity : ℕ) :
    BudgetBalance capacity (init capacity : State Target) :=
  Nat.add_zero capacity

variable [DecidableEq Target]

/-- One step of the budget supervisor with guard `reachable`, age bound `bound` and admission
limit `maxAttempts`; each constructor mirrors the action of the same name in the Veil model
`PlanarArmBudgetSupervisor`, with its `require` clauses as hypotheses.

* `request t`: the planner requests `t`.
* `admit t`: a requested target that satisfies the guard and has been admitted fewer than
  `maxAttempts` times is commanded while the supervisor is idle; the request is consumed, the
  supervisor becomes busy, the age is reset to zero and the admission count of `t` increases by
  one (`Function.update`, Veil's `attempts t := attempts t + 1`).
* `reject t`: a requested target that fails the guard is rejected; the request is consumed.
* `finish`: the arm controller finishes the active command; its age is added to `ticksClosed`,
  the supervisor becomes idle and the age is reset to zero.
* `tick`: while a command is active, its age is below the bound and the budget is at least one,
  the age and `ticksTotal` increase by one and the budget becomes `budget - 1` (Veil's
  `require budget ≥ 1` and `budget := budget - 1`; `ℕ` subtraction, exact under the guard).
* `timeout`: while a command is active and its age equals the bound, the active command is
  recorded in `timedOut` and cleared, its age is added to `ticksClosed`, the supervisor becomes
  idle and the age is reset to zero.

The guard is any predicate on targets; for the planar two-link arm it is `planarGuard a b`
(MLS p. 95, eq. (3.12), through design row C04). A design model, not from MLS. -/
inductive Step (reachable : Target → Prop) (bound maxAttempts : ℕ) :
    State Target → State Target → Prop
  /-- The planner requests `t` (Veil action `request`). -/
  | request (s : State Target) (t : Target) :
      Step reachable bound maxAttempts s { s with requested := insert t s.requested }
  /-- A requested target that satisfies the guard and is below the admission limit is commanded
  while the supervisor is idle (Veil action `admit`). -/
  | admit (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hreachable : reachable t) (hidle : s.busy = false) (hattempts : s.attempts t < maxAttempts) :
      Step reachable bound maxAttempts s
        { s with requested := s.requested \ {t}, commanded := insert t s.commanded, busy := true,
                 age := 0, attempts := Function.update s.attempts t (s.attempts t + 1) }
  /-- A requested target that fails the guard is rejected (Veil action `reject`). -/
  | reject (s : State Target) (t : Target) (hrequested : t ∈ s.requested)
      (hunreachable : ¬ reachable t) :
      Step reachable bound maxAttempts s
        { s with requested := s.requested \ {t}, rejected := insert t s.rejected }
  /-- The arm controller finishes the active command (Veil action `finish`). -/
  | finish (s : State Target) (hbusy : s.busy = true) :
      Step reachable bound maxAttempts s
        { s with commanded := ∅, busy := false, ticksClosed := s.ticksClosed + s.age, age := 0 }
  /-- One clock tick while a command is active, below the age bound and with budget left (Veil
  action `tick`). -/
  | tick (s : State Target) (hbusy : s.busy = true) (hage : s.age < bound)
      (hbudget : 1 ≤ s.budget) :
      Step reachable bound maxAttempts s
        { s with age := s.age + 1, budget := s.budget - 1, ticksTotal := s.ticksTotal + 1 }
  /-- The active command has reached the age bound and times out (Veil action `timeout`). -/
  | timeout (s : State Target) (hbusy : s.busy = true) (hage : s.age = bound) :
      Step reachable bound maxAttempts s
        { s with timedOut := s.timedOut ∪ s.commanded, commanded := ∅, busy := false,
                 ticksClosed := s.ticksClosed + s.age, age := 0 }

/-- The states of the budget supervisor with guard `reachable`, age bound `bound`, admission limit
`maxAttempts` and tick capacity `capacity` that some finite sequence of steps reaches from
`init capacity`: the reflexive-transitive closure of `Step reachable bound maxAttempts` from
`init capacity`. A design model, not from MLS. -/
def ReachableState (reachable : Target → Prop) (bound maxAttempts capacity : ℕ)
    (s : State Target) : Prop :=
  Relation.ReflTransGen (Step reachable bound maxAttempts) (init capacity) s

/-- Every step of the budget supervisor preserves `CommandedReachable`: `admit` commands only a
target that satisfies the guard, `finish` and `timeout` clear the command, and `request`,
`reject` and `tick` leave it unchanged. The six cases are the counterparts of Veil's verification
conditions `<action>_commanded_reachable`. Design row C13, not from MLS. -/
theorem Step.commandedReachable {reachable : Target → Prop} {bound maxAttempts : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s')
    (hs : CommandedReachable reachable s) : CommandedReachable reachable s' := by
  cases h with
  | request => exact hs
  | admit t _ hreachable _ _ =>
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

/-- Every step of the budget supervisor preserves `AgeBounded`: `tick` fires only below the
bound, `admit`, `finish` and `timeout` reset the age to zero, and `request` and `reject` leave it
unchanged. The six cases are the counterparts of Veil's verification conditions
`<action>_age_bounded`. Design row C13, not from MLS. -/
theorem Step.ageBounded {reachable : Target → Prop} {bound maxAttempts : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s') (hs : AgeBounded bound s) :
    AgeBounded bound s' := by
  cases h with
  | request => exact hs
  | admit => exact Nat.zero_le bound
  | reject => exact hs
  | finish => exact Nat.zero_le bound
  | tick _ hage _ => exact hage
  | timeout => exact Nat.zero_le bound

/-- Every step of the budget supervisor preserves `IdleAgeZero`: `admit` makes the supervisor
busy, `tick` fires only while it is busy and keeps it busy, `finish` and `timeout` reset the age
to zero, and `request` and `reject` change neither `busy` nor the age. The six cases are the
counterparts of Veil's verification conditions `<action>_idle_age_zero`. Design row C13, not from
MLS. -/
theorem Step.idleAgeZero {reachable : Target → Prop} {bound maxAttempts : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s') (hs : IdleAgeZero s) :
    IdleAgeZero s' := by
  cases h with
  | request => exact hs
  | admit => exact fun _ => rfl
  | reject => exact hs
  | finish => exact fun _ => rfl
  | tick hbusy _ _ =>
    intro hidle
    simp [hbusy] at hidle
  | timeout => exact fun _ => rfl

/-- Every step of the budget supervisor preserves `AttemptsBounded`: `admit t` fires only when
`attempts t < maxAttempts` and changes the count of `t` alone, and the other actions leave the
counts unchanged. The six cases are the counterparts of Veil's verification conditions
`<action>_attempts_bounded`; the `admit` case is the one with arithmetic under the quantifier.
Design row C13, not from MLS. -/
theorem Step.attemptsBounded {reachable : Target → Prop} {bound maxAttempts : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s')
    (hs : AttemptsBounded maxAttempts s) : AttemptsBounded maxAttempts s' := by
  cases h with
  | request => exact hs
  | admit t _ _ _ hattempts =>
    intro u
    show Function.update s.attempts t (s.attempts t + 1) u ≤ maxAttempts
    rcases eq_or_ne u t with rfl | hu
    · rw [Function.update_self]
      exact hattempts
    · rw [Function.update_of_ne hu]
      exact hs u
  | reject => exact hs
  | finish => exact hs
  | tick => exact hs
  | timeout => exact hs

/-- Every step of the budget supervisor from a state with `IdleAgeZero` preserves `TicksBalance`:
`tick` increments the age and `ticksTotal` together, `finish` and `timeout` move the age into
`ticksClosed`, `admit` resets an age that is already zero because the supervisor is idle (this is
where `IdleAgeZero` is needed), and `request` and `reject` change no counter. The six cases are the
counterparts of Veil's verification conditions `<action>_ticks_balance`, which assume all clauses.
Design row C13, not from MLS. -/
theorem Step.ticksBalance {reachable : Target → Prop} {bound maxAttempts : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s') (hidle : IdleAgeZero s)
    (hs : TicksBalance s) : TicksBalance s' := by
  unfold TicksBalance at hs ⊢
  cases h with
  | request => exact hs
  | admit _ _ _ hbusy _ =>
    have h0 := hidle hbusy
    simp only
    omega
  | reject => exact hs
  | finish =>
    simp only
    omega
  | tick =>
    simp only
    omega
  | timeout =>
    simp only
    omega

/-- Every step of the budget supervisor preserves `BudgetBalance`: `tick` fires only with
`1 ≤ budget`, so `budget - 1` is the exact difference and the sum `budget + ticksTotal` is
unchanged, and the other actions change neither the budget nor `ticksTotal`. The six cases are the
counterparts of Veil's verification conditions `<action>_budget_balance`; the `tick` case is the
one with `ℕ` subtraction. Design row C13, not from MLS. -/
theorem Step.budgetBalance {reachable : Target → Prop} {bound maxAttempts capacity : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s')
    (hs : BudgetBalance capacity s) : BudgetBalance capacity s' := by
  unfold BudgetBalance at hs ⊢
  cases h with
  | request => exact hs
  | admit => exact hs
  | reject => exact hs
  | finish => exact hs
  | tick _ _ hbudget =>
    simp only
    omega
  | timeout => exact hs

/-- **Supervisor invariant, guard.** In every reachable state of the budget supervisor, every
commanded target satisfies the guard, for every guard `reachable` on every target type and all
`bound`, `maxAttempts` and `capacity`. Proved by induction over the steps from
`commandedReachable_init` and `Step.commandedReachable`. Design row C13, not from MLS. -/
theorem ReachableState.commandedReachable {reachable : Target → Prop}
    {bound maxAttempts capacity : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity s) :
    CommandedReachable reachable s := by
  induction h with
  | refl => exact commandedReachable_init reachable capacity
  | tail _ hstep ih => exact hstep.commandedReachable ih

/-- **Supervisor invariant, age.** In every reachable state of the budget supervisor, the age of
the active command is at most the bound. Proved by induction over the steps from
`ageBounded_init` and `Step.ageBounded`. Design row C13, not from MLS. -/
theorem ReachableState.ageBounded {reachable : Target → Prop} {bound maxAttempts capacity : ℕ}
    {s : State Target} (h : ReachableState reachable bound maxAttempts capacity s) :
    AgeBounded bound s := by
  induction h with
  | refl => exact ageBounded_init bound capacity
  | tail _ hstep ih => exact hstep.ageBounded ih

/-- **Supervisor invariant, idle age.** In every reachable state of the budget supervisor, an idle
supervisor has age zero. Proved by induction over the steps from `idleAgeZero_init` and
`Step.idleAgeZero`. Design row C13, not from MLS. -/
theorem ReachableState.idleAgeZero {reachable : Target → Prop} {bound maxAttempts capacity : ℕ}
    {s : State Target} (h : ReachableState reachable bound maxAttempts capacity s) :
    IdleAgeZero s := by
  induction h with
  | refl => exact idleAgeZero_init capacity
  | tail _ hstep ih => exact hstep.idleAgeZero ih

/-- **Supervisor invariant, retry limit.** In every reachable state of the budget supervisor, no
target has been admitted more than `maxAttempts` times. Proved by induction over the steps from
`attemptsBounded_init` and `Step.attemptsBounded`. Design row C13, not from MLS. -/
theorem ReachableState.attemptsBounded {reachable : Target → Prop}
    {bound maxAttempts capacity : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity s) :
    AttemptsBounded maxAttempts s := by
  induction h with
  | refl => exact attemptsBounded_init maxAttempts capacity
  | tail _ hstep ih => exact hstep.attemptsBounded ih

/-- **Supervisor invariant, tick balance.** In every reachable state of the budget supervisor, the
ticks spent by closed commands and the age of the active command add up to the ticks spent by all
commands. Proved by induction over the steps from `ticksBalance_init` and `Step.ticksBalance`,
with `ReachableState.idleAgeZero` at the state before each step. Design row C13, not from MLS. -/
theorem ReachableState.ticksBalance {reachable : Target → Prop} {bound maxAttempts capacity : ℕ}
    {s : State Target} (h : ReachableState reachable bound maxAttempts capacity s) :
    TicksBalance s := by
  induction h with
  | refl => exact ticksBalance_init capacity
  | tail hreach hstep ih => exact hstep.ticksBalance (ReachableState.idleAgeZero hreach) ih

/-- **Supervisor invariant, budget balance.** In every reachable state of the budget supervisor
with capacity `capacity`, the remaining budget and the ticks spent add up to `capacity`; in
particular at most `capacity` ticks are ever spent. Proved by induction over the steps from
`budgetBalance_init` and `Step.budgetBalance`. Design row C13, not from MLS. -/
theorem ReachableState.budgetBalance {reachable : Target → Prop} {bound maxAttempts capacity : ℕ}
    {s : State Target} (h : ReachableState reachable bound maxAttempts capacity s) :
    BudgetBalance capacity s := by
  induction h with
  | refl => exact budgetBalance_init capacity
  | tail _ hstep ih => exact hstep.budgetBalance ih

/-- **Simulation, one step.** Forgetting `attempts`, `budget`, `ticksTotal` and `ticksClosed`,
each step of the budget supervisor is the step of the same name of the timeout supervisor
`PlanarArmTimeoutSupervisor` with the same guard and bound (the new guards `attempts t <
maxAttempts` and `1 ≤ budget` only strengthen `admit` and `tick`). Design row C14, not from MLS. -/
theorem Step.toTimeoutState {reachable : Target → Prop} {bound maxAttempts : ℕ}
    {s s' : State Target} (h : Step reachable bound maxAttempts s s') :
    PlanarArmTimeoutSupervisor.Step reachable bound s.toTimeoutState s'.toTimeoutState := by
  cases h with
  | request t => exact PlanarArmTimeoutSupervisor.Step.request s.toTimeoutState t
  | admit t hrequested hreachable hidle _ =>
    exact PlanarArmTimeoutSupervisor.Step.admit s.toTimeoutState t hrequested hreachable hidle
  | reject t hrequested hunreachable =>
    exact PlanarArmTimeoutSupervisor.Step.reject s.toTimeoutState t hrequested hunreachable
  | finish hbusy => exact PlanarArmTimeoutSupervisor.Step.finish s.toTimeoutState hbusy
  | tick hbusy hage _ => exact PlanarArmTimeoutSupervisor.Step.tick s.toTimeoutState hbusy hage
  | timeout hbusy hage =>
    exact PlanarArmTimeoutSupervisor.Step.timeout s.toTimeoutState hbusy hage

/-- **Simulation.** Forgetting `attempts`, `budget`, `ticksTotal` and `ticksClosed`, every
reachable state of the budget supervisor with guard `reachable`, bound `bound` and any admission
limit and capacity is a reachable state of the timeout supervisor `PlanarArmTimeoutSupervisor`
with the same guard and bound. By induction over the steps from `Step.toTimeoutState`. Design row
C14, not from MLS. -/
theorem ReachableState.toTimeoutState {reachable : Target → Prop}
    {bound maxAttempts capacity : ℕ} {s : State Target}
    (h : ReachableState reachable bound maxAttempts capacity s) :
    PlanarArmTimeoutSupervisor.ReachableState reachable bound s.toTimeoutState := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.toTimeoutState

open RoboLean.Examples

/-- **Refinement, targets with positions.** For positive link lengths `a, b`, all `bound`,
`maxAttempts` and `capacity`, and a target type whose targets have tool positions `pos t`, run the
budget supervisor with guard `fun t => planarGuard a b (pos t)`. Then every target commanded in a
reachable state is reached by the planar two-link arm: some joint vector `q` puts the tool at
`pos t`. From the simulation `ReachableState.toTimeoutState` and the timeout supervisor's
refinement `PlanarArmTimeoutSupervisor.ReachableState.exists_planarTwoLinkPosition_eq_pos` (row
C12, through C10, C04 and C02, whose joint vectors come from the inverse kinematics of MLS p. 98,
eq. (3.16)); the reachable workspace is that of MLS p. 95, eq. (3.12). Design row C14, not from
MLS. Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq_pos {a b : ℝ}
    {bound maxAttempts capacity : ℕ} (ha : 0 < a) (hb : 0 < b) (pos : Target → Vec3)
    {s : State Target}
    (hs : ReachableState (fun t => planarGuard a b (pos t)) bound maxAttempts capacity s)
    {t : Target} (ht : t ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = pos t :=
  hs.toTimeoutState.exists_planarTwoLinkPosition_eq_pos ha hb pos ht

/-- **Refinement.** For positive link lengths `a, b` and all `bound`, `maxAttempts` and
`capacity`, run the budget supervisor over tool targets `x : Vec3` with guard `planarGuard a b`.
Then every target commanded in a reachable state is the tool position
`Examples.planarTwoLinkPosition a b q` of some joint vector `q`. From the simulation
`ReachableState.toTimeoutState` and
`PlanarArmTimeoutSupervisor.ReachableState.exists_planarTwoLinkPosition_eq` (row C12; MLS p. 98,
eq. (3.16), and the reachable workspace of MLS p. 95, eq. (3.12)). Design row C14, not from MLS.
Position reachability of the ideal model only. -/
theorem ReachableState.exists_planarTwoLinkPosition_eq {a b : ℝ} {bound maxAttempts capacity : ℕ}
    (ha : 0 < a) (hb : 0 < b) {s : State Vec3}
    (hs : ReachableState (planarGuard a b) bound maxAttempts capacity s) {x : Vec3}
    (hx : x ∈ s.commanded) :
    ∃ q : Fin 2 → ℝ, planarTwoLinkPosition a b q = x :=
  hs.toTimeoutState.exists_planarTwoLinkPosition_eq ha hb hx

/-- **Refinement, workspace form.** For positive link lengths `a, b` and all `bound`,
`maxAttempts` and `capacity`, in every reachable state of the budget supervisor over tool targets
with guard `planarGuard a b`, the commanded targets lie in the reachable workspace `W_R` of MLS
eq. (3.12), printed p. 95, of `Examples.planarTwoLink a b` with unrestricted joints
(`Q = Set.univ`). From the simulation `ReachableState.toTimeoutState` and
`PlanarArmTimeoutSupervisor.ReachableState.commanded_subset_reachableWorkspace` (row C12). Design
row C14, not from MLS. Position reachability of the ideal model only. -/
theorem ReachableState.commanded_subset_reachableWorkspace {a b : ℝ}
    {bound maxAttempts capacity : ℕ} (ha : 0 < a) (hb : 0 < b) {s : State Vec3}
    (hs : ReachableState (planarGuard a b) bound maxAttempts capacity s) :
    s.commanded ⊆ (planarTwoLink a b).reachableWorkspace Set.univ :=
  hs.toTimeoutState.commanded_subset_reachableWorkspace ha hb

end PlanarArmBudgetSupervisor

end RoboLean.Design
