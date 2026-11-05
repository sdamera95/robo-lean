import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/-!
# A cell supervisor with a protective stop

A supervisor sits between a task planner, which requests waypoints, and the arm controller,
which moves the arm from the waypoint it is at to one commanded waypoint at a time. This file
states the supervisor of a pick-and-place cell as a transition system over an abstract waypoint
type `W` and a relation `linked : W → W → Prop` between waypoints. The supervisor remembers the
waypoint `current` the arm is at (initially a home waypoint), admits a requested waypoint only
while it is idle, not faulted, and when the waypoint is linked to `current`, rejects a requested
waypoint that is not linked to `current`, moves `current` to the commanded waypoint when the
controller finishes the move, counts clock ticks of the active move up to a bound, and on a
timeout clears the move, records it and faults for good: a faulted supervisor admits nothing and
no action clears the fault (a protective stop).

For the cell, `linked a b` is read as "some certified cell contains both `a` and `b`", so every
admitted move runs between two waypoints of a common cell; that reading, the certificates of the
cells and the motion between the waypoints are outside this file.

The file proves, each by induction over the steps from the initial state, five invariants of
every reachable state: a busy supervisor has exactly one commanded waypoint and it is linked to
`current` (`ReachableState.busyCommanded`); an idle supervisor has no commanded waypoint
(`ReachableState.idleUncommanded`); the age is at most the bound (`ReachableState.ageBounded`);
an idle supervisor has age zero (`ReachableState.idleAgeZero`); a faulted supervisor is idle
(`ReachableState.faultedIdle`). From the first, every commanded waypoint is linked to `current`
(`ReachableState.commandedLinked`). Three step facts complete the picture: `current` changes only
to a waypoint linked to it (`ReachableState.current_eq_or_linked`), a step from an age other than
the bound leaves the fault flag unchanged (`Step.faulted_eq_of_age_ne`), and a step from a
faulted reachable state stays faulted, idle and without a command
(`ReachableState.faulted_step`).

Correspondence with the Veil model. The same transition system is modelled in Veil, in the
sibling project `robo-lean-veil`, file `Examples/RoboLean/CellSupervisor.lean`: the fields of
`State` mirror Veil's relations `requested`, `commanded`, `rejected`, `timedOut` and the
individuals `busy`, `faulted`, `age`, `current`; `init` mirrors `after_init`; the constructors of
`Step` mirror the actions of the same name; `bound` and `linked` mirror the immutable individual
`bound` and the immutable relation `linked`, which Veil leaves uninterpreted; the invariants
mirror the clauses of the same names. A Veil relation `r : waypoint → Bool` is a Lean set, with
`w ∈ s.r` read as `r w = true`, and Veil's `Nat` is Lean's `ℕ`. The two projects run on
different Lean versions and cannot import each other, so this correspondence is a recorded
convention, not a kernel-checked link.

The supervisor is a design model, not taken from MLS. The statements concern the ideal
transition system: the age counts abstract `tick` steps, not physical time, and nothing here
says that a move finishes (a liveness property), how often the clock ticks, or anything about
the arm, its controller, the obstacles of the cell or a physical robot.
-/

namespace RoboLean.Design

namespace CellSupervisor

/-- The state of the cell supervisor over a waypoint type `W`: the pending requests, the
commanded waypoint (a set, which the invariants show to be empty or a single waypoint), the
rejected waypoints, the waypoints whose move timed out, whether a move is active, whether the
supervisor has faulted, the number of ticks since the active move was admitted, and the waypoint
`current` the arm is at. This mirrors the mutable state of the Veil model `CellSupervisor`
(relations `requested`, `commanded`, `rejected`, `timedOut : waypoint → Bool`, individuals
`busy`, `faulted : Bool`, `age : Nat`, `current : waypoint`); a Veil relation is a Lean set. A
design model, not from MLS. -/
structure State (W : Type*) where
  /-- Pending requests from the planner. -/
  requested : Set W
  /-- The waypoint of the active move. -/
  commanded : Set W
  /-- Waypoints the supervisor has rejected. -/
  rejected : Set W
  /-- Waypoints whose move timed out. -/
  timedOut : Set W
  /-- A move is active. -/
  busy : Bool
  /-- The supervisor has timed out a move; it admits nothing from then on. -/
  faulted : Bool
  /-- The number of ticks since the active move was admitted. -/
  age : ℕ
  /-- The waypoint the arm is at: the home waypoint, then the goal of the last finished move. -/
  current : W

variable {W : Type*}

/-- The initial state at the home waypoint `home`: no request, no command, no rejection, no
timeout, idle, not faulted, age zero, the arm at `home`. This mirrors the `after_init` block of
the Veil model `CellSupervisor`, whose home waypoint is an immutable individual. A design model,
not from MLS. -/
def init (home : W) : State W where
  requested := ∅
  commanded := ∅
  rejected := ∅
  timedOut := ∅
  busy := false
  faulted := false
  age := 0
  current := home

/-- One step of the cell supervisor with link relation `linked` and age bound `bound`; each
constructor mirrors the action of the same name in the Veil model `CellSupervisor`, with its
`require` clauses as hypotheses.

* `request w`: the planner requests `w`.
* `admit w`: a requested waypoint linked to `current` is commanded while the supervisor is idle
  and not faulted; the request is consumed, `w` becomes the only commanded waypoint, the
  supervisor becomes busy and the age is reset to zero.
* `reject w`: a requested waypoint not linked to `current` is rejected; the request is consumed.
* `finish w`: the controller finishes the move to the commanded waypoint `w`; the arm is at `w`,
  the command is cleared, the supervisor becomes idle and the age is reset to zero.
* `tick`: while a move is active and its age is below the bound, the age increases by one.
* `timeout`: while a move is active and its age equals the bound, the commanded waypoint is
  recorded in `timedOut` and cleared, the supervisor becomes idle, the age is reset to zero and
  the supervisor faults; `current` is unchanged.

`linked` is any relation on waypoints; for the cell it is "some certified cell contains both".
A design model, not from MLS. -/
inductive Step (linked : W → W → Prop) (bound : ℕ) : State W → State W → Prop
  /-- The planner requests `w` (Veil action `request`). Not from MLS. -/
  | request (s : State W) (w : W) :
      Step linked bound s { s with requested := insert w s.requested }
  /-- A requested waypoint linked to the current one is commanded while the supervisor is idle
  and not faulted (Veil action `admit`). Not from MLS. -/
  | admit (s : State W) (w : W) (hrequested : w ∈ s.requested) (hidle : s.busy = false)
      (hok : s.faulted = false) (hlinked : linked s.current w) :
      Step linked bound s
        { s with requested := s.requested \ {w}, commanded := {w}, busy := true, age := 0 }
  /-- A requested waypoint not linked to the current one is rejected (Veil action `reject`).
  Not from MLS. -/
  | reject (s : State W) (w : W) (hrequested : w ∈ s.requested)
      (hunlinked : ¬ linked s.current w) :
      Step linked bound s
        { s with requested := s.requested \ {w}, rejected := insert w s.rejected }
  /-- The controller finishes the move to the commanded waypoint `w` (Veil action `finish`).
  Not from MLS. -/
  | finish (s : State W) (w : W) (hbusy : s.busy = true) (hcommanded : w ∈ s.commanded) :
      Step linked bound s { s with commanded := ∅, busy := false, age := 0, current := w }
  /-- One clock tick while a move is active and below the age bound (Veil action `tick`).
  Not from MLS. -/
  | tick (s : State W) (hbusy : s.busy = true) (hage : s.age < bound) :
      Step linked bound s { s with age := s.age + 1 }
  /-- The active move has reached the age bound: it times out and the supervisor faults (Veil
  action `timeout`). Not from MLS. -/
  | timeout (s : State W) (hbusy : s.busy = true) (hage : s.age = bound) :
      Step linked bound s
        { s with timedOut := s.timedOut ∪ s.commanded, commanded := ∅, busy := false,
                 faulted := true, age := 0 }

/-- The states of the cell supervisor with link relation `linked`, age bound `bound` and home
waypoint `home` that some finite sequence of steps reaches from `init home`: the
reflexive-transitive closure of `Step linked bound` from `init home`. A design model, not from
MLS. -/
def ReachableState (linked : W → W → Prop) (bound : ℕ) (home : W) (s : State W) : Prop :=
  Relation.ReflTransGen (Step linked bound) (init home) s

/-- First invariant: a busy supervisor has exactly one commanded waypoint, and it is linked to
the waypoint the arm is at. This mirrors the Veil clause
`invariant [busy_commanded] busy → ∃ w, linked current w ∧ ∀ u, commanded u ↔ u = w`. A design
statement, not from MLS. -/
def BusyCommanded (linked : W → W → Prop) (s : State W) : Prop :=
  s.busy = true → ∃ w, s.commanded = {w} ∧ linked s.current w

/-- Second invariant: an idle supervisor has no commanded waypoint. This mirrors the Veil clause
`invariant [idle_uncommanded] ¬ busy → ¬ commanded w`. A design statement, not from MLS. -/
def IdleUncommanded (s : State W) : Prop :=
  s.busy = false → s.commanded = ∅

/-- Third invariant: the age of the active move never exceeds the bound. This mirrors the Veil
clause `safety [age_bounded] age ≤ bound`. A design statement, not from MLS. -/
def AgeBounded (bound : ℕ) (s : State W) : Prop :=
  s.age ≤ bound

/-- Fourth invariant: an idle supervisor has age zero. This mirrors the Veil clause
`invariant [idle_age_zero] ¬ busy → age = 0`. A design statement, not from MLS. -/
def IdleAgeZero (s : State W) : Prop :=
  s.busy = false → s.age = 0

/-- Fifth invariant: a faulted supervisor is idle. This mirrors the Veil clause
`invariant [faulted_idle] faulted → ¬ busy`. A design statement, not from MLS. -/
def FaultedIdle (s : State W) : Prop :=
  s.faulted = true → s.busy = false

/-- Every commanded waypoint is linked to the waypoint the arm is at. This mirrors the Veil
clause `safety [commanded_linked] commanded w → linked current w`. A design statement, not from
MLS. -/
def CommandedLinked (linked : W → W → Prop) (s : State W) : Prop :=
  ∀ w ∈ s.commanded, linked s.current w

/-- The initial state satisfies `BusyCommanded`, since it is idle. A design statement, not from
MLS. -/
theorem busyCommanded_init (linked : W → W → Prop) (home : W) :
    BusyCommanded linked (init home) := by
  intro h
  simp [init] at h

/-- The initial state satisfies `IdleUncommanded`, since nothing is commanded. A design
statement, not from MLS. -/
theorem idleUncommanded_init (home : W) : IdleUncommanded (init home) :=
  fun _ => rfl

/-- The initial state satisfies `AgeBounded`, since its age is zero. A design statement, not from
MLS. -/
theorem ageBounded_init (bound : ℕ) (home : W) : AgeBounded bound (init home) :=
  Nat.zero_le bound

/-- The initial state satisfies `IdleAgeZero`, since its age is zero. A design statement, not from
MLS. -/
theorem idleAgeZero_init (home : W) : IdleAgeZero (init home) :=
  fun _ => rfl

/-- The initial state satisfies `FaultedIdle`, since it is not faulted. A design statement, not
from MLS. -/
theorem faultedIdle_init (home : W) : FaultedIdle (init home) := by
  intro h
  simp [init] at h

/-- Every step preserves `BusyCommanded`: `admit` commands one waypoint linked to `current`,
`finish` and `timeout` make the supervisor idle, and `request`, `reject` and `tick` change
neither `busy`, `commanded` nor `current`. The six cases are the counterparts of Veil's
verification conditions `<action>_busy_commanded`. A design statement, not from MLS. -/
theorem Step.busyCommanded {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hs : BusyCommanded linked s) : BusyCommanded linked s' := by
  cases h with
  | request => exact hs
  | admit w _ _ _ hlinked => exact fun _ => ⟨w, rfl, hlinked⟩
  | reject => exact hs
  | finish => intro h; simp at h
  | tick => exact hs
  | timeout => intro h; simp at h

/-- Every step preserves `IdleUncommanded`: `admit` makes the supervisor busy, `finish` and
`timeout` clear the command, `tick` keeps the supervisor busy, and `request` and `reject` change
neither `busy` nor `commanded`. A design statement, not from MLS. -/
theorem Step.idleUncommanded {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hs : IdleUncommanded s) : IdleUncommanded s' := by
  cases h with
  | request => exact hs
  | admit => intro h; simp at h
  | reject => exact hs
  | finish => exact fun _ => rfl
  | tick => exact hs
  | timeout => exact fun _ => rfl

/-- Every step preserves `AgeBounded`: `tick` fires only below the bound, `admit`, `finish` and
`timeout` reset the age to zero, and `request` and `reject` leave it unchanged. A design
statement, not from MLS. -/
theorem Step.ageBounded {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hs : AgeBounded bound s) : AgeBounded bound s' := by
  cases h with
  | request => exact hs
  | admit => exact Nat.zero_le bound
  | reject => exact hs
  | finish => exact Nat.zero_le bound
  | tick _ hage => exact hage
  | timeout => exact Nat.zero_le bound

/-- Every step preserves `IdleAgeZero`: `admit` makes the supervisor busy, `tick` fires only while
it is busy and keeps it busy, `finish` and `timeout` reset the age to zero, and `request` and
`reject` change neither `busy` nor the age. A design statement, not from MLS. -/
theorem Step.idleAgeZero {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hs : IdleAgeZero s) : IdleAgeZero s' := by
  cases h with
  | request => exact hs
  | admit => exact fun _ => rfl
  | reject => exact hs
  | finish => exact fun _ => rfl
  | tick hbusy _ =>
    intro hidle
    simp [hbusy] at hidle
  | timeout => exact fun _ => rfl

/-- Every step preserves `FaultedIdle`: `admit` fires only while not faulted and leaves the flag
unchanged, `finish` and `timeout` make the supervisor idle, `tick` fires only while busy, hence
not faulted, and `request` and `reject` change neither flag. A design statement, not from MLS. -/
theorem Step.faultedIdle {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hs : FaultedIdle s) : FaultedIdle s' := by
  cases h with
  | request => exact hs
  | admit _ _ _ hok =>
    intro hf
    simp [hok] at hf
  | reject => exact hs
  | finish => exact fun _ => rfl
  | tick hbusy _ =>
    intro hf
    simp [hs hf] at hbusy
  | timeout => exact fun _ => rfl

/-- **Supervisor invariant, one commanded waypoint.** In every reachable state of the cell
supervisor, for every link relation, bound and home waypoint, a busy supervisor has exactly one
commanded waypoint and it is linked to the waypoint the arm is at. By induction over the steps.
A design statement, not from MLS. -/
theorem ReachableState.busyCommanded {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s : State W} (h : ReachableState linked bound home s) : BusyCommanded linked s := by
  induction h with
  | refl => exact busyCommanded_init linked home
  | tail _ hstep ih => exact hstep.busyCommanded ih

/-- **Supervisor invariant, no command when idle.** In every reachable state of the cell
supervisor, an idle supervisor has no commanded waypoint. By induction over the steps. A design
statement, not from MLS. -/
theorem ReachableState.idleUncommanded {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s : State W} (h : ReachableState linked bound home s) : IdleUncommanded s := by
  induction h with
  | refl => exact idleUncommanded_init home
  | tail _ hstep ih => exact hstep.idleUncommanded ih

/-- **Supervisor invariant, age.** In every reachable state of the cell supervisor, the age of the
active move is at most the bound. By induction over the steps. A design statement, not from
MLS. -/
theorem ReachableState.ageBounded {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s : State W} (h : ReachableState linked bound home s) : AgeBounded bound s := by
  induction h with
  | refl => exact ageBounded_init bound home
  | tail _ hstep ih => exact hstep.ageBounded ih

/-- **Supervisor invariant, idle age.** In every reachable state of the cell supervisor, an idle
supervisor has age zero. By induction over the steps. A design statement, not from MLS. -/
theorem ReachableState.idleAgeZero {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s : State W} (h : ReachableState linked bound home s) : IdleAgeZero s := by
  induction h with
  | refl => exact idleAgeZero_init home
  | tail _ hstep ih => exact hstep.idleAgeZero ih

/-- **Supervisor invariant, protective stop.** In every reachable state of the cell supervisor, a
faulted supervisor is idle. By induction over the steps. A design statement, not from MLS. -/
theorem ReachableState.faultedIdle {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s : State W} (h : ReachableState linked bound home s) : FaultedIdle s := by
  induction h with
  | refl => exact faultedIdle_init home
  | tail _ hstep ih => exact hstep.faultedIdle ih

/-- **Commanded waypoints are linked.** In every reachable state of the cell supervisor, every
commanded waypoint is linked to the waypoint the arm is at: a commanded waypoint makes the
supervisor busy by `ReachableState.idleUncommanded`, and then it is the single commanded waypoint
of `ReachableState.busyCommanded`. A design statement, not from MLS. -/
theorem ReachableState.commandedLinked {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s : State W} (h : ReachableState linked bound home s) : CommandedLinked linked s := by
  intro w hw
  cases hb : s.busy with
  | false =>
    rw [h.idleUncommanded hb] at hw
    exact absurd hw (Set.notMem_empty w)
  | true =>
    obtain ⟨u, hu, hlinked⟩ := h.busyCommanded hb
    rw [hu, Set.mem_singleton_iff] at hw
    rw [hw]
    exact hlinked

/-- A step either leaves the waypoint the arm is at unchanged or, by `finish`, moves it to a
commanded waypoint; when every commanded waypoint is linked to `current`, the new waypoint is
linked to the old one. A design statement, not from MLS. -/
theorem Step.current_eq_or_linked {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hs : CommandedLinked linked s) :
    s'.current = s.current ∨ linked s.current s'.current := by
  cases h with
  | request => exact Or.inl rfl
  | admit => exact Or.inl rfl
  | reject => exact Or.inl rfl
  | finish w _ hw => exact Or.inr (hs w hw)
  | tick => exact Or.inl rfl
  | timeout => exact Or.inl rfl

/-- **Moves stay linked.** For a step from a reachable state of the cell supervisor, the waypoint
the arm is at afterwards is the one before or a waypoint linked to it; with `linked` read as
"some cell contains both", every change of `current` stays within one cell. From
`Step.current_eq_or_linked` and `ReachableState.commandedLinked`. A design statement, not from
MLS. -/
theorem ReachableState.current_eq_or_linked {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s s' : State W} (h : ReachableState linked bound home s) (hstep : Step linked bound s s') :
    s'.current = s.current ∨ linked s.current s'.current :=
  hstep.current_eq_or_linked h.commandedLinked

/-- Only a timeout changes the fault flag: a step from a state whose age differs from the bound
leaves `faulted` unchanged. A design statement, not from MLS. -/
theorem Step.faulted_eq_of_age_ne {linked : W → W → Prop} {bound : ℕ} {s s' : State W}
    (h : Step linked bound s s') (hage : s.age ≠ bound) : s'.faulted = s.faulted := by
  cases h with
  | request => rfl
  | admit => rfl
  | reject => rfl
  | finish => rfl
  | tick => rfl
  | timeout _ hage' => exact absurd hage' hage

/-- **The protective stop is permanent.** A step from a faulted reachable state of the cell
supervisor leads to a state that is faulted, idle and has no commanded waypoint: only `request`
and `reject` are enabled there. From `ReachableState.faultedIdle` and
`ReachableState.idleUncommanded`. A design statement, not from MLS. -/
theorem ReachableState.faulted_step {linked : W → W → Prop} {bound : ℕ} {home : W}
    {s s' : State W} (h : ReachableState linked bound home s) (hstep : Step linked bound s s')
    (hf : s.faulted = true) :
    s'.faulted = true ∧ s'.busy = false ∧ s'.commanded = ∅ := by
  have hidle := h.faultedIdle hf
  have hnone := h.idleUncommanded hidle
  cases hstep with
  | request => exact ⟨hf, hidle, hnone⟩
  | admit _ _ _ hok => simp [hf] at hok
  | reject => exact ⟨hf, hidle, hnone⟩
  | finish _ hbusy => simp [hidle] at hbusy
  | tick hbusy => simp [hidle] at hbusy
  | timeout hbusy => simp [hidle] at hbusy

end CellSupervisor

end RoboLean.Design
