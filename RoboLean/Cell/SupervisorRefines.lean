import RoboLean.Cell.Supervisor
import RoboLean.Design.CellSupervisor

/-!
# The executable cell supervisor refines the design supervisor

`RoboLean.Cell.Supervisor` defines an executable cell supervisor over rational degree waypoints
whose link relation searches a list of rational boxes. This file relates it to the design
relation `RoboLean.Design.CellSupervisor.Step` with the link relation `CellLinked cells`, "some
cell of the list contains both waypoints":

* the list search decides that relation exactly: `linked cells a b = true ↔ CellLinked cells a b`
  (`linked_eq_true_iff`), through `Box.contains_eq_true_iff` for one box;
* a concrete state is read as a design state by `State.abstract`, each list as the set of its
  members; every transition of `step` is a design step on the abstracted states (`step_sound`),
  and `step` blocks an action exactly when a guard of the design constructor of the same name
  fails (`step_isSome_iff`); every state that `run` reaches from `State.init p.home` abstracts
  to a reachable state of the design supervisor (`reachableState_of_run`);
* hence, on the concrete state reached by any run: the age never exceeds the bound, an idle
  supervisor has age zero and no commanded waypoint, a busy supervisor has exactly one commanded
  waypoint and it is linked to the waypoint the arm is at, and a faulted supervisor is idle.

The supervisor is a design model, not taken from MLS. These theorems concern the Lean
definitions of the executable supervisor; the compiler or interpreter that executes them, the
operating system, the text protocol, the controller, the motion between waypoints, timing, the
certificates of the cells and a physical arm are outside them.
-/

namespace RoboLean.Cell.Supervisor

open RoboLean.Design

/-- The cell contains the waypoint, as a proposition: `lo.k ≤ w.k ≤ hi.k` for each of the three
joint angles, over `ℚ` in degrees. A design model, not from MLS. -/
def Box.Mem (c : Box) (w : Waypoint) : Prop :=
  c.lo.1 ≤ w.1 ∧ w.1 ≤ c.hi.1 ∧ c.lo.2.1 ≤ w.2.1 ∧ w.2.1 ≤ c.hi.2.1 ∧
    c.lo.2.2 ≤ w.2.2 ∧ w.2.2 ≤ c.hi.2.2

/-- The link relation of the cell supervisor for a list of cells: some cell of the list contains
both waypoints. A design model, not from MLS. -/
def CellLinked (cells : List Box) (a b : Waypoint) : Prop :=
  ∃ c ∈ cells, c.Mem a ∧ c.Mem b

/-- The executable box test decides box membership: `c.contains w = true` exactly when the six
inequalities of `Box.Mem` hold. A design model, not from MLS. -/
theorem Box.contains_eq_true_iff (c : Box) (w : Waypoint) : c.contains w = true ↔ c.Mem w := by
  simp [Box.contains, Box.Mem, and_assoc]

/-- **The list search decides the link relation.** For every list of cells and all waypoints
`a`, `b`, `linked cells a b = true` exactly when some cell of the list contains both. A design
model, not from MLS. -/
theorem linked_eq_true_iff (cells : List Box) (a b : Waypoint) :
    linked cells a b = true ↔ CellLinked cells a b := by
  simp [linked, CellLinked, Box.contains_eq_true_iff]

/-- Read a concrete state as a state of the design supervisor `RoboLean.Design.CellSupervisor`:
each list becomes the set of its members, the flags, the age and the current waypoint are kept.
A design convention, not from MLS. -/
def State.abstract (s : State) : CellSupervisor.State Waypoint where
  requested := {w | w ∈ s.requested}
  commanded := {w | w ∈ s.commanded}
  rejected := {w | w ∈ s.rejected}
  timedOut := {w | w ∈ s.timedOut}
  busy := s.busy
  faulted := s.faulted
  age := s.age
  current := s.current

/-- Two states of the design supervisor with the same eight components are equal. -/
private theorem cellState_ext {u v : CellSupervisor.State Waypoint}
    (h₁ : u.requested = v.requested) (h₂ : u.commanded = v.commanded)
    (h₃ : u.rejected = v.rejected) (h₄ : u.timedOut = v.timedOut) (h₅ : u.busy = v.busy)
    (h₆ : u.faulted = v.faulted) (h₇ : u.age = v.age) (h₈ : u.current = v.current) : u = v := by
  rcases u with ⟨_, _, _, _, _, _, _, _⟩
  rcases v with ⟨_, _, _, _, _, _, _, _⟩
  simp only at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  rfl

/-- Membership in a list into which another list is inserted element by element. -/
private theorem mem_foldr_insert (u : Waypoint) (l m : List Waypoint) :
    u ∈ l.foldr List.insert m ↔ u ∈ l ∨ u ∈ m := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.foldr_cons, List.mem_insert_iff, ih, List.mem_cons]
    exact or_assoc.symm

/-- **Soundness of one step.** Every transition of the executable supervisor is a step of the
design relation `CellSupervisor.Step` with the link relation `CellLinked p.cells` and the same
age bound, on the abstracted states: an action that `step` accepts satisfies the guards of the
design constructor of the same name (through `linked_eq_true_iff` for the link guard), `finish`
is the design `finish` of the head of the commanded list, and the effect on the lists is the
design effect on the sets of their members. A design model, not from MLS. -/
theorem step_sound {p : Params} {s s' : State} {act : Action} (h : step p s act = some s') :
    CellSupervisor.Step (CellLinked p.cells) p.bound s.abstract s'.abstract := by
  unfold step at h
  split at h
  · exact absurd h (by simp)
  rename_i hb
  cases h
  cases act with
  | request w =>
    convert CellSupervisor.Step.request s.abstract w using 1
    apply cellState_ext <;> simp [State.abstract, State.apply, Set.ext_iff]
  | admit w =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂ h₃ h₄
    have hreq : w ∈ s.abstract.requested := by simpa [State.abstract] using h₁
    have hidle : s.abstract.busy = false := by simpa [State.abstract] using h₂
    have hok : s.abstract.faulted = false := by simpa [State.abstract] using h₃
    have hlinked : CellLinked p.cells s.abstract.current w :=
      (linked_eq_true_iff p.cells s.current w).mp (by simpa using h₄)
    convert CellSupervisor.Step.admit (bound := p.bound) s.abstract w hreq hidle hok hlinked
      using 1
    apply cellState_ext <;> simp [State.abstract, State.apply, Set.ext_iff]
  | reject w =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    have hreq : w ∈ s.abstract.requested := by simpa [State.abstract] using h₁
    have hunlinked : ¬ CellLinked p.cells s.abstract.current w := by
      rw [← linked_eq_true_iff]
      exact h₂
    convert CellSupervisor.Step.reject (bound := p.bound) s.abstract w hreq hunlinked using 1
    apply cellState_ext <;> simp [State.abstract, State.apply, Set.ext_iff]
  | finish =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    obtain ⟨u, l, hl⟩ := List.exists_cons_of_ne_nil (by simpa using h₂)
    have hbusy : s.abstract.busy = true := by simpa [State.abstract] using h₁
    have hcmd : u ∈ s.abstract.commanded := by simp [State.abstract, hl]
    convert CellSupervisor.Step.finish (linked := CellLinked p.cells) (bound := p.bound)
      s.abstract u hbusy hcmd using 1
    apply cellState_ext <;> simp [State.abstract, State.apply, hl]
  | tick =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    have hbusy : s.abstract.busy = true := by simpa [State.abstract] using h₁
    have hage : s.abstract.age < p.bound := h₂
    convert CellSupervisor.Step.tick (linked := CellLinked p.cells) s.abstract hbusy hage using 1
    apply cellState_ext <;> simp [State.abstract, State.apply]
  | timeout =>
    simp only [Action.blocker] at hb
    split_ifs at hb with h₁ h₂
    have hbusy : s.abstract.busy = true := by simpa [State.abstract] using h₁
    have hage : s.abstract.age = p.bound := h₂
    convert CellSupervisor.Step.timeout (linked := CellLinked p.cells) s.abstract hbusy hage
      using 1
    apply cellState_ext <;> simp [State.abstract, State.apply, Set.ext_iff, mem_foldr_insert,
      or_comm]

/-- The guards of an action in a state, with the link relation `CellLinked p.cells`: those of
the constructor of the same name of `RoboLean.Design.CellSupervisor.Step`, the waypoint of
`finish` being any commanded one. A design model, not from MLS. -/
def Action.Enabled (p : Params) (s : State) : Action → Prop
  | .request _ => True
  | .admit w => w ∈ s.requested ∧ s.busy = false ∧ s.faulted = false ∧
      CellLinked p.cells s.current w
  | .reject w => w ∈ s.requested ∧ ¬ CellLinked p.cells s.current w
  | .finish => s.busy = true ∧ ∃ w, w ∈ s.commanded
  | .tick => s.busy = true ∧ s.age < p.bound
  | .timeout => s.busy = true ∧ s.age = p.bound

/-- **Blocked exactly when a design guard fails.** The executable supervisor accepts an action
exactly when the guards of the design constructor of the same name hold (`Action.Enabled`), with
the link relation `CellLinked p.cells`; otherwise `step` returns `none` and `Action.blocker` names
the first failing guard. A design model, not from MLS. -/
theorem step_isSome_iff (p : Params) (s : State) (act : Action) :
    (step p s act).isSome = true ↔ act.Enabled p s := by
  cases act <;>
    simp only [step, Action.blocker, Action.Enabled, ← linked_eq_true_iff] <;>
    (try split_ifs) <;> simp_all [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]

/-- **Soundness of runs.** If the executable supervisor runs a list of actions from a state `s`
to a state `s'`, the design supervisor reaches the abstraction of `s'` from that of `s` in
finitely many steps, with the link relation `CellLinked p.cells` and the same bound. By induction
over the actions from `step_sound`. A design model, not from MLS. -/
theorem run_sound {p : Params} {s s' : State} {acts : List Action} (h : run p s acts = some s') :
    Relation.ReflTransGen (CellSupervisor.Step (CellLinked p.cells) p.bound)
      s.abstract s'.abstract := by
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

/-- The initial state of the executable supervisor at `home` abstracts to the initial state of
the design supervisor at `home`. A design model, not from MLS. -/
theorem abstract_init (home : Waypoint) :
    (State.init home).abstract = CellSupervisor.init home := by
  apply cellState_ext <;> simp [State.abstract, State.init, CellSupervisor.init]

/-- **Refinement.** Every state that the executable supervisor reaches from `State.init p.home`
by a list of accepted actions abstracts to a reachable state of the design supervisor with the
link relation `CellLinked p.cells`, the same age bound and the same home waypoint, so every
invariant proved for the design supervisor holds on it. A design model, not from MLS. -/
theorem reachableState_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) :
    CellSupervisor.ReachableState (CellLinked p.cells) p.bound p.home s.abstract := by
  unfold CellSupervisor.ReachableState
  rw [← abstract_init]
  exact run_sound h

/-- **The age bound on the concrete state.** In every state that the executable supervisor
reaches from `State.init p.home`, the age of the active move is at most the bound. From
`reachableState_of_run` and `CellSupervisor.ReachableState.ageBounded`. A design model, not from
MLS. -/
theorem age_le_bound_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) : s.age ≤ p.bound :=
  (reachableState_of_run h).ageBounded

/-- **Idle means age zero on the concrete state.** In every state that the executable supervisor
reaches from `State.init p.home`, an idle supervisor has age zero. From `reachableState_of_run`
and `CellSupervisor.ReachableState.idleAgeZero`. A design model, not from MLS. -/
theorem age_eq_zero_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) (hidle : s.busy = false) : s.age = 0 :=
  (reachableState_of_run h).idleAgeZero hidle

/-- **Idle means no command on the concrete state.** In every state that the executable
supervisor reaches from `State.init p.home`, an idle supervisor has an empty command list. From
`reachableState_of_run` and `CellSupervisor.ReachableState.idleUncommanded`. A design model, not
from MLS. -/
theorem commanded_eq_nil_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) (hidle : s.busy = false) : s.commanded = [] := by
  have hset := (reachableState_of_run h).idleUncommanded hidle
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro w hw
  have hw' : w ∈ s.abstract.commanded := hw
  rw [hset] at hw'
  exact hw'

/-- **One linked command while busy, on the concrete state.** In every state that the executable
supervisor reaches from `State.init p.home`, a busy supervisor has exactly one commanded
waypoint (every member of the command list is it), and the list search links it to the waypoint
the arm is at. From `reachableState_of_run`, `CellSupervisor.ReachableState.busyCommanded` and
`linked_eq_true_iff`. A design model, not from MLS. -/
theorem exists_commanded_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) (hbusy : s.busy = true) :
    ∃ w, (∀ u, u ∈ s.commanded ↔ u = w) ∧ linked p.cells s.current w = true := by
  obtain ⟨w, hw, hlinked⟩ := (reachableState_of_run h).busyCommanded hbusy
  refine ⟨w, fun u => ?_, (linked_eq_true_iff _ _ _).mpr hlinked⟩
  have hu : u ∈ s.abstract.commanded ↔ u ∈ ({w} : Set Waypoint) := by rw [hw]
  exact hu

/-- **Commanded waypoints are linked, on the concrete state.** In every state that the
executable supervisor reaches from `State.init p.home`, the list search links every commanded
waypoint to the waypoint the arm is at. From `reachableState_of_run`,
`CellSupervisor.ReachableState.commandedLinked` and `linked_eq_true_iff`. A design model, not from
MLS. -/
theorem linked_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) :
    ∀ w ∈ s.commanded, linked p.cells s.current w = true :=
  fun w hw => (linked_eq_true_iff _ _ _).mpr ((reachableState_of_run h).commandedLinked w hw)

/-- **A faulted supervisor is idle, on the concrete state.** In every state that the executable
supervisor reaches from `State.init p.home`, a faulted supervisor is idle. From
`reachableState_of_run` and `CellSupervisor.ReachableState.faultedIdle`. A design model, not from
MLS. -/
theorem busy_eq_false_of_run {p : Params} {acts : List Action} {s : State}
    (h : run p (State.init p.home) acts = some s) (hf : s.faulted = true) : s.busy = false :=
  (reachableState_of_run h).faultedIdle hf

end RoboLean.Cell.Supervisor
